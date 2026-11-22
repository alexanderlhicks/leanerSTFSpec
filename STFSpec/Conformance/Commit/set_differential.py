#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Encoded setter frontend observations and completed nominal projection.

The pinned setter's key conversion, encoding, mutation and separate completion
stages are captured with assertions enabled. Use --write-catalog for the pinned
inputs and --write-historical-catalog for the earlier source evidence.
--self-test uses no reference import and supports Python -O.
"""

import argparse
import base64
import datetime
import hashlib
import importlib.metadata
import json
import marshal
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import tomllib
import traceback
import types
import zipfile

ROOT = Path(__file__).resolve().parents[3]
DEFAULT_SEED = 195
PIN = "59c1473ddfba341babaeca1c97a50e996f639a0b"
HISTORICAL_CATALOG_SHA = "89b64aac00f0afef83e461d51fbc8f79be5de1f2bd3e86cf6c5238b21eab28bf"
FRONTEND_ERRORS = {
    "nondefault-none": ("builtins", "AssertionError", "cannot encode `None`", "mpt_set", 431),
    "missing-storage-root": ("builtins", "AssertionError", "", "mpt_set", 428),
    "unsupported-encoding": (
        "ethereum_rlp.exceptions", "EncodingError",
        "RLP Encoding of type <class 'object'> is not supported", "encode", 87,
    ),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def natural(value):
    require(type(value) is int and value >= 0, "non-natural field")
    return value


def object_pairs(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate field")
        result[key] = value
    return result


def reject_constant(value):
    raise ValueError("nonfinite JSON constant: " + value)


def load_json(text):
    return json.loads(text, object_pairs_hook=object_pairs, parse_constant=reject_constant)


def validate_catalog(payload):
    frozen = load_json(payload)
    require(
        json.dumps(frozen, sort_keys=True) == json.dumps(catalog(), sort_keys=True),
        "catalog must equal the complete frozen generator",
    )
    return frozen


class Reader:
    def __init__(self, values):
        require(type(values) is list, "wire must be list")
        self.values, self.offset = values, 0

    def take(self):
        require(self.offset < len(self.values), "truncated field")
        value = natural(self.values[self.offset])
        self.offset += 1
        return value

    def octets(self, count, bound=256):
        require(count <= len(self.values) - self.offset, "truncated byte field")
        values = [self.take() for _ in range(count)]
        require(all(x < bound for x in values), "out of range field")
        return values

    def array(self, bound=256):
        return self.octets(self.take(), bound)

    def cache(self):
        raw, tag = self.array(), self.take()
        require(tag in (0, 1), "hash option tag")
        return raw, None if tag == 0 else self.octets(32)

    def ref(self):
        tag = self.take()
        require(tag in range(5), "Ref tag")
        if tag == 0:
            return (0,)
        if tag == 1:
            return (1, self.octets(32))
        if tag == 2:
            return (2, self.array(16), self.array(), self.cache())
        if tag == 3:
            path, child = self.array(16), self.ref()
            require(child[0] != 0, "absent extension child")
            return (3, path, child, self.cache())
        count = self.take()
        require(count <= len(self.values) - self.offset, "truncated actual slots")
        return (4, [self.ref() for _ in range(count)], self.array(), self.cache())

    def result(self):
        tag = self.take()
        require(tag in (0, 1), "setter result tag")
        if tag == 0:
            flag = self.take()
            require(flag in (0, 1), "secured result flag")
            return (0, flag, self.ref())
        error = self.take()
        require(error in (0, 1, 2), "TrieError tag")
        if error != 1:
            return (1, error, self.octets(32))
        reason = self.take()
        require(reason in range(13), "malformed tag")
        width = 2 if reason == 11 else 1 if reason in (6, 7, 9, 12) else 0
        return (1, 1, reason, [self.take() for _ in range(width)])

    def finish(self):
        require(self.offset == len(self.values), "trailing fields")


def parse_records(text, count):
    lines = text.splitlines()
    require(len(lines) == count, "missing/trailing records")
    rows = []
    for index, line in enumerate(lines):
        row = load_json(line)
        require(
            type(row) is dict
            and set(row)
            == {
                "case",
                "secured",
                "input",
                "key",
                "encoded",
                "result",
                "recorded",
                "queries",
                "answers",
                "counter",
            },
            "reply fields",
        )
        require(natural(row["case"]) == index, "case order")
        require(type(row["secured"]) is bool, "secured must be Bool")
        for name in ("key", "encoded"):
            if name == "encoded" and row[name] is None:
                continue
            require(
                type(row[name]) is list and all(natural(x) < 256 for x in row[name]),
                "complete raw bytes",
            )
        reader = Reader(row["input"])
        reader.ref()
        reader.finish()
        for name in ("result", "recorded"):
            reader = Reader(row[name])
            result = reader.result()
            reader.finish()
            if result[0] == 0:
                require(result[1] == int(row["secured"]), "supplied result flag")
        require(type(row["queries"]) is type(row["answers"]) is list, "query/answer list")
        require(
            len(row["queries"]) == len(row["answers"]) == natural(row["counter"]),
            "complete query/answer/counter arity",
        )
        for raw, answer in zip(row["queries"], row["answers"]):
            reader = Reader(raw)
            reader.array()
            reader.finish()
            reader = Reader(answer)
            reader.octets(32)
            reader.finish()
        rows.append(row)
    return rows


def reject_resume(arguments):
    """Reject unsupported retained-phase reuse before touching artifacts."""
    require(
        not any(arg.split("=", 1)[0].startswith(("--resume", "--retry")) for arg in arguments),
        "resume/retry is unsupported; use fresh output artifacts",
    )


def resume_cli_tests():
    """Exercise the actual early CLI guard against every removed option."""
    with tempfile.TemporaryDirectory(prefix="set-reuse-control-") as folder:
        root = Path(folder)
        journal = root / "prior.jsonl"
        journal.write_text('{"phase":"complete","driver_sha256":"stale"}\n')
        original = journal.read_bytes()
        output, catalog_path = root / "result.lean", root / "catalog.json"
        controls = []
        for option in ("--resume-journal", "--resume-driver-body", "--retry-observer-case"):
            value = "2" if option == "--retry-observer-case" else str(journal)
            controls.extend([[option, value], [option + "=" + value], [option]])
        controls.extend(
            [
                ["--resume", str(journal)],
                ["--retry", "2"],
                ["--write-catalog", str(catalog_path), "--resume-journal", str(journal)],
                ["--self-test", "--retry-observer-case", "2"],
            ]
        )
        for options in controls:
            argv = [sys.executable, "-I", "-B"]
            if sys.flags.optimize:
                argv.append("-O")
            result = subprocess.run(
                [*argv, str(Path(__file__).resolve()), *options, "--output", str(output)],
                capture_output=True,
            )
            require(
                result.returncode != 0 and b"resume/retry is unsupported" in result.stderr,
                "unsupported reuse CLI accepted",
            )
            require(
                set(root.iterdir()) == {journal} and journal.read_bytes() == original,
                "reuse rejection touched artifacts",
            )
    return len(controls)


def parser_tests():
    h = list(range(32))
    leaf = [2, 1, 15, 2, 0, 255, 2, 193, 128, 1, *h]
    tree = [3, 0, 4, 3, 0, 1, *h, *leaf, 2, 0, 255, 0, 0, 0, 0]
    good = dict(
        case=0,
        secured=True,
        input=tree,
        key=[0, 255],
        encoded=[0, 255],
        result=[0, 1, *leaf],
        recorded=[0, 1, *leaf],
        queries=[[0], [2, 0, 255]],
        answers=[h, h],
        counter=2,
    )
    positive = [
        good,
        dict(
            good,
            secured=False,
            input=[0],
            encoded=None,
            result=[0, 0, 0],
            recorded=[0, 0, 0],
            queries=[],
            answers=[],
            counter=0,
        ),
    ]
    for error in (0, 2):
        positive.append(dict(good, result=[1, error, *h]))
    for reason in range(13):
        fields = [65537, 257] if reason == 11 else [65537] if reason in (6, 7, 9, 12) else []
        positive.append(dict(good, result=[1, 1, reason, *fields]))
    for row in positive:
        require(parse_records(json.dumps(row), 1) == [row], "valid complete setter frame")
    bad = [
        "",
        json.dumps(good) + "\n" + json.dumps(good),
        '{"case":0,"case":0}',
        json.dumps(dict(good, extra=0)),
    ]
    for name in good:
        bad.append(json.dumps({k: v for k, v in good.items() if k != name}))
    for name in ("case", "counter"):
        for value in (True, False, -1, 0.0, None, float("nan"), float("inf")):
            bad.append(json.dumps(dict(good, **{name: value})))
    for value in (0, 1, None, "true"):
        bad.append(json.dumps(dict(good, secured=value)))
    for name in ("input", "result", "recorded", "key", "encoded"):
        for cut in range(len(good[name])):
            if name not in ("key", "encoded"):
                bad.append(json.dumps(dict(good, **{name: good[name][:cut]})))
        if name not in ("key", "encoded"):
            bad.append(json.dumps(dict(good, **{name: good[name] + [0]})))
        for i in range(len(good[name])):
            for value in (True, False, -1, 0.0, None, float("nan"), float("inf")):
                xs = good[name].copy()
                xs[i] = value
                bad.append(json.dumps(dict(good, **{name: xs})))
    for name in ("queries", "answers"):
        for index, original in enumerate(good[name]):
            for cut in range(len(original)):
                xs = [x.copy() for x in good[name]]
                xs[index] = original[:cut]
                bad.append(json.dumps(dict(good, **{name: xs})))
            xs = [x.copy() for x in good[name]]
            xs[index] = original + [0]
            bad.append(json.dumps(dict(good, **{name: xs})))
            for i in range(len(original)):
                for value in (True, False, -1, 0.0, None, float("nan"), float("inf")):
                    xs = [x.copy() for x in good[name]]
                    xs[index][i] = value
                    bad.append(json.dumps(dict(good, **{name: xs})))
    for name, value in (
        ("input", [3, 0, 0, 0, 0]),
        ("result", [0, 2, 0]),
        ("result", [1, 1, 13]),
        ("result", [1, 1, 11, 1]),
        ("queries", [[1, 256], [0]]),
        ("answers", [h]),
        ("key", [256]),
        ("encoded", [256]),
    ):
        bad.append(json.dumps(dict(good, **{name: value})))
    for text in bad:
        try:
            parse_records(text, 1)
        except (ValueError, TypeError, json.JSONDecodeError):
            continue
        raise RuntimeError("invalid setter frame accepted: " + text)
    frozen = catalog()
    valid = json.dumps(frozen, indent=2)
    changed = valid.replace('"case": 0', '"case": false', 1)
    require(load_json(changed) == frozen, "catalogue control must differ only by numeric type")
    require(type(validate_catalog(valid)["cases"][0]["case"]) is int, "valid complete catalogue")
    try:
        validate_catalog(changed)
    except ValueError as error:
        require(str(error) == "catalog must equal the complete frozen generator", "catalogue test")
    else:
        raise RuntimeError("setter catalogue accepted case 0 changed to JSON false")
    resume_cli_tests()
    print(
        json.dumps(
            dict(
                accepted=len(positive), rejected=len(bad), optimized=sys.flags.optimize,
                catalog_case_false_rejected=True,
            )
        )
    )


def historical_catalog():
    return {
        "schema": 1,
        "pin": "e1a316a06fc3d3e0a5da36fdc78580811e9d8a36",
        "cases": [
            {
                "case": 0,
                "family": "O01",
                "secured": False,
                "key": [],
                "default": {"kind": "none"},
                "value": {"kind": "none"},
                "root": None,
                "data_before": [],
                "callback": "none",
                "boundary": None,
                "encoded": None,
                "comparison": "completed projection",
            },
            {
                "case": 1,
                "family": "O01",
                "secured": False,
                "key": [],
                "default": {"kind": "none"},
                "value": {"kind": "none"},
                "root": None,
                "data_before": [{"key": [], "value": {"kind": "bytes", "bytes": [9]}}],
                "callback": "none",
                "boundary": None,
                "encoded": None,
                "comparison": "completed projection",
            },
            {
                "case": 2,
                "family": "O02",
                "secured": False,
                "key": [0],
                "default": {"kind": "none"},
                "value": {"kind": "bytes", "bytes": []},
                "root": None,
                "data_before": [],
                "callback": "none",
                "boundary": None,
                "encoded": [],
                "comparison": "completed projection; _data stores empty value",
            },
            {
                "case": 3,
                "family": "O04-default-empty",
                "secured": False,
                "key": [0],
                "default": {"kind": "bytes", "bytes": []},
                "value": {"kind": "bytes", "bytes": []},
                "root": None,
                "data_before": [],
                "callback": "none",
                "boundary": None,
                "encoded": [],
                "comparison": "completed projection; _data default erasure",
            },
            {
                "case": 4,
                "family": "O03/O05",
                "secured": False,
                "key": [],
                "default": {"kind": "none"},
                "value": {"kind": "bytes", "bytes": [0]},
                "root": None,
                "data_before": [],
                "callback": "none",
                "boundary": None,
                "encoded": [0],
                (
                    'comparison'
                ): (
                    'fresh completed leaf; source key and own completion queries '
                    'separate'
                ),
            },
            {
                "case": 5,
                "family": "O03/O05",
                "secured": False,
                "key": [0],
                "default": {"kind": "none"},
                "value": {"kind": "bytes", "bytes": [255]},
                "root": None,
                "data_before": [],
                "callback": "none",
                "boundary": None,
                "encoded": [255],
                (
                    'comparison'
                ): (
                    'fresh completed leaf; source key and own completion queries '
                    'separate'
                ),
            },
            {
                "case": 6,
                "family": "O03/O05",
                "secured": False,
                "key": [0, 0, 255],
                "default": {"kind": "none"},
                "value": {"kind": "bytes", "bytes": [0, 255, 0]},
                "root": None,
                "data_before": [],
                "callback": "none",
                "boundary": None,
                "encoded": [0, 255, 0],
                (
                    'comparison'
                ): (
                    'fresh completed leaf; source key and own completion queries '
                    'separate'
                ),
            },
            {
                "case": 7,
                "family": "O03/O05",
                "secured": False,
                "key": [
                    0,
                    1,
                    2,
                    3,
                    4,
                    5,
                    6,
                    7,
                    8,
                    9,
                    10,
                    11,
                    12,
                    13,
                    14,
                    15,
                    16,
                    17,
                    18,
                    19,
                    20,
                    21,
                    22,
                    23,
                    24,
                    25,
                    26,
                    27,
                    28,
                    29,
                    30,
                ],
                "default": {"kind": "none"},
                "value": {
                    "kind": "bytes",
                    "bytes": [
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                    ],
                },
                "root": None,
                "data_before": [],
                "callback": "none",
                "boundary": None,
                "encoded": [
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                ],
                (
                    'comparison'
                ): (
                    'fresh completed leaf; source key and own completion queries '
                    'separate'
                ),
            },
            {
                "case": 8,
                "family": "O03/O05",
                "secured": False,
                "key": [
                    0,
                    1,
                    2,
                    3,
                    4,
                    5,
                    6,
                    7,
                    8,
                    9,
                    10,
                    11,
                    12,
                    13,
                    14,
                    15,
                    16,
                    17,
                    18,
                    19,
                    20,
                    21,
                    22,
                    23,
                    24,
                    25,
                    26,
                    27,
                    28,
                    29,
                    30,
                    31,
                ],
                "default": {"kind": "none"},
                "value": {
                    "kind": "bytes",
                    "bytes": [
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                    ],
                },
                "root": None,
                "data_before": [],
                "callback": "none",
                "boundary": None,
                "encoded": [
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                ],
                (
                    'comparison'
                ): (
                    'fresh completed leaf; source key and own completion queries '
                    'separate'
                ),
            },
            {
                "case": 9,
                "family": "O03/O05",
                "secured": False,
                "key": [
                    0,
                    1,
                    2,
                    3,
                    4,
                    5,
                    6,
                    7,
                    8,
                    9,
                    10,
                    11,
                    12,
                    13,
                    14,
                    15,
                    16,
                    17,
                    18,
                    19,
                    20,
                    21,
                    22,
                    23,
                    24,
                    25,
                    26,
                    27,
                    28,
                    29,
                    30,
                    31,
                    32,
                ],
                "default": {"kind": "none"},
                "value": {
                    "kind": "bytes",
                    "bytes": [
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                    ],
                },
                "root": None,
                "data_before": [],
                "callback": "none",
                "boundary": None,
                "encoded": [
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                ],
                (
                    'comparison'
                ): (
                    'fresh completed leaf; source key and own completion queries '
                    'separate'
                ),
            },
            {
                "case": 10,
                "family": "O07-stub",
                "secured": False,
                "key": [0],
                "default": {"kind": "none"},
                "value": {"kind": "none"},
                "root": {
                    "tag": "hashed",
                    "hash": [
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        1,
                        0,
                        1,
                    ],
                },
                "data_before": [],
                "callback": "none",
                "boundary": "stub",
                "encoded": None,
                "comparison": "first original exception/partial map; exact nominal unresolved "
                "adaptation",
            },
            {
                "case": 11,
                "family": "O07-bounds",
                "secured": False,
                "key": [240],
                "default": {"kind": "none"},
                "value": {"kind": "none"},
                "root": {
                    "tag": "branch",
                    "children": [],
                    "value": [255],
                    "enc": {"raw": [], "hash": None},
                },
                "data_before": [],
                "callback": "none",
                "boundary": "selected-index",
                "encoded": None,
                (
                    'comparison'
                ): (
                    'first original IndexError/partial map; selected nominal inde'
                    'x/actual arity'
                ),
            },
            {
                "case": 12,
                "family": "O07-stub",
                "secured": False,
                "key": [0],
                "default": {"kind": "none"},
                "value": {"kind": "bytes", "bytes": []},
                "root": {
                    "tag": "hashed",
                    "hash": [
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        1,
                        0,
                        1,
                    ],
                },
                "data_before": [],
                "callback": "none",
                "boundary": "stub",
                "encoded": [],
                "comparison": "first original exception/partial map; exact nominal unresolved "
                "adaptation",
            },
            {
                "case": 13,
                "family": "O07-bounds",
                "secured": False,
                "key": [240],
                "default": {"kind": "none"},
                "value": {"kind": "bytes", "bytes": []},
                "root": {
                    "tag": "branch",
                    "children": [],
                    "value": [255],
                    "enc": {"raw": [], "hash": None},
                },
                "data_before": [],
                "callback": "none",
                "boundary": "selected-index",
                "encoded": [],
                (
                    'comparison'
                ): (
                    'first original IndexError/partial map; selected nominal inde'
                    'x/actual arity'
                ),
            },
            {
                "case": 14,
                "family": "O07-stub",
                "secured": False,
                "key": [0],
                "default": {"kind": "none"},
                "value": {"kind": "bytes", "bytes": [255]},
                "root": {
                    "tag": "hashed",
                    "hash": [
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        1,
                        0,
                        1,
                    ],
                },
                "data_before": [],
                "callback": "none",
                "boundary": "stub",
                "encoded": [255],
                "comparison": "first original exception/partial map; exact nominal unresolved "
                "adaptation",
            },
            {
                "case": 15,
                "family": "O07-bounds",
                "secured": False,
                "key": [240],
                "default": {"kind": "none"},
                "value": {"kind": "bytes", "bytes": [255]},
                "root": {
                    "tag": "branch",
                    "children": [],
                    "value": [255],
                    "enc": {"raw": [], "hash": None},
                },
                "data_before": [],
                "callback": "none",
                "boundary": "selected-index",
                "encoded": [255],
                (
                    'comparison'
                ): (
                    'first original IndexError/partial map; selected nominal inde'
                    'x/actual arity'
                ),
            },
            {
                "case": 16,
                "family": "O08",
                "secured": False,
                "key": [],
                "default": {"kind": "bytes", "bytes": []},
                "value": {"kind": "none"},
                "root": None,
                "data_before": [],
                "callback": "none",
                "boundary": "nondefault-none",
                "encoded": None,
                "comparison": "source-only encoding assertion after map/key; nominal None is a "
                "distinct preencoded action",
            },
            {
                "case": 17,
                "family": "O09-missing-callback",
                "secured": False,
                "key": [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                "default": {"kind": "none"},
                "value": {
                    "kind": "account",
                    "nonce": 1,
                    "balance": 2,
                    "code_hash": [
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        9,
                    ],
                },
                "root": None,
                "data_before": [],
                "callback": "none",
                "boundary": "missing-callback",
                "comparison": "source-only callback assertion after map/key",
            },
            {
                "case": 18,
                "family": "O09-invalid-address",
                "secured": False,
                "key": [0],
                "default": {"kind": "none"},
                "value": {
                    "kind": "account",
                    "nonce": 1,
                    "balance": 2,
                    "code_hash": [
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        9,
                    ],
                },
                "root": None,
                "data_before": [],
                "callback": "fixed-root",
                "boundary": "invalid-address",
                "comparison": "source-only Address width failure before callback",
            },
            {
                "case": 19,
                "family": "O09-contextual",
                "secured": False,
                "key": [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                "default": {"kind": "none"},
                "value": {
                    "kind": "account",
                    "nonce": 1,
                    "balance": 2,
                    "code_hash": [
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        9,
                    ],
                },
                "root": None,
                "data_before": [],
                "callback": "fixed-root",
                "boundary": None,
                "encoded": [
                    248,
                    68,
                    1,
                    2,
                    160,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    160,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    9,
                ],
                "comparison": "explicit contextual callback bytes and completed projection only",
            },
            {
                "case": 20,
                "family": "O10-unsupported-encoding",
                "secured": False,
                "key": [0],
                "default": {"kind": "none"},
                "value": {"kind": "unsupported-object"},
                "root": None,
                "data_before": [],
                "callback": "none",
                "boundary": "unsupported-encoding",
                "comparison": "source-only RLP failure after map/key, not a nominal error",
            },
            {
                "case": 21,
                "family": "O01",
                "secured": True,
                "key": [],
                "default": {"kind": "none"},
                "value": {"kind": "none"},
                "root": None,
                "data_before": [],
                "callback": "none",
                "boundary": None,
                "encoded": None,
                "comparison": "completed projection",
            },
            {
                "case": 22,
                "family": "O01",
                "secured": True,
                "key": [],
                "default": {"kind": "none"},
                "value": {"kind": "none"},
                "root": None,
                "data_before": [{"key": [], "value": {"kind": "bytes", "bytes": [9]}}],
                "callback": "none",
                "boundary": None,
                "encoded": None,
                "comparison": "completed projection",
            },
            {
                "case": 23,
                "family": "O02",
                "secured": True,
                "key": [0],
                "default": {"kind": "none"},
                "value": {"kind": "bytes", "bytes": []},
                "root": None,
                "data_before": [],
                "callback": "none",
                "boundary": None,
                "encoded": [],
                "comparison": "completed projection; _data stores empty value",
            },
            {
                "case": 24,
                "family": "O04-default-empty",
                "secured": True,
                "key": [0],
                "default": {"kind": "bytes", "bytes": []},
                "value": {"kind": "bytes", "bytes": []},
                "root": None,
                "data_before": [],
                "callback": "none",
                "boundary": None,
                "encoded": [],
                "comparison": "completed projection; _data default erasure",
            },
            {
                "case": 25,
                "family": "O03/O05",
                "secured": True,
                "key": [],
                "default": {"kind": "none"},
                "value": {"kind": "bytes", "bytes": [0]},
                "root": None,
                "data_before": [],
                "callback": "none",
                "boundary": None,
                "encoded": [0],
                (
                    'comparison'
                ): (
                    'fresh completed leaf; source key and own completion queries '
                    'separate'
                ),
            },
            {
                "case": 26,
                "family": "O03/O05",
                "secured": True,
                "key": [0],
                "default": {"kind": "none"},
                "value": {"kind": "bytes", "bytes": [255]},
                "root": None,
                "data_before": [],
                "callback": "none",
                "boundary": None,
                "encoded": [255],
                (
                    'comparison'
                ): (
                    'fresh completed leaf; source key and own completion queries '
                    'separate'
                ),
            },
            {
                "case": 27,
                "family": "O03/O05",
                "secured": True,
                "key": [0, 0, 255],
                "default": {"kind": "none"},
                "value": {"kind": "bytes", "bytes": [0, 255, 0]},
                "root": None,
                "data_before": [],
                "callback": "none",
                "boundary": None,
                "encoded": [0, 255, 0],
                (
                    'comparison'
                ): (
                    'fresh completed leaf; source key and own completion queries '
                    'separate'
                ),
            },
            {
                "case": 28,
                "family": "O03/O05",
                "secured": True,
                "key": [
                    0,
                    1,
                    2,
                    3,
                    4,
                    5,
                    6,
                    7,
                    8,
                    9,
                    10,
                    11,
                    12,
                    13,
                    14,
                    15,
                    16,
                    17,
                    18,
                    19,
                    20,
                    21,
                    22,
                    23,
                    24,
                    25,
                    26,
                    27,
                    28,
                    29,
                    30,
                ],
                "default": {"kind": "none"},
                "value": {
                    "kind": "bytes",
                    "bytes": [
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                    ],
                },
                "root": None,
                "data_before": [],
                "callback": "none",
                "boundary": None,
                "encoded": [
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                ],
                (
                    'comparison'
                ): (
                    'fresh completed leaf; source key and own completion queries '
                    'separate'
                ),
            },
            {
                "case": 29,
                "family": "O03/O05",
                "secured": True,
                "key": [
                    0,
                    1,
                    2,
                    3,
                    4,
                    5,
                    6,
                    7,
                    8,
                    9,
                    10,
                    11,
                    12,
                    13,
                    14,
                    15,
                    16,
                    17,
                    18,
                    19,
                    20,
                    21,
                    22,
                    23,
                    24,
                    25,
                    26,
                    27,
                    28,
                    29,
                    30,
                    31,
                ],
                "default": {"kind": "none"},
                "value": {
                    "kind": "bytes",
                    "bytes": [
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                        255,
                    ],
                },
                "root": None,
                "data_before": [],
                "callback": "none",
                "boundary": None,
                "encoded": [
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                    255,
                ],
                (
                    'comparison'
                ): (
                    'fresh completed leaf; source key and own completion queries '
                    'separate'
                ),
            },
            {
                "case": 30,
                "family": "O03/O05",
                "secured": True,
                "key": [
                    0,
                    1,
                    2,
                    3,
                    4,
                    5,
                    6,
                    7,
                    8,
                    9,
                    10,
                    11,
                    12,
                    13,
                    14,
                    15,
                    16,
                    17,
                    18,
                    19,
                    20,
                    21,
                    22,
                    23,
                    24,
                    25,
                    26,
                    27,
                    28,
                    29,
                    30,
                    31,
                    32,
                ],
                "default": {"kind": "none"},
                "value": {
                    "kind": "bytes",
                    "bytes": [
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                        0,
                        255,
                    ],
                },
                "root": None,
                "data_before": [],
                "callback": "none",
                "boundary": None,
                "encoded": [
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                ],
                (
                    'comparison'
                ): (
                    'fresh completed leaf; source key and own completion queries '
                    'separate'
                ),
            },
            {
                "case": 31,
                "family": "O07-stub",
                "secured": True,
                "key": [0],
                "default": {"kind": "none"},
                "value": {"kind": "none"},
                "root": {
                    "tag": "hashed",
                    "hash": [
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        1,
                        0,
                        1,
                    ],
                },
                "data_before": [],
                "callback": "none",
                "boundary": "stub",
                "encoded": None,
                "comparison": "first original exception/partial map; exact nominal unresolved "
                "adaptation",
            },
            {
                "case": 32,
                "family": "O07-bounds",
                "secured": True,
                "key": [240],
                "default": {"kind": "none"},
                "value": {"kind": "none"},
                "root": {
                    "tag": "branch",
                    "children": [],
                    "value": [255],
                    "enc": {"raw": [], "hash": None},
                },
                "data_before": [],
                "callback": "none",
                "boundary": "selected-index",
                "encoded": None,
                (
                    'comparison'
                ): (
                    'first original IndexError/partial map; selected nominal inde'
                    'x/actual arity'
                ),
            },
            {
                "case": 33,
                "family": "O07-stub",
                "secured": True,
                "key": [0],
                "default": {"kind": "none"},
                "value": {"kind": "bytes", "bytes": []},
                "root": {
                    "tag": "hashed",
                    "hash": [
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        1,
                        0,
                        1,
                    ],
                },
                "data_before": [],
                "callback": "none",
                "boundary": "stub",
                "encoded": [],
                "comparison": "first original exception/partial map; exact nominal unresolved "
                "adaptation",
            },
            {
                "case": 34,
                "family": "O07-bounds",
                "secured": True,
                "key": [240],
                "default": {"kind": "none"},
                "value": {"kind": "bytes", "bytes": []},
                "root": {
                    "tag": "branch",
                    "children": [],
                    "value": [255],
                    "enc": {"raw": [], "hash": None},
                },
                "data_before": [],
                "callback": "none",
                "boundary": "selected-index",
                "encoded": [],
                (
                    'comparison'
                ): (
                    'first original IndexError/partial map; selected nominal inde'
                    'x/actual arity'
                ),
            },
            {
                "case": 35,
                "family": "O07-stub",
                "secured": True,
                "key": [0],
                "default": {"kind": "none"},
                "value": {"kind": "bytes", "bytes": [255]},
                "root": {
                    "tag": "hashed",
                    "hash": [
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        1,
                        0,
                        1,
                    ],
                },
                "data_before": [],
                "callback": "none",
                "boundary": "stub",
                "encoded": [255],
                "comparison": "first original exception/partial map; exact nominal unresolved "
                "adaptation",
            },
            {
                "case": 36,
                "family": "O07-bounds",
                "secured": True,
                "key": [240],
                "default": {"kind": "none"},
                "value": {"kind": "bytes", "bytes": [255]},
                "root": {
                    "tag": "branch",
                    "children": [],
                    "value": [255],
                    "enc": {"raw": [], "hash": None},
                },
                "data_before": [],
                "callback": "none",
                "boundary": "selected-index",
                "encoded": [255],
                (
                    'comparison'
                ): (
                    'first original IndexError/partial map; selected nominal inde'
                    'x/actual arity'
                ),
            },
            {
                "case": 37,
                "family": "O08",
                "secured": True,
                "key": [],
                "default": {"kind": "bytes", "bytes": []},
                "value": {"kind": "none"},
                "root": None,
                "data_before": [],
                "callback": "none",
                "boundary": "nondefault-none",
                "encoded": None,
                "comparison": "source-only encoding assertion after map/key; nominal None is a "
                "distinct preencoded action",
            },
            {
                "case": 38,
                "family": "O09-missing-callback",
                "secured": True,
                "key": [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                "default": {"kind": "none"},
                "value": {
                    "kind": "account",
                    "nonce": 1,
                    "balance": 2,
                    "code_hash": [
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        9,
                    ],
                },
                "root": None,
                "data_before": [],
                "callback": "none",
                "boundary": "missing-callback",
                "comparison": "source-only callback assertion after map/key",
            },
            {
                "case": 39,
                "family": "O09-invalid-address",
                "secured": True,
                "key": [0],
                "default": {"kind": "none"},
                "value": {
                    "kind": "account",
                    "nonce": 1,
                    "balance": 2,
                    "code_hash": [
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        9,
                    ],
                },
                "root": None,
                "data_before": [],
                "callback": "fixed-root",
                "boundary": "invalid-address",
                "comparison": "source-only Address width failure before callback",
            },
            {
                "case": 40,
                "family": "O09-contextual",
                "secured": True,
                "key": [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                "default": {"kind": "none"},
                "value": {
                    "kind": "account",
                    "nonce": 1,
                    "balance": 2,
                    "code_hash": [
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        9,
                    ],
                },
                "root": None,
                "data_before": [],
                "callback": "fixed-root",
                "boundary": None,
                "encoded": [
                    248,
                    68,
                    1,
                    2,
                    160,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    0,
                    255,
                    160,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    9,
                ],
                "comparison": "explicit contextual callback bytes and completed projection only",
            },
            {
                "case": 41,
                "family": "O10-unsupported-encoding",
                "secured": True,
                "key": [0],
                "default": {"kind": "none"},
                "value": {"kind": "unsupported-object"},
                "root": None,
                "data_before": [],
                "callback": "none",
                "boundary": "unsupported-encoding",
                "comparison": "source-only RLP failure after map/key, not a nominal error",
            },
            {
                "case": 42,
                "family": "O06-noop-leaf",
                "secured": False,
                "key": [255],
                "default": {"kind": "none"},
                "value": {"kind": "none"},
                "root": {
                    "tag": "leaf",
                    "path": [0, 0],
                    "value": [0, 255],
                    "enc": {"raw": [], "hash": None},
                },
                "data_before": [],
                "callback": "none",
                "boundary": None,
                "encoded": None,
                "comparison": "visited root cache completed after frontend no-op",
            },
            {
                "case": 43,
                "family": "O06-matching-leaf",
                "secured": False,
                "key": [0],
                "default": {"kind": "none"},
                "value": {"kind": "none"},
                "root": {
                    "tag": "leaf",
                    "path": [0, 0],
                    "value": [0, 255],
                    "enc": {"raw": [], "hash": None},
                },
                "data_before": [],
                "callback": "none",
                "boundary": None,
                "encoded": None,
                "comparison": "successful disappearance projection",
            },
            {
                "case": 44,
                "family": "O07-zero",
                "secured": False,
                "key": [],
                "default": {"kind": "none"},
                "value": {"kind": "none"},
                "root": {
                    "tag": "branch",
                    "children": [],
                    "value": [255],
                    "enc": {"raw": [], "hash": None},
                },
                "data_before": [],
                "callback": "none",
                "boundary": "zero-collapse",
                "encoded": None,
                "comparison": "original reached occupancy assertion versus nominal occupancy0",
            },
            {
                "case": 45,
                "family": "O06-noop-leaf",
                "secured": False,
                "key": [255],
                "default": {"kind": "none"},
                "value": {"kind": "bytes", "bytes": []},
                "root": {
                    "tag": "leaf",
                    "path": [0, 0],
                    "value": [0, 255],
                    "enc": {"raw": [], "hash": None},
                },
                "data_before": [],
                "callback": "none",
                "boundary": None,
                "encoded": [],
                "comparison": "visited root cache completed after frontend no-op",
            },
            {
                "case": 46,
                "family": "O06-matching-leaf",
                "secured": False,
                "key": [0],
                "default": {"kind": "none"},
                "value": {"kind": "bytes", "bytes": []},
                "root": {
                    "tag": "leaf",
                    "path": [0, 0],
                    "value": [0, 255],
                    "enc": {"raw": [], "hash": None},
                },
                "data_before": [],
                "callback": "none",
                "boundary": None,
                "encoded": [],
                "comparison": "successful disappearance projection",
            },
            {
                "case": 47,
                "family": "O07-zero",
                "secured": False,
                "key": [],
                "default": {"kind": "none"},
                "value": {"kind": "bytes", "bytes": []},
                "root": {
                    "tag": "branch",
                    "children": [],
                    "value": [255],
                    "enc": {"raw": [], "hash": None},
                },
                "data_before": [],
                "callback": "none",
                "boundary": "zero-collapse",
                "encoded": [],
                "comparison": "original reached occupancy assertion versus nominal occupancy0",
            },
            {
                "case": 48,
                "family": "O07-index",
                "secured": False,
                "key": [],
                "default": {"kind": "none"},
                "value": {"kind": "none"},
                "root": {
                    "tag": "branch",
                    "children": [
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        {
                            "tag": "leaf",
                            "path": [0],
                            "value": [0],
                            "enc": {"raw": [], "hash": None},
                        },
                    ],
                    "value": [255],
                    "enc": {"raw": [], "hash": None},
                },
                "data_before": [],
                "callback": "none",
                "boundary": "high-survivor-16",
                "encoded": None,
                "comparison": "explicit nonnibble completion boundary; record immediate and later "
                "stages, no equal source payload or completed image",
            },
            {
                "case": 49,
                "family": "O07-stub-before-index",
                "secured": False,
                "key": [],
                "default": {"kind": "none"},
                "value": {"kind": "none"},
                "root": {
                    "tag": "branch",
                    "children": [
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        {
                            "tag": "hashed",
                            "hash": [
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                1,
                                0,
                                1,
                            ],
                        },
                    ],
                    "value": [255],
                    "enc": {"raw": [], "hash": None},
                },
                "data_before": [],
                "callback": "none",
                "boundary": "stub-before-index",
                "encoded": None,
                "comparison": "actual stub exception before source index construction; nominal "
                "unresolved before collapseIndex",
            },
            {
                "case": 50,
                "family": "O07-index",
                "secured": False,
                "key": [],
                "default": {"kind": "none"},
                "value": {"kind": "none"},
                "root": {
                    "tag": "branch",
                    "children": [
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        {
                            "tag": "leaf",
                            "path": [0],
                            "value": [0],
                            "enc": {"raw": [], "hash": None},
                        },
                    ],
                    "value": [255],
                    "enc": {"raw": [], "hash": None},
                },
                "data_before": [],
                "callback": "none",
                "boundary": "high-survivor-255",
                "encoded": None,
                "comparison": "explicit nonnibble completion boundary; record immediate and later "
                "stages, no equal source payload or completed image",
            },
            {
                "case": 51,
                "family": "O07-stub-before-index",
                "secured": False,
                "key": [],
                "default": {"kind": "none"},
                "value": {"kind": "none"},
                "root": {
                    "tag": "branch",
                    "children": [
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        {
                            "tag": "hashed",
                            "hash": [
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                1,
                                0,
                                1,
                            ],
                        },
                    ],
                    "value": [255],
                    "enc": {"raw": [], "hash": None},
                },
                "data_before": [],
                "callback": "none",
                "boundary": "stub-before-index",
                "encoded": None,
                "comparison": "actual stub exception before source index construction; nominal "
                "unresolved before collapseIndex",
            },
            {
                "case": 52,
                "family": "O07-index",
                "secured": False,
                "key": [],
                "default": {"kind": "none"},
                "value": {"kind": "none"},
                "root": {
                    "tag": "branch",
                    "children": [
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        {
                            "tag": "leaf",
                            "path": [0],
                            "value": [0],
                            "enc": {"raw": [], "hash": None},
                        },
                    ],
                    "value": [255],
                    "enc": {"raw": [], "hash": None},
                },
                "data_before": [],
                "callback": "none",
                "boundary": "high-survivor-256",
                "encoded": None,
                "comparison": "explicit nonnibble completion boundary; record immediate and later "
                "stages, no equal source payload or completed image",
            },
            {
                "case": 53,
                "family": "O07-stub-before-index",
                "secured": False,
                "key": [],
                "default": {"kind": "none"},
                "value": {"kind": "none"},
                "root": {
                    "tag": "branch",
                    "children": [
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        {
                            "tag": "hashed",
                            "hash": [
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                0,
                                1,
                                0,
                                1,
                            ],
                        },
                    ],
                    "value": [255],
                    "enc": {"raw": [], "hash": None},
                },
                "data_before": [],
                "callback": "none",
                "boundary": "stub-before-index",
                "encoded": None,
                "comparison": "actual stub exception before source index construction; nominal "
                "unresolved before collapseIndex",
            },
        ],
        "excluded": [
            "Unstable/custom equality or key classes",
            "Aliases/cycles",
            "Arbitrary dirty/cache/source histories",
            "Injected original hash/provider failures",
        ],
        (
            'qualification'
        ): (
            'Fresh original mpt_set cases only after separate ROOT releas'
            'e. No source operation executed to prepare this catalog. Nom'
            'inal None is not nondefault source None. Full _data/default/'
            'encoder/witness/mutable states are observations; only explic'
            'it successful preencoding/provider-premised completed secure'
            'd/root projection is compared.'
        ),
    }


def catalog():
    historical = historical_catalog()
    cases = []
    for old in historical["cases"]:
        boundary = old["boundary"]
        encoded = old.get("encoded")
        family = old["family"]
        if boundary == "invalid-address":
            # The following historical case encodes the same account with the
            # same storage root. The pinned setter accepts the short raw key.
            encoded = historical["cases"][old["case"] + 1]["encoded"]
            boundary = None
            family = "O09-short-account-key"
        elif boundary == "missing-callback":
            boundary = "missing-storage-root"
            family = "O09-missing-storage-root"
        elif family == "O09-contextual":
            family = "O09-supplied-storage-root"
        case = {
            name: old[name] for name in ("case", "secured", "key", "default", "value", "root")
        }
        case.update(
            family=family,
            storage_root=[0, 255] * 16 if old["callback"] == "fixed-root" else None,
            boundary=boundary,
            encoded=encoded,
        )
        cases.append(case)

    account = cases[19]["value"]
    control_root = {
        "tag": "leaf",
        "path": [int(digit, 16) for digit in "6db025fbfccb3ff94f8425d7a893ea703ae9c341acf2d13f24142bfdbdc3fe99"],
        "value": [9, 128],
        "enc": {"raw": [], "hash": None},
    }
    return {
        "schema": 2,
        "pin": PIN,
        "historical_pin": historical["pin"],
        "historical_catalog_sha256": HISTORICAL_CATALOG_SHA,
        "cases": cases,
        "frontend_controls": [
            dict(
                case=54, family="equal-account-default", secured=True, key=[171, 0, 205, 94],
                default=account, value=account, root=control_root, storage_root=None,
                boundary=None, encoded=None,
            ),
            dict(
                case=55, family="nondefault-u256-zero", secured=True, key=[171, 0, 205, 94],
                default={"kind": "u256", "number": 5}, value={"kind": "u256", "number": 0},
                root=control_root, storage_root=None, boundary=None, encoded=[128],
            ),
        ],
        "storage_control": {
            "writes": [[9, 0], [6, 24], [2, 0], [3, 7]],
            "initial": [[9, 123], [6, 123], [2, 123]],
            "order": [6, 3, 9, 2],
            "readback": [None, [24], None, [7]],
        },
        "excluded": historical["excluded"],
        "qualification": (
            "The 54 historical raw inputs are replayed through the pinned assertion-enabled "
            "setter. The comparison uses successfully preencoded nominal inputs under "
            "the clean-entry and provider premises. The source frontend and storage-slot "
            "controls are kept with their observed carrier and effects."
        ),
    }


def stage_plan(catalog_sha):
    return {
        "pin": PIN,
        "catalog_sha256": catalog_sha,
        "stages": [
            "A complete carrier, input value and optional storage root",
            "C original full key query, answer and converted key",
            "D default or encoder route and exact encoding or frontend exception",
            "E mutation, including witness access, consulted cache and immediate state",
            "F separate captured-return completions for successful projections",
            "G complete nominal Id/recording results and Q60 diagnostic adaptations",
            "S original storage-slot traversal and separate encoded readback",
        ],
        "comparison_premises": [
            "Finite acyclic nonaliasing exact original classes and typed supported "
            "values/default equality",
            "Exact original raw key and actual Hash32 full-byte interpretation",
            "Successful original preencoding or separately excluded encoding boundary",
            "Accepted update/delete source "
            "origin/dirty/guard/cache/consulted-embedding/Encodable/Id/host premises",
            "Own materialization stages separate from original frontend/mutation query histories",
        ],
    }


def main():
    reject_resume(sys.argv[1:])
    if sys.argv[1:] == ["--self-test"]:
        parser_tests()
        return 0
    if len(sys.argv) == 3 and sys.argv[1] in ("--write-catalog", "--write-historical-catalog"):
        destination = Path(sys.argv[2])
        historical = sys.argv[1] == "--write-historical-catalog"
        data = historical_catalog() if historical else catalog()
        payload = (json.dumps(data, indent=2) + "\n").encode()
        digest = hashlib.sha256(payload).hexdigest()
        if historical:
            require(digest == HISTORICAL_CATALOG_SHA, "historical catalogue bytes changed")
        with destination.open("xb") as stream:
            stream.write(payload)
        print(
            json.dumps(
                dict(cases=len(data["cases"]), sha256=digest)
            )
        )
        return 0
    require(
        sys.flags.isolated and sys.flags.dont_write_bytecode and not sys.flags.optimize,
        "pinned unoptimized -I -B",
    )
    extra = argparse.ArgumentParser(add_help=False)
    extra.add_argument("--rlp-wheel", type=Path, required=True)
    extra.add_argument("--types-wheel", type=Path, required=True)
    extra.add_argument("--catalog", type=Path, required=True)
    extra.add_argument("--preflight", action="store_true")
    own, remainder = extra.parse_known_args()
    payload = own.catalog.read_bytes()
    frozen = validate_catalog(payload)
    catalog_sha = hashlib.sha256(payload).hexdigest()
    sys.argv = [sys.argv[0]] + remainder
    dst = argparse.ArgumentParser(add_help=False)
    dst.add_argument("--output", type=Path, required=True)
    dst.add_argument("--eels", type=Path, required=True)
    args, _ = dst.parse_known_args(remainder)
    out = args.output.resolve()
    require(
        not out.is_relative_to(ROOT) and not out.is_relative_to(args.eels.resolve()),
        "generated evidence must be outside both repositories",
    )
    require(not out.exists(), "fresh output path")
    log = out.parent / (out.stem + "-commands")
    log.mkdir(exist_ok=False)
    counter = 0

    def command(argv, cwd, stdin=None, env=None):
        nonlocal counter
        counter += 1
        d = log / f"{counter:04d}"
        d.mkdir()
        start = datetime.datetime.now(datetime.timezone.utc).isoformat()
        p = subprocess.run(argv, cwd=cwd, input=stdin, env=env, capture_output=True)
        for name, b in [("stdin", stdin or b""), ("stdout", p.stdout), ("stderr", p.stderr)]:
            (d / name).write_bytes(b)
        (d / "record.json").write_text(
            json.dumps(
                dict(
                    argv=[str(x) for x in argv],
                    cwd=str(cwd),
                    start_utc=start,
                    end_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                    exit=p.returncode,
                ),
                indent=2,
            )
            + "\n"
        )
        return p

    sys.path.insert(0, str(ROOT / "scripts"))
    sys.path.insert(0, str(ROOT / "STFSpec/Conformance/Codec"))
    from differential import Driver
    from rlp_typed_differential import RlpSourceAuth, RlpFreshFinder

    git_env = {
        **{k: v for k, v in os.environ.items() if not k.startswith("GIT_")},
        "GIT_NO_LAZY_FETCH": "1",
        "GIT_TERMINAL_PROMPT": "0",
    }

    class CapturedDriver(Driver):
        def git(self, *argv, input=None, text=False):
            p = command(
                ["git", "--no-replace-objects", "--no-optional-locks", *argv],
                self.eels,
                input,
                git_env,
            )
            require(p.returncode == 0, "reference Git read")
            return p.stdout.decode() if text else p.stdout

    context = CapturedDriver(__doc__, Path(__file__), DEFAULT_SEED)
    require(context.head == frozen["pin"], "catalogue source pin")
    auth = RlpSourceAuth(context)
    sys.meta_path.insert(0, RlpFreshFinder(auth))
    lock = tomllib.loads((context.eels / "uv.lock").read_text())

    def locked_package(distribution):
        name = distribution.metadata["Name"].lower().replace("_", "-")
        versions = tomllib.loads((ROOT / "reference.toml").read_text())["release"]["python_dependencies"]
        require(distribution.version == versions[name], "reference dependency version")
        locked = [
            row for row in lock["package"]
            if row["name"] == name and row["version"] == distribution.version
        ]
        require(len(locked) == 1, "dependency version absent from pinned lock")
        return locked[0]

    dependency = []
    for pkg, wheel in [
        ("ethereum_rlp", own.rlp_wheel.resolve()),
        ("ethereum_types", own.types_wheel.resolve()),
    ]:
        dist = importlib.metadata.distribution(pkg.replace("_", "-"))
        wheel_bytes = wheel.read_bytes()
        digest = hashlib.sha256(wheel_bytes).hexdigest()
        locked_wheels = [
            row for row in locked_package(dist)["wheels"]
            if row["hash"] == "sha256:" + digest and row["size"] == len(wheel_bytes)
        ]
        require(len(locked_wheels) == 1, "raw dependency wheel differs from pinned lock")
        with zipfile.ZipFile(wheel) as z:
            raw = {
                n: z.read(n) for n in z.namelist() if n.startswith(pkg + "/") and n.endswith(".py")
            }
        require(
            set(Path(dist.locate_file(pkg)).rglob("*.py"))
            == {Path(dist.locate_file(n)) for n in raw},
            "installed .py inventory",
        )
        for n, b in raw.items():
            require(Path(dist.locate_file(n)).read_bytes() == b, "installed actual source bytes")
        dependency.append(
            dict(
                package=pkg,
                version=dist.version,
                wheel=str(wheel),
                sha256=digest,
                lock=locked_wheels[0],
                installed={
                    n: dict(
                        path=str(dist.locate_file(n)),
                        sha256=hashlib.sha256(b).hexdigest(),
                        mode=oct(Path(dist.locate_file(n)).stat().st_mode & 0o777),
                    )
                    for n, b in raw.items()
                },
            )
        )
    from ethereum.forks.amsterdam import incremental_mpt as inc
    from ethereum import merkle_patricia_trie as mpt
    from ethereum.crypto import hash as hash_module
    from ethereum_rlp import rlp
    from ethereum_types.bytes import Bytes, Bytes32

    for mod, rel in [
        (inc, "ethereum/forks/amsterdam/incremental_mpt.py"),
        (mpt, "ethereum/merkle_patricia_trie.py"),
        (hash_module, "ethereum/crypto/hash.py"),
    ]:
        context.check_source(mod, rel)
    context.check_source(rlp, "ethereum_rlp/rlp.py", dependency=True)
    classes = (
        inc.MutableLeafNode,
        inc.MutableExtensionNode,
        inc.MutableBranchNode,
        inc.HashedNode,
    )
    from ethereum_types.numeric import Uint, U256
    from ethereum import state as state_module

    context.check_source(state_module, "ethereum/state.py")
    retained_classes = classes + (
        inc.IncrementalMPT,
        inc.Witness,
        inc.Account,
        Uint,
        U256,
        Bytes32,
    )
    function_paths = [
        (inc, n)
        for n in (
            "mpt_set",
            "mpt_set_storage_slots",
            "mpt_get",
            "_mpt_insert_node",
            "_insert_into_leaf",
            "_create_branch_from_two_leaves",
            "_insert_into_extension",
            "_split_extension",
            "_insert_into_branch",
            "_mpt_delete_node",
            "_delete_from_extension",
            "_delete_from_branch",
            "_collapse_branch",
            "_record_witness",
            "_compute_node_hash_and_rlp",
            "_encode_mutable_node",
            "_encode_mutable_node_to_extended",
            "_invalidate_hash",
        )
    ] + [
        (mpt, "bytes_to_nibble_list"),
        (mpt, "nibble_list_to_compact"),
        (mpt, "encode_node"),
        (mpt, "encode_account"),
        (hash_module, "keccak256"),
        (rlp, "encode"),
        (rlp, "decode"),
    ]
    functions = tuple(getattr(mod, name) for mod, name in function_paths)
    held = [(id(f), id(f.__code__)) for f in functions]

    def code_data(c):
        def const(x):
            if isinstance(x, types.CodeType):
                return code_data(x)
            if isinstance(x, bytes):
                return dict(bytes=list(x))
            if isinstance(x, tuple):
                return [const(y) for y in x]
            return dict(type=type(x).__name__, repr=repr(x))

        return dict(
            bytecode=list(c.co_code),
            names=list(c.co_names),
            varnames=list(c.co_varnames),
            freevars=list(c.co_freevars),
            cellvars=list(c.co_cellvars),
            constants=[const(x) for x in c.co_consts],
            argcount=c.co_argcount,
            posonlyargcount=c.co_posonlyargcount,
            kwonlyargcount=c.co_kwonlyargcount,
            flags=c.co_flags,
            exceptiontable=list(c.co_exceptiontable),
        )

    def identity():
        context.check_clean()
        context.check_dependency()
        auth.check()
        require(
            classes
            == (
                inc.MutableLeafNode,
                inc.MutableExtensionNode,
                inc.MutableBranchNode,
                inc.HashedNode,
            ),
            "class replaced",
        )
        require(
            functions == tuple(getattr(mod, name) for mod, name in function_paths),
            "callable replaced",
        )
        require(
            inc.encode_node is mpt.encode_node
            and inc.keccak256 is hash_module.keccak256
            and inc.bytes_to_nibble_list is mpt.bytes_to_nibble_list,
            "original global alias replaced",
        )
        require(
            retained_classes
            == classes + (inc.IncrementalMPT, inc.Witness, inc.Account, Uint, U256, Bytes32),
            "carrier/value class replaced",
        )
        require(held == [(id(f), id(f.__code__)) for f in functions], "held code replaced")
        require(Bytes is bytes and hash_module.Hash32 is Bytes32, "Bytes/Hash32 actual class")
        return dict(
            pin=context.head,
            original_index=context.git("ls-files", "--stage", "-z").decode(),
            original_status=context.git("status", "--porcelain", "--untracked-files=all").decode(),
            original_tree=context.git("ls-tree", "-rz", context.head).decode(),
            executable=sys.executable,
            version=sys.version,
            dependencies=dependency,
            classes=[
                dict(
                    module=c.__module__,
                    name=c.__qualname__,
                    id=id(c),
                    methods={
                        n: dict(
                            function_id=id(f),
                            code_id=id(f.__code__),
                            code_identity_v2=hashlib.sha256(
                                marshal.dumps(f.__code__, 2)
                            ).hexdigest(),
                            semantic_code=code_data(f.__code__),
                        )
                        for n, f in c.__dict__.items()
                        if type(f) is types.FunctionType
                    },
                )
                for c in retained_classes
            ],
            functions=[
                dict(
                    module=f.__module__,
                    name=f.__qualname__,
                    function_id=id(f),
                    code_id=id(f.__code__),
                    filename=f.__code__.co_filename,
                    firstline=f.__code__.co_firstlineno,
                    code_identity_v2=hashlib.sha256(marshal.dumps(f.__code__, 2)).hexdigest(),
                    semantic_code=code_data(f.__code__),
                )
                for f in functions
            ],
        )

    def inputs(tag):
        dest = out.parent / (out.stem + "-inputs-" + tag)
        dest.mkdir()
        rows = []
        for name in [
            "src/ethereum/forks/amsterdam/incremental_mpt.py",
            "src/ethereum/merkle_patricia_trie.py",
            "src/ethereum/crypto/hash.py",
            "src/ethereum/state.py",
            "uv.lock",
        ]:
            p = context.eels / name
            b = p.read_bytes()
            oid = context.oracle_blobs[name]
            actual = command(
                ["git", "--no-replace-objects", "--no-optional-locks", "cat-file", "blob", oid],
                context.eels,
                env=git_env,
            )
            mode = command(
                [
                    "git",
                    "--no-replace-objects",
                    "--no-optional-locks",
                    "ls-files",
                    "--stage",
                    name,
                ],
                context.eels,
                env=git_env,
            )
            require(
                actual.returncode == mode.returncode == 0 and actual.stdout == b,
                "actual original blob bytes",
            )
            q = dest / name
            q.parent.mkdir(parents=True, exist_ok=True)
            q.write_bytes(b)
            rows.append(
                dict(
                    path=name,
                    blob=oid,
                    size=len(b),
                    sha256=hashlib.sha256(b).hexdigest(),
                    fs_mode=oct(p.stat().st_mode & 0o777),
                    git_index=mode.stdout.decode(),
                )
            )
        for entry in dependency:
            p = Path(entry["wheel"])
            b = p.read_bytes()
            require(hashlib.sha256(b).hexdigest() == entry["sha256"], "raw wheel changed")
            (dest / p.name).write_bytes(b)
            rows.append(
                dict(
                    path=p.name,
                    size=len(b),
                    sha256=hashlib.sha256(b).hexdigest(),
                    fs_mode=oct(p.stat().st_mode & 0o777),
                )
            )
            with zipfile.ZipFile(p) as z:
                for info in z.infolist():
                    if info.is_dir():
                        continue
                    data = z.read(info)
                    q = dest / p.stem / info.filename
                    q.parent.mkdir(parents=True, exist_ok=True)
                    q.write_bytes(data)
                    rows.append(
                        dict(
                            path=p.stem + "/" + info.filename,
                            size=len(data),
                            sha256=hashlib.sha256(data).hexdigest(),
                            zip_external_attr=info.external_attr,
                        )
                    )
            for name, meta in entry["installed"].items():
                data = Path(meta["path"]).read_bytes()
                require(
                    hashlib.sha256(data).hexdigest() == meta["sha256"], "installed code changed"
                )
                q = dest / "installed" / name
                q.parent.mkdir(parents=True, exist_ok=True)
                q.write_bytes(data)
                rows.append(
                    dict(
                        path="installed/" + name,
                        source_path=meta["path"],
                        size=len(data),
                        sha256=hashlib.sha256(data).hexdigest(),
                        fs_mode=oct(Path(meta["path"]).stat().st_mode & 0o777),
                    )
                )
        (dest / "manifest.json").write_text(json.dumps(rows, indent=2) + "\n")
        return rows

    def file_identity(path):
        p = Path(path)
        data = p.read_bytes()
        return dict(
            path=str(p),
            resolved=str(p.resolve()),
            size=len(data),
            sha256=hashlib.sha256(data).hexdigest(),
            mode=oct(p.stat().st_mode & 0o777),
        )

    def runtime_identity():
        crypto = importlib.metadata.distribution("pycryptodome")
        crypto_lock = locked_package(crypto)
        crypto_entries = {}
        records = []
        for entry in crypto.files or []:
            p = Path(crypto.locate_file(entry)).absolute()
            if entry.name == "RECORD":
                records.append(file_identity(p))
            if entry.parts and entry.parts[0] == "Crypto" and entry.hash is not None:
                data = p.read_bytes()
                require(
                    entry.hash.mode == "sha256" and entry.size == len(data), "crypto RECORD width"
                )
                digest = (
                    base64.urlsafe_b64encode(hashlib.sha256(data).digest()).decode().rstrip("=")
                )
                require(digest == entry.hash.value, "actual crypto RECORD bytes")
                crypto_entries[str(p)] = file_identity(p)
        require(len(records) == 1 and crypto_entries, "crypto RECORD/package inventory")
        loaded = []
        for name, module in sorted(sys.modules.items()):
            origin = getattr(module, "__file__", None)
            if origin is None or not Path(origin).is_file():
                continue
            p = Path(origin).absolute()
            if name.split(".", 1)[0] in ("ethereum", "ethereum_types", "ethereum_rlp", "Crypto"):
                require(p.resolve() == p, "loaded source alias")
                if name.startswith("ethereum.") or name == "ethereum":
                    relative = p.relative_to(context.eels).as_posix()
                    require(relative in context.oracle_blobs, "loaded original source inventory")
                    require(
                        context.git("hash-object", "--stdin", "--no-filters", input=p.read_bytes())
                        .decode()
                        .strip()
                        == context.oracle_blobs[relative],
                        "loaded original current bytes",
                    )
                loaded.append(dict(module=name, **file_identity(p)))
        mapped = []
        for line in Path("/proc/self/maps").read_text().splitlines():
            path = line.split()[-1]
            if path.startswith("/") and (
                "Crypto/" in path or "_hashlib" in path or "libcrypto" in path
            ):
                require(Path(path).is_file(), "actual mapped crypto file")
                entry = file_identity(path)
                if "Crypto/" in path:
                    require(
                        path in crypto_entries and entry == crypto_entries[path],
                        "mapped crypto authenticated RECORD",
                    )
                if entry not in mapped:
                    mapped.append(entry)
        require(mapped, "actual crypto backend map")
        startup = [file_identity(context.eels / ".venv/pyvenv.cfg")]
        import site

        for folder in site.getsitepackages():
            for p in sorted(Path(folder).glob("*.pth")):
                startup.append(file_identity(p))
        for name in ("sitecustomize", "usercustomize", "site", "_hashlib", "ssl"):
            module = sys.modules.get(name)
            p = getattr(module, "__file__", None)
            if p and Path(p).is_file():
                startup.append(file_identity(p))
        return dict(
            executable=file_identity(sys.executable),
            resolved_executable=file_identity(Path(sys.executable).resolve()),
            version=sys.version,
            prefix=sys.prefix,
            base_prefix=sys.base_prefix,
            flags=repr(sys.flags),
            startup=startup,
            sys_path=list(sys.path),
            loaded=loaded,
            crypto_version=crypto.version,
            crypto_lock=crypto_lock,
            crypto_RECORD=records,
            crypto_files=crypto_entries,
            mapped_crypto=mapped,
            use_hashlib=hash_module._USE_HASHLIB,
            actual_digest=dict(
                id=id(hash_module._keccak256_digest),
                code_identity_v2=hashlib.sha256(
                    marshal.dumps(hash_module._keccak256_digest.__code__, 2)
                ).hexdigest(),
                code=code_data(hash_module._keccak256_digest.__code__),
            ),
        )

    before = identity()
    before["runtime"] = runtime_identity()
    before["catalog_sha256"] = catalog_sha
    before["candidate_inputs"] = [
        file_identity(ROOT / name)
        for name in (
            "reference.toml",
            "STFSpec/Commit/Set.lean",
            "STFSpec/Conformance/Commit/SetGuards.lean",
            "STFSpec/Conformance/Commit/SetCallerProofs.lean",
            "STFSpec/Conformance/Commit/set_differential.py",
            "scripts/differential.py",
            "STFSpec/Conformance/Codec/rlp_typed_differential.py",
        )
    ]
    before_inputs = inputs("before")
    out.with_suffix(".before-identity.json").write_text(json.dumps(before, indent=2) + "\n")
    if own.preflight:
        after = identity()
        after["runtime"] = runtime_identity()
        require(before["runtime"] == after["runtime"], "preflight runtime identity changed")
        out.with_suffix(".preflight.json").write_text(
            json.dumps(
                dict(
                    schema=2,
                    catalog_sha256=catalog_sha,
                    cases=len(frozen["cases"]),
                    scope=frozen["qualification"],
                    stages=stage_plan(catalog_sha),
                    candidate_inputs=before["candidate_inputs"],
                    before=before,
                    after=after,
                    source_inputs=before_inputs,
                    original_protocol_executed=False,
                ),
                indent=2,
            )
            + "\n"
        )
        print(
            json.dumps(
                dict(
                    preflight=True,
                    cases=len(frozen["cases"]),
                    catalog_sha256=catalog_sha,
                    path=str(out.with_suffix(".preflight.json")),
                )
            )
        )
        return 0

    origin_labels = {}

    def label(node):
        return origin_labels.setdefault(id(node), (node, len(origin_labels)))[1]

    def view(node):
        if node is None:
            return dict(tag=0)
        if type(node) is classes[3]:
            return dict(tag=1, hash=list(node._hash), origin=label(node))
        require(type(node) in classes[:3] and type(node._dirty) is bool, "actual node class/dirty")
        fields = dict(
            raw=None if node._rlp is None else list(node._rlp),
            hash=None if node._hash is None else list(node._hash),
            dirty=node._dirty,
            origin=label(node),
        )
        if type(node) is classes[0]:
            return dict(tag=2, path=list(node.rest_of_key), value=list(node.value), **fields)
        if type(node) is classes[1]:
            return dict(tag=3, path=list(node.key_segment), child=view(node.child), **fields)
        return dict(
            tag=4, children=[view(c) for c in node.children], value=list(node.value), **fields
        )

    def build(node):
        if node is None:
            return None
        tag = node["tag"]
        if tag == "hashed":
            return inc.HashedNode(Bytes32(bytes(node["hash"])))
        # This bounded entry interpretation is explicit: empty nominal raw represents
        # absent source raw, with absent hash and clean dirty flag. It is not a
        # global source admission or arbitrary dirty/cache/history theorem.
        enc = node["enc"]
        common = dict(
            _rlp=None if not enc["raw"] else Bytes(enc["raw"]),
            _hash=None if enc["hash"] is None else Bytes32(bytes(enc["hash"])),
            _dirty=False,
        )
        if tag == "leaf":
            return inc.MutableLeafNode(Bytes(node["path"]), Bytes(node["value"]), **common)
        if tag == "ext":
            return inc.MutableExtensionNode(Bytes(node["path"]), build(node["child"]), **common)
        return inc.MutableBranchNode(
            [build(c) for c in node["children"]], Bytes(node["value"]), **common
        )

    def build_value(value):
        if value["kind"] == "none":
            return None
        if value["kind"] == "bytes":
            return Bytes(value["bytes"])
        if value["kind"] == "u256":
            return U256(value["number"])
        if value["kind"] == "account":
            return inc.Account(
                nonce=Uint(value["nonce"]),
                balance=U256(value["balance"]),
                code_hash=Bytes32(bytes(value["code_hash"])),
            )
        require(value["kind"] == "unsupported-object", "frozen value kind")
        return object()

    def value_view(value):
        if value is None:
            return dict(kind="none", type="builtins.NoneType")
        if type(value) is bytes:
            return dict(kind="bytes", bytes=list(value), type="builtins.bytes")
        if type(value) is U256:
            return dict(kind="u256", number=int(value), type="ethereum_types.numeric.U256")
        if type(value) is inc.Account:
            return dict(
                kind="account",
                nonce=int(value.nonce),
                balance=int(value.balance),
                code_hash=list(value.code_hash),
                type=type(value).__module__ + "." + type(value).__qualname__,
            )
        return dict(
            kind="unsupported",
            type=type(value).__module__ + "." + type(value).__qualname__,
            repr=repr(value),
        )

    def carrier_view(state):
        return dict(
            secured=state.secured,
            root=view(state.root_node),
            default=value_view(state.default),
            witness=[
                dict(hash=list(h), raw=list(raw))
                for h, raw in state.witness.accessed_nodes.items()
            ],
        )

    def arr(values):
        return [len(values), *values]

    def wire(node):
        tag = node["tag"]
        if tag == 0:
            return [0]
        if tag == 1:
            return [1, *node["hash"]]
        enc = arr(node["raw"] or []) + ([0] if node["hash"] is None else [1, *node["hash"]])
        if tag == 2:
            return [2, *arr(node["path"]), *arr(node["value"]), *enc]
        if tag == 3:
            return [3, *arr(node["path"]), *wire(node["child"]), *enc]
        return [
            4,
            len(node["children"]),
            *[x for c in node["children"] for x in wire(c)],
            *arr(node["value"]),
            *enc,
        ]

    def expression(node):
        def bs(xs):
            return "(bytes [" + ",".join(map(str, xs)) + "])"

        def hs(xs):
            return (
                "(Hash32.ofBytes32 (FixedBytes.ofNat "
                + str(int.from_bytes(bytes(xs), "big"))
                + "))"
            )

        if node["tag"] == 0:
            return "none"
        if node["tag"] == 1:
            return "some (.hashed " + hs(node["hash"]) + ")"
        enc = (
            "(Enc.mk "
            + bs(node["raw"] or [])
            + " "
            + ("none" if node["hash"] is None else "(some " + hs(node["hash"]) + ")")
            + ")"
        )
        path = "(path [" + ",".join(map(str, node.get("path", []))) + "])"
        if node["tag"] == 2:
            return "some (.leaf " + path + " " + bs(node["value"]) + " " + enc + ")"
        if node["tag"] == 3:
            return "some (.ext " + path + " (" + expression(node["child"])[5:] + ") " + enc + ")"
        return (
            "some (.branch #["
            + ",".join(expression(c) for c in node["children"])
            + "] "
            + bs(node["value"])
            + " "
            + enc
            + ")"
        )

    journal = out.with_suffix(".source-journal.jsonl")
    with journal.open("x"):
        pass
    driver_sha = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()

    def record(row):
        row = dict(row, pin=context.head, catalog_sha256=catalog_sha, driver_sha256=driver_sha)
        with journal.open("a") as stream:
            stream.write(json.dumps(row) + "\n")
            stream.flush()
            os.fsync(stream.fileno())

    def exception_view(exception):
        return dict(
            module=type(exception).__module__,
            name=type(exception).__qualname__,
            message=str(exception),
            args=[dict(type=type(value).__name__, repr=repr(value)) for value in exception.args],
        )

    def assert_exception(error, expected):
        module, name, message, function, line = expected
        require(
            error is not None
            and (error["module"], error["name"], error["message"], error["function"], error["line"])
            == expected
            and error["args"] == ([dict(type="str", repr=repr(message))] if message else []),
            f"original exception at {module}.{function}:{line} ({name})",
        )

    def nibble_path(raw):
        return [digit for byte in raw for digit in (byte // 16, byte % 16)]

    guards = (ROOT / "STFSpec/Conformance/Commit/SetGuards.lean").read_text()
    observers = guards.split("-- BEGIN complete structural observers\n", 1)[1].split(
        "-- END complete structural observers", 1
    )[0]
    lean_header = (
        "import STFSpec.Commit.Set\nopen STFSpec.Base STFSpec.Hash STFSpec.Commit\n"
        + observers
        + (
            '\nprivate abbrev SourceTrace := List (ByteArray × Hash32)\npri'
            'vate abbrev sourceQuery : KeccakQuery (StateM SourceTrace) :'
            '=\n  ⟨fun raw s => let h := keccak256 raw; (h,s ++ [(raw,h)])'
            '⟩\nprivate def emitSource (secured : Bool) (root : Ref) (key '
            ': ByteArray)\n    (encoded : Option ByteArray) : IO Unit := d'
            'o\n  let t := IncrementalMPT.mk secured root\n  let pureResult'
            ' := mptSet (m := Id) t key encoded\n  let (recorded,s) := (@m'
            'ptSet (StateM SourceTrace) inferInstance sourceQuery t key e'
            'ncoded).run []\n  let ev := match encoded with\n    | none => '
            '"null"\n    | some v => toString (v.data.toList.map UInt8.toN'
            'at)\n  let flag := if secured then "true" else "false"\n  IO.p'
            'rintln s!"\\{\\"case\\":0,\\"secured\\":{flag},\\"input\\":{wireRef'
            ' root},\\"key\\":{key.data.toList.map UInt8.toNat},\\"encoded\\"'
            ':{ev},\\"result\\":{wireResult pureResult},\\"recorded\\":{wireR'
            'esult recorded},\\"queries\\":{s.map (fun p => wireBytes p.1)}'
            ',\\"answers\\":{s.map (fun p => wireHash p.2)},\\"counter\\":{s.'
            'length}}"\n'
        )
    )
    observations = []
    mutation_codes = {
        getattr(inc, n).__code__
        for n in (
            "_mpt_insert_node",
            "_insert_into_leaf",
            "_create_branch_from_two_leaves",
            "_insert_into_extension",
            "_split_extension",
            "_insert_into_branch",
            "_mpt_delete_node",
            "_delete_from_extension",
            "_delete_from_branch",
            "_collapse_branch",
        )
    }
    return_codes = {inc._mpt_insert_node.__code__, inc._mpt_delete_node.__code__}
    codes = {f.__code__: f.__module__ + "." + f.__qualname__ for f in functions}
    frontend_controls = []
    for descriptor in frozen["cases"] + frozen["frontend_controls"]:
        index = descriptor["case"]
        boundary = descriptor["boundary"]
        frontend_control = index >= len(frozen["cases"])
        origin_labels.clear()
        root = build(descriptor["root"])
        key = Bytes(descriptor["key"])
        default, value = build_value(descriptor["default"]), build_value(descriptor["value"])
        state = inc.IncrementalMPT(secured=descriptor["secured"], default=default, root_node=root)
        storage_root = (
            None if descriptor["storage_root"] is None else Bytes32(bytes(descriptor["storage_root"]))
        )
        initial_carrier = carrier_view(state)
        initial_value = value_view(value)
        source_input = view(root)
        events, calls, visited, completions = [], [], [], []
        actual_path, actual_encoding, error, completion_error = None, None, None, None
        stage = "original"

        def root_argument(root):
            if root is None:
                return None
            require(type(root) is Bytes32, "actual storage root class")
            return dict(type="ethereum_types.bytes.Bytes32", bytes=list(root))

        def phase(frame):
            if stage.startswith("F-"):
                return stage
            current = frame
            while current is not None:
                if current.f_code in mutation_codes:
                    return "E-mutation"
                if (
                    current.f_code is mpt.encode_node.__code__
                    or current.f_code is mpt.encode_account.__code__
                ):
                    return "D-encoding"
                if current.f_code is inc.mpt_set.__code__:
                    if current.f_lineno >= 435:
                        return "E-mutation"
                    if current.f_lineno >= 425:
                        return "D-encoding"
                    if current.f_lineno >= 420:
                        return "C-key"
                    return "A-entry"
                current = current.f_back
            return "C-key"

        def trace(frame, event, arg):
            nonlocal actual_path, actual_encoding
            if frame.f_code is hash_module.keccak256.__code__:
                if event == "call":
                    calls.append(
                        dict(
                            stage=phase(frame),
                            ordinal=len(calls),
                            preimage=list(frame.f_locals["buffer"]),
                            answer=None,
                        )
                    )
                elif event == "return":
                    calls[-1]["answer"] = None if arg is None else list(arg)
            if (
                frame.f_code is inc.mpt_set.__code__
                and event == "line"
                and frame.f_lineno in (425, 426, 428, 429, 431, 433, 435)
            ):
                stages = {
                    425: "C-converted",
                    426: "D-default",
                    428: "D-account-root-check",
                    429: "D-account-encode",
                    431: "D-nondefault-none",
                    433: "D-value-encode",
                    435: "D-encoded",
                }
                item = dict(
                    stage=stages[frame.f_lineno],
                    file=frame.f_code.co_filename,
                    line=frame.f_lineno,
                    carrier=carrier_view(state),
                )
                if frame.f_lineno == 425:
                    actual_path = list(frame.f_locals["nibble_key"])
                    item["path"] = actual_path
                if frame.f_lineno == 435:
                    actual_encoding = list(frame.f_locals["encoded_value"])
                    item["encoded"] = actual_encoding
                events.append(item)
            if (
                frame.f_code is inc._collapse_branch.__code__
                and event == "line"
                and frame.f_lineno in (790, 791)
            ):
                events.append(
                    dict(
                        stage=phase(frame), function=codes[frame.f_code], event=event,
                        file=frame.f_code.co_filename, line=frame.f_lineno,
                        index=frame.f_locals["idx"], child=view(frame.f_locals["child"]),
                        carrier=carrier_view(state),
                    )
                )
            if frame.f_code in codes and event in ("call", "return", "exception"):
                item = dict(
                    stage=phase(frame),
                    function=codes[frame.f_code],
                    event=event,
                    file=frame.f_code.co_filename,
                    line=frame.f_lineno,
                    carrier=carrier_view(state),
                )
                if "node" in frame.f_locals:
                    node_value = frame.f_locals["node"]
                    if node_value is None or type(node_value) in classes:
                        item["node"] = view(node_value)
                    elif frame.f_code is mpt.encode_node.__code__:
                        item["encoder_value"] = value_view(node_value)
                        item["storage_root"] = root_argument(frame.f_locals["storage_root"])
                if frame.f_code is inc.mpt_set.__code__:
                    item["storage_root"] = root_argument(frame.f_locals["storage_root"])
                if frame.f_code in mutation_codes and "key" in frame.f_locals:
                    item["key"] = list(frame.f_locals["key"])
                    item["level"] = int(frame.f_locals.get("level", 0))
                    if "value" in frame.f_locals:
                        item["value"] = list(frame.f_locals["value"])
                if event == "return" and frame.f_code in return_codes:
                    item["returned"] = view(arg)
                    if arg is not None:
                        visited.append(arg)
                if event == "exception":
                    item["exception"] = exception_view(arg[1])
                events.append(item)
            return trace

        def captured_error(exception):
            deepest = traceback.extract_tb(exception.__traceback__)[-1]
            return dict(
                exception_view(exception),
                function=deepest.name,
                file=deepest.filename,
                line=deepest.lineno,
                traceback=traceback.format_exc(),
            )

        record(
            dict(
                phase="before",
                case=index,
                descriptor=descriptor,
                carrier=initial_carrier,
                value=initial_value,
                storage_root=root_argument(storage_root),
            )
        )
        previous_trace = sys.gettrace()
        sys.settrace(trace)
        try:
            try:
                returned = inc.mpt_set(state, key, value, storage_root)
            except Exception as exception:
                error = captured_error(exception)
            else:
                require(returned is None, "original setter returns None")
            immediate = carrier_view(state)
            if error is None and boundary is None and not frontend_control:
                try:
                    for ordinal, node in enumerate(visited):
                        stage = "F-separate-own-completion-" + str(ordinal)
                        item = dict(
                            stage=stage,
                            origin=label(node),
                            before=view(node),
                            carrier_before=carrier_view(state),
                        )
                        returned_hash, returned_raw = inc._compute_node_hash_and_rlp(node)
                        item.update(
                            after=view(node),
                            carrier_after=carrier_view(state),
                            raw=list(returned_raw),
                            hash=None if returned_hash is None else list(returned_hash),
                        )
                        completions.append(item)
                except Exception as exception:
                    completion_error = dict(captured_error(exception), stage=stage)
        finally:
            sys.settrace(previous_trace)
        row = dict(
            phase="original-returned",
            case=index,
            descriptor=descriptor,
            input=source_input,
            before=initial_carrier,
            before_value=initial_value,
            storage_root=root_argument(storage_root),
            immediate=immediate,
            after=carrier_view(state),
            actual_path=actual_path,
            actual_encoding=actual_encoding,
            events=events,
            queries=calls,
            materializations=completions,
            error=error,
            completion_error=completion_error,
        )
        record(row)
        key_calls = [q for q in row["queries"] if q["stage"] == "C-key"]
        require(
            len(key_calls) == int(descriptor["secured"]), "one original full key query iff secured"
        )
        if key_calls:
            require(
                key_calls[0]["preimage"] == descriptor["key"]
                and len(key_calls[0]["answer"] or []) == 32,
                "actual complete original key preimage/answer before encoding/dispatch",
            )
        expected_path = nibble_path(key_calls[0]["answer"] if key_calls else descriptor["key"])
        require(row["actual_path"] == expected_path, "complete original high-before-low key")
        require(
            immediate["secured"] is descriptor["secured"]
            and immediate["default"] == initial_carrier["default"],
            "original secured/default fields retained",
        )

        frontend_lines = [event["line"] for event in events if "function" not in event]
        default_route = descriptor["default"] == descriptor["value"]
        if default_route:
            expected_lines = [425, 426, 435]
        elif boundary == "missing-storage-root":
            expected_lines = [425, 428]
        elif boundary == "nondefault-none":
            expected_lines = [425, 431]
        elif boundary == "unsupported-encoding":
            expected_lines = [425, 433]
        elif type(value) is inc.Account:
            expected_lines = [425, 428, 429, 435]
        else:
            expected_lines = [425, 433, 435]
        require(frontend_lines == expected_lines, "original key/default/encoding route")

        if boundary in FRONTEND_ERRORS:
            assert_exception(error, FRONTEND_ERRORS[boundary])
            require(
                actual_encoding is None and immediate == initial_carrier
                and not any(event["stage"] == "E-mutation" for event in events),
                "frontend exception before mutation with all carrier fields retained",
            )
            row = dict(
                row,
                phase="complete",
                comparison=False,
                actual=None,
                qualification="Original source frontend exception.",
            )
            record(row)
            observations.append(row)
            continue
        require(
            row["actual_encoding"] == (descriptor["encoded"] or []),
            "exact frozen preencoding bytes",
        )
        if storage_root is not None:
            fields = rlp.decode(bytes(actual_encoding))
            require(
                fields == [value.nonce.to_be_bytes(), value.balance.to_be_bytes(), storage_root,
                           value.code_hash],
                "all four original encoded account fields",
            )
            row["decoded_account"] = [list(field) for field in fields]

        dispatch = inc._mpt_insert_node if actual_encoding else inc._mpt_delete_node
        selected = next(event for event in events if event["stage"] == "E-mutation"
                        and event["event"] == "call")
        require(
            selected["function"] == codes[dispatch.__code__]
            and selected["key"] == expected_path
            and selected["level"] == 0
            and selected["node"] == source_input
            and selected.get("value") == (actual_encoding or None),
            "original mutation entry with full input path, value and carrier root",
        )
        if boundary is None:
            require(
                error is None and completion_error is None,
                "unexpected frontend/provider/materialization failure",
            )
        elif boundary == "stub":
            assert_exception(error, (
                "builtins", "AssertionError", "HashedNode cannot be invalidated", "_invalidate_hash", 236,
            ))
        elif boundary == "stub-before-index":
            assert_exception(error, (
                "builtins", "AssertionError", "HashedNode cannot be witnessed", "_record_witness", 248,
            ))
        elif boundary == "zero-collapse":
            assert_exception(error, ("builtins", "AssertionError", "", "_collapse_branch", 786))
        elif boundary == "selected-index":
            function, line = (
                ("_insert_into_branch", 664) if actual_encoding else ("_delete_from_branch", 761)
            )
            assert_exception(error, ("builtins", "IndexError", "list index out of range", function, line))
        elif boundary == "high-survivor-256":
            assert_exception(
                error, ("builtins", "ValueError", "bytes must be in range(0, 256)", "_collapse_branch", 791)
            )
        else:
            require(boundary in ("high-survivor-16", "high-survivor-255"), "known Q60 boundary")
            survivor_index = int(boundary.rsplit("-", 1)[1])
            survivor = source_input["children"][survivor_index]
            result = immediate["root"]
            require(
                error is None and result["tag"] == survivor["tag"] == 2
                and result["path"] == [survivor_index, *survivor["path"]]
                and result["value"] == survivor["value"],
                "exact out-of-nibble original survivor result",
            )
        if boundary == "stub-before-index" or (boundary or "").startswith("high-survivor-"):
            collapse = [event["line"] for event in events
                        if event.get("function") == codes[inc._collapse_branch.__code__]
                        and event.get("event") == "line"]
            require(
                collapse == ([790] if boundary == "stub-before-index" else [790, 791]),
                "source witnesses the survivor before accessing its byte index",
            )

        if frontend_control:
            original_root = immediate["root"]
            require(
                original_root == {"tag": 0} if default_route else
                original_root["tag"] == 2 and original_root["path"] == expected_path
                and original_root["value"] == actual_encoding
                and original_root["dirty"] and original_root["raw"] is None
                and original_root["hash"] is None,
                "typed frontend immediate root",
            )
            row = dict(row, phase="complete", qualification="Original typed frontend control.")
            record(row)
            frontend_controls.append(row)
            continue

        key_expr = "(bytes [" + ",".join(map(str, descriptor["key"])) + "])"
        value_expr = (
            "none"
            if descriptor["encoded"] is None
            else "(some (bytes [" + ",".join(map(str, descriptor["encoded"])) + "]))"
        )
        case_module = out.parent / (out.stem + "-case" + str(index).zfill(4) + ".lean")
        require(not case_module.exists(), "fresh failed/unstarted Lean phase destination")
        case_module.write_text(
            lean_header
            + "\n#eval emitSource "
            + str(descriptor["secured"]).lower()
            + " ("
            + expression(row["input"])
            + ") "
            + key_expr
            + " "
            + value_expr
            + "\n"
        )
        execution = command(["lake", "env", "lean", str(case_module)], ROOT)
        require(execution.returncode == 0, "complete setter public observer at " + str(index))
        actual = parse_records(execution.stdout.decode(), 1)[0]
        require(
            actual["input"] == wire(row["input"])
            and actual["key"] == descriptor["key"]
            and actual["encoded"] == descriptor["encoded"]
            and actual["secured"] == descriptor["secured"],
            "complete nominal inputs retained",
        )
        require(actual["result"] == actual["recorded"], "concrete Id/recording complete result")
        if key_calls:
            require(
                actual["queries"][:1] == [arr(key_calls[0]["preimage"])]
                and actual["answers"][:1] == [key_calls[0]["answer"]],
                "Lean recording starts with the same complete secured key query and answer",
            )
        if boundary is None:
            expected = [0, int(descriptor["secured"]), *wire(row["after"]["root"])]
            require(
                actual["result"] == expected, "full completed successful secured/root projection"
            )
        elif boundary in ("stub", "stub-before-index"):
            node = (
                row["input"]
                if boundary == "stub"
                else next(c for c in row["input"]["children"] if c["tag"] != 0)
            )
            require(
                actual["result"] == [1, 2, *node["hash"]],
                "exact nominal unresolved before collapse index",
            )
        elif boundary == "selected-index":
            require(
                actual["result"] == [1, 1, 11, expected_path[0], len(row["input"]["children"])],
                "exact actual nominal index/arity",
            )
        elif boundary == "zero-collapse":
            require(actual["result"] == [1, 1, 9, 0], "exact nominal reached occupancy0")
        else:
            require(boundary.startswith("high-survivor-"), "explicit source/nominal boundary")
            require(
                actual["result"] == [1, 1, 12, int(boundary.rsplit("-", 1)[1])],
                "chosen nonnibble completion",
            )
        row = dict(
            row,
            phase="complete",
            comparison=(boundary is None),
            actual=actual,
            generated_module=file_identity(case_module),
            qualification="Completed nominal projection or Q60 diagnostic with original source trace.",
        )
        record(row)
        observations.append(row)

    storage_descriptor = frozen["storage_control"]
    origin_labels.clear()
    storage = inc.IncrementalMPT(True, U256(0))

    def slot_key(number):
        return Bytes32(number.to_bytes(32, "big"))

    slots = {slot_key(number): U256(value) for number, value in storage_descriptor["writes"]}
    for number, value in storage_descriptor["initial"]:
        inc.mpt_set(storage, slot_key(number), U256(value))
    storage_before = carrier_view(storage)
    writes = []
    setter_code = inc.mpt_set.__code__
    key_code = hash_module.keccak256.__code__

    def trace_storage(frame, event, arg):
        if frame.f_code is setter_code:
            if event == "call":
                require(
                    frame.f_back.f_code is inc.mpt_set_storage_slots.__code__
                    and frame.f_locals["mpt"] is storage
                    and frame.f_locals["storage_root"] is None,
                    "actual storage helper dispatch",
                )
                writes.append(
                    dict(
                        key=list(frame.f_locals["key"]), value=value_view(frame.f_locals["value"]),
                        line=frame.f_back.f_lineno, before=carrier_view(storage), queries=[],
                    )
                )
            elif event == "line" and frame.f_lineno == 435:
                writes[-1].update(
                    path=list(frame.f_locals["nibble_key"]),
                    encoded=list(frame.f_locals["encoded_value"]),
                )
            elif event == "return":
                writes[-1]["immediate"] = carrier_view(storage)
            elif event == "exception":
                writes[-1]["exception"] = exception_view(arg[1])
        elif frame.f_code is key_code and frame.f_back.f_code is setter_code:
            queries = writes[-1]["queries"]
            if event == "call":
                queries.append(dict(preimage=list(frame.f_locals["buffer"])))
            elif event == "return":
                queries[-1]["answer"] = None if arg is None else list(arg)
        return trace_storage

    previous_trace = sys.gettrace()
    sys.settrace(trace_storage)
    try:
        inc.mpt_set_storage_slots(storage, slots)
    finally:
        sys.settrace(previous_trace)
    storage_immediate = carrier_view(storage)
    reads = [inc.mpt_get(storage, key) for key in slots]
    readback = [None if value is None else list(value) for value in reads]
    storage_control = dict(
        phase="storage-slots", descriptor=storage_descriptor, before=storage_before,
        writes=writes, immediate=storage_immediate, readback=readback, after=carrier_view(storage),
    )
    record(storage_control)
    require(len(writes) == len(storage_descriptor["order"]), "complete storage setter calls")
    for write, number in zip(writes, storage_descriptor["order"], strict=True):
        key = slot_key(number)
        value = slots[key]
        queries = write["queries"]
        require(
            write["key"] == list(key) and write["value"] == value_view(value)
            and write["line"] == (460 if value else 463) and "exception" not in write
            and len(queries) == 1 and queries[0]["preimage"] == list(key)
            and len(queries[0]["answer"] or []) == 32
            and write["path"] == nibble_path(queries[0]["answer"])
            and write["encoded"] == (list(rlp.encode(value)) if value else []),
            "original two-pass storage setter call and complete secured key path",
        )
    require(readback == storage_descriptor["readback"], "complete original encoded storage readback")

    after = identity()
    after["runtime"] = runtime_identity()
    require(before["runtime"] == after["runtime"], "actual source/runtime/crypto inputs changed")
    after_inputs = inputs("after")
    require(before_inputs == after_inputs, "focused original/wheel inputs changed")
    require(
        before["candidate_inputs"]
        == [
            file_identity(ROOT / name)
            for name in (
                "reference.toml",
                "STFSpec/Commit/Set.lean",
                "STFSpec/Conformance/Commit/SetGuards.lean",
                "STFSpec/Conformance/Commit/SetCallerProofs.lean",
                "STFSpec/Conformance/Commit/set_differential.py",
                "scripts/differential.py",
                "STFSpec/Conformance/Codec/rlp_typed_differential.py",
            )
        ],
        "frozen source-phase subject changed",
    )
    out.with_suffix(".after-identity.json").write_text(json.dumps(after, indent=2) + "\n")
    out.with_suffix(".observations.json").write_text(
        json.dumps(
            dict(
                schema=2, pin=context.head, catalog_sha256=catalog_sha, driver_sha256=driver_sha,
                cases=observations, frontend_controls=frontend_controls,
                storage_control=storage_control, before_identity=before, after_identity=after,
            ),
            indent=2,
        )
        + "\n"
    )
    out.write_text("-- Complete per-case source setter observers retained beside this summary.\n")
    print(
        json.dumps(
            dict(
                cases=len(observations),
                successful_completed_projections=sum(r["comparison"] for r in observations),
                nominal_cases=sum(r["actual"] is not None for r in observations),
                source_frontend_errors=sum(r["actual"] is None for r in observations),
                q60_controls=sum(r["actual"] is not None and not r["comparison"] for r in observations),
                original_key_queries=sum(
                    query["stage"] == "C-key" for row in observations for query in row["queries"]
                ),
                completion_queries=sum(
                    query["stage"].startswith("F-") for row in observations for query in row["queries"]
                ),
                materializations=sum(len(row["materializations"]) for row in observations),
                frontend_controls=len(frontend_controls),
                storage_writes=len(writes),
                pin=context.head,
                catalog_sha256=catalog_sha,
            )
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
