#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Encoded setter frontend observations and completed nominal projection.

The original _data/default/encoding/key/mutation/completion stages stay distinct.
Use --write-catalog, then authenticated --preflight before separately authorized
original execution. --self-test uses no reference import and supports Python -O.
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
import traceback
import types
import zipfile

ROOT = Path(__file__).resolve().parents[3]
DEFAULT_SEED = 195


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
    resume_cli_tests()
    print(
        json.dumps(dict(accepted=len(positive), rejected=len(bad), optimized=sys.flags.optimize))
    )


def catalog():
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


def stage_plan():
    return {
        "status": "PREPARED; REAL SOURCE HOLD",
        "catalog_sha256": "89b64aac00f0afef83e461d51fbc8f79be5de1f2bd3e86cf6c5238b21eab28bf",
        "cases": 54,
        "stages": [
            "A full carrier/root/default/value/data/witness before frontend",
            "B actual map membership/write/removal snapshots at original key conversion call",
            "C full original key hash query/answer and converted key",
            "D default/encoder/Account callback/Address failure and exact encoded bytes",
            "E actual selected insertion/deletion entry/return/exception, "
            "origin/dirty/cache/witness writes",
            "F captured returns and separate bottom-up provider completion actions",
            "G complete nominal Id/recording result and successful secured/root comparison under "
            "named premises",
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
        "source_execution": "HOLD",
        (
            'replay'
        ): (
            'No previous direct deletion/insertion operation replay; fres'
            'h frontend calls only after ROOT release'
        ),
    }


def main():
    reject_resume(sys.argv[1:])
    if sys.argv[1:] == ["--self-test"]:
        parser_tests()
        return 0
    if len(sys.argv) == 3 and sys.argv[1] == "--write-catalog":
        destination = Path(sys.argv[2])
        require(not destination.exists(), "fresh catalog path")
        destination.write_text(json.dumps(catalog(), indent=2) + "\n")
        print(
            json.dumps(
                dict(
                    cases=len(catalog()["cases"]),
                    sha256=hashlib.sha256(destination.read_bytes()).hexdigest(),
                )
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
    sys.argv = [sys.argv[0]] + remainder
    dst = argparse.ArgumentParser(add_help=False)
    dst.add_argument("--output", type=Path, required=True)
    args, _ = dst.parse_known_args(remainder)
    out = args.output.resolve()
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
    auth = RlpSourceAuth(context)
    sys.meta_path.insert(0, RlpFreshFinder(auth))
    dependency = []
    for pkg, wheel, digest in [
        (
            "ethereum_rlp",
            own.rlp_wheel,
            "f4144caa96b975720c62b967bbfd6c98601e95ee3c36457ece11ef4ce0cffa04",
        ),
        (
            "ethereum_types",
            own.types_wheel,
            "33de3e2a0c0e57ea1b67802485de556b92d557aae7c8c640070800f2b4f639e3",
        ),
    ]:
        require(hashlib.sha256(wheel.read_bytes()).hexdigest() == digest, "raw wheel identity")
        dist = importlib.metadata.distribution(pkg.replace("_", "-"))
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
                wheel=str(wheel),
                sha256=digest,
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
        inc.Account,
        inc.Address,
        Uint,
        U256,
        Bytes32,
    )
    function_paths = [
        (inc, n)
        for n in (
            "mpt_set",
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
            == classes + (inc.IncrementalMPT, inc.Account, inc.Address, Uint, U256, Bytes32),
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

    payload = own.catalog.read_bytes()
    frozen = load_json(payload)
    require(frozen == catalog(), "catalog must equal the complete frozen generator")
    catalog_sha = hashlib.sha256(payload).hexdigest()

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
        require(crypto.version == "3.23.0", "pinned crypto distribution")
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
                    schema=1,
                    catalog_sha256=catalog_sha,
                    cases=len(frozen["cases"]),
                    scope=frozen["qualification"],
                    stages=stage_plan(),
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
        if node is None:
            return None
        origin_labels.setdefault(id(node), len(origin_labels))
        return origin_labels[id(node)]

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
            data=[dict(key=list(k), value=value_view(v)) for k, v in state._data.items()],
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
        row = dict(row, catalog_sha256=catalog_sha, driver_sha256=driver_sha)
        with journal.open("a") as stream:
            stream.write(json.dumps(row) + "\n")
            stream.flush()
            os.fsync(stream.fileno())

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
    source_only = {
        "nondefault-none",
        "missing-callback",
        "invalid-address",
        "unsupported-encoding",
    }
    for descriptor in frozen["cases"]:
        index = descriptor["case"]
        origin_labels.clear()
        root = build(descriptor["root"])
        key = Bytes(descriptor["key"])
        default, value = build_value(descriptor["default"]), build_value(descriptor["value"])
        state = inc.IncrementalMPT(secured=descriptor["secured"], default=default, root_node=root)
        for entry in descriptor["data_before"]:
            state._data[Bytes(entry["key"])] = build_value(entry["value"])
        initial_carrier = carrier_view(state)
        initial_value = value_view(value)
        source_input = view(root)
        events, calls, visited, completions, callback_calls = [], [], [], [], []
        actual_path, actual_encoding, error, immediate = None, None, None, None
        stage = "frontend"

        def contextual_root(address):
            require(type(address) is inc.Address, "actual callback Address")
            returned = Bytes32(bytes([0, 255] * 16))
            callback_calls.append(dict(address=list(address), root=list(returned)))
            return returned

        callback_identity = dict(
            function_id=id(contextual_root),
            code_id=id(contextual_root.__code__),
            code_sha256=hashlib.sha256(marshal.dumps(contextual_root.__code__, 2)).hexdigest(),
            role="explicit caller argument; original functions/providers unchanged",
        )
        callback = contextual_root if descriptor["callback"] == "fixed-root" else None

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
                    if current.f_lineno >= 463:
                        return "E-mutation"
                    if current.f_lineno >= 452:
                        return "D-encoding"
                    if current.f_lineno >= 447:
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
                and frame.f_lineno in (447, 452, 463)
            ):
                item = dict(
                    stage={447: "B-map", 452: "C-converted", 463: "D-encoded"}[frame.f_lineno],
                    file=frame.f_code.co_filename,
                    line=frame.f_lineno,
                    carrier=carrier_view(state),
                )
                if frame.f_lineno == 452:
                    actual_path = list(frame.f_locals["nibble_key"])
                    item["path"] = actual_path
                if frame.f_lineno == 463:
                    actual_encoding = list(frame.f_locals["encoded_value"])
                    item["encoded"] = actual_encoding
                events.append(item)
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
                if frame.f_code in mutation_codes and "key" in frame.f_locals:
                    item["key"] = list(frame.f_locals["key"])
                    item["level"] = int(frame.f_locals.get("level", 0))
                if event == "return" and frame.f_code in return_codes:
                    item["returned"] = view(arg)
                    if arg is not None:
                        visited.append(arg)
                if event == "exception":
                    item["exception"] = dict(
                        module=arg[0].__module__,
                        name=arg[0].__qualname__,
                        message=str(arg[1]),
                        args=[dict(type=type(x).__name__, repr=repr(x)) for x in arg[1].args],
                    )
                events.append(item)
            return trace

        record(
            dict(
                phase="before",
                case=index,
                descriptor=descriptor,
                carrier=initial_carrier,
                value=value_view(value),
                callback_identity=callback_identity,
            )
        )
        previous_trace = sys.gettrace()
        sys.settrace(trace)
        try:
            try:
                inc.mpt_set(state, key, value, callback)
                immediate = carrier_view(state)
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
                sites = [
                    e
                    for e in events
                    if e.get("exception", {}).get("name") == type(exception).__qualname__
                ]
                error_stage = (
                    stage if stage.startswith("F-") else (sites[-1]["stage"] if sites else stage)
                )
                error = dict(
                    stage=error_stage,
                    module=type(exception).__module__,
                    name=type(exception).__qualname__,
                    message=str(exception),
                    args=[dict(type=type(x).__name__, repr=repr(x)) for x in exception.args],
                    traceback=traceback.format_exc(),
                )
        finally:
            sys.settrace(previous_trace)
        row = dict(
            phase="original-returned",
            case=index,
            descriptor=descriptor,
            input=source_input,
            before=initial_carrier,
            before_value=initial_value,
            immediate=immediate,
            after=carrier_view(state),
            actual_path=actual_path,
            actual_encoding=actual_encoding,
            events=events,
            queries=calls,
            materializations=completions,
            callback_calls=callback_calls,
            callback_identity=callback_identity,
            error=error,
        )
        record(row)
        key_calls = [q for q in row["queries"] if q["stage"] == "C-key"]
        require(
            len(key_calls) == int(descriptor["secured"]), "one original full key query iff secured"
        )
        if key_calls:
            require(
                key_calls[0]["preimage"] == descriptor["key"]
                and key_calls[0]["answer"] is not None,
                "actual complete original key preimage/answer before encoding/dispatch",
            )
        map_stages = [e for e in row["events"] if e.get("stage") == "B-map"]
        require(len(map_stages) == 1, "actual post-map/pre-key stage")
        expected_data = [dict(e) for e in row["before"]["data"]]
        old_position = next(
            (i for i, e in enumerate(expected_data) if e["key"] == descriptor["key"]), None
        )
        if descriptor["value"] == descriptor["default"]:
            if old_position is not None:
                expected_data.pop(old_position)
        else:
            source_value = next(
                e["value"]
                for e in map_stages[0]["carrier"]["data"]
                if e["key"] == descriptor["key"]
            )
            expected_value = row["before_value"]
            require(source_value == expected_value, "full original stored value/class fields")
            entry = dict(key=descriptor["key"], value=expected_value)
            if old_position is None:
                expected_data.append(entry)
            else:
                expected_data[old_position] = entry
        require(
            map_stages[0]["carrier"]["data"] == expected_data, "complete original ordered map step"
        )
        if descriptor["callback"] == "fixed-root" and descriptor["boundary"] is None:
            require(
                row["callback_calls"] == [dict(address=descriptor["key"], root=[0, 255] * 16)],
                "complete contextual Address/callback root",
            )
        elif descriptor["boundary"] in ("missing-callback", "invalid-address"):
            require(
                not row["callback_calls"], "callback must not run before admission/address failure"
            )

        # These are genuinely different source values/default/encoding inputs.
        # They are observed, never coerced into the nominal preencoded None case.
        if descriptor["boundary"] in source_only:
            require(
                row["error"] is not None
                and not any(e.get("stage") == "E-mutation" for e in row["events"]),
                "source-only encoding boundary must precede mutation",
            )
            row = dict(
                row,
                phase="complete",
                comparison=False,
                actual=None,
                qualification=(
                    'source-only value/default/encoder boundary; no nominal proje'
                    'ction asserted'
                ),
            )
            record(row)
            observations.append(row)
            continue
        require(
            row["actual_encoding"] == (descriptor["encoded"] or []),
            "exact frozen preencoding bytes",
        )
        key_calls = [q for q in row["queries"] if q["stage"] == "C-key"]
        require(
            len(key_calls) == int(descriptor["secured"]), "one original full key query iff secured"
        )
        if key_calls:
            require(
                key_calls[0]["preimage"] == descriptor["key"]
                and key_calls[0]["answer"] is not None,
                "actual complete original key preimage/answer",
            )
        expected_path = [
            d
            for b in (key_calls[0]["answer"] if key_calls else descriptor["key"])
            for d in (b // 16, b % 16)
        ]
        require(row["actual_path"] == expected_path, "complete original high-before-low key")
        boundary = descriptor["boundary"]
        if boundary is None:
            require(row["error"] is None, "unexpected frontend/provider/materialization failure")
        elif boundary in ("stub", "stub-before-index", "zero-collapse"):
            require(
                row["error"] is not None and row["error"]["name"] == "AssertionError",
                "first original assertion",
            )
        elif boundary == "selected-index":
            require(
                row["error"] is not None and row["error"]["name"] == "IndexError",
                "first original selected access",
            )
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
            qualification=(
                'Completed nominal projection only; source map/default/dirty/'
                'witness/query histories remain separate'
            ),
        )
        record(row)
        observations.append(row)

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
            dict(schema=1, cases=observations, before_identity=before, after_identity=after),
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
                queries=sum(len(r["queries"]) for r in observations),
                pin=context.head,
            )
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
