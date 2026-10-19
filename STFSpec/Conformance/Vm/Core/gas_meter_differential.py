#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Whole-result charge-kernel controls and pinned numeric-helper comparison.

Status: local conformance, not a whole EVM/tracing/settlement claim. Date: 2026-10-17.
--self-test runs strict parser controls normally and under -O. --emit-lean emits
an ordinary public-import client, with complete six-field results and nominal
exception tags/payloads. Source execution takes the exact --frames stream and
runs each original helper once, retaining input on OOG. check_gas's holder is
only its numeric gas_meter field projection, not a production EVM.
"""

import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys

CATALOG = {
    "meter": [
        {
            "case": 0,
            "label": "check-zero",
            "op": "check",
            "input": [10, 7, 3, -11, 13, 17],
            "amount": 0,
            "result": "ok",
            "meter": [10, 7, 3, -11, 13, 17],
        },
        {
            "case": 1,
            "label": "check-exact",
            "op": "check",
            "input": [10, 7, 3, -11, 13, 17],
            "amount": 10,
            "result": "ok",
            "meter": [10, 7, 3, -11, 13, 17],
        },
        {
            "case": 2,
            "label": "check-over",
            "op": "check",
            "input": [10, 7, 3, -11, 13, 17],
            "amount": 11,
            "result": "oog",
            "meter": [10, 7, 3, -11, 13, 17],
        },
        {
            "case": 3,
            "label": "charge-zero",
            "op": "charge",
            "input": [10, 7, 3, -11, 13, 17],
            "amount": 0,
            "result": "ok",
            "meter": [10, 7, 3, -11, 13, 17],
        },
        {
            "case": 4,
            "label": "charge-small",
            "op": "charge",
            "input": [10, 7, 3, -11, 13, 17],
            "amount": 4,
            "result": "ok",
            "meter": [6, 7, 3, -11, 13, 17],
        },
        {
            "case": 5,
            "label": "charge-exact",
            "op": "charge",
            "input": [10, 7, 3, -11, 13, 17],
            "amount": 10,
            "result": "ok",
            "meter": [0, 7, 3, -11, 13, 17],
        },
        {
            "case": 6,
            "label": "charge-over",
            "op": "charge",
            "input": [10, 7, 3, -11, 13, 17],
            "amount": 11,
            "result": "oog",
            "meter": [10, 7, 3, -11, 13, 17],
        },
        {
            "case": 7,
            "label": "state-zero",
            "op": "state",
            "input": [10, 7, 3, -11, 13, 17],
            "amount": 0,
            "result": "ok",
            "meter": [10, 7, 3, -11, 13, 17],
        },
        {
            "case": 8,
            "label": "state-small",
            "op": "state",
            "input": [10, 7, 3, -11, 13, 17],
            "amount": 3,
            "result": "ok",
            "meter": [10, 4, 3, -11, 13, 17],
        },
        {
            "case": 9,
            "label": "state-exact-reservoir",
            "op": "state",
            "input": [10, 7, 3, -11, 13, 17],
            "amount": 7,
            "result": "ok",
            "meter": [10, 0, 3, -11, 13, 17],
        },
        {
            "case": 10,
            "label": "state-first-spill",
            "op": "state",
            "input": [10, 7, 3, -11, 13, 17],
            "amount": 8,
            "result": "ok",
            "meter": [9, 0, 3, -11, 14, 17],
        },
        {
            "case": 11,
            "label": "state-exact-total",
            "op": "state",
            "input": [10, 7, 3, -11, 13, 17],
            "amount": 17,
            "result": "ok",
            "meter": [0, 0, 3, -11, 23, 17],
        },
        {
            "case": 12,
            "label": "state-over-total",
            "op": "state",
            "input": [10, 7, 3, -11, 13, 17],
            "amount": 18,
            "result": "oog",
            "meter": [10, 7, 3, -11, 13, 17],
        },
        {
            "case": 13,
            "label": "empty-check-zero",
            "op": "check",
            "input": [0, 0, 0, 0, 0, 0],
            "amount": 0,
            "result": "ok",
            "meter": [0, 0, 0, 0, 0, 0],
        },
        {
            "case": 14,
            "label": "empty-check-one",
            "op": "check",
            "input": [0, 0, 0, 0, 0, 0],
            "amount": 1,
            "result": "oog",
            "meter": [0, 0, 0, 0, 0, 0],
        },
        {
            "case": 15,
            "label": "empty-charge-zero",
            "op": "charge",
            "input": [0, 0, 0, 0, 0, 0],
            "amount": 0,
            "result": "ok",
            "meter": [0, 0, 0, 0, 0, 0],
        },
        {
            "case": 16,
            "label": "empty-charge-one",
            "op": "charge",
            "input": [0, 0, 0, 0, 0, 0],
            "amount": 1,
            "result": "oog",
            "meter": [0, 0, 0, 0, 0, 0],
        },
        {
            "case": 17,
            "label": "empty-state-zero",
            "op": "state",
            "input": [0, 0, 0, 0, 0, 0],
            "amount": 0,
            "result": "ok",
            "meter": [0, 0, 0, 0, 0, 0],
        },
        {
            "case": 18,
            "label": "empty-state-one",
            "op": "state",
            "input": [0, 0, 0, 0, 0, 0],
            "amount": 1,
            "result": "oog",
            "meter": [0, 0, 0, 0, 0, 0],
        },
        {
            "case": 19,
            "label": "no-exec-reservoir",
            "op": "state",
            "input": [0, 5, 0, -1, 2, 3],
            "amount": 5,
            "result": "ok",
            "meter": [0, 0, 0, -1, 2, 3],
        },
        {
            "case": 20,
            "label": "no-exec-over",
            "op": "state",
            "input": [0, 5, 0, -1, 2, 3],
            "amount": 6,
            "result": "oog",
            "meter": [0, 5, 0, -1, 2, 3],
        },
        {
            "case": 21,
            "label": "no-reservoir-spill",
            "op": "state",
            "input": [5, 0, 9, 23, 7, 8],
            "amount": 1,
            "result": "ok",
            "meter": [4, 0, 9, 23, 8, 8],
        },
        {
            "case": 22,
            "label": "no-reservoir-exact",
            "op": "state",
            "input": [5, 0, 9, 23, 7, 8],
            "amount": 5,
            "result": "ok",
            "meter": [0, 0, 9, 23, 12, 8],
        },
        {
            "case": 23,
            "label": "no-reservoir-over",
            "op": "state",
            "input": [5, 0, 9, 23, 7, 8],
            "amount": 6,
            "result": "oog",
            "meter": [5, 0, 9, 23, 7, 8],
        },
        {
            "case": 24,
            "label": "large-check",
            "op": "check",
            "input": [
                18446744073709551617,
                18446744073709551618,
                1,
                -18446744073709551619,
                18446744073709551620,
                18446744073709551621,
            ],
            "amount": 18446744073709551617,
            "result": "ok",
            "meter": [
                18446744073709551617,
                18446744073709551618,
                1,
                -18446744073709551619,
                18446744073709551620,
                18446744073709551621,
            ],
        },
        {
            "case": 25,
            "label": "large-charge",
            "op": "charge",
            "input": [18446744073709551617, 2, 0, -5, 3, 4],
            "amount": 18446744073709551616,
            "result": "ok",
            "meter": [1, 2, 0, -5, 3, 4],
        },
        {
            "case": 26,
            "label": "large-charge-over",
            "op": "charge",
            "input": [18446744073709551617, 2, 0, -5, 3, 4],
            "amount": 18446744073709551618,
            "result": "oog",
            "meter": [18446744073709551617, 2, 0, -5, 3, 4],
        },
        {
            "case": 27,
            "label": "large-state-reservoir",
            "op": "state",
            "input": [3, 18446744073709551618, 0, -7, 9, 11],
            "amount": 18446744073709551617,
            "result": "ok",
            "meter": [3, 1, 0, -7, 9, 11],
        },
        {
            "case": 28,
            "label": "large-state-spill",
            "op": "state",
            "input": [18446744073709551617, 2, 0, -7, 9, 11],
            "amount": 18446744073709551618,
            "result": "ok",
            "meter": [1, 0, 0, -7, 18446744073709551625, 11],
        },
        {
            "case": 29,
            "label": "large-state-exact",
            "op": "state",
            "input": [18446744073709551617, 2, 0, -7, 9, 11],
            "amount": 18446744073709551619,
            "result": "ok",
            "meter": [0, 0, 0, -7, 18446744073709551626, 11],
        },
        {
            "case": 30,
            "label": "large-state-over",
            "op": "state",
            "input": [18446744073709551617, 2, 0, -7, 9, 11],
            "amount": 18446744073709551620,
            "result": "oog",
            "meter": [18446744073709551617, 2, 0, -7, 9, 11],
        },
    ],
    "exceptions": [
        *[
            {"tag": "stackUnderflow", "payload": None},
            {"tag": "stackOverflow", "payload": None},
            {"tag": "outOfGas", "payload": None},
            {"tag": "invalidJumpDest", "payload": None},
            {"tag": "stackDepthLimit", "payload": None},
            {"tag": "writeInStaticContext", "payload": None},
            {"tag": "outOfBoundsRead", "payload": None},
            {"tag": "invalidParameter", "payload": None},
            {"tag": "invalidContractPrefix", "payload": None},
            {"tag": "addressCollision", "payload": None},
            {"tag": "kzgProofError", "payload": None},
        ],
        *({"tag": "invalidOpcode", "payload": code} for code in range(256)),
        *[
            {"tag": "precompileHalt", "payload": ""},
            {"tag": "precompileHalt", "payload": "MODEXP input error"},
            {"tag": "precompileHalt", "payload": 'a\x00b\n"\\'},
            {"tag": "precompileHalt", "payload": "λ🙂"},
            {"tag": "precompileHalt", "payload": "negative exponent"},
        ],
    ],
    "defaults": [2, 3, 4, 0, 0, 0],
}


class FrameError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise FrameError(message)


def pairs(items):
    out = {}
    for key, value in items:
        require(key not in out, "duplicate field")
        out[key] = value
    return out


def bad_constant(value):
    raise FrameError("nonfinite JSON: " + value)


def integer(value, signed=False):
    require(type(value) is int and (signed or value >= 0), "invalid integer")


def meter(value):
    require(type(value) is list and len(value) == 6, "meter must have six fields")
    for i, field in enumerate(value):
        integer(field, i == 3)


def exception(value):
    require(type(value) is dict and set(value) == {"tag", "payload"}, "exception fields")
    tag, payload = value["tag"], value["payload"]
    require(type(tag) is str, "exception tag")
    if tag == "invalidOpcode":
        integer(payload)
        require(payload < 256, "UInt8 range")
    elif tag == "precompileHalt":
        require(type(payload) is str, "String payload")
    else:
        require(
            tag
            in {
                "stackUnderflow",
                "stackOverflow",
                "outOfGas",
                "invalidJumpDest",
                "stackDepthLimit",
                "writeInStaticContext",
                "outOfBoundsRead",
                "invalidParameter",
                "invalidContractPrefix",
                "addressCollision",
                "kzgProofError",
            },
            "unknown tag",
        )
        require(payload is None, "unexpected payload")


def parse_frames(text):
    require(type(text) is str and bool(text), "empty stream")
    result = []
    for i, line in enumerate(text.splitlines()):
        require(bool(line.strip()), "blank frame")
        try:
            frame = json.loads(line, object_pairs_hook=pairs, parse_constant=bad_constant)
        except (ValueError, TypeError) as error:
            raise FrameError(str(error)) from error
        require(type(frame) is dict and set(frame) == {"kind", "case", "value"}, "frame fields")
        integer(frame["case"])
        require(frame["case"] == i, "frame order")
        kind, value = frame["kind"], frame["value"]
        if kind == "meter":
            require(
                type(value) is dict
                and set(value) == {"label", "op", "input", "amount", "result", "meter"},
                "result fields",
            )
            require(type(value["label"]) is str and bool(value["label"]), "label")
            require(
                type(value["op"]) is str and value["op"] in {"check", "charge", "state"},
                "operation",
            )
            meter(value["input"])
            meter(value["meter"])
            integer(value["amount"])
            require(
                type(value["result"]) is str and value["result"] in {"ok", "oog"}, "result tag"
            )
        elif kind == "exception":
            exception(value)
        elif kind == "defaults":
            meter(value)
        else:
            raise FrameError("unknown frame kind")
        result.append(frame)
    require(bool(result), "empty stream")
    return result


def expected_frames():
    rows = [
        {"kind": "meter", "case": i, "value": {k: v for k, v in frame.items() if k != "case"}}
        for i, frame in enumerate(CATALOG["meter"])
    ]
    rows += [
        {"kind": "exception", "case": len(rows) + i, "value": value}
        for i, value in enumerate(CATALOG["exceptions"])
    ]
    rows.append({"kind": "defaults", "case": len(rows), "value": CATALOG["defaults"]})
    return rows


def compare_frames(text):
    actual = parse_frames(text)
    require(actual == expected_frames(), "complete frozen frames disagree")
    return actual


def self_test():
    frames = expected_frames()
    text = "".join(json.dumps(f, ensure_ascii=False) + "\n" for f in frames)
    require(compare_frames(text) == frames, "whole positive stream")
    negatives = [
        "",
        "\n",
        "null",
        "[]",
        "true",
        "{}",
        text + "\n",
        text + "extra",
        text[:-2],
        text + json.dumps(frames[-1]),
        text.replace('"case": 0', '"case": 0, "case": 0', 1),
        text.replace('"amount": 0', '"amount": NaN', 1),
    ]
    base = frames[0]

    def bad(path, value):
        frame = copy.deepcopy(base)
        target = frame
        for key in path[:-1]:
            target = target[key]
        target[path[-1]] = value
        negatives.append(json.dumps(frame))

    for value in [True, False, None, "0", 0.0, [], {}, -1]:
        bad(["case"], value)
        bad(["value", "amount"], value)
        for field in ["input", "meter"]:
            for i in range(6):
                if i != 3 or value != -1:
                    bad(["value", field, i], value)
    for field in base:
        frame = copy.deepcopy(base)
        del frame[field]
        negatives.append(json.dumps(frame))
    for field in base["value"]:
        frame = copy.deepcopy(base)
        del frame["value"][field]
        negatives.append(json.dumps(frame))
    for value in [[], [0] * 5, [0] * 7, None, True, {}, "meter"]:
        bad(["value", "input"], value)
        bad(["value", "meter"], value)
    bad(["value", "extra"], 0)
    bad(["extra"], 0)
    for tag, payload in [
        ("invalidOpcode", True),
        ("invalidOpcode", 256),
        ("invalidOpcode", -1),
        ("precompileHalt", None),
        ("precompileHalt", 0),
        ("outOfGas", "x"),
        ("revert", None),
        (True, None),
    ]:
        negatives.append(
            json.dumps({"kind": "exception", "case": 0, "value": {"tag": tag, "payload": payload}})
        )
    for invalid in negatives:
        try:
            parse_frames(invalid)
        except FrameError:
            continue
        raise FrameError("invalid parser control accepted: " + repr(invalid))
    # Typed parsing may admit valid but semantically wrong frames. Comparison must reject them.
    wrong = copy.deepcopy(frames)
    wrong[0]["value"]["meter"][3] -= 1
    try:
        compare_frames("".join(json.dumps(f) + "\n" for f in wrong))
    except FrameError:
        pass
    else:
        raise FrameError("wrong whole signed field accepted")
    print(
        json.dumps(
            {
                "positive_frames": len(frames),
                "negative_streams": len(negatives),
                "optimization": sys.flags.optimize,
            }
        )
    )


def lean_string(value):
    # Lean accepts JSON string escaping except JSON surrogate pairs; keep Unicode literal.
    return json.dumps(value, ensure_ascii=False).replace("\\u0000", "\\x00")


def lean_meter(value):
    a, b, c, q, s, t = value
    return (
        (
            '{ gasLeft := %s, stateGasLeft := %s, stateGasBaseline := %s,'
            ' refundCounter := (%s), stateGasSpilled := %s, stateGasCommi'
            'ttedSpill := %s }'
        )
        % (a, b, c, q, s, t)
    )


def emit_lean():
    print("import Lean\nimport STFSpec.Vm.Core\nopen STFSpec.Vm.Core\n")
    print(lean_observers())
    for i, frame in enumerate(CATALOG["meter"]):
        source = lean_meter(frame["input"])
        op = {"check": "observeCheck", "charge": "observeCharge", "state": "observeState"}[
            frame["op"]
        ]
        prefix = {k: v for k, v in frame.items() if k not in {"case", "meter", "result"}}
        print("private def result%d := %s (%s) %d" % (i, op, source, frame["amount"]))
        print(
            (
                '#eval IO.println ((Lean.Json.mkObj [("kind", Lean.toJson "me'
                'ter"), ("case", Lean.toJson %d), ("value", Lean.Json.mkObj ['
                '("label", Lean.toJson %s), ("op", Lean.toJson %s), ("input",'
                ' meterJson (%s)), ("amount", Lean.toJson %d), ("result", Lea'
                'n.toJson result%d.1), ("meter", fieldsJson result%d.2)])]).c'
                'ompress)'
            )
            % (
                i,
                lean_string(frame["label"]),
                lean_string(frame["op"]),
                source,
                frame["amount"],
                i,
                i,
            )
        )
    offset = len(CATALOG["meter"])
    for i, value in enumerate(CATALOG["exceptions"]):
        tag, payload = value["tag"], value["payload"]
        arg = (
            (" " + str(payload))
            if tag == "invalidOpcode"
            else (" " + lean_string(payload))
            if tag == "precompileHalt"
            else ""
        )
        print(
            (
                '#eval IO.println ((Lean.Json.mkObj [("kind", Lean.toJson "ex'
                'ception"), ("case", Lean.toJson %d), ("value", exceptionJson'
                ' (.%s%s))]).compress)'
            )
            % (offset + i, tag, arg)
        )
    print(
        (
            '#eval IO.println ((Lean.Json.mkObj [("kind", Lean.toJson "de'
            'faults"), ("case", Lean.toJson %d), ("value", meterJson { ga'
            'sLeft := 2, stateGasLeft := 3, stateGasBaseline := 4 })]).co'
            'mpress)'
        )
        % (offset + len(CATALOG["exceptions"]))
    )


def lean_observers():
    """Read the single owning private serializer block from committed guards."""
    path = Path(__file__).with_name("GasMeterGuards.lean")
    text = path.read_text()
    start = "-- BEGIN charge-kernel observers\n"
    end = "-- END charge-kernel observers"
    require(text.count(start) == text.count(end) == 1, "observer block markers")
    return text.split(start, 1)[1].split(end, 1)[0]


PIN = "e1a316a06fc3d3e0a5da36fdc78580811e9d8a36"


def source_compare(args):
    """Compare authenticated original numeric helpers with complete frozen Lean frames."""
    import base64
    import dataclasses
    import datetime
    import importlib.abc
    import importlib.machinery
    import importlib.metadata
    import inspect
    import marshal
    import os
    import platform
    import subprocess
    import tomllib
    import types
    import zipfile

    require(
        sys.flags.isolated and sys.flags.dont_write_bytecode,
        "original mode requires pinned venv interpreter -I -B",
    )
    require(sys.flags.optimize == 0, "original schedule is normal Python exactly once")
    eels, output, wheels = args.eels.resolve(), args.output.resolve(), args.wheels.resolve()
    require(
        Path(sys.executable).absolute() == eels / ".venv/bin/python", "wrong lexical interpreter"
    )
    require(Path(sys.prefix).resolve() == eels / ".venv", "wrong interpreter environment")
    require(not output.exists(), "output must be fresh")
    output.mkdir(parents=True)
    require(
        not any(
            name.split(".")[0] in {"ethereum", "ethereum_types", "ethereum_rlp"}
            for name in sys.modules
        ),
        "source was already imported",
    )
    serial = 0

    def sha(data):
        return hashlib.sha256(data).hexdigest()

    def identity(path, capture=None):
        path = Path(path).absolute()
        require(path.resolve() == path, "aliased identity input")
        data = path.read_bytes()
        if capture is not None:
            capture.parent.mkdir(parents=True, exist_ok=True)
            capture.write_bytes(data)
            capture.chmod(path.stat().st_mode & 0o7777)
        return {
            "path": str(path),
            "size": len(data),
            "sha256": sha(data),
            "mode": oct(path.stat().st_mode & 0o7777),
        }

    def git(*argv):
        nonlocal serial
        directory = output / "git" / f"{serial:03d}"
        serial += 1
        directory.mkdir(parents=True)
        command = ["git", "--no-replace-objects", "--no-optional-locks", *argv]
        env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
        env.update(GIT_NO_LAZY_FETCH="1", GIT_TERMINAL_PROMPT="0")
        start = datetime.datetime.now(datetime.timezone.utc).isoformat()
        result = subprocess.run(command, cwd=eels, env=env, input=b"", capture_output=True)
        (directory / "stdin").write_bytes(b"")
        (directory / "stdout").write_bytes(result.stdout)
        (directory / "stderr").write_bytes(result.stderr)
        (directory / "record.json").write_text(
            json.dumps(
                {
                    "argv": command,
                    "cwd": str(eels),
                    "start_utc": start,
                    "end_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                    "exit": result.returncode,
                    "stdin": "stdin",
                    "timeout_seconds": None,
                    "stdout_sha256": sha(result.stdout),
                    "stderr_sha256": sha(result.stderr),
                },
                indent=2,
            )
        )
        require(result.returncode == 0, "original Git identity command failed")
        return result.stdout

    def pin_snapshot():
        require(git("rev-parse", "HEAD").decode().strip() == PIN, "wrong source commit")
        require(
            not git("status", "--porcelain=v1", "--untracked-files=all"), "dirty source checkout"
        )
        entries = git("ls-tree", "-rz", PIN, "--", "src/ethereum", "uv.lock", "pyproject.toml")
        rows = {}
        for entry in entries.split(b"\0"):
            if not entry:
                continue
            header, raw_path = entry.split(b"\t", 1)
            mode, kind, oid = header.decode().split()
            path = raw_path.decode()
            require(kind == "blob" and mode in {"100644", "100755"}, "unexpected source kind")
            file = eels / path
            require(not file.is_symlink() and file.is_file(), "missing/aliased source")
            data = file.read_bytes()
            actual = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
            require(actual == oid, "source bytes differ from actual pinned blob: " + path)
            require(
                bool(file.stat().st_mode & 0o111) == (mode == "100755"), "source mode mismatch"
            )
            rows[path] = {
                "oid": oid,
                "git_mode": mode,
                "sha256": sha(data),
                "size": len(data),
                "fs_mode": oct(file.stat().st_mode & 0o7777),
            }
        require(bool(rows), "empty source inventory")
        return {
            "pin": PIN,
            "tree": git("rev-parse", PIN + "^{tree}").decode().strip(),
            "files": rows,
        }

    pinned_before = pin_snapshot()
    (output / "pin-before.json").write_text(json.dumps(pinned_before, indent=2))
    lock = tomllib.loads((eels / "uv.lock").read_text())
    packages = {p["name"]: p for p in lock["package"]}
    installed = {}
    wheel_records = {}
    record_files = {}
    distributions = list(importlib.metadata.distributions())

    def authenticated_dependency(path, data):
        path = Path(path).absolute()
        key = str(path)
        if key in installed:
            require(installed[key]["sha256"] == sha(data), "dependency changed during import")
            return
        require(
            path.resolve() == path and path.is_relative_to(eels / ".venv"),
            "dependency alias/location",
        )
        for distribution in distributions:
            files = distribution.files or []
            matched = next(
                (f for f in files if Path(distribution.locate_file(f)).absolute() == path), None
            )
            if matched is None:
                continue
            name = distribution.metadata["Name"].lower().replace("_", "-")
            require(
                name in packages and distribution.version == packages[name]["version"],
                "dependency not locked: " + name,
            )
            require(
                matched.hash is not None
                and matched.hash.mode == "sha256"
                and matched.size == len(data)
                and matched.hash.value
                == base64.urlsafe_b64encode(hashlib.sha256(data).digest()).decode().rstrip("="),
                "installed dependency RECORD mismatch",
            )
            if name not in wheel_records:
                selected = []
                for locked in packages[name].get("wheels", []):
                    file = wheels / locked["url"].rsplit("/", 1)[-1]
                    if file.is_file():
                        info = identity(file)
                        if (
                            info["size"] == locked["size"]
                            and "sha256:" + info["sha256"] == locked["hash"]
                        ):
                            selected.append((file, info))
                require(len(selected) <= 1, "ambiguous actual raw wheels for " + name)
                if name in {"ethereum-types", "ethereum-rlp"}:
                    require(len(selected) == 1, "need actual locked raw wheel for " + name)
                if not selected:
                    wheel_records[name] = {
                        "version": distribution.version,
                        "raw_wheel_authenticated": False,
                        "basis": "installed RECORD and locked version",
                    }
                else:
                    file, info = selected[0]
                    with zipfile.ZipFile(file) as archive:
                        members = {
                            m.filename: {
                                "size": m.file_size,
                                "sha256": sha(archive.read(m)),
                                "crc": m.CRC,
                                "external_attr": m.external_attr,
                            }
                            for m in archive.infolist()
                        }
                    wheel_records[name] = info | {
                        "version": distribution.version,
                        "raw_wheel_authenticated": True,
                        "members": members,
                    }
                for f in files:
                    if str(f).endswith(".dist-info/RECORD"):
                        record = Path(distribution.locate_file(f)).absolute()
                        record_files[str(record)] = identity(
                            record, output / "records" / name / "RECORD"
                        )
            info = wheel_records[name]
            member = str(matched)
            if info["raw_wheel_authenticated"]:
                require(
                    member in info["members"] and info["members"][member]["sha256"] == sha(data),
                    "installed bytes differ from locked raw wheel",
                )
            installed[key] = identity(path, output / "installed" / name / member)
            return
        raise FrameError("installed dependency has no RECORD owner: " + key)

    loaded_sources = {}

    class SourceLoader(importlib.machinery.SourceFileLoader):
        def get_code(self, fullname):
            path = Path(self.get_filename(fullname)).absolute()
            require(path.resolve() == path, "source import alias")
            data = path.read_bytes()
            if path.is_relative_to(eels / "src"):
                relative = path.relative_to(eels).as_posix()
                require(
                    relative in pinned_before["files"]
                    and sha(data) == pinned_before["files"][relative]["sha256"],
                    "untrusted source import",
                )
                loaded_sources[fullname] = identity(path, output / "source" / relative)
            else:
                authenticated_dependency(path, data)
            return self.source_to_code(data, str(path))

    class SourceFinder(importlib.abc.MetaPathFinder):
        def find_spec(self, fullname, path=None, target=None):
            spec = importlib.machinery.PathFinder.find_spec(fullname, path)
            if spec is None:
                return None
            oracle = fullname.split(".")[0] in {"ethereum", "ethereum_types", "ethereum_rlp"}
            if spec.loader is None and spec.submodule_search_locations is not None:
                if oracle:
                    expected = eels / "src" / Path(*fullname.split("."))
                    require(
                        fullname.split(".")[0] == "ethereum"
                        and all(
                            Path(p).resolve() == expected for p in spec.submodule_search_locations
                        ),
                        "untrusted oracle namespace",
                    )
                    prefix = expected.relative_to(eels).as_posix() + "/"
                    require(
                        any(p.startswith(prefix) for p in pinned_before["files"]),
                        "empty source namespace",
                    )
                    spec.submodule_search_locations = list(spec.submodule_search_locations)
                return spec
            origin = (
                Path(spec.origin).absolute()
                if spec.origin and spec.origin not in {"built-in", "frozen"}
                else None
            )
            within = origin is not None and (
                origin.is_relative_to(eels / "src") or origin.is_relative_to(eels / ".venv")
            )
            if oracle:
                require(within, "oracle outside frozen environment")
            if not within:
                return None
            require(origin.resolve() == origin, "module origin alias")
            if isinstance(spec.loader, importlib.machinery.SourceFileLoader):
                spec.loader = SourceLoader(fullname, str(origin))
            elif origin.suffix in {".so", ".pyd"} or ".so." in origin.name:
                authenticated_dependency(origin, origin.read_bytes())
            else:
                raise FrameError("unexpected installed loader: " + fullname)
            return spec

    initial_modules = set(sys.modules)
    startup_inputs = {}
    sys.path.insert(0, str(eels / "src"))
    finder = SourceFinder()
    sys.meta_path.insert(0, finder)
    import importlib

    gas = importlib.import_module("ethereum.forks.amsterdam.vm.gas")
    errors = importlib.import_module("ethereum.forks.amsterdam.vm.exceptions")
    numeric = importlib.import_module("ethereum_types.numeric")
    fork_types = importlib.import_module("ethereum.forks.amsterdam.fork_types")

    def functions():
        return [
            gas.check_gas,
            gas.charge_gas_from_meter,
            gas.charge_state_gas_from_meter,
            gas.GasMeter.__init__,
            numeric.Uint.__init__,
            numeric.Uint.__sub__,
            numeric.Uint.__isub__,
            numeric.Uint.__add__,
            numeric.Uint.__iadd__,
            numeric.Uint.__ge__,
            numeric.Uint.__lt__,
            numeric.Uint._in_range,
        ]

    def globals_now():
        return {
            "GasMeter": gas.GasMeter,
            "OutOfGasError": gas.OutOfGasError,
            "gas.Uint": gas.Uint,
            "numeric.Uint": numeric.Uint,
            "gas.ExecutionGas": gas.ExecutionGas,
            "gas.StateGas": gas.StateGas,
            "fork.ExecutionGas": fork_types.ExecutionGas,
            "fork.StateGas": fork_types.StateGas,
            "charge.OutOfGasError": gas.charge_gas_from_meter.__globals__["OutOfGasError"],
            "state.Uint": gas.charge_state_gas_from_meter.__globals__["Uint"],
            "exception.OutOfGasError": errors.OutOfGasError,
        }

    require(
        gas.OutOfGasError is errors.OutOfGasError
        and gas.Uint is numeric.Uint
        and gas.ExecutionGas is fork_types.ExecutionGas
        and gas.StateGas is fork_types.StateGas,
        "source aliases differ",
    )
    fields = [
        "gas_left",
        "state_gas_left",
        "state_gas_baseline",
        "refund_counter",
        "state_gas_spilled",
        "state_gas_committed_spill",
    ]
    require([f.name for f in dataclasses.fields(gas.GasMeter)] == fields, "wrong original schema")

    def snapshot():
        # Include every loaded dependency/source file and native backend mapped by Python.
        for name, module in list(sys.modules.items()):
            file = getattr(module, "__file__", None)
            if not file:
                continue
            path = Path(file).absolute()
            if path.is_relative_to(eels / ".venv") and path.suffix != ".pyc":
                if name in initial_modules:
                    startup_inputs[str(path)] = identity(path)
                else:
                    authenticated_dependency(path, path.read_bytes())
        # Cached import observations must be independently rebound to current bytes/modes.
        for path, expected in installed.items():
            require(identity(Path(path)) == expected, "installed input identity changed")
        for path, expected in record_files.items():
            require(identity(Path(path)) == expected, "installed RECORD identity changed")
        for info in wheel_records.values():
            if info["raw_wheel_authenticated"]:
                current = identity(Path(info["path"]))
                require(all(current[k] == info[k] for k in current), "raw wheel identity changed")
        mapped = {}
        for line in Path("/proc/self/maps").read_text().splitlines():
            parts = line.split(maxsplit=5)
            if len(parts) == 6 and parts[5].startswith("/"):
                path = Path(parts[5])
                if path.is_file() and path.is_relative_to(eels / ".venv"):
                    authenticated_dependency(path, path.read_bytes())
                    mapped[str(path)] = identity(path)
        result = {
            "runtime": {
                "executable": str(Path(sys.executable).absolute()),
                "binary": identity(Path(sys.executable).resolve()),
                "version": sys.version,
                "implementation": platform.python_implementation(),
                "flags": str(sys.flags),
                "sys_path": list(sys.path),
                "recursion_limit": sys.getrecursionlimit(),
            },
            "functions": [
                {
                    "module": f.__module__,
                    "qualname": f.__qualname__,
                    "id": id(f),
                    "source": inspect.getsourcefile(f),
                    "code_sha256": sha(marshal.dumps(f.__code__, 2)),
                }
                for f in functions()
            ],
            "bindings": {
                k: {
                    "id": id(v),
                    "module": getattr(v, "__module__", None),
                    "qualname": getattr(v, "__qualname__", None),
                }
                for k, v in globals_now().items()
            },
            "schema": [
                {"name": f.name, "type": str(f.type)} for f in dataclasses.fields(gas.GasMeter)
            ],
            "sources": loaded_sources,
            "installed": installed,
            "wheels": wheel_records,
            "records": record_files,
            "mapped_venv_backends": mapped,
            "trusted_startup_files": startup_inputs,
            (
                'adapter'
            ): (
                "SimpleNamespace(gas_meter=meter) is only check_gas's numeric"
                ' field projection; no EVM validity claim'
            ),
        }
        return json.loads(json.dumps(result))

    before = snapshot()
    (output / "before.json").write_text(json.dumps(before, indent=2))
    if args.preflight:
        after = snapshot()
        require(
            before == after and pin_snapshot() == pinned_before, "preflight identities changed"
        )
        (output / "after.json").write_text(json.dumps(after, indent=2))
        print(
            json.dumps(
                {
                    "status": "authenticated preflight only",
                    "source_calls": 0,
                    "catalog_sha256": hashlib.sha256(
                        json.dumps(CATALOG, sort_keys=True).encode()
                    ).hexdigest(),
                }
            )
        )
        return
    require(args.frames is not None, "source comparison needs complete frozen Lean frames")
    frames = compare_frames(args.frames.read_text())
    (output / "frames-input.jsonl").write_bytes(args.frames.read_bytes())
    progress = 0

    def observe(m):
        values = [getattr(m, f) for f in fields]
        require(type(values[3]) is int, "signed refund class")
        require(
            all(type(v) is numeric.Uint for i, v in enumerate(values) if i != 3), "gas field class"
        )
        return [int(v) for v in values]

    try:
        with (output / "observations.jsonl").open("x") as observed:
            for row in CATALOG["meter"]:
                values = [numeric.Uint(v) if i != 3 else v for i, v in enumerate(row["input"])]
                m = gas.GasMeter(*values)
                original = observe(m)
                function = {
                    "check": gas.check_gas,
                    "charge": gas.charge_gas_from_meter,
                    "state": gas.charge_state_gas_from_meter,
                }[row["op"]]
                argument = types.SimpleNamespace(gas_meter=m) if row["op"] == "check" else m
                tag = "ok"
                try:
                    returned = function(argument, numeric.Uint(row["amount"]))
                    require(returned is None, "numeric helper returned a value")
                except errors.OutOfGasError as error:
                    require(
                        type(error) is errors.OutOfGasError and error.args == (),
                        "unexpected OOG payload",
                    )
                    tag = "oog"
                result = observe(m)
                require(
                    tag == row["result"] and result == row["meter"],
                    "original whole meter mismatch",
                )
                if tag == "oog":
                    require(result == original, "source mutated meter before OOG")
                observed.write(
                    json.dumps(
                        {
                            "case": row["case"],
                            "op": row["op"],
                            "input": original,
                            "amount": row["amount"],
                            "result": tag,
                            "meter": result,
                        }
                    )
                    + "\n"
                )
                observed.flush()
                progress += 1
    finally:
        after = snapshot()
        (output / "after.json").write_text(json.dumps(after, indent=2))
        pin_after = pin_snapshot()
        (output / "pin-after.json").write_text(json.dumps(pin_after, indent=2))
        (output / "progress.json").write_text(
            json.dumps({"completed": progress, "total": len(CATALOG["meter"])})
        )
        require(
            before == after and pinned_before == pin_after, "source/runtime identities changed"
        )
    print(
        json.dumps(
            {
                "source_cases": progress,
                "complete_lean_frames": len(frames),
                "identities_unchanged": True,
                "exception_producers_executed": False,
            }
        )
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--self-test", action="store_true")
    modes.add_argument("--emit-lean", action="store_true")
    modes.add_argument("--check-frames", type=Path)
    modes.add_argument("--source", action="store_true")
    modes.add_argument("--preflight", action="store_true")
    parser.add_argument("--eels", type=Path)
    parser.add_argument("--wheels", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--frames", type=Path)
    args = parser.parse_args()
    if args.self_test:
        self_test()
    elif args.emit_lean:
        emit_lean()
    elif args.check_frames:
        compare_frames(args.check_frames.read_text())
        print(
            json.dumps(
                {"whole_frames": len(expected_frames()), "optimization": sys.flags.optimize}
            )
        )
    else:
        require(all([args.eels, args.wheels, args.output]), "original paths required")
        source_compare(args)


if __name__ == "__main__":
    main()
