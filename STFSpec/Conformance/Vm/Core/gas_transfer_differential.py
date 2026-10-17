#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Complete return/meter controls and authenticated pinned gas-transfer comparison.

Status: bounded local conformance. Date: 2026-10-17.
--self-test supports normal/-O; source execution keeps assertions enabled.
--preflight authenticates imports; --source calls only the four original transfer helpers.
The original max_message_call_gas is used only as withhold_create_gas's actual callee.
"""

import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys

# Literal complete expectations frozen before the first provider/target execution.
CATALOG = {
    "compositions": {
        "entry": [[10, 4, 9, 0, 6, 7], [23, 12, 12, 0, 0, 0], [0, 12, 12, 0, 0, 0]],
        "ordinary": [
            [10, 4, 9, -3, 6, 7],
            [16, 9, 9, 0, 0, 7],
            [0, 9, 9, 0, 0, 7],
            [0, 9, 9, 0, 0, 7],
        ],
        "roundtrip": [
            [130, 9, 2, -7, 5, 11],
            [128, [2, 9, 2, -7, 5, 11]],
            [9, [2, 0, 2, -7, 5, 11]],
            [0, [2, 0, 2, -7, 5, 11]],
            [130, 9, 2, -7, 5, 11],
            [2, 0, 2, -7, 5, 11],
        ],
    },
    "invalid_forfeit": [
        [17, 9, 2, -7, 1, 11],
        [0, 9, 2, -7, 1, 11],
        [18446744073709551616, 9, 2, -7, 18446744073709551619, 11],
    ],
    "meter": [
        {
            "args": None,
            "case": 0,
            "input": [0, 0, 0, 0, 0, 0],
            "label": "forfeit-zero",
            "meter": [0, 0, 0, 0, 0, 0],
            "op": "forfeit",
            "returned": None,
        },
        {
            "args": None,
            "case": 1,
            "input": [17, 9, 2, -7, 0, 11],
            "label": "forfeit-raw",
            "meter": [0, 9, 2, -7, 0, 11],
            "op": "forfeit",
            "returned": None,
        },
        {
            "args": None,
            "case": 2,
            "input": [0, 9, 2, 7, 0, 11],
            "label": "forfeit-zero-execution",
            "meter": [0, 9, 2, 7, 0, 11],
            "op": "forfeit",
            "returned": None,
        },
        {
            "args": None,
            "case": 3,
            "input": [0, 9, 2, -7, 5, 11],
            "label": "withhold-0",
            "meter": [0, 9, 2, -7, 5, 11],
            "op": "withhold",
            "returned": 0,
        },
        {
            "args": None,
            "case": 4,
            "input": [1, 9, 2, -7, 5, 11],
            "label": "withhold-1",
            "meter": [0, 9, 2, -7, 5, 11],
            "op": "withhold",
            "returned": 1,
        },
        {
            "args": None,
            "case": 5,
            "input": [63, 9, 2, -7, 5, 11],
            "label": "withhold-63",
            "meter": [0, 9, 2, -7, 5, 11],
            "op": "withhold",
            "returned": 63,
        },
        {
            "args": None,
            "case": 6,
            "input": [64, 9, 2, -7, 5, 11],
            "label": "withhold-64",
            "meter": [1, 9, 2, -7, 5, 11],
            "op": "withhold",
            "returned": 63,
        },
        {
            "args": None,
            "case": 7,
            "input": [65, 9, 2, -7, 5, 11],
            "label": "withhold-65",
            "meter": [1, 9, 2, -7, 5, 11],
            "op": "withhold",
            "returned": 64,
        },
        {
            "args": None,
            "case": 8,
            "input": [127, 9, 2, -7, 5, 11],
            "label": "withhold-127",
            "meter": [1, 9, 2, -7, 5, 11],
            "op": "withhold",
            "returned": 126,
        },
        {
            "args": None,
            "case": 9,
            "input": [128, 9, 2, -7, 5, 11],
            "label": "withhold-128",
            "meter": [2, 9, 2, -7, 5, 11],
            "op": "withhold",
            "returned": 126,
        },
        {
            "args": None,
            "case": 10,
            "input": [129, 9, 2, -7, 5, 11],
            "label": "withhold-129",
            "meter": [2, 9, 2, -7, 5, 11],
            "op": "withhold",
            "returned": 127,
        },
        {
            "args": None,
            "case": 11,
            "input": [0, 0, 0, 0, 0, 0],
            "label": "drain-zero",
            "meter": [0, 0, 0, 0, 0, 0],
            "op": "drain",
            "returned": 0,
        },
        {
            "args": None,
            "case": 12,
            "input": [17, 0, 2, -7, 5, 11],
            "label": "drain-empty",
            "meter": [17, 0, 2, -7, 5, 11],
            "op": "drain",
            "returned": 0,
        },
        {
            "args": None,
            "case": 13,
            "input": [17, 9, 2, -7, 5, 11],
            "label": "drain-raw",
            "meter": [17, 0, 2, -7, 5, 11],
            "op": "drain",
            "returned": 9,
        },
        {
            "args": [0, 0],
            "case": 14,
            "input": [17, 9, 2, -7, 5, 11],
            "label": "restore-0-0",
            "meter": [17, 9, 2, -7, 5, 11],
            "op": "restore",
            "returned": None,
        },
        {
            "args": [0, 13],
            "case": 15,
            "input": [17, 9, 2, -7, 5, 11],
            "label": "restore-0-13",
            "meter": [17, 22, 2, -7, 5, 11],
            "op": "restore",
            "returned": None,
        },
        {
            "args": [19, 0],
            "case": 16,
            "input": [17, 9, 2, -7, 5, 11],
            "label": "restore-19-0",
            "meter": [36, 9, 2, -7, 5, 11],
            "op": "restore",
            "returned": None,
        },
        {
            "args": [19, 13],
            "case": 17,
            "input": [17, 9, 2, -7, 5, 11],
            "label": "restore-19-13",
            "meter": [36, 22, 2, -7, 5, 11],
            "op": "restore",
            "returned": None,
        },
        {
            "args": None,
            "case": 18,
            "input": [
                18446744073709551616,
                18446744073709551617,
                3,
                -18446744073709551618,
                0,
                18446744073709551620,
            ],
            "label": "forfeit-beyond-word",
            "meter": [0, 18446744073709551617, 3, -18446744073709551618, 0, 18446744073709551620],
            "op": "forfeit",
            "returned": None,
        },
        {
            "args": None,
            "case": 19,
            "input": [
                18446744073709551616,
                18446744073709551617,
                3,
                -18446744073709551618,
                18446744073709551619,
                18446744073709551620,
            ],
            "label": "withhold-beyond-word",
            "meter": [
                288230376151711744,
                18446744073709551617,
                3,
                -18446744073709551618,
                18446744073709551619,
                18446744073709551620,
            ],
            "op": "withhold",
            "returned": 18158513697557839872,
        },
        {
            "args": None,
            "case": 20,
            "input": [
                18446744073709551616,
                18446744073709551617,
                3,
                -18446744073709551618,
                18446744073709551619,
                18446744073709551620,
            ],
            "label": "drain-beyond-word",
            "meter": [
                18446744073709551616,
                0,
                3,
                -18446744073709551618,
                18446744073709551619,
                18446744073709551620,
            ],
            "op": "drain",
            "returned": 18446744073709551617,
        },
        {
            "args": [18446744073709551621, 18446744073709551622],
            "case": 21,
            "input": [
                18446744073709551616,
                18446744073709551617,
                3,
                -18446744073709551618,
                18446744073709551619,
                18446744073709551620,
            ],
            "label": "restore-beyond-word",
            "meter": [
                36893488147419103237,
                36893488147419103239,
                3,
                -18446744073709551618,
                18446744073709551619,
                18446744073709551620,
            ],
            "op": "restore",
            "returned": None,
        },
        {
            "args": None,
            "case": 22,
            "input": [130, 9, 2, -7, 5, 11],
            "label": "sequence-withhold",
            "meter": [2, 9, 2, -7, 5, 11],
            "op": "withhold",
            "returned": 128,
        },
        {
            "args": None,
            "case": 23,
            "input": [2, 9, 2, -7, 5, 11],
            "label": "sequence-drain",
            "meter": [2, 0, 2, -7, 5, 11],
            "op": "drain",
            "returned": 9,
        },
        {
            "args": None,
            "case": 24,
            "input": [2, 0, 2, -7, 5, 11],
            "label": "sequence-drain-again",
            "meter": [2, 0, 2, -7, 5, 11],
            "op": "drain",
            "returned": 0,
        },
        {
            "args": [128, 9],
            "case": 25,
            "input": [2, 0, 2, -7, 5, 11],
            "label": "sequence-restore",
            "meter": [130, 9, 2, -7, 5, 11],
            "op": "restore",
            "returned": None,
        },
        {
            "args": [0, 0],
            "case": 26,
            "input": [2, 0, 2, -7, 5, 11],
            "label": "sequence-restore-zero",
            "meter": [2, 0, 2, -7, 5, 11],
            "op": "restore",
            "returned": None,
        },
        {
            "args": None,
            "case": 27,
            "input": [16, 9, 9, 0, 0, 7],
            "label": "ordinary-rollback-forfeit",
            "meter": [0, 9, 9, 0, 0, 7],
            "op": "forfeit",
            "returned": None,
        },
        {
            "args": None,
            "case": 28,
            "input": [0, 9, 9, 0, 0, 7],
            "label": "ordinary-forfeit-again",
            "meter": [0, 9, 9, 0, 0, 7],
            "op": "forfeit",
            "returned": None,
        },
        {
            "args": None,
            "case": 29,
            "input": [23, 12, 12, 0, 0, 0],
            "label": "entry-rollback-forfeit",
            "meter": [0, 12, 12, 0, 0, 0],
            "op": "forfeit",
            "returned": None,
        },
    ],
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
        require(type(frame["kind"]) is str and frame["kind"] == "transfer", "frame kind")
        value = frame["value"]
        require(
            type(value) is dict
            and set(value) == {"label", "op", "input", "args", "returned", "meter"},
            "result fields",
        )
        require(type(value["label"]) is str and bool(value["label"]), "label")
        require(
            type(value["op"]) is str
            and value["op"] in {"forfeit", "withhold", "drain", "restore"},
            "operation",
        )
        meter(value["input"])
        meter(value["meter"])
        if value["op"] == "restore":
            require(type(value["args"]) is list and len(value["args"]) == 2, "restore arguments")
            for amount in value["args"]:
                integer(amount)
        else:
            require(value["args"] is None, "unexpected arguments")
        if value["op"] in {"withhold", "drain"}:
            integer(value["returned"])
        else:
            require(value["returned"] is None, "unexpected return value")
        result.append(frame)
    require(bool(result), "empty stream")
    return result


def expected_frames():
    return [
        {"kind": "transfer", "case": i, "value": {k: v for k, v in row.items() if k != "case"}}
        for i, row in enumerate(CATALOG["meter"])
    ]


def compare_frames(text):
    actual = parse_frames(text)
    require(actual == expected_frames(), "complete frozen frames disagree")
    return actual


def self_test():
    frames = expected_frames()
    stream = "".join(json.dumps(f) + "\n" for f in frames)
    require(compare_frames(stream) == frames, "whole positive stream")
    negatives = [
        "",
        "\n",
        "null",
        "[]",
        "true",
        "{}",
        stream + "\n",
        stream + "extra",
        stream[:-2],
        stream + json.dumps(frames[-1]),
        stream.replace('"case": 0', '"case": 0, "case": 0', 1),
        stream.replace('"case": 0', '"case": NaN', 1),
    ]

    def bad(base, path, value):
        frame = copy.deepcopy(base)
        frame["case"] = 0
        target = frame
        for key in path[:-1]:
            target = target[key]
        target[path[-1]] = value
        negatives.append(json.dumps(frame))

    for base in [frames[0], frames[3], frames[11], frames[14]]:
        for value in [True, False, None, "0", 0.0, [], {}, -1]:
            bad(base, ["case"], value)
            for field in ["input", "meter"]:
                for i in range(6):
                    if i != 3 or value != -1:
                        bad(base, ["value", field, i], value)
            if base["value"]["op"] in {"withhold", "drain"}:
                bad(base, ["value", "returned"], value)
            if base["value"]["op"] == "restore":
                for i in range(2):
                    bad(base, ["value", "args", i], value)
        for field in base:
            frame = copy.deepcopy(base)
            frame["case"] = 0
            del frame[field]
            negatives.append(json.dumps(frame))
        for field in base["value"]:
            frame = copy.deepcopy(base)
            frame["case"] = 0
            del frame["value"][field]
            negatives.append(json.dumps(frame))
        for value in [[], [0] * 5, [0] * 7, None, True, {}, "meter"]:
            bad(base, ["value", "input"], value)
            bad(base, ["value", "meter"], value)
        bad(base, ["value", "extra"], 0)
        bad(base, ["extra"], 0)
        bad(base, ["kind"], True)
        bad(base, ["value", "op"], True)
        bad(base, ["value", "op"], "charge")
        bad(base, ["value", "label"], True)
    for value in [[], [0], [0, 0, 0], True, {}, "args", None]:
        bad(frames[14], ["value", "args"], value)
    bad(frames[0], ["value", "returned"], 0)
    bad(frames[0], ["value", "args"], [0, 0])
    negatives.append(stream.replace('"returned": null', '"returned": null, "returned": null', 1))
    negatives.append(stream.replace('"gas"', '"gas"', 1) + "Infinity")
    for invalid in negatives:
        try:
            parse_frames(invalid)
        except FrameError:
            continue
        raise FrameError("invalid parser control accepted: " + repr(invalid))
    mismatches = [frames[:-1], frames[1:], list(reversed(frames))]
    for i in range(6):
        wrong = copy.deepcopy(frames)
        wrong[0]["value"]["meter"][i] += 1
        mismatches.append(wrong)
    wrong = copy.deepcopy(frames)
    wrong[3]["value"]["returned"] += 1
    mismatches.append(wrong)
    wrong = copy.deepcopy(frames)
    wrong[13]["value"]["returned"] = 0
    mismatches.append(wrong)
    wrong = copy.deepcopy(frames)
    wrong[3]["value"]["returned"], wrong[3]["value"]["meter"] = (
        wrong[3]["value"]["meter"],
        wrong[3]["value"]["returned"],
    )
    mismatches.append(wrong)
    wrong = copy.deepcopy(frames)
    wrong[14]["value"]["args"] = [0, 1]
    mismatches.append(wrong)
    for wrong in mismatches:
        try:
            compare_frames("".join(json.dumps(f) + "\n" for f in wrong))
        except FrameError:
            continue
        raise FrameError("incorrect complete stream accepted")
    print(
        json.dumps(
            {
                "positive_frames": len(frames),
                "negative_streams": len(negatives),
                "whole_mismatches": len(mismatches),
                "optimization": sys.flags.optimize,
            }
        )
    )


def lean_meter(value):
    return (
        "{ gasLeft := %s, stateGasLeft := %s, stateGasBaseline := %s, "
        "refundCounter := (%s), stateGasSpilled := %s, "
        "stateGasCommittedSpill := %s }"
    ) % tuple(value)


def emit_lean():
    print("import Lean\nimport STFSpec.Vm.Core\nopen STFSpec.Vm.Core\n")
    print("""private def meterJson (g : GasMeter) : Lean.Json :=
  Lean.toJson ([Lean.toJson g.gasLeft, Lean.toJson g.stateGasLeft,
    Lean.toJson g.stateGasBaseline, Lean.toJson g.refundCounter,
    Lean.toJson g.stateGasSpilled, Lean.toJson g.stateGasCommittedSpill] : List Lean.Json)
""")
    for row in CATALOG["meter"]:
        i, op = row["case"], row["op"]
        print("private def input%d : GasMeter := %s" % (i, lean_meter(row["input"])))
        if op == "forfeit":
            call = "forfeitRemainingGas input%d (by rfl)" % i
        elif op == "withhold":
            call = "withholdCreateGas input%d" % i
        elif op == "drain":
            call = "drainStateGasReservoir input%d" % i
        else:
            call = "restoreChildGas input%d %d %d" % (i, *row["args"])
        print("private def result%d := %s" % (i, call))
        args_json = (
            ".null"
            if row["args"] is None
            else "Lean.toJson ([%d, %d] : List Nat)" % tuple(row["args"])
        )
        returned = "Lean.toJson result%d.1" % i if op in {"withhold", "drain"} else ".null"
        result_meter = "result%d.2" % i if op in {"withhold", "drain"} else "result%d" % i
        print(
            '#eval IO.println ((Lean.Json.mkObj [("kind", Lean.toJson "transfer"), '
            '("case", Lean.toJson %d), ("value", Lean.Json.mkObj [("label", Lean.toJson %s), '
            '("op", Lean.toJson %s), ("input", meterJson input%d), ("args", %s), '
            '("returned", %s), ("meter", meterJson (%s))])]).compress)'
            % (i, json.dumps(row["label"]), json.dumps(op), i, args_json, returned, result_meter)
        )


PIN = "e1a316a06fc3d3e0a5da36fdc78580811e9d8a36"


def source_compare(args):
    """Compare saved transfer returns, all meter fields and original forfeit assertions."""
    import builtins
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
    numeric = importlib.import_module("ethereum_types.numeric")
    fork_types = importlib.import_module("ethereum.forks.amsterdam.fork_types")

    def functions():
        return [
            gas.forfeit_remaining_gas,
            gas.withhold_create_gas,
            gas.drain_state_gas_reservoir,
            gas.restore_child_gas,
            gas.max_message_call_gas,
            gas.GasMeter.__init__,
            numeric.Uint.__init__,
            numeric.Uint.__add__,
            numeric.Uint.__iadd__,
            numeric.Uint.__sub__,
            numeric.Uint.__isub__,
            numeric.Uint.__floordiv__,
            numeric.Uint.__eq__,
            numeric.Uint.__int__,
            numeric.Uint._in_range,
        ]

    def helper_binding(function, name):
        return (
            function.__globals__[name]
            if name in function.__globals__
            else function.__builtins__[name]
        )

    def globals_now():
        out = {
            "GasMeter": gas.GasMeter,
            "numeric.Uint": numeric.Uint,
            "gas.ExecutionGas": gas.ExecutionGas,
            "gas.StateGas": gas.StateGas,
            "fork.ExecutionGas": fork_types.ExecutionGas,
            "fork.StateGas": fork_types.StateGas,
            "gas.Uint": gas.Uint,
            "withhold.max": helper_binding(gas.withhold_create_gas, "max_message_call_gas"),
            "ExecutionGas.supertype": gas.ExecutionGas.__supertype__,
            "StateGas.supertype": gas.StateGas.__supertype__,
        }
        for function in functions()[:5]:
            prefix = function.__name__
            out[prefix] = function
            out[prefix + ".globals"] = function.__globals__
            for name in ["Uint", "ExecutionGas", "StateGas"]:
                if name in function.__code__.co_names:
                    out[prefix + "." + name] = helper_binding(function, name)
        return out

    require(
        gas.ExecutionGas is fork_types.ExecutionGas
        and gas.StateGas is fork_types.StateGas
        and gas.Uint is numeric.Uint
        and gas.ExecutionGas.__supertype__ is numeric.Uint
        and gas.StateGas.__supertype__ is numeric.Uint,
        "source aliases differ",
    )
    require(
        [f.__code__.co_firstlineno for f in functions()[:5]] == [662, 678, 701, 725, 861],
        "wrong original helper/callee locations",
    )
    require(all(f.__globals__ is vars(gas) for f in functions()[:5]), "wrong helper globals")
    require(
        helper_binding(gas.withhold_create_gas, "max_message_call_gas")
        is gas.max_message_call_gas,
        "withhold callee is not original max_message_call_gas",
    )
    for function in functions()[:5]:
        for name in ["Uint", "ExecutionGas", "StateGas"]:
            if name in function.__code__.co_names:
                require(helper_binding(function, name) is getattr(gas, name), "wrong helper alias")
    fields = [
        "gas_left",
        "state_gas_left",
        "state_gas_baseline",
        "refund_counter",
        "state_gas_spilled",
        "state_gas_committed_spill",
    ]
    require([f.name for f in dataclasses.fields(gas.GasMeter)] == fields, "wrong original schema")
    arithmetic = []
    for n, d, g, r in [
        (0, 0, 0, 0),
        (1, 0, 1, 0),
        (63, 0, 63, 0),
        (64, 1, 63, 1),
        (65, 1, 64, 1),
        (127, 1, 126, 1),
        (128, 2, 126, 2),
        (129, 2, 127, 2),
        (18446744073709551616, 288230376151711744, 18158513697557839872, 288230376151711744),
    ]:
        u = numeric.Uint(n)
        divided = u // numeric.Uint(64)
        grant = u - divided
        retained = u - grant
        require(
            all(type(v) is numeric.Uint for v in [divided, grant, retained])
            and [int(divided), int(grant), int(retained)] == [d, g, r],
            "Uint floor/subtraction semantics",
        )
        arithmetic.append(
            {"input": n, "division_grant_retained": [int(divided), int(grant), int(retained)]}
        )

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
            "arithmetic_probes": arithmetic,
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
                'actual GasMeter and four original transfer helpers plus real'
                ' max callee; no trace wrapper'
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
    progress = invalid_progress = 0

    def observe(m):
        values = [getattr(m, f) for f in fields]
        require(type(values[3]) is int, "signed refund class")
        require(
            all(type(v) is numeric.Uint for i, v in enumerate(values) if i != 3), "gas field class"
        )
        return [int(v) for v in values]

    def typed_meter(values):
        return gas.GasMeter(*[numeric.Uint(v) if i != 3 else v for i, v in enumerate(values)])

    try:
        with (output / "observations.jsonl").open("x") as observed:
            for row in CATALOG["meter"]:
                m = typed_meter(row["input"])
                original = observe(m)
                function = {
                    "forfeit": gas.forfeit_remaining_gas,
                    "withhold": gas.withhold_create_gas,
                    "drain": gas.drain_state_gas_reservoir,
                    "restore": gas.restore_child_gas,
                }[row["op"]]
                arguments = (
                    (m, *[numeric.Uint(a) for a in row["args"]])
                    if row["args"] is not None
                    else (m,)
                )
                returned = function(*arguments)
                if row["op"] in {"withhold", "drain"}:
                    require(type(returned) is numeric.Uint, "returned grant class")
                    returned_value = int(returned)
                else:
                    require(returned is None, "original helper returned a value")
                    returned_value = None
                result = observe(m)
                require(
                    result == row["meter"] and returned_value == row["returned"],
                    "original complete return/meter mismatch",
                )
                observed.write(
                    json.dumps(
                        {
                            "label": row["label"],
                            "op": row["op"],
                            "input": original,
                            "args": row["args"],
                            "returned": returned_value,
                            "return_class": type(returned).__module__
                            + "."
                            + type(returned).__qualname__,
                            "meter": result,
                        }
                    )
                    + "\n"
                )
                observed.flush()
                progress += 1
        with (output / "invalid-forfeit.jsonl").open("x") as observed:
            for values in CATALOG["invalid_forfeit"]:
                m = typed_meter(values)
                original = observe(m)
                try:
                    gas.forfeit_remaining_gas(m)
                except AssertionError as error:
                    frames_tb = []
                    tb = error.__traceback__
                    while tb is not None:
                        frames_tb.append(
                            {
                                "file": tb.tb_frame.f_code.co_filename,
                                "line": tb.tb_lineno,
                                "name": tb.tb_frame.f_code.co_name,
                            }
                        )
                        tb = tb.tb_next
                    location = frames_tb[-1]
                    require(
                        location
                        == {
                            "file": str(eels / "src/ethereum/forks/amsterdam/vm/gas.py"),
                            "line": 674,
                            "name": "forfeit_remaining_gas",
                        },
                        "wrong assertion location",
                    )
                    require(observe(m) == original == values, "assertion mutated complete meter")
                    observed.write(
                        json.dumps(
                            {
                                "input": original,
                                "meter": observe(m),
                                "exception": "AssertionError",
                                "traceback": frames_tb,
                            }
                        )
                        + "\n"
                    )
                    observed.flush()
                    invalid_progress += 1
                else:
                    raise FrameError("invalid original forfeit was accepted")
    finally:
        after = snapshot()
        (output / "after.json").write_text(json.dumps(after, indent=2))
        pin_after = pin_snapshot()
        (output / "pin-after.json").write_text(json.dumps(pin_after, indent=2))
        (output / "progress.json").write_text(
            json.dumps(
                {
                    "completed": progress,
                    "total": len(CATALOG["meter"]),
                    "invalid_completed": invalid_progress,
                    "invalid_total": len(CATALOG["invalid_forfeit"]),
                }
            )
        )
        require(
            before == after and pinned_before == pin_after, "source/runtime identities changed"
        )
    print(
        json.dumps(
            {
                "source_cases": progress,
                "complete_lean_frames": len(frames),
                "invalid_forfeit_probes": invalid_progress,
                "identities_unchanged": True,
                "assertions_enabled": True,
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
