#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Complete-field refund controls and authenticated pinned helper comparison.

Status: bounded local conformance. Date: 2026-10-17.
--self-test supports normal/-O; source execution keeps assertions enabled.
--preflight authenticates imports; --source calls only untouched credit/repay.
"""

import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys

# Literal complete-field expectations frozen before target execution.
CATALOG = {
    "compositions": {
        "charge-refund": [
            [20, 10, 10, -4, 0, 3],
            [15, 0, 10, -4, 5, 3],
            [17, 0, 10, -4, 3, 3],
            [20, 3, 10, -4, 0, 3],
        ],
        "counterexample": [[10, 4, 1, -3, 6, 7], [10, 2, 1, -3, 6, 7], [12, 2, 1, -3, 4, 7]],
        "credit-repay": [
            [10, 4, 1, -3, 6, 7],
            [12, 4, 1, -3, 4, 7],
            [16, 0, 1, -3, 0, 7],
            [16, 0, 1, -3, 0, 7],
        ],
    },
    "meter": [
        {
            "amount": 0,
            "case": 0,
            "input": [0, 0, 0, 0, 0, 0],
            "label": "credit-zero",
            "meter": [0, 0, 0, 0, 0, 0],
            "op": "credit",
        },
        {
            "amount": 0,
            "case": 1,
            "input": [10, 4, 1, -3, 6, 7],
            "label": "credit-zero-raw",
            "meter": [10, 4, 1, -3, 6, 7],
            "op": "credit",
        },
        {
            "amount": 2,
            "case": 2,
            "input": [10, 4, 1, -3, 6, 7],
            "label": "credit-less",
            "meter": [12, 4, 1, -3, 4, 7],
            "op": "credit",
        },
        {
            "amount": 6,
            "case": 3,
            "input": [10, 4, 1, -3, 6, 7],
            "label": "credit-equal",
            "meter": [16, 4, 1, -3, 0, 7],
            "op": "credit",
        },
        {
            "amount": 8,
            "case": 4,
            "input": [10, 4, 1, -3, 6, 7],
            "label": "credit-greater",
            "meter": [16, 6, 1, -3, 0, 7],
            "op": "credit",
        },
        {
            "amount": 8,
            "case": 5,
            "input": [0, 0, 9, 4, 0, 7],
            "label": "credit-no-pending",
            "meter": [0, 8, 9, 4, 0, 7],
            "op": "credit",
        },
        {
            "amount": 8,
            "case": 6,
            "input": [0, 0, 9, -4, 6, 7],
            "label": "credit-zero-execution",
            "meter": [6, 2, 9, -4, 0, 7],
            "op": "credit",
        },
        {
            "amount": None,
            "case": 7,
            "input": [0, 0, 0, 0, 0, 0],
            "label": "repay-zero",
            "meter": [0, 0, 0, 0, 0, 0],
            "op": "repay",
        },
        {
            "amount": None,
            "case": 8,
            "input": [10, 0, 1, -3, 6, 7],
            "label": "repay-no-reservoir",
            "meter": [10, 0, 1, -3, 6, 7],
            "op": "repay",
        },
        {
            "amount": None,
            "case": 9,
            "input": [10, 4, 1, -3, 0, 7],
            "label": "repay-no-pending",
            "meter": [10, 4, 1, -3, 0, 7],
            "op": "repay",
        },
        {
            "amount": None,
            "case": 10,
            "input": [10, 4, 1, -3, 6, 7],
            "label": "repay-less",
            "meter": [14, 0, 1, -3, 2, 7],
            "op": "repay",
        },
        {
            "amount": None,
            "case": 11,
            "input": [10, 6, 1, 4, 6, 7],
            "label": "repay-equal",
            "meter": [16, 0, 1, 4, 0, 7],
            "op": "repay",
        },
        {
            "amount": None,
            "case": 12,
            "input": [0, 8, 1, -3, 6, 7],
            "label": "repay-greater-zero-execution",
            "meter": [6, 2, 1, -3, 0, 7],
            "op": "repay",
        },
        {
            "amount": 1361129467683753853853498429727072845829,
            "case": 13,
            "input": [
                1361129467683753853853498429727072845824,
                1361129467683753853853498429727072845825,
                0,
                -1361129467683753853853498429727072845824,
                1361129467683753853853498429727072845826,
                1361129467683753853853498429727072845827,
            ],
            "label": "credit-beyond-word",
            "meter": [
                2722258935367507707706996859454145691650,
                1361129467683753853853498429727072845828,
                0,
                -1361129467683753853853498429727072845824,
                0,
                1361129467683753853853498429727072845827,
            ],
            "op": "credit",
        },
        {
            "amount": None,
            "case": 14,
            "input": [
                1361129467683753853853498429727072845824,
                1361129467683753853853498429727072845825,
                0,
                -1361129467683753853853498429727072845824,
                1361129467683753853853498429727072845826,
                1361129467683753853853498429727072845827,
            ],
            "label": "repay-beyond-word",
            "meter": [
                2722258935367507707706996859454145691649,
                0,
                0,
                -1361129467683753853853498429727072845824,
                1,
                1361129467683753853853498429727072845827,
            ],
            "op": "repay",
        },
        {
            "amount": 2,
            "case": 15,
            "input": [15, 0, 10, -4, 5, 3],
            "label": "charge-sequence-credit-two",
            "meter": [17, 0, 10, -4, 3, 3],
            "op": "credit",
        },
        {
            "amount": 6,
            "case": 16,
            "input": [17, 0, 10, -4, 3, 3],
            "label": "charge-sequence-credit-six",
            "meter": [20, 3, 10, -4, 0, 3],
            "op": "credit",
        },
        {
            "amount": None,
            "case": 17,
            "input": [12, 4, 1, -3, 4, 7],
            "label": "credit-sequence-repay",
            "meter": [16, 0, 1, -3, 0, 7],
            "op": "repay",
        },
        {
            "amount": None,
            "case": 18,
            "input": [16, 0, 1, -3, 0, 7],
            "label": "credit-sequence-repay-again",
            "meter": [16, 0, 1, -3, 0, 7],
            "op": "repay",
        },
        {
            "amount": 2,
            "case": 19,
            "input": [10, 2, 1, -3, 6, 7],
            "label": "counterexample-credit",
            "meter": [12, 2, 1, -3, 4, 7],
            "op": "credit",
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
        require(frame["kind"] == "refund", "frame kind")
        value = frame["value"]
        require(
            type(value) is dict and set(value) == {"label", "op", "input", "amount", "meter"},
            "result fields",
        )
        require(type(value["label"]) is str and bool(value["label"]), "label")
        require(type(value["op"]) is str and value["op"] in {"credit", "repay"}, "operation")
        meter(value["input"])
        meter(value["meter"])
        if value["op"] == "credit":
            integer(value["amount"])
        else:
            require(value["amount"] is None, "unexpected amount")
        result.append(frame)
    require(bool(result), "empty stream")
    return result


def expected_frames():
    return [
        {"kind": "refund", "case": i, "value": {k: v for k, v in row.items() if k != "case"}}
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
    bad(["kind"], True)
    bad(["value", "amount"], None)
    bad(["value", "op"], True)
    bad(["value", "op"], "charge")
    bad(["value", "label"], True)
    for value in [True, False, None, "0", 0.0, [], {}, -1]:
        frame = copy.deepcopy(frames[2])
        frame["case"] = 0
        frame["value"]["amount"] = value
        negatives.append(json.dumps(frame))
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
        call = (
            ("creditStateGasRefund input%d %d" % (i, row["amount"]))
            if op == "credit"
            else ("repayStateGasSpill input%d" % i)
        )
        amount = ".null" if row["amount"] is None else "Lean.toJson %d" % row["amount"]
        print(
            '#eval IO.println ((Lean.Json.mkObj [("kind", Lean.toJson "refund"), '
            '("case", Lean.toJson %d), ("value", Lean.Json.mkObj [("label", Lean.toJson %s), '
            '("op", Lean.toJson %s), ("input", meterJson input%d), ("amount", %s), '
            '("meter", meterJson (%s))])]).compress)'
            % (i, json.dumps(row["label"]), json.dumps(op), i, amount, call)
        )


PIN = "e1a316a06fc3d3e0a5da36fdc78580811e9d8a36"


def source_compare(args):
    """Compare complete credit/repay meters, None returns and enabled postconditions."""
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
            gas.credit_state_gas_refund,
            gas.repay_state_gas_spill,
            gas.GasMeter.__init__,
            numeric.Uint.__init__,
            numeric.Uint.__add__,
            numeric.Uint.__iadd__,
            numeric.Uint.__sub__,
            numeric.Uint.__isub__,
            numeric.Uint.__lt__,
            numeric.Uint.__le__,
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
        return {
            "GasMeter": gas.GasMeter,
            "numeric.Uint": numeric.Uint,
            "gas.ExecutionGas": gas.ExecutionGas,
            "gas.StateGas": gas.StateGas,
            "fork.ExecutionGas": fork_types.ExecutionGas,
            "fork.StateGas": fork_types.StateGas,
            "credit": gas.credit_state_gas_refund,
            "repay": gas.repay_state_gas_spill,
            "gas.Uint": gas.Uint,
            "min": helper_binding(gas.credit_state_gas_refund, "min"),
            "repay.min": helper_binding(gas.repay_state_gas_spill, "min"),
            "builtins.min": builtins.min,
            "credit.globals": gas.credit_state_gas_refund.__globals__,
            "repay.globals": gas.repay_state_gas_spill.__globals__,
            "credit.Uint": helper_binding(gas.credit_state_gas_refund, "Uint"),
            "repay.Uint": helper_binding(gas.repay_state_gas_spill, "Uint"),
            "credit.ExecutionGas": helper_binding(gas.credit_state_gas_refund, "ExecutionGas"),
            "repay.ExecutionGas": helper_binding(gas.repay_state_gas_spill, "ExecutionGas"),
        }

    require(
        gas.ExecutionGas is fork_types.ExecutionGas and gas.StateGas is fork_types.StateGas,
        "source aliases differ",
    )
    require(
        [f.__code__.co_firstlineno for f in functions()[:2]] == [606, 631],
        "wrong original helper locations",
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

    require(
        gas.credit_state_gas_refund.__globals__ is vars(gas)
        and gas.repay_state_gas_spill.__globals__ is vars(gas),
        "wrong helper global dictionaries",
    )
    require(
        gas.Uint is numeric.Uint
        and globals_now()["min"] is builtins.min
        and globals_now()["repay.min"] is builtins.min,
        "wrong Uint/min bindings",
    )
    require(
        builtins.min.__module__ == "builtins" and builtins.min.__name__ == "min",
        "wrong builtin minimum",
    )
    arithmetic = []
    for a, b, x, ra, rb in [(0, 6, 0, 0, 6), (2, 6, 2, 0, 4), (6, 6, 6, 0, 0), (8, 6, 6, 2, 0)]:
        ua, ub = numeric.Uint(a), numeric.Uint(b)
        ux = builtins.min(ua, ub)
        actual = [int(ux), int(ua - ux), int(ub - ux)]
        require(
            type(ux) is numeric.Uint and actual == [x, ra, rb], "Uint/min/subtraction semantics"
        )
        arithmetic.append({"input": [a, b], "minimum_residuals": actual})

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
            "minimum": {
                "id": id(builtins.min),
                "module": builtins.min.__module__,
                "name": builtins.min.__name__,
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
            "adapter": "actual GasMeter and original credit/repay helpers; no trace wrapper",
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
                    "credit": gas.credit_state_gas_refund,
                    "repay": gas.repay_state_gas_spill,
                }[row["op"]]
                arguments = (m, numeric.Uint(row["amount"])) if row["op"] == "credit" else (m,)
                returned = function(*arguments)
                require(returned is None, "original helper returned a value")
                result = observe(m)
                require(result == row["meter"], "original whole meter mismatch")
                post = result[1] == 0 or result[4] == 0
                if row["op"] == "repay":
                    require(post, "original repayment postcondition")
                observed.write(
                    json.dumps(
                        {
                            "label": row["label"],
                            "op": row["op"],
                            "input": original,
                            "amount": row["amount"],
                            "returned": returned,
                            "meter": result,
                            "repay_post": post if row["op"] == "repay" else None,
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
                "repay_assertions_enabled": True,
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
