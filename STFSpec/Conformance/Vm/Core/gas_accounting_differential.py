#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Complete signed refund/scalar controls and authenticated pinned numeric comparison.

Status: bounded local conformance. Date: 2026-10-17.
Source mode projects exactly original vm/__init__.py:242 on distinct typed meters;
it does not execute incorporate_child or storage handlers. The scalar maximum is
called directly. Source imports/execution require separately authorized inputs.
"""

import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys

# Literal full observations frozen before first target execution.
CATALOG = [
    {
        "arg": 0,
        "case": 0,
        "input": [0, 0, 0, 0, 0, 0],
        "label": "zero",
        "meter": [0, 0, 0, 0, 0, 0],
        "op": "refund",
        "returned": None,
    },
    {
        "arg": 0,
        "case": 1,
        "input": [17, 9, 2, -7, 5, 11],
        "label": "raw-zero",
        "meter": [17, 9, 2, -7, 5, 11],
        "op": "refund",
        "returned": None,
    },
    {
        "arg": -7,
        "case": 2,
        "input": [17, 9, 2, 3, 5, 11],
        "label": "negative",
        "meter": [17, 9, 2, -4, 5, 11],
        "op": "refund",
        "returned": None,
    },
    {
        "arg": 3,
        "case": 3,
        "input": [17, 9, 2, -7, 5, 11],
        "label": "positive",
        "meter": [17, 9, 2, -4, 5, 11],
        "op": "refund",
        "returned": None,
    },
    {
        "arg": 10,
        "case": 4,
        "input": [17, 9, 2, -7, 5, 11],
        "label": "cross-positive",
        "meter": [17, 9, 2, 3, 5, 11],
        "op": "refund",
        "returned": None,
    },
    {
        "arg": -10,
        "case": 5,
        "input": [17, 9, 2, 7, 5, 11],
        "label": "cross-negative",
        "meter": [17, 9, 2, -3, 5, 11],
        "op": "refund",
        "returned": None,
    },
    {
        "arg": -7,
        "case": 6,
        "input": [17, 9, 2, 7, 5, 11],
        "label": "cancel-positive",
        "meter": [17, 9, 2, 0, 5, 11],
        "op": "refund",
        "returned": None,
    },
    {
        "arg": 7,
        "case": 7,
        "input": [17, 9, 2, -7, 5, 11],
        "label": "cancel-negative",
        "meter": [17, 9, 2, 0, 5, 11],
        "op": "refund",
        "returned": None,
    },
    {
        "arg": -1,
        "case": 8,
        "input": [0, 9, 2, 0, 5, 11],
        "label": "add-zero",
        "meter": [0, 9, 2, -1, 5, 11],
        "op": "refund",
        "returned": None,
    },
    {
        "arg": 1,
        "case": 9,
        "input": [
            17,
            9,
            2,
            115792089237316195423570985008687907853269984665640564039457584007913129639936,
            5,
            11,
        ],
        "label": "beyond-u256-positive",
        "meter": [
            17,
            9,
            2,
            115792089237316195423570985008687907853269984665640564039457584007913129639937,
            5,
            11,
        ],
        "op": "refund",
        "returned": None,
    },
    {
        "arg": -1,
        "case": 10,
        "input": [
            17,
            9,
            2,
            -115792089237316195423570985008687907853269984665640564039457584007913129639936,
            5,
            11,
        ],
        "label": "beyond-u256-negative",
        "meter": [
            17,
            9,
            2,
            -115792089237316195423570985008687907853269984665640564039457584007913129639937,
            5,
            11,
        ],
        "op": "refund",
        "returned": None,
    },
    {
        "arg": 1361129467683753853853498429727072845829,
        "case": 11,
        "input": [
            1361129467683753853853498429727072845824,
            1361129467683753853853498429727072845825,
            3,
            -1361129467683753853853498429727072845826,
            1361129467683753853853498429727072845827,
            1361129467683753853853498429727072845828,
        ],
        "label": "large-all-fields",
        "meter": [
            1361129467683753853853498429727072845824,
            1361129467683753853853498429727072845825,
            3,
            3,
            1361129467683753853853498429727072845827,
            1361129467683753853853498429727072845828,
        ],
        "op": "refund",
        "returned": None,
    },
    {
        "arg": 0,
        "case": 12,
        "input": None,
        "label": "max-0",
        "meter": None,
        "op": "maximum",
        "returned": 0,
    },
    {
        "arg": 1,
        "case": 13,
        "input": None,
        "label": "max-1",
        "meter": None,
        "op": "maximum",
        "returned": 1,
    },
    {
        "arg": 62,
        "case": 14,
        "input": None,
        "label": "max-62",
        "meter": None,
        "op": "maximum",
        "returned": 62,
    },
    {
        "arg": 63,
        "case": 15,
        "input": None,
        "label": "max-63",
        "meter": None,
        "op": "maximum",
        "returned": 63,
    },
    {
        "arg": 64,
        "case": 16,
        "input": None,
        "label": "max-64",
        "meter": None,
        "op": "maximum",
        "returned": 63,
    },
    {
        "arg": 65,
        "case": 17,
        "input": None,
        "label": "max-65",
        "meter": None,
        "op": "maximum",
        "returned": 64,
    },
    {
        "arg": 127,
        "case": 18,
        "input": None,
        "label": "max-127",
        "meter": None,
        "op": "maximum",
        "returned": 126,
    },
    {
        "arg": 128,
        "case": 19,
        "input": None,
        "label": "max-128",
        "meter": None,
        "op": "maximum",
        "returned": 126,
    },
    {
        "arg": 129,
        "case": 20,
        "input": None,
        "label": "max-129",
        "meter": None,
        "op": "maximum",
        "returned": 127,
    },
    {
        "arg": 4095,
        "case": 21,
        "input": None,
        "label": "max-4095",
        "meter": None,
        "op": "maximum",
        "returned": 4032,
    },
    {
        "arg": 4096,
        "case": 22,
        "input": None,
        "label": "max-4096",
        "meter": None,
        "op": "maximum",
        "returned": 4032,
    },
    {
        "arg": 4097,
        "case": 23,
        "input": None,
        "label": "max-4097",
        "meter": None,
        "op": "maximum",
        "returned": 4033,
    },
    {
        "arg": 18446744073709551616,
        "case": 24,
        "input": None,
        "label": "max-18446744073709551616",
        "meter": None,
        "op": "maximum",
        "returned": 18158513697557839872,
    },
    {
        "arg": 115792089237316195423570985008687907853269984665640564039457584007913129639936,
        "case": 25,
        "input": None,
        (
            'label'
        ): (
            'max-11579208923731619542357098500868790785326998466564056403'
            '9457584007913129639936'
        ),
        "meter": None,
        "op": "maximum",
        "returned": 113982837842983129870077688367927159293062641155239930226341059257789486989312,
    },
]


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
        require(type(frame["kind"]) is str and frame["kind"] == "accounting", "frame kind")
        value = frame["value"]
        require(
            type(value) is dict
            and set(value) == {"label", "op", "input", "arg", "returned", "meter"},
            "result fields",
        )
        require(type(value["label"]) is str and bool(value["label"]), "label")
        require(type(value["op"]) is str and value["op"] in {"refund", "maximum"}, "operation")
        integer(value["arg"], value["op"] == "refund")
        if value["op"] == "refund":
            meter(value["input"])
            meter(value["meter"])
            require(value["returned"] is None, "unexpected return")
        else:
            require(value["input"] is None and value["meter"] is None, "scalar meter")
            integer(value["returned"])
        result.append(frame)
    require(bool(result), "empty stream")
    return result


def expected_frames():
    return [
        {"kind": "accounting", "case": i, "value": {k: v for k, v in row.items() if k != "case"}}
        for i, row in enumerate(CATALOG)
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
        stream.replace('"case": 0', '"case": Infinity', 1),
    ]

    def bad(base, path, value):
        frame = copy.deepcopy(base)
        frame["case"] = 0
        target = frame
        for key in path[:-1]:
            target = target[key]
        target[path[-1]] = value
        negatives.append(json.dumps(frame))

    for base in [frames[0], frames[12]]:
        for value in [True, False, None, "0", 0.0, [], {}, -1]:
            bad(base, ["case"], value)
            if base["value"]["op"] == "maximum" or value != -1:
                bad(base, ["value", "arg"], value)
            if base["value"]["op"] == "refund":
                for field in ["input", "meter"]:
                    for i in range(6):
                        if i != 3 or value != -1:
                            bad(base, ["value", field, i], value)
            else:
                bad(base, ["value", "returned"], value)
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
        bad(base, ["extra"], 0)
        bad(base, ["value", "extra"], 0)
        bad(base, ["kind"], True)
        bad(base, ["value", "op"], True)
        bad(base, ["value", "op"], "charge")
        bad(base, ["value", "label"], True)
    for value in [[], [0] * 5, [0] * 7, None, True, {}, "meter"]:
        bad(frames[0], ["value", "input"], value)
        bad(frames[0], ["value", "meter"], value)
    bad(frames[0], ["value", "returned"], 0)
    for field in ["input", "meter"]:
        for value in [0, True, [], [0] * 6]:
            bad(frames[12], ["value", field], value)
    negatives.append(stream.replace('"returned": null', '"returned": null, "returned": null', 1))
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
    wrong[12]["value"]["returned"] += 1
    mismatches.append(wrong)
    wrong = copy.deepcopy(frames)
    wrong[0]["value"]["arg"] += 1
    mismatches.append(wrong)
    wrong = copy.deepcopy(frames)
    wrong[0]["value"]["label"] += "x"
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
    for row in CATALOG:
        i, op = row["case"], row["op"]
        if op == "refund":
            print("private def input%d : GasMeter := %s" % (i, lean_meter(row["input"])))
            print("private def result%d := addRefund input%d (%d)" % (i, i, row["arg"]))
            input_json = "meterJson input%d" % i
            meter_json = "meterJson result%d" % i
            returned = ".null"
        else:
            print("private def result%d := maxMessageCallGas %d" % (i, row["arg"]))
            input_json = meter_json = ".null"
            returned = "Lean.toJson result%d" % i
        print(
            '#eval IO.println ((Lean.Json.mkObj [("kind", Lean.toJson "accounting"), '
            '("case", Lean.toJson %d), ("value", Lean.Json.mkObj [("label", Lean.toJson %s), '
            '("op", Lean.toJson %s), ("input", %s), ("arg", Lean.toJson (%d : Int)), '
            '("returned", %s), ("meter", %s)])]).compress)'
            % (
                i,
                json.dumps(row["label"]),
                json.dumps(op),
                input_json,
                row["arg"],
                returned,
                meter_json,
            )
        )


PIN = "e1a316a06fc3d3e0a5da36fdc78580811e9d8a36"


def source_compare(args):
    """Compare exact original refund statements and scalar calls with complete frozen frames."""
    import builtins
    import ast
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
    vm = importlib.import_module("ethereum.forks.amsterdam.vm")
    statement_path = eels / "src/ethereum/forks/amsterdam/vm/__init__.py"
    source_text = statement_path.read_text()
    syntax = ast.parse(source_text, filename=str(statement_path))
    original_function = next(
        n for n in syntax.body if isinstance(n, ast.FunctionDef) and n.name == "incorporate_child"
    )
    selected = [
        n for n in ast.walk(original_function) if isinstance(n, ast.AugAssign) and n.lineno == 242
    ]
    require(len(selected) == 1, "original statement location")
    statement = selected[0]
    expected_ast = (
        "AugAssign(target=Attribute(value=Name(id='gas_meter', ctx=Lo"
        "ad()), attr='refund_counter', ctx=Store()), op=Add(), value="
        "Attribute(value=Name(id='child_meter', ctx=Load()), attr='re"
        "fund_counter', ctx=Load()))"
    )
    require(
        ast.dump(statement) == expected_ast and statement.end_lineno == 242,
        "original statement shape",
    )
    require(
        ast.get_source_segment(source_text, statement)
        == "gas_meter.refund_counter += child_meter.refund_counter",
        "original source span",
    )
    projected_code = compile(
        ast.Module(body=[statement], type_ignores=[]), str(statement_path), "exec"
    )
    projection = {
        "source": str(statement_path),
        "line": 242,
        "source_sha256": sha(source_text.encode()),
        "ast": ast.dump(statement, include_attributes=True),
        "segment": ast.get_source_segment(source_text, statement),
        "code_sha256": sha(marshal.dumps(projected_code, 2)),
        "co_names": list(projected_code.co_names),
        "original_globals_id": id(vars(vm)),
        "builtin_int_id": id(builtins.int),
        "builtin_int_add_id": id(builtins.int.__add__),
    }

    def functions():
        return [
            gas.max_message_call_gas,
            gas.GasMeter.__init__,
            numeric.Uint.__init__,
            numeric.Uint.__sub__,
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
        return {
            "GasMeter": gas.GasMeter,
            "numeric.Uint": numeric.Uint,
            "gas.ExecutionGas": gas.ExecutionGas,
            "gas.StateGas": gas.StateGas,
            "fork.ExecutionGas": fork_types.ExecutionGas,
            "fork.StateGas": fork_types.StateGas,
            "gas.Uint": gas.Uint,
            "max_message_call_gas": gas.max_message_call_gas,
            "max.globals": gas.max_message_call_gas.__globals__,
            "max.ExecutionGas": helper_binding(gas.max_message_call_gas, "ExecutionGas"),
            "ExecutionGas.supertype": gas.ExecutionGas.__supertype__,
            "StateGas.supertype": gas.StateGas.__supertype__,
            "builtin.int": builtins.int,
            "builtin.int.add": builtins.int.__add__,
            "projection.code": projected_code,
            "projection.globals": vars(vm),
        }

    require(
        gas.ExecutionGas is fork_types.ExecutionGas
        and gas.StateGas is fork_types.StateGas
        and gas.Uint is numeric.Uint
        and gas.ExecutionGas.__supertype__ is numeric.Uint
        and gas.StateGas.__supertype__ is numeric.Uint,
        "source aliases differ",
    )
    require(
        gas.max_message_call_gas.__code__.co_firstlineno == 861
        and gas.max_message_call_gas.__globals__ is vars(gas),
        "original maximum location/globals",
    )
    require(
        helper_binding(gas.max_message_call_gas, "ExecutionGas") is gas.ExecutionGas,
        "original maximum alias",
    )
    fields = [
        "gas_left",
        "state_gas_left",
        "state_gas_baseline",
        "refund_counter",
        "state_gas_spilled",
        "state_gas_committed_spill",
    ]
    require([f.name for f in dataclasses.fields(gas.GasMeter)] == fields, "original schema")
    arithmetic = []
    for n, d, g in [
        (0, 0, 0),
        (63, 0, 63),
        (64, 1, 63),
        (65, 1, 64),
        (128, 2, 126),
        (18446744073709551616, 288230376151711744, 18158513697557839872),
    ]:
        u = numeric.Uint(n)
        divided = u // numeric.Uint(64)
        grant = u - divided
        require(
            type(divided) is numeric.Uint
            and type(grant) is numeric.Uint
            and [int(divided), int(grant)] == [d, g],
            "Uint floor/subtraction semantics",
        )
        arithmetic.append({"input": n, "division_grant": [int(divided), int(grant)]})

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
            "projection": projection,
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
                'exact original refund AugAssign projection on distinct actua'
                'l GasMeters; direct original max helper; no merge/old-helper'
                ' replay'
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

    def typed_meter(values):
        return gas.GasMeter(*[numeric.Uint(v) if i != 3 else v for i, v in enumerate(values)])

    try:
        with (output / "observations.jsonl").open("x") as observed:
            for row in CATALOG:
                child_before = child_after = None
                if row["op"] == "refund":
                    parent = typed_meter(row["input"])
                    child = typed_meter([31, 37, 41, row["arg"], 43, 47])
                    require(parent is not child, "aliased source holders")
                    original = observe(parent)
                    child_before = observe(child)
                    bindings = {"gas_meter": parent, "child_meter": child}
                    returned = exec(projected_code, vars(vm), bindings)
                    require(returned is None, "statement return")
                    require(
                        bindings == {"gas_meter": parent, "child_meter": child},
                        "statement bindings",
                    )
                    child_after = observe(child)
                    require(child_before == child_after, "statement mutated child")
                    result = observe(parent)
                    returned_value = None
                else:
                    original = result = None
                    returned = gas.max_message_call_gas(numeric.Uint(row["arg"]))
                    require(type(returned) is numeric.Uint, "scalar return class")
                    returned_value = int(returned)
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
                            "arg": row["arg"],
                            "returned": returned_value,
                            "return_class": type(returned).__module__
                            + "."
                            + type(returned).__qualname__,
                            "meter": result,
                            "child_before": child_before,
                            "child_after": child_after,
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
            json.dumps({"completed": progress, "total": len(CATALOG)})
        )
        require(
            before == after and pinned_before == pin_after, "source/runtime identities changed"
        )
    print(
        json.dumps(
            {
                "source_cases": progress,
                "complete_lean_frames": len(frames),
                "refund_statement_projections": 12,
                "direct_maximum_calls": 14,
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
