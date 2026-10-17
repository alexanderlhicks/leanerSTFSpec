#!/usr/bin/env python3
"""Complete signed transaction-usage observations with authenticated original-source comparison."""

import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys

PIN = "e1a316a06fc3d3e0a5da36fdc78580811e9d8a36"
# Independent complete literals frozen before any target/source execution.
CATALOG = [
    {
        "case": 0,
        "label": "all-zero",
        "input": [0, 0, 0, 0, 0, 0],
        "grant": 0,
        "returned": 0,
        "meter": [0, 0, 0, 0, 0, 0],
    },
    {
        "case": 1,
        "label": "reservoir-draw",
        "input": [17, 7, 4, -31, 0, 0],
        "grant": 10,
        "returned": 3,
        "meter": [17, 7, 4, -31, 0, 0],
    },
    {
        "case": 2,
        "label": "negative-without-spill",
        "input": [3, 19, 5, -11, 0, 0],
        "grant": 8,
        "returned": -11,
        "meter": [3, 19, 5, -11, 0, 0],
    },
    {
        "case": 3,
        "label": "spill-cancellation",
        "input": [7, 29, 4, -71, 8, 10],
        "grant": 11,
        "returned": 0,
        "meter": [7, 29, 4, -71, 8, 10],
    },
    {
        "case": 4,
        "label": "pending-only",
        "input": [2, 17, 8, 91, 13, 0],
        "grant": 9,
        "returned": 5,
        "meter": [2, 17, 8, 91, 13, 0],
    },
    {
        "case": 5,
        "label": "committed-only",
        "input": [2, 17, 8, 91, 0, 19],
        "grant": 9,
        "returned": 11,
        "meter": [2, 17, 8, 91, 0, 19],
    },
    {
        "case": 6,
        "label": "both-spills",
        "input": [0, 17, 8, -91, 13, 19],
        "grant": 9,
        "returned": 24,
        "meter": [0, 17, 8, -91, 13, 19],
    },
    {
        "case": 7,
        "label": "negative-both-spills",
        "input": [23, 51, 9, -17, 7, 11],
        "grant": 12,
        "returned": -21,
        "meter": [23, 51, 9, -17, 7, 11],
    },
    {
        "case": 8,
        "label": "guidance-negative-witness",
        "input": [13, 21, 9, 99, 3, 5],
        "grant": 10,
        "returned": -3,
        "meter": [13, 21, 9, 99, 3, 5],
    },
    {
        "case": 9,
        "label": "ignored-fields-low-baseline",
        "input": [0, 21, 0, -999999, 3, 5],
        "grant": 10,
        "returned": -3,
        "meter": [0, 21, 0, -999999, 3, 5],
    },
    {
        "case": 10,
        "label": "ignored-fields-exact-baseline",
        "input": [999999, 21, 10, 0, 3, 5],
        "grant": 10,
        "returned": -3,
        "meter": [999999, 21, 10, 0, 3, 5],
    },
    {
        "case": 11,
        "label": "grant-increment",
        "input": [13, 21, 9, 99, 3, 5],
        "grant": 11,
        "returned": -2,
        "meter": [13, 21, 9, 99, 3, 5],
    },
    {
        "case": 12,
        "label": "reservoir-increment",
        "input": [13, 22, 9, 99, 3, 5],
        "grant": 10,
        "returned": -4,
        "meter": [13, 22, 9, 99, 3, 5],
    },
    {
        "case": 13,
        "label": "pending-increment",
        "input": [13, 21, 9, 99, 4, 5],
        "grant": 10,
        "returned": -2,
        "meter": [13, 21, 9, 99, 4, 5],
    },
    {
        "case": 14,
        "label": "committed-increment",
        "input": [13, 21, 9, 99, 3, 6],
        "grant": 10,
        "returned": -2,
        "meter": [13, 21, 9, 99, 3, 6],
    },
    {
        "case": 15,
        "label": "baseline-is-not-grant",
        "input": [0, 4, 99, 71, 0, 0],
        "grant": 100,
        "returned": 96,
        "meter": [0, 4, 99, 71, 0, 0],
    },
    {
        "case": 16,
        "label": "beyond-u64-negative",
        "input": [
            18446744073709551617,
            18446744073709551619,
            18446744073709551615,
            -18446744073709551618,
            1,
            1,
        ],
        "grant": 18446744073709551616,
        "returned": -1,
        "meter": [
            18446744073709551617,
            18446744073709551619,
            18446744073709551615,
            -18446744073709551618,
            1,
            1,
        ],
    },
    {
        "case": 17,
        "label": "beyond-u256-signed-subtraction",
        "input": [
            115792089237316195423570985008687907853269984665640564039457584007913129639937,
            115792089237316195423570985008687907853269984665640564039457584007913129639953,
            115792089237316195423570985008687907853269984665640564039457584007913129639935,
            -115792089237316195423570985008687907853269984665640564039457584007913129639937,
            3,
            5,
        ],
        "grant": 115792089237316195423570985008687907853269984665640564039457584007913129639936,
        "returned": -9,
        "meter": [
            115792089237316195423570985008687907853269984665640564039457584007913129639937,
            115792089237316195423570985008687907853269984665640564039457584007913129639953,
            115792089237316195423570985008687907853269984665640564039457584007913129639935,
            -115792089237316195423570985008687907853269984665640564039457584007913129639937,
            3,
            5,
        ],
    },
    {
        "case": 18,
        "label": "beyond-u256-spill-sum",
        "input": [
            0,
            0,
            0,
            -3,
            115792089237316195423570985008687907853269984665640564039457584007913129639936,
            115792089237316195423570985008687907853269984665640564039457584007913129639936,
        ],
        "grant": 0,
        "returned": 231584178474632390847141970017375815706539969331281128078915168015826259279872,
        "meter": [
            0,
            0,
            0,
            -3,
            115792089237316195423570985008687907853269984665640564039457584007913129639936,
            115792089237316195423570985008687907853269984665640564039457584007913129639936,
        ],
    },
    {
        "case": 19,
        "label": "beyond-u256-negative-return",
        "input": [
            19,
            115792089237316195423570985008687907853269984665640564039457584007913129639937,
            0,
            115792089237316195423570985008687907853269984665640564039457584007913129639936,
            0,
            0,
        ],
        "grant": 0,
        (
            'returned'
        ): -115792089237316195423570985008687907853269984665640564039457584007913129639937,
        "meter": [
            19,
            115792089237316195423570985008687907853269984665640564039457584007913129639937,
            0,
            115792089237316195423570985008687907853269984665640564039457584007913129639936,
            0,
            0,
        ],
    },
]
INVALID = [
    {
        "case": 0,
        "label": "zero-grant-one-over-baseline",
        "input": [0, 0, 1, 0, 0, 0],
        "grant": 0,
        "exception": "builtins.AssertionError",
        "line": 597,
        "meter": [0, 0, 1, 0, 0, 0],
    },
    {
        "case": 1,
        "label": "one-over-with-negative-refund-and-spills",
        "input": [13, 29, 11, -31, 7, 19],
        "grant": 10,
        "exception": "builtins.AssertionError",
        "line": 597,
        "meter": [13, 29, 11, -31, 7, 19],
    },
    {
        "case": 2,
        "label": "beyond-u64-invalid-baseline",
        "input": [19, 3, 18446744073709551617, 17, 11, 23],
        "grant": 18446744073709551616,
        "exception": "builtins.AssertionError",
        "line": 597,
        "meter": [19, 3, 18446744073709551617, 17, 11, 23],
    },
]


class FrameError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise FrameError(message)


def pairs(items):
    result = {}
    for key, value in items:
        require(key not in result, "duplicate field")
        result[key] = value
    return result


def bad_constant(value):
    raise FrameError("nonfinite JSON: " + value)


def integer(value, signed=False):
    require(type(value) is int and (signed or value >= 0), "invalid integer")


def meter(value):
    require(type(value) is list and len(value) == 6, "six-field meter required")
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
        require(type(frame["kind"]) is str and frame["kind"] == "tx-state-gas-usage", "kind")
        integer(frame["case"])
        require(frame["case"] == i, "frame order")
        value = frame["value"]
        require(
            type(value) is dict and set(value) == {"label", "input", "grant", "returned", "meter"},
            "value fields",
        )
        require(type(value["label"]) is str and bool(value["label"]), "label")
        meter(value["input"])
        meter(value["meter"])
        integer(value["grant"])
        integer(value["returned"], True)
        result.append(frame)
    require(bool(result), "empty stream")
    return result


def expected_frames():
    return [
        {
            "kind": "tx-state-gas-usage",
            "case": row["case"],
            "value": {k: v for k, v in row.items() if k != "case"},
        }
        for row in CATALOG
    ]


def compare_frames(text):
    frames = parse_frames(text)
    require(frames == expected_frames(), "complete frozen frames disagree")
    return frames


def stream(frames):
    return "".join(json.dumps(f) + "\n" for f in frames)


def self_test():
    frames = expected_frames()
    positive = stream(frames)
    require(compare_frames(positive) == frames, "whole positive stream")
    negatives = [
        "",
        "\n",
        "null",
        "true",
        "[]",
        "{}",
        positive + "\n",
        positive + "extra",
        positive[:-2],
        positive.replace('"case": 0', '"case": NaN', 1),
        positive.replace('"case": 0', '"case": Infinity', 1),
        positive.replace('"case": 0', '"case": -Infinity', 1),
        positive.replace('"case": 0', '"case": 0, "case": 0', 1),
        positive.replace('"grant": 0', '"grant": 0, "grant": 0', 1),
    ]

    def bad(path, value):
        wrong = copy.deepcopy(frames[0])
        target = wrong
        for key in path[:-1]:
            target = target[key]
        target[path[-1]] = value
        negatives.append(json.dumps(wrong))

    aliases = [True, False, 0.0, "0", None, [], {}]
    for value in aliases + [-1]:
        bad(["case"], value)
        bad(["value", "grant"], value)
    for value in aliases:
        bad(["value", "returned"], value)
    for field in ["input", "meter"]:
        for i in range(6):
            for value in aliases + ([] if i == 3 else [-1]):
                bad(["value", field, i], value)
        for value in [[], [0] * 5, [0] * 7, None, True, {}, "meter"]:
            bad(["value", field], value)
    for field in frames[0]:
        wrong = copy.deepcopy(frames[0])
        del wrong[field]
        negatives.append(json.dumps(wrong))
    for field in frames[0]["value"]:
        wrong = copy.deepcopy(frames[0])
        del wrong["value"][field]
        negatives.append(json.dumps(wrong))
    bad(["extra"], 0)
    bad(["value", "extra"], 0)
    for value in [True, None, [], {}, 0, ""]:
        bad(["kind"], value)
        bad(["value", "label"], value)
    bad(["kind"], "wrong")
    for invalid in negatives:
        try:
            parse_frames(invalid)
        except FrameError:
            continue
        raise FrameError("invalid parser control accepted: " + repr(invalid))
    mismatches = [frames[:-1], frames[1:], frames + [frames[-1]], list(reversed(frames))]
    for field in ["input", "meter"]:
        for i in range(6):
            wrong = copy.deepcopy(frames)
            wrong[8]["value"][field][i] += 1
            mismatches.append(wrong)
    for field in ["grant", "returned"]:
        wrong = copy.deepcopy(frames)
        wrong[8]["value"][field] += 1
        mismatches.append(wrong)
    wrong = copy.deepcopy(frames)
    wrong[8]["value"]["label"] += "x"
    mismatches.append(wrong)
    for wrong in mismatches:
        try:
            compare_frames(stream(wrong))
        except FrameError:
            continue
        raise FrameError("incorrect whole stream accepted")
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


def lean_meter(values):
    return (
        "{ gasLeft := %s, stateGasLeft := %s, stateGasBaseline := %s, "
        "refundCounter := (%s), stateGasSpilled := %s, stateGasCommittedSpill := %s }"
    ) % tuple(values)


def emit_lean():
    print("import Lean\nimport STFSpec.Vm.Core\nopen STFSpec.Vm.Core\n")
    print("""private def meterJson (m : GasMeter) : Lean.Json :=
  Lean.toJson ([Lean.toJson m.gasLeft, Lean.toJson m.stateGasLeft,
    Lean.toJson m.stateGasBaseline, Lean.toJson m.refundCounter,
    Lean.toJson m.stateGasSpilled, Lean.toJson m.stateGasCommittedSpill] : List Lean.Json)
""")
    for row in CATALOG:
        i = row["case"]
        print("private def input%d : GasMeter := %s" % (i, lean_meter(row["input"])))
        print(
            "private def result%d : Int := txStateGasUsed input%d %d (by decide)"
            % (i, i, row["grant"])
        )
        print(
            '#eval IO.println ((Lean.Json.mkObj [("kind", Lean.toJson "tx-state-gas-usage"), '
            '("case", Lean.toJson %d), ("value", Lean.Json.mkObj [("label", Lean.toJson %s), '
            '("input", meterJson input%d), ("grant", Lean.toJson (%d : Nat)), '
            '("returned", Lean.toJson result%d), ("meter", meterJson input%d)])]).compress)'
            % (i, json.dumps(row["label"]), i, row["grant"], i, i)
        )


def source_compare(args):
    """Compare complete frozen frames with the authenticated original transaction-usage helper."""
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
    original = gas.tx_state_gas_used
    helper_path = eels / "src/ethereum/forks/amsterdam/vm/gas.py"
    syntax = ast.parse(helper_path.read_text(), filename=str(helper_path))
    node = next(
        n for n in syntax.body if isinstance(n, ast.FunctionDef) and n.name == "tx_state_gas_used"
    )
    require(node.lineno == 570 and node.end_lineno == 603, "original helper source span")
    require(
        original.__code__.co_firstlineno == 570
        and original.__code__.co_filename == str(helper_path)
        and original.__globals__ is vars(gas),
        "original helper code binding",
    )
    require(__debug__ and sys.flags.optimize == 0, "source assertions disabled")
    require(original.__builtins__["int"] is builtins.int, "source int binding")
    fields = [
        "gas_left",
        "state_gas_left",
        "state_gas_baseline",
        "refund_counter",
        "state_gas_spilled",
        "state_gas_committed_spill",
    ]
    require([f.name for f in dataclasses.fields(gas.GasMeter)] == fields, "original schema")
    require(
        gas.ExecutionGas is fork_types.ExecutionGas
        and gas.StateGas is fork_types.StateGas
        and gas.Uint is numeric.Uint
        and gas.ExecutionGas.__supertype__ is numeric.Uint
        and gas.StateGas.__supertype__ is numeric.Uint,
        "source aliases differ",
    )
    helper_source = {
        "path": str(helper_path),
        "start": 570,
        "end": 603,
        "assertion_line": 597,
        "source_sha256": sha(helper_path.read_bytes()),
        "segment": ast.get_source_segment(helper_path.read_text(), node),
    }

    def functions():
        return [
            original,
            gas.GasMeter.__init__,
            numeric.Uint.__init__,
            numeric.Uint.__le__,
            numeric.Uint.__int__,
            numeric.Uint._in_range,
        ]

    def globals_now():
        return {
            "helper": gas.tx_state_gas_used,
            "helper.globals": original.__globals__,
            "helper.code": original.__code__,
            "helper.int": original.__builtins__["int"],
            "GasMeter": gas.GasMeter,
            "Uint": numeric.Uint,
            "ExecutionGas": gas.ExecutionGas,
            "StateGas": gas.StateGas,
            "fork.ExecutionGas": fork_types.ExecutionGas,
            "fork.StateGas": fork_types.StateGas,
            "ExecutionGas.supertype": gas.ExecutionGas.__supertype__,
            "StateGas.supertype": gas.StateGas.__supertype__,
            "builtin.int": builtins.int,
            "builtin.int.sub": builtins.int.__sub__,
            "builtin.int.add": builtins.int.__add__,
        }

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
            "helper_source": helper_source,
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
                'direct unchanged original tx_state_gas_used on fresh typed G'
                'asMeter/StateGas grants; no old-helper replay'
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
        require(type(m) is gas.GasMeter, "meter class")
        values = [getattr(m, f) for f in fields]
        require(type(values[3]) is int, "signed refund class")
        require(
            all(type(v) is numeric.Uint for i, v in enumerate(values) if i != 3), "gas field class"
        )
        return [int(v) for v in values]

    def typed_meter(values):
        E, R, B, q, S, C = values
        return gas.GasMeter(
            gas.ExecutionGas(numeric.Uint(E)),
            gas.StateGas(numeric.Uint(R)),
            gas.StateGas(numeric.Uint(B)),
            q,
            gas.StateGas(numeric.Uint(S)),
            gas.StateGas(numeric.Uint(C)),
        )

    try:
        with (output / "observations.jsonl").open("x") as observed:
            for row in CATALOG:
                m = typed_meter(row["input"])
                grant = gas.StateGas(numeric.Uint(row["grant"]))
                require(type(grant) is numeric.Uint, "grant class")
                initial = observe(m)
                returned = original(m, grant)
                require(type(returned) is int, "exact builtin signed result class")
                after_meter = observe(m)
                require(
                    initial == row["input"]
                    and after_meter == row["meter"]
                    and after_meter == initial
                    and returned == row["returned"],
                    "original whole mismatch",
                )
                observed.write(
                    json.dumps(
                        {
                            "case": row["case"],
                            "label": row["label"],
                            "input": initial,
                            "grant": int(grant),
                            "returned": returned,
                            "meter": after_meter,
                            "return_class": type(returned).__module__
                            + "."
                            + type(returned).__qualname__,
                        }
                    )
                    + "\n"
                )
                observed.flush()
                progress += 1
        with (output / "invalid-observations.jsonl").open("x") as observed:
            for row in INVALID:
                m = typed_meter(row["input"])
                grant = gas.StateGas(numeric.Uint(row["grant"]))
                initial = observe(m)
                try:
                    original(m, grant)
                except AssertionError as error:
                    require(type(error) is AssertionError, "exact assertion class")
                    tb = error.__traceback__
                    while tb.tb_next is not None:
                        tb = tb.tb_next
                    require(
                        tb.tb_frame.f_code is original.__code__
                        and tb.tb_lineno == row["line"]
                        and tb.tb_frame.f_code.co_filename == str(helper_path),
                        "assertion location",
                    )
                    after_meter = observe(m)
                    require(
                        initial == row["input"]
                        and after_meter == row["meter"]
                        and initial == after_meter,
                        "invalid helper changed meter",
                    )
                    observed.write(
                        json.dumps(
                            row
                            | {
                                "exception": type(error).__module__
                                + "."
                                + type(error).__qualname__,
                                "filename": tb.tb_frame.f_code.co_filename,
                            }
                        )
                        + "\n"
                    )
                    observed.flush()
                    invalid_progress += 1
                else:
                    raise FrameError("source assertion not raised")
    finally:
        after = snapshot()
        (output / "after.json").write_text(json.dumps(after, indent=2))
        pin_after = pin_snapshot()
        (output / "pin-after.json").write_text(json.dumps(pin_after, indent=2))
        (output / "progress.json").write_text(
            json.dumps(
                {
                    "completed": progress,
                    "total": len(CATALOG),
                    "invalid_completed": invalid_progress,
                    "invalid_total": len(INVALID),
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
                "source_only_assertions": invalid_progress,
                "complete_lean_frames": len(frames),
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
