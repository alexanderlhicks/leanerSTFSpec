#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Bounded ADD/SUB/MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND frame comparison; no dispatch, trace, reachability or guest claim.

Parser: canonical Python 3.12, --check-target FILE. Source mode: the frozen
EELS/.venv/bin/python [-O] -I -B SCRIPT --source --eels EELS --wheels WHEELS
--output FRESH_DIRECTORY --frames FILE. --preflight authenticates without calls.
The real Evm and original ADD/SUB/MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND execute with a fail-on-access PreState provider;
that provider is instrumentation, not a state backend or interpreter execution.
"""

import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys

PIN = "59c1473ddfba341babaeca1c97a50e996f639a0b"


class FrameError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise FrameError(message)


def pairs(items):
    result = {}
    for key, value in items:
        require(key not in result, "duplicate JSON key")
        result[key] = value
    return result


def cases():
    """Input-only deterministic catalogue; seeded words do not depend on Lean output."""
    import random
    result = []
    maximum = 2**256 - 1
    for op in ["add", "sub"]:
        def emit(words, price, gas):
            i = len(result)
            result.append(dict(case=i, op=op, cost=price, otherCost=2**301 + i,
                               veryLow=71 + i, gas=gas,
                               pc=0 if i == 0 else 2**300 + 19 + i,
                               upper=bool(i % 2), words=words))
        for words in [[], [maximum]]:
            emit(words, 3, 0)
            emit(words, 2**300 + 7, 2**300 + 8)
        for price in [0, 1, 3, 2**300 + 7]:
            for gas in [max(0, price - 1), price, price + 1]:
                emit([maximum, 1, 17, 0], price, gas)
        for x, y in [(0, 0), (maximum, 1), (0, 1), (9, 2), (2, 9),
                     (2**255, 2**255), (1, maximum)]:
            emit([x, y], 3, 3)
        emit(list(range(1024, 0, -1)), 3, 2)
        emit([maximum, 1] + list(range(1022, 0, -1)), 3, 4)
        rng = random.Random(835)
        for _ in range(16):
            emit([rng.getrandbits(256) for _ in range(rng.randrange(0, 7))],
                 3, rng.randrange(0, 7))
    for op in ["mul", "div"]:
        for words in [[], [maximum]]:
            emit(words, 5, 0)
            emit(words, 2**300 + 7, 2**300 + 8)
        for price in [0, 1, 5, 2**300 + 7]:
            for gas in [max(0, price - 1), price, price + 1]:
                emit([maximum, 0, 17, 0], price, gas)
        for x, y in [(0, 0), (0, 1), (1, 0), (maximum, 0), (0, maximum),
                     (maximum, 1), (1, maximum), (maximum, maximum),
                     (9, 2), (2, 9), (10, 3), (3, 10), (2**255, 2), (2, 2**255),
                     (2**255, 2**255), (2**128, 2**128), (2**128 + 1, 2**128 + 1),
                     (maximum, 2), (2, maximum)]:
            emit([x, y], 5, 5)
        emit(list(range(1024, 0, -1)), 5, 4)
        emit([maximum, 0] + list(range(1022, 0, -1)), 5, 6)
        rng = random.Random(857)
        for _ in range(20):
            emit([rng.getrandbits(256) for _ in range(rng.randrange(0, 7))],
                 5, rng.randrange(0, 9))
    signed_min = 2**255
    signed_max = signed_min - 1
    for op in ["sdiv", "mod", "smod"]:
        for words in [[], [maximum]]:
            emit(words, 5, 0)
            emit(words, 2**300 + 7, 2**300 + 8)
        for price in [0, 1, 5, 2**300 + 7]:
            for gas in [max(0, price - 1), price, price + 1]:
                emit([signed_min, maximum, 17, 0], price, gas)
        for x, y in [(7, 2), (-7, 2), (7, -2), (-7, -2), (2, 7), (1, -2), (-1, 2),
                     (signed_min, -1), (signed_min, 1), (signed_min, signed_min),
                     (signed_min, 2), (signed_min, -2), (signed_max, -1), (-1, signed_min),
                     (signed_min, 3), (signed_min, -3), (signed_max, signed_min),
                     (0, 0), (-7, 0), (signed_min, 0), (0, signed_min), (-1, 0),
                     (-1, -1), (10, 3), (3, 10), (maximum, signed_min),
                     (maximum, 1), (signed_min, 3)]:
            emit([x % 2**256, y % 2**256], 5, 5)
        emit([signed_min, 0, 17], 5, 4)
        emit([signed_min, maximum, 17], 5, 4)
        emit(list(range(1024, 0, -1)), 5, 4)
        emit([signed_min, maximum] + list(range(1022, 0, -1)), 5, 6)
        rng = random.Random(876)
        for _ in range(20):
            emit([rng.getrandbits(256) for _ in range(rng.randrange(0, 7))],
                 5, rng.randrange(0, 9))
    # Frozen input-only controls cover every byte position and independent raw prices.
    extra = json.loads(Path(__file__).with_name("arithmetic_signextend_inputs.json").read_text())
    result.extend(extra)
    return result


def write_input(path):
    rows = []
    for c in cases():
        rows.append("\t".join(map(str, [c["case"], c["op"], c["cost"], c["otherCost"],
            c["veryLow"], c["gas"], c["pc"], int(c["upper"]),
            ",".join(map(str, c["words"])) or "-"])))
    path.write_text("\n".join(rows) + "\n")


def expected_frames():
    world = {
        "blockAccountOrder": 157, "blockStorageOrder": 163,
        "revAccountOrder": 173, "revStorageOrder": 179,
        "oldestAncestorOffset": 2**290 + 167, "emptyCodeHash": 127,
        "storageProviderSample": 109, "created199": True, "read197": True,
    }
    rows = []
    for c in cases():
        before = {
            "pc": c["pc"], "stack": c["words"],
            "memory": [0, 0, 0, 128, 255, 1] + [0] * 26,
            "meter": [c["gas"], 101, 2, -17, 5, 11],
            "logs": [[256, [256, 1, 256], [255, 0, 128]]] * 2,
            "deleted": [256], "returnData": [0, 255, 128, 0],
            "warmAddresses": [1], "warmSlots": [[1, 256], [256, 1]],
        }
        after = copy.deepcopy(before)
        tag, error = "halt", "stackUnderflow"
        if after["stack"]:
            x = after["stack"].pop(0)
            if after["stack"]:
                y = after["stack"].pop(0)
                if c["gas"] < c["cost"]:
                    error = "outOfGas"
                else:
                    tag, error = "continue", None
                    if c["op"] == "add":
                        value = x + y
                    elif c["op"] == "sub":
                        value = x - y
                    elif c["op"] == "mul":
                        value = x * y
                    elif c["op"] == "div":
                        value = 0 if y == 0 else x // y
                    elif c["op"] == "mod":
                        value = 0 if y == 0 else x % y
                    elif c["op"] in {"sdiv", "smod"}:
                        a = x if x < 2**255 else x - 2**256
                        b = y if y < 2**255 else y - 2**256
                        if b == 0:
                            value = 0
                        elif c["op"] == "sdiv":
                            magnitude = abs(a) // abs(b)
                            value = -magnitude if (a < 0) != (b < 0) else magnitude
                        else:
                            magnitude = abs(a) % abs(b)
                            value = -magnitude if a < 0 else magnitude
                    elif c["op"] == "signextend":
                        if x > 31:
                            value = y
                        else:
                            width = 2**(8 * (x + 1))
                            low = y % width
                            value = low + (2**256 - width if low >= width // 2 else 0)
                    else:
                        raise FrameError("unknown arithmetic opcode")
                    after["stack"].insert(0, value % 2**256)
                    after["meter"][0] -= c["cost"]
                    after["pc"] += 1
        row = {key: c[key] for key in ["case", "op", "cost", "otherCost", "veryLow", "upper"]}
        row.update(schema="arithmetic-v1", before=before, after=after, tag=tag, error=error,
                   phiBefore=c["gas"] + 16, phiAfter=after["meter"][0] + 16,
                   worldBefore=world, worldAfter=world)
        rows.append(row)
    return rows


def exact(actual, expected):
    require(type(actual) is type(expected), "JSON observation type mismatch")
    if isinstance(expected, dict):
        require(actual.keys() == expected.keys(), "JSON observation keys")
        for key in expected:
            exact(actual[key], expected[key])
    elif isinstance(expected, list):
        require(len(actual) == len(expected), "JSON observation length")
        for a, e in zip(actual, expected):
            exact(a, e)
    else:
        require(actual == expected, "JSON observation value mismatch")


def compare_frames(data):
    require(len(data) <= 3_000_000, "oversized ADD/SUB/MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND evidence")
    try:
        rows = [json.loads(line, object_pairs_hook=pairs,
                           parse_constant=lambda _: (_ for _ in ()).throw(FrameError("constant")))
                for line in data.splitlines()]
    except (ValueError, RecursionError) as error:
        raise FrameError("malformed ADD/SUB/MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND evidence") from error
    exact(rows, expected_frames())
    return rows


def source_compare(args):
    """Authenticate the frozen source and installed imports before executing ADD/SUB/MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND."""
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
    require(sys.flags.optimize in (0, 1), "source requires normal Python or -O")
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

    vm = importlib.import_module("ethereum.forks.amsterdam.vm")
    control = importlib.import_module("ethereum.forks.amsterdam.vm.instructions.arithmetic")
    numeric = importlib.import_module("ethereum_types.numeric")
    fork = importlib.import_module("ethereum.forks.amsterdam.fork_types")
    tracker = importlib.import_module("ethereum.forks.amsterdam.state_tracker")
    access = importlib.import_module("ethereum.forks.amsterdam.block_access_lists")
    exceptions = importlib.import_module("ethereum.forks.amsterdam.vm.exceptions")
    bytes_module = importlib.import_module("ethereum_types.bytes")
    Uint, U256, U64 = numeric.Uint, numeric.U256, numeric.U64
    gas_module = importlib.import_module("ethereum.forks.amsterdam.vm.gas")
    stack_module = importlib.import_module("ethereum.forks.amsterdam.vm.stack")
    sign_module = importlib.import_module("ethereum.utils.numeric")
    require(all(f.__globals__ is vars(control) for f in
                [control.add, control.sub, control.mul, control.div,
                 control.sdiv, control.mod, control.smod, control.signextend]),
            "original arithmetic globals")
    require(control.Uint is Uint and control.U256 is U256 and
            control.GasCosts is gas_module.GasCosts and control.pop is stack_module.pop and
            control.push is stack_module.push and control.charge_gas is gas_module.charge_gas and
            control.get_sign is sign_module.get_sign and control.U255_CEIL_VALUE == 2**255 and control.Bytes is bytes_module.Bytes and
            control.Bytes is bytes,
            "original arithmetic helper bindings")
    require([f.__code__.co_firstlineno for f in
             [control.add, control.sub, control.mul, control.div,
              control.sdiv, control.mod, control.smod, control.signextend]] == [25, 52, 79, 106, 139, 172, 202, 331],
            "arithmetic source locations")
    require(int(gas_module.GasCosts.OPCODE_ADD) == int(gas_module.GasCosts.OPCODE_SUB) == 3
            and int(gas_module.GasCosts.OPCODE_MUL) == int(gas_module.GasCosts.OPCODE_DIV) ==
            int(gas_module.GasCosts.OPCODE_SDIV) == int(gas_module.GasCosts.OPCODE_MOD) ==
            int(gas_module.GasCosts.OPCODE_SMOD) == int(gas_module.GasCosts.OPCODE_SIGNEXTEND) == 5,
            "pinned selected prices")
    require(importlib.metadata.version("ethereum-types") == "0.4.1" and
            importlib.metadata.version("ethereum-rlp") == "0.1.6", "numeric/RLP pin")
    functions = [control.add, control.sub, control.mul, control.div,
                 control.sdiv, control.mod, control.smod, control.signextend, vm.Evm.__init__,
                 stack_module.pop, stack_module.push,
                 gas_module.charge_gas, gas_module.charge_gas_from_meter,
                 U256.wrapping_add, U256.wrapping_sub, U256.wrapping_mul, U256.__floordiv__, U256.__mod__, U256.__eq__,
                 U256.to_signed, U256.from_signed, sign_module.get_sign,
                 U256.__init__, Uint.__init__, Uint.__add__, Uint.__sub__,
                 U256.to_be_bytes32, U256.from_be_bytes.__func__,
                 U256.__gt__, U256.__add__, U256.__sub__, U256.__int__]
    original_functions = list(functions)
    require([int(Uint(x) + Uint(1)) for x in (0, 2**64, 2**300 + 19)] ==
            [1, 2**64 + 1, 2**300 + 20], "Uint exact successor relation")

    def snapshot():
        for name, module in list(sys.modules.items()):
            file = getattr(module, "__file__", None)
            if file:
                path = Path(file).absolute()
                if path.is_relative_to(eels / ".venv") and path.suffix != ".pyc":
                    if name in initial_modules:
                        startup_inputs[str(path)] = identity(path)
                    else:
                        authenticated_dependency(path, path.read_bytes())
        for path, expected in installed.items():
            require(identity(Path(path)) == expected, "installed identity changed")
        for path, expected in record_files.items():
            require(identity(Path(path)) == expected, "RECORD changed")
        for info in wheel_records.values():
            if info["raw_wheel_authenticated"]:
                current = identity(Path(info["path"]))
                require(all(current[k] == info[k] for k in current), "wheel changed")
        require([control.add, control.sub, control.mul, control.div,
                 control.sdiv, control.mod, control.smod, control.signextend, vm.Evm.__init__,
                 stack_module.pop, stack_module.push,
                 gas_module.charge_gas, gas_module.charge_gas_from_meter,
                 U256.wrapping_add, U256.wrapping_sub, U256.wrapping_mul, U256.__floordiv__, U256.__mod__, U256.__eq__,
                 U256.to_signed, U256.from_signed, sign_module.get_sign,
                 U256.__init__, Uint.__init__, Uint.__add__, Uint.__sub__,
                 U256.to_be_bytes32, U256.from_be_bytes.__func__,
                 U256.__gt__, U256.__add__, U256.__sub__, U256.__int__]
                == original_functions and control.Uint is Uint and control.U256 is U256 and
            control.GasCosts is gas_module.GasCosts and
                all(f.__globals__ is vars(control) for f in original_functions[:8]) and
                int(gas_module.GasCosts.OPCODE_ADD) == int(gas_module.GasCosts.OPCODE_SUB) == 3 and
                int(gas_module.GasCosts.OPCODE_MUL) == int(gas_module.GasCosts.OPCODE_DIV) ==
                int(gas_module.GasCosts.OPCODE_SDIV) == int(gas_module.GasCosts.OPCODE_MOD) ==
                int(gas_module.GasCosts.OPCODE_SMOD) == int(gas_module.GasCosts.OPCODE_SIGNEXTEND) == 5 and
                control.pop is stack_module.pop and
                control.push is stack_module.push and control.charge_gas is gas_module.charge_gas and
            control.get_sign is sign_module.get_sign and control.U255_CEIL_VALUE == 2**255 and control.Bytes is bytes_module.Bytes and
            control.Bytes is bytes,
                "source binding changed")
        return {
            "runtime": {"executable": str(Path(sys.executable).absolute()),
                        "binary": identity(Path(sys.executable).resolve()),
                        "version": sys.version, "flags": str(sys.flags),
                        "sys_path": list(sys.path)},
            "functions": [{"module": f.__module__, "qualname": f.__qualname__,
                           "id": id(f), "source": inspect.getsourcefile(f),
                           "code_sha256": sha(marshal.dumps(f.__code__, 2))} for f in functions],
            "sources": loaded_sources, "installed": installed, "records": record_files,
            "wheels": wheel_records, "trusted_startup_files": startup_inputs,
            "adapter": "real Evm and original ADD/SUB/MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND; fail-on-access PreState; direct body only",
        }

    before_identity = snapshot()
    (output / "before.json").write_text(json.dumps(before_identity, indent=2))
    if args.preflight:
        after_identity = snapshot()
        require(before_identity == after_identity and pin_snapshot() == pinned_before,
                "preflight identities changed")
        (output / "after.json").write_text(json.dumps(after_identity, indent=2))
        print(json.dumps({"status": "authenticated preflight only", "source_calls": 0}))
        return
    require(args.frames is not None, "source needs actual Lean frames")
    frames = compare_frames(args.frames.read_text())
    (output / "frames-input.jsonl").write_bytes(args.frames.read_bytes())

    class UnreadPreState:
        def get_account_optional(self, address):
            raise FrameError("ADD/SUB/MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND accessed pre-state account")
        def get_storage(self, address, key):
            raise FrameError("ADD/SUB/MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND accessed pre-state storage")
        def get_code(self, code_hash):
            raise FrameError("ADD/SUB/MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND accessed pre-state code")
        def state_root(self, diff):
            raise FrameError("ADD/SUB/MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND accessed pre-state root")

    def address(n):
        return fork.Address(n.to_bytes(20, "big"))

    def h32(n):
        return fork.Hash32(n.to_bytes(32, "big"))

    def encode(value):
        if value is None or type(value) in (bool, str, int):
            return value
        if isinstance(value, numeric.Unsigned):
            return int(value)
        if isinstance(value, (bytes, bytearray)):
            return list(value)
        if dataclasses.is_dataclass(value):
            return {f.name: encode(getattr(value, f.name)) for f in dataclasses.fields(value)}
        if isinstance(value, (list, tuple)):
            return [encode(v) for v in value]
        if isinstance(value, set):
            return sorted([encode(v) for v in value], key=lambda x: json.dumps(x, sort_keys=True))
        if isinstance(value, dict):
            return sorted([[encode(k), encode(v)] for k, v in value.items()],
                          key=lambda x: json.dumps(x[0], sort_keys=True))
        if isinstance(value, UnreadPreState):
            return {"provider": "fail-on-access", "identity": id(value)}
        if isinstance(value, BaseException):
            return {"exception": type(value).__module__ + "." + type(value).__qualname__,
                    "args": encode(value.args)}
        raise FrameError("unobserved source field " + str(type(value)))

    def source_frame(row, raw_output=b"", raw_error=None):
        f = row["before"]
        block = tracker.BlockState(UnreadPreState(), account_writes={address(149): None},
                                   oldest_ancestor_offset=Uint(2**290 + 167))
        tx = tracker.TransactionState(block, account_reads={address(197)},
                                      created_accounts={address(199)},
                                      transient_storage={(address(181), h32(191)): U256(193)})
        be = vm.BlockEnvironment(U64(11), block, Uint(13), [h32(17), h32(19)], address(23),
                Uint(29), Uint(31), U256(37), h32(41), U64(43), h32(47),
                access.BlockAccessListBuilder(), U64(53))
        te = vm.TransactionEnvironment(address(59), address(61), True, b"\x00\x80\x00",
                U256(67), Uint(71), Uint(73), fork.ExecutionGas(Uint(79)),
                fork.StateGas(Uint(83)), Uint(89), set(), set(), set(), tx, (), (),
                Uint(0), h32(97))
        meter = vm.GasMeter(*(Uint(v) if i != 3 else v for i, v in enumerate(f["meter"])))
        logs = tuple(vm.Log(address(a), tuple(h32(t) for t in topics), bytes(data))
                     for a, topics, data in f["logs"])
        upper = row["upper"]
        return vm.Evm(Uint(f["pc"]), [U256(v) for v in reversed(f["stack"])],
                bytearray(f["memory"]), b"\x60\x5b\xff", meter, {Uint(0), Uint(2)},
                logs, True, be, te, address(101), address(103), U256(2**256 - 1),
                b"\xff\x00\x80", address(0), Uint(1024 if upper else 0), True, upper,
                False, None, raw_output, {address(256)}, bytes(f["returnData"]), raw_error,
                {address(1)}, {(address(1), h32(256)), (address(256), h32(1))})

    def frame_observation(evm):
        return {"pc": int(evm.pc), "stack": [int(v) for v in reversed(evm.stack)],
                "memory": list(evm.memory),
                "meter": [int(getattr(evm.gas_meter, field.name))
                          for field in dataclasses.fields(evm.gas_meter)],
                "logs": [[int.from_bytes(l.address, "big"),
                          [int.from_bytes(t, "big") for t in l.topics], list(l.data)]
                         for l in evm.logs],
                "deleted": sorted(int.from_bytes(a, "big") for a in evm.accounts_to_delete),
                "returnData": list(evm.return_data),
                "warmAddresses": sorted(int.from_bytes(a, "big") for a in evm.accessed_addresses),
                "warmSlots": sorted([[int.from_bytes(a, "big"), int.from_bytes(k, "big")]
                                     for a, k in evm.accessed_storage_keys])}

    source_functions = {"add": control.add, "sub": control.sub,
                        "mul": control.mul, "div": control.div, "sdiv": control.sdiv,
                        "mod": control.mod, "smod": control.smod, "signextend": control.signextend}
    source_prices = {"add": int(gas_module.GasCosts.OPCODE_ADD),
                     "sub": int(gas_module.GasCosts.OPCODE_SUB),
                     "mul": int(gas_module.GasCosts.OPCODE_MUL),
                     "div": int(gas_module.GasCosts.OPCODE_DIV),
                     "sdiv": int(gas_module.GasCosts.OPCODE_SDIV),
                     "mod": int(gas_module.GasCosts.OPCODE_MOD),
                     "smod": int(gas_module.GasCosts.OPCODE_SMOD),
                     "signextend": int(gas_module.GasCosts.OPCODE_SIGNEXTEND)}
    related = [row for row in frames if row["cost"] == source_prices[row["op"]]]
    progress = 0
    try:
        with (output / "observations.jsonl").open("x") as observed:
            for row in related:
                evm = source_frame(row)
                original = encode(evm)
                exact(frame_observation(evm), row["before"])
                function = source_functions[row["op"]]
                caught = None
                try:
                    returned = function(evm)
                    require(returned is None, "arithmetic return value")
                except (exceptions.StackUnderflowError, exceptions.OutOfGasError) as error:
                    caught = error
                error_tag = ("stackUnderflow" if isinstance(caught, exceptions.StackUnderflowError)
                             else "outOfGas" if caught is not None else None)
                exact(error_tag, row["error"])
                exact("halt" if caught is not None else "continue", row["tag"])
                result = encode(evm)
                expected = copy.deepcopy(original)
                expected["pc"] = row["after"]["pc"]
                expected["stack"] = list(reversed(row["after"]["stack"]))
                expected["gas_meter"]["gas_left"] = row["after"]["meter"][0]
                exact(result, expected)
                exact(frame_observation(evm), row["after"])
                require(evm.running is True and evm.output == b"" and evm.error is None,
                        "direct body is not interpreter halt settlement")
                observed.write(json.dumps({"case": row["case"], "op": row["op"],
                    "caught": encode(caught), "before": original, "after": result,
                    "related_frame_before": row["before"], "related_frame_after": row["after"]}) + "\n")
                observed.flush()
                progress += 1
    finally:
        after_identity = snapshot()
        (output / "after.json").write_text(json.dumps(after_identity, indent=2))
        pin_after = pin_snapshot()
        (output / "pin-after.json").write_text(json.dumps(pin_after, indent=2))
        (output / "progress.json").write_text(json.dumps({"completed": progress, "total": len(related)}))
        require(before_identity == after_identity and pinned_before == pin_after,
                "source/runtime identities changed")
    print(json.dumps({"source_calls": progress, "raw_price_lean_only": len(frames) - len(related),
                      "actual_original_ADD_SUB_MUL_DIV_SDIV_MOD_SMOD_SIGNEXTEND": True, "dispatch_or_guest_execution": False}))



def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--write-input", type=Path)
    modes.add_argument("--check-target", type=Path)
    modes.add_argument("--source", action="store_true")
    modes.add_argument("--preflight", action="store_true")
    parser.add_argument("--eels", type=Path)
    parser.add_argument("--wheels", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--frames", type=Path)
    args = parser.parse_args()
    if args.write_input:
        write_input(args.write_input)
    elif args.check_target:
        rows = compare_frames(args.check_target.read_text())
        print(json.dumps({"arithmetic_frames": len(rows), "optimization": sys.flags.optimize}))
    else:
        require(all([args.eels, args.wheels, args.output]), "source paths required")
        source_compare(args)


if __name__ == "__main__":
    main()
