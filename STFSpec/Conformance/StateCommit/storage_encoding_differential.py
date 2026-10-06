#!/usr/bin/env python3
"""Strict whole-byte SC2 comparison with pinned original U256 encoding.

Status: conformance driver, not a state/root/decoder claim. Date: 2026-10-06.
Run parser controls with --self-test under normal Python and -O. Comparison takes
JSONL {case,value,encoded} frames emitted by StorageEncodingGuards' private emitter
(or the same public-operation frames), --eels, --wheels and --identities-dir.
No source function/class substitution, assertion-based validation or resume CLI.
"""
import argparse
import dataclasses
import datetime
import hashlib
import importlib
import inspect
import json
import marshal
import os
from pathlib import Path
import platform
import subprocess
import sys
import tomllib
import zipfile

PIN = "e1a316a06fc3d3e0a5da36fdc78580811e9d8a36"
_git_log_dir = None
_git_serial = 0


class FrameError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise FrameError(message)


def exact_int(value, lower, upper, name):
    require(type(value) is int and lower <= value < upper, f"invalid {name}")
    return value


def object_pairs(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate field")
        result[key] = value
    return result


def reject_constant(value):
    raise FrameError(f"nonfinite JSON constant {value}")


def parse_frames(text):
    require(type(text) is str and bool(text), "empty frame stream")
    frames = []
    for index, line in enumerate(text.splitlines()):
        require(bool(line.strip()), "blank frame")
        try:
            frame = json.loads(line, object_pairs_hook=object_pairs,
                               parse_constant=reject_constant)
        except (ValueError, TypeError) as error:
            raise FrameError(f"frame {index}: {error}") from error
        require(type(frame) is dict and set(frame) == {"case", "value", "encoded"},
                "wrong frame fields")
        exact_int(frame["case"], 0, sys.maxsize, "case")
        require(frame["case"] == index, "wrong case order/count")
        exact_int(frame["value"], 0, 2**256, "U256 value")
        encoded = frame["encoded"]
        require(type(encoded) is list and 1 <= len(encoded) <= 33, "invalid encoded arity")
        for byte in encoded:
            exact_int(byte, 0, 256, "encoded byte")
        frames.append(frame)
    require(bool(frames), "empty frames")
    return frames


def self_test():
    positives = [
        {"case": 0, "value": 0, "encoded": [128]},
        {"case": 0, "value": 1, "encoded": [1]},
        {"case": 0, "value": 127, "encoded": [127]},
        {"case": 0, "value": 128, "encoded": [129, 128]},
        {"case": 0, "value": 256, "encoded": [130, 1, 0]},
        {"case": 0, "value": 2**256-1, "encoded": [160] + [255]*32},
    ]
    for frame in positives:
        require(parse_frames(json.dumps(frame)+"\n") == [frame], "positive parser control")
    base = positives[0]
    negatives = ["", "\n", "[]", "null", "true", "0", '"text"', "{}",
                 json.dumps(base)+"\n\n", json.dumps(base)+"\nextra",
                 '{"case":0,"case":0,"value":0,"encoded":[128]}',
                 json.dumps(base)+"\n"+json.dumps(base),
                 '{"case":0,"value":NaN,"encoded":[128]}',
                 '{"case":0,"value":Infinity,"encoded":[128]}',
                 json.dumps(base)+" extra"]
    for field in base:
        missing = dict(base); del missing[field]; negatives.append(json.dumps(missing))
    extra = dict(base, unexpected=1); negatives.append(json.dumps(extra))
    for field in ["case", "value"]:
        invalids = [True, False, None, "0", [], {}, 0.0, -1, 2**256]
        if field == "case":
            invalids.append(1)
        for value in invalids:
            bad = dict(base); bad[field] = value; negatives.append(json.dumps(bad))
    for encoded in [None, True, "80", {}, [], [128]*34, [[128]]]:
        bad = dict(base, encoded=encoded); negatives.append(json.dumps(bad))
    for byte in [True, False, None, "0", [], {}, 0.0, -1, 256]:
        for position in range(33):
            encoded = [0]*33; encoded[position] = byte
            negatives.append(json.dumps(dict(base, encoded=encoded)))
    for text in negatives:
        try:
            parse_frames(text)
        except FrameError:
            continue
        raise FrameError(f"negative parser control accepted: {text!r}")
    print(json.dumps({"parser_positive": len(positives), "parser_negative": len(negatives),
                      "optimization": sys.flags.optimize}))


def identity_file(path):
    data = path.read_bytes()
    return {"path": str(path), "size": len(data), "sha256": hashlib.sha256(data).hexdigest(),
            "fs_mode": oct(path.stat().st_mode & 0o7777)}


def function_identity(function):
    require(inspect.isfunction(function), "expected original Python function")
    return {"module": function.__module__, "qualname": function.__qualname__,
            "object_id": id(function), "source": inspect.getsourcefile(function),
            "code_sha256": hashlib.sha256(marshal.dumps(function.__code__, 2)).hexdigest()}


def git(eels, *args):
    global _git_serial
    env = dict(os.environ, GIT_NO_LAZY_FETCH="1", GIT_TERMINAL_PROMPT="0")
    argv = ["git", "--no-replace-objects", "--no-optional-locks", *args]
    directory = _git_log_dir / f"{_git_serial:03d}"
    _git_serial += 1
    directory.mkdir(parents=True)
    record = {"argv": argv, "cwd": str(eels),
              "started": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "environment": {"GIT_NO_LAZY_FETCH": "1", "GIT_TERMINAL_PROMPT": "0"}}
    result = subprocess.run(argv,
                            cwd=eels, env=env, check=False, capture_output=True)
    record.update(ended=datetime.datetime.now(datetime.timezone.utc).isoformat(), exit=result.returncode)
    (directory / "command.json").write_text(json.dumps(record, indent=2)+"\n")
    (directory / "argv.nul").write_bytes(b"\0".join(os.fsencode(a) for a in argv)+b"\0")
    (directory / "stdout").write_bytes(result.stdout)
    (directory / "stderr").write_bytes(result.stderr)
    require(result.returncode == 0, f"Git identity failure: {result.stderr!r}")
    return result.stdout.decode().strip()


def authenticate(eels, wheels, modules):
    require(git(eels, "rev-parse", "HEAD") == PIN, "wrong original pin")
    require(not git(eels, "status", "--porcelain=v1", "--untracked-files=no"), "dirty original source")
    lock_path = eels / "uv.lock"
    lock = tomllib.loads(lock_path.read_text())
    records = []
    installed = []
    for name, version in [("ethereum-rlp", "0.1.6"), ("ethereum-types", "0.4.1")]:
        package = next(p for p in lock["package"] if p["name"] == name)
        require(package["version"] == version, "wrong locked version")
        filename = f"{name.replace('-', '_')}-{version}-py3-none-any.whl"
        wheel = wheels / filename
        record = identity_file(wheel)
        locked = next(w for w in package["wheels"] if w["url"].endswith("/"+filename))
        require(locked["hash"] == "sha256:"+record["sha256"] and locked["size"] == record["size"], "raw wheel lock mismatch")
        members = []
        with zipfile.ZipFile(wheel) as archive:
            for info in archive.infolist():
                data = archive.read(info)
                members.append({"name": info.filename, "size": len(data),
                                "sha256": hashlib.sha256(data).hexdigest(), "crc": info.CRC,
                                "external_attr": info.external_attr})
            for module in modules:
                if module.__name__.split('.')[0] != name.replace('-', '_'):
                    continue
                member = module.__name__.replace('.', '/')
                member += '/__init__.py' if hasattr(module, '__path__') else '.py'
                path = Path(module.__file__).resolve()
                require(path.suffix == '.py', "original source module required")
                require(path.read_bytes() == archive.read(member), "installed source/wheel mismatch")
                installed.append(identity_file(path) | {"module": module.__name__, "object_id": id(module)})
        records.append(record | {"locked_version": version, "members": members})
    return {"pin": PIN, "tree": git(eels, "rev-parse", "HEAD^{tree}"),
            "lock": identity_file(lock_path), "wheels": records, "installed": installed}


def compare(args):
    global _git_log_dir
    frames = parse_frames(args.cases.read_text())
    eels = args.eels.resolve(); wheels = args.wheels.resolve()
    require(not args.identities_dir.exists(), "identity directory already exists")
    args.identities_dir.mkdir(parents=True)
    _git_log_dir = args.identities_dir / "git-commands"
    sys.path.insert(0, str(eels / "src"))
    mpt = importlib.import_module("ethereum.merkle_patricia_trie")
    numeric = importlib.import_module("ethereum_types.numeric")
    bytes_module = importlib.import_module("ethereum_types.bytes")
    rlp = importlib.import_module("ethereum_rlp.rlp")
    package_modules = [importlib.import_module("ethereum_types"), numeric, bytes_module,
                       importlib.import_module("ethereum_rlp"), rlp]
    require(Path(mpt.__file__).resolve() == eels / "src/ethereum/merkle_patricia_trie.py", "wrong MPT module")
    require(mpt.rlp is rlp and mpt.Bytes is bytes_module.Bytes is bytes, "original MPT aliases")
    require(numeric.U256.__base__ is numeric.FixedUnsigned, "original U256 superclass")
    require(rlp.FixedUnsigned is numeric.FixedUnsigned and rlp.Uint is numeric.Uint, "original RLP integer aliases")
    def snapshot():
        functions = [mpt.encode_node, rlp.encode, rlp.encode_bytes, numeric.U256.to_be_bytes,
                     numeric.U256.__init__, numeric.U256._in_range]
        bindings = {"mpt.rlp": mpt.encode_node.__globals__["rlp"],
                    "mpt.Bytes": mpt.encode_node.__globals__["Bytes"],
                    "mpt.Account": mpt.encode_node.__globals__["Account"],
                    "rlp.Uint": rlp.encode.__globals__["Uint"],
                    "rlp.FixedUnsigned": rlp.encode.__globals__["FixedUnsigned"],
                    "rlp.encode_bytes": rlp.encode.__globals__["encode_bytes"],
                    "rlp.encode_sequence": rlp.encode.__globals__["encode_sequence"]}
        return authenticate(eels, wheels, package_modules) | {
            "mpt": identity_file(Path(mpt.__file__)), "functions": [function_identity(f) for f in functions],
            "globals": {name: {"object_id": id(value), "module": getattr(value, "__module__", getattr(value, "__name__", None)),
                               "qualname": getattr(value, "__qualname__", None)} for name, value in bindings.items()},
            "account_schema": [{"name": f.name, "type": str(f.type)} for f in dataclasses.fields(mpt.Account)],
            "account_source": identity_file(Path(inspect.getsourcefile(mpt.Account))),
            "classes": [{"name": c.__qualname__, "module": c.__module__, "object_id": id(c),
                         "mro": [f"{t.__module__}.{t.__qualname__}" for t in c.__mro__]}
                        for c in [numeric.U256, numeric.FixedUnsigned, mpt.Account, bytes]],
            "runtime": {"executable": str(Path(sys.executable).resolve()),
                        "executable_identity": identity_file(Path(sys.executable).resolve()),
                        "version": sys.version, "implementation": platform.python_implementation(),
                        "optimization": sys.flags.optimize, "dont_write_bytecode": sys.dont_write_bytecode,
                        "sys_path": list(sys.path)},
            "source_relation": "actual original normal U256(n), 0<=n<2^256; original classes/aliases/host integer allocation; no Account/default/root/decoder claim"}

    before = snapshot()
    (args.identities_dir / "before.json").write_text(json.dumps(before, indent=2)+"\n")
    passed = 0
    try:
        for frame in frames:
            value = numeric.U256(frame["value"])
            require(type(value) is numeric.U256 and int(value) == frame["value"], "original checked U256 value")
            encoded = mpt.encode_node(value)
            integer_encoding = rlp.encode(value)
            require(type(encoded) is bytes and encoded == integer_encoding, "original integer dispatch mismatch")
            require(list(encoded) == frame["encoded"], f"complete storage encoding mismatch at {frame['case']}")
            print(json.dumps(frame | {"source_encoded": list(encoded), "minimal": list(value.to_be_bytes())}), flush=True)
            passed += 1
    finally:
        after = snapshot()
        (args.identities_dir / "after.json").write_text(json.dumps(after, indent=2)+"\n")
        (args.identities_dir / "progress.json").write_text(json.dumps({"passed": passed, "total": len(frames)})+"\n")
        require(before == after, "original identities changed")
    print(json.dumps({"source_cases": passed, "complete_bytes_agree": True,
                      "identities_unchanged": True}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--cases", type=Path)
    parser.add_argument("--eels", type=Path)
    parser.add_argument("--wheels", type=Path)
    parser.add_argument("--identities-dir", type=Path)
    args = parser.parse_args()
    if args.self_test:
        require(not any([args.cases, args.eels, args.wheels, args.identities_dir]), "self-test takes no comparison inputs")
        self_test()
    else:
        require(all([args.cases, args.eels, args.wheels, args.identities_dir]), "comparison paths required")
        compare(args)


if __name__ == "__main__":
    main()
