#!/usr/bin/env python3
"""Strict full-field SC1 comparison with both pinned original account encoders.

Status: pure account encoding conformance, not decoder/injectivity/backend closure.
Date: 2026-10-06. JSONL exact {case,nonce,balance,storage_root,code_hash,encoded}.
Nonce is an unbounded natural; all other fields retain their complete bounded bytes.
--self-test is independent of original imports, in normal and optimized Python.
No constructor/hash/function substitution or speculative resume CLI.
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



def natural(value, name):
    require(type(value) is int and value >= 0, f"invalid {name}")
    return value


def byte_list(value, length, name):
    require(type(value) is list and (length is None or len(value) == length),
            f"wrong {name} arity")
    for byte in value:
        exact_int(byte, 0, 256, name+" byte")
    return value


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
        require(type(frame) is dict and set(frame) ==
                {"case", "nonce", "balance", "storage_root", "code_hash", "encoded"},
                "wrong frame fields")
        natural(frame["case"], "case")
        require(frame["case"] == index, "wrong case order/count")
        natural(frame["nonce"], "nonce")
        exact_int(frame["balance"], 0, 2**256, "balance")
        byte_list(frame["storage_root"], 32, "storage_root")
        byte_list(frame["code_hash"], 32, "code_hash")
        byte_list(frame["encoded"], None, "encoded")
        require(bool(frame["encoded"]), "empty encoded output")
        frames.append(frame)
    return frames


def minimal(n):
    return n.to_bytes((n.bit_length()+7)//8, "big")


def string_wire(payload):
    if len(payload) == 1 and payload[0] < 128:
        return payload
    if len(payload) < 56:
        return bytes([128+len(payload)])+payload
    digits = minimal(len(payload))
    require(len(digits) <= 8, "manual standard-domain string length")
    return bytes([183+len(digits)])+digits+payload


def manual(frame):
    payload = b"".join(string_wire(part) for part in
                       [minimal(frame["nonce"]), minimal(frame["balance"]),
                        bytes(frame["storage_root"]), bytes(frame["code_hash"])])
    if len(payload) < 56:
        return bytes([192+len(payload)])+payload
    digits = minimal(len(payload))
    require(len(digits) <= 8, "manual standard-domain assembled-list length")
    return bytes([247+len(digits)])+digits+payload


def self_test():
    base = {"case": 0, "nonce": 0, "balance": 0, "storage_root": [0]*32,
            "code_hash": [0]*32, "encoded": [248,68,128,128,160]+[0]*32+[160]+[0]*32}
    positives = [base, dict(base, nonce=2**256+1), dict(base, nonce=2**2048),
                 dict(base, balance=2**256-1)]
    for frame in positives:
        require(parse_frames(json.dumps(frame)+"\n") == [frame], "positive parser control")
    negatives = ["", "\n", "[]", "null", "true", "0", '"text"', "{}",
                 json.dumps(base)+"\n\n", json.dumps(base)+"\nextra",
                 json.dumps(base)+"\n"+json.dumps(base),
                 json.dumps(base)+" extra", json.dumps(base)[:-1],
                 '{"case":0,"case":0}',
                 json.dumps(base).replace('"nonce": 0', '"nonce": NaN'),
                 json.dumps(base).replace('"nonce": 0', '"nonce": Infinity')]
    for field in base:
        missing = dict(base); del missing[field]; negatives.append(json.dumps(missing))
        negatives.append(json.dumps(base).replace('"'+field+'":', '"'+field+'": 0, "'+field+'":', 1))
    negatives.append(json.dumps(dict(base, unexpected=0)))
    for field in ["case", "nonce", "balance"]:
        for value in [True, False, None, "0", [], {}, 0.0, -1]:
            bad = dict(base); bad[field] = value; negatives.append(json.dumps(bad))
    negatives.extend([json.dumps(dict(base, case=1)), json.dumps(dict(base, balance=2**256))])
    for field in ["storage_root", "code_hash", "encoded"]:
        for value in [True, False, None, "00", {}, [], [[0]]]:
            bad = dict(base); bad[field] = value; negatives.append(json.dumps(bad))
        if field != "encoded":
            for length in [1,31,33,64]:
                bad = dict(base); bad[field] = [0]*length; negatives.append(json.dumps(bad))
        for value in [True, False, None, "0", [], {}, 0.0, -1, 256]:
            for position in range(32):
                bad = dict(base); data = list(base[field]); data[position] = value
                bad[field] = data; negatives.append(json.dumps(bad))
    for text in negatives:
        try:
            parse_frames(text)
        except FrameError:
            continue
        raise FrameError(f"negative control accepted: {text!r}")
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
    fork = importlib.import_module("ethereum.forks.amsterdam.fork_types")
    state = importlib.import_module("ethereum.state")
    numeric = importlib.import_module("ethereum_types.numeric")
    bm = importlib.import_module("ethereum_types.bytes")
    rlp = importlib.import_module("ethereum_rlp.rlp")
    packages = [importlib.import_module("ethereum_types"), numeric, bm,
                importlib.import_module("ethereum_rlp"), rlp]
    require(mpt.Account is fork.Account is state.Account, "original shared Account class")
    require(mpt.rlp is fork.rlp is rlp, "original RLP aliases")
    require(state.Uint is numeric.Uint and state.U256 is numeric.U256, "original field types")
    require(state.Hash32 is bm.Bytes32, "original Hash32 class")
    require(rlp.Uint is numeric.Uint and rlp.FixedUnsigned is numeric.FixedUnsigned,
            "original integer dispatch")
    def snapshot(label):
        auth = authenticate(eels, wheels, packages)
        # Authenticate EVERY installed provider .py against raw wheel, including unloaded modules.
        installed = []
        sources_dir = args.identities_dir / label
        for record in auth["wheels"]:
            with zipfile.ZipFile(record["path"]) as archive:
                for info in archive.infolist():
                    data = archive.read(info)
                    dest = sources_dir / "wheel-members" / Path(record["path"]).name / info.filename
                    dest.parent.mkdir(parents=True, exist_ok=True); dest.write_bytes(data)
                    if info.filename.endswith('.py'):
                        package_name = info.filename.split('/')[0]
                        package = importlib.import_module(package_name)
                        path = Path(package.__file__).resolve().parent.parent / info.filename
                        require(path.read_bytes() == data, "all installed provider source mismatch")
                        target = sources_dir / "installed" / info.filename
                        target.parent.mkdir(parents=True, exist_ok=True); target.write_bytes(data)
                        installed.append(identity_file(path))
        tree = git(eels, "ls-tree", "-r", PIN, "--", "src/ethereum", "uv.lock")
        originals = {row.split('\t')[1]: row.split('\t')[0].split() for row in tree.splitlines()}
        loaded = []
        for name,module in sorted(sys.modules.items()):
            if not name.startswith('ethereum.') or not getattr(module, '__file__', None):
                continue
            path = Path(module.__file__).resolve()
            require(path.is_relative_to(eels), "foreign original module")
            relative = path.relative_to(eels).as_posix()
            require(relative in originals, "untracked original module")
            mode, kind, blob = originals[relative]
            data = path.read_bytes()
            require(hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest() == blob,
                    "loaded original blob mismatch")
            target = sources_dir / "original" / relative
            target.parent.mkdir(parents=True, exist_ok=True); target.write_bytes(data)
            loaded.append(identity_file(path) | {"module": name, "git_mode": mode, "blob": blob})
        functions = [mpt.encode_account, fork.encode_account, rlp.encode, rlp.encode_bytes,
                     rlp.encode_sequence, numeric.Uint.to_be_bytes, numeric.U256.to_be_bytes,
                     numeric.Uint.__init__, numeric.U256.__init__, numeric.U256._in_range,
                     state.Account.__init__]
        bindings = {"mpt.rlp": mpt.encode_account.__globals__["rlp"],
                    "fork.rlp": fork.encode_account.__globals__["rlp"],
                    "rlp.Uint": rlp.encode.__globals__["Uint"],
                    "rlp.FixedUnsigned": rlp.encode.__globals__["FixedUnsigned"],
                    "rlp.encode_bytes": rlp.encode.__globals__["encode_bytes"],
                    "rlp.encode_sequence": rlp.encode.__globals__["encode_sequence"]}
        return auth | {"all_installed_provider_sources": installed, "loaded_originals": loaded,
                       "functions": [function_identity(f) for f in functions],
                       "globals": {k: {"object_id": id(v), "module": getattr(v, "__module__", getattr(v, "__name__", None)),
                                        "qualname": getattr(v, "__qualname__", None)} for k,v in bindings.items()},
                       "account_schema": [{"name": f.name, "type": str(f.type)} for f in dataclasses.fields(state.Account)],
                       "classes": [{"module": cls.__module__, "qualname": cls.__qualname__, "object_id": id(cls),
                                    "mro": [t.__module__+"."+t.__qualname__ for t in cls.__mro__]}
                                   for cls in [state.Account,numeric.Uint,numeric.U256,numeric.FixedUnsigned,bm.Bytes32,bytes]],
                       "runtime": {"executable": identity_file(Path(sys.executable).resolve()), "version": sys.version,
                                   "implementation": platform.python_implementation(), "optimization": sys.flags.optimize,
                                   "dont_write_bytecode": sys.dont_write_bytecode, "isolated": sys.flags.isolated,
                                   "sys_path": list(sys.path)}}
    before = snapshot("before-source-bytes")
    (args.identities_dir / "before.json").write_text(json.dumps(before, indent=2)+"\n")
    passed = 0
    try:
        for frame in frames:
            nonce = numeric.Uint(frame["nonce"]); balance = numeric.U256(frame["balance"])
            root = bm.Bytes32(bytes(frame["storage_root"])); code = bm.Bytes32(bytes(frame["code_hash"]))
            account = state.Account(nonce, balance, code)
            require(type(account.nonce) is numeric.Uint and type(account.balance) is numeric.U256 and
                    type(account.code_hash) is bm.Bytes32 and type(root) is bm.Bytes32, "actual typed fields")
            original = mpt.encode_account(account, root); duplicate = fork.encode_account(account, root)
            independent = manual(frame)
            require(type(original) is bytes and type(duplicate) is bytes, "original result class")
            require(original == duplicate == independent and list(original) == frame["encoded"],
                    f"whole account encoding mismatch at {frame['case']}")
            print(json.dumps(frame | {"source_shared": list(original), "source_fork": list(duplicate),
                                      "manual": list(independent), "nonce_minimal": list(nonce.to_be_bytes()),
                                      "balance_minimal": list(balance.to_be_bytes()),
                                      "input_after": {"nonce": int(account.nonce), "balance": int(account.balance),
                                                      "code_hash": list(account.code_hash), "storage_root": list(root)}}), flush=True)
            passed += 1
        for name,account,root in [
                ("plain_int_nonce", state.Account(0,numeric.U256(0),bm.Bytes32(bytes(32))),bm.Bytes32(bytes(32))),
                ("short_supplied_root",state.Account(numeric.Uint(0),numeric.U256(0),bm.Bytes32(bytes(32))),b"\x01")]:
            for function in [mpt.encode_account, fork.encode_account]:
                try:
                    result = function(account,root)
                    observation = {"result": list(result), "class": type(result).__module__+"."+type(result).__qualname__}
                except Exception as error:
                    observation = {"error_class": type(error).__module__+"."+type(error).__qualname__,
                                   "error_args": [repr(a) for a in error.args]}
                print(json.dumps({"source_domain_control": name, "function": function.__module__+"."+function.__name__,
                                  "nonce": int(account.nonce), "nonce_class": type(account.nonce).__module__+"."+type(account.nonce).__qualname__,
                                  "balance": int(account.balance), "code_hash": list(account.code_hash),
                                  "storage_root": list(root), "observation": observation,
                                  "scope": "outside typed Lean input bridge; no Lean rejection claim"}), flush=True)
    finally:
        after = snapshot("after-source-bytes")
        (args.identities_dir / "after.json").write_text(json.dumps(after, indent=2)+"\n")
        (args.identities_dir / "progress.json").write_text(json.dumps({"passed": passed, "total": len(frames)})+"\n")
        require(before == after, "original identities changed")
    print(json.dumps({"source_cases": passed, "source_encoders": 2, "complete_bytes_agree": True,
                      "identities_unchanged": True}))


def main():
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--cases", type=Path)
    parser.add_argument("--eels", type=Path)
    parser.add_argument("--wheels", type=Path)
    parser.add_argument("--identities-dir", type=Path)
    args = parser.parse_args()
    if args.self_test:
        require(not any([args.cases,args.eels,args.wheels,args.identities_dir]), "self-test paths invalid")
        self_test()
    else:
        require(all([args.cases,args.eels,args.wheels,args.identities_dir]), "comparison paths required")
        compare(args)


if __name__ == "__main__":
    main()
