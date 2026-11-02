#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Finite field-shape/order observations of the actual pinned witness decoder.

Run EELS/.venv/bin/python -I -B with --eels EELS --output EXTERNAL.lean.
Emit full actual RLP/compact seam comparisons; whole-node diagnostic dispatch is
unimplemented. Source/lock/installed RECORD and exact result classes are checked
before/after; hooks are restored and calls replayed untraced. Frozen interpreter,
installation/RECORD and host remain trust inputs. No guest execution is claimed.
"""
import sys

if not sys.flags.isolated or not sys.flags.dont_write_bytecode or sys.flags.optimize:
    raise RuntimeError("unoptimized lexical EELS .venv/bin/python -I -B required")

from pathlib import Path
import base64
import hashlib
import importlib.metadata
import json
import platform
import ssl
import subprocess
import tomllib

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "STFSpec/Conformance/Codec"))
from rlp_typed_differential import setup_driver, RlpSourceAuth, RlpFreshFinder

context = setup_driver(__doc__, Path(__file__), 52)
auth = RlpSourceAuth(context)
sys.meta_path.insert(0, RlpFreshFinder(auth))
pin = tomllib.loads((ROOT / "reference.toml").read_text())["release"]

# Crypto may be imported by the actual module and used for longer control nodes.
# Verify its full installed RECORD inventory, including native backend files.
dist = importlib.metadata.distribution("pycryptodome")
assert dist.version == pin["python_dependencies"]["pycryptodome"]
crypto_files = {}
records = []
for item in dist.files or []:
    path = Path(dist.locate_file(item)).absolute()
    if item.name == "RECORD" and item.parent.name.endswith(".dist-info"):
        records.append(path)
    if item.parts and item.parts[0] == "Crypto":
        assert path.resolve() == path and path.is_relative_to(context.eels / ".venv")
        assert item.hash is not None and item.hash.mode == "sha256" and item.size is not None
        data = path.read_bytes()
        actual = base64.urlsafe_b64encode(hashlib.sha256(data).digest()).decode().rstrip("=")
        assert (actual, len(data)) == (item.hash.value, item.size)
        crypto_files[path] = (hashlib.sha256(data).hexdigest(), len(data))
assert len(records) == 1 and records[0].resolve() == records[0]
crypto_record = records[0].read_bytes()
crypto_package = Path(dist.locate_file("Crypto")).absolute()
assert set(crypto_package.rglob("*.py")) == {p for p in crypto_files if p.suffix == ".py"}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def snapshot():
    context.check_clean()
    context.check_dependency()
    auth.check()
    assert records[0].read_bytes() == crypto_record
    assert set(crypto_package.rglob("*.py")) == {p for p in crypto_files if p.suffix == ".py"}
    for path, expected in crypto_files.items():
        data = path.read_bytes()
        assert (sha(data), len(data)) == expected
    return {
        "pin": context.head,
        "source_lock": {path: {"git_blob": blob, "sha256": sha((context.eels / path).read_bytes())}
                        for path, blob in context.oracle_blobs.items()},
        "types_sources": context.dependency_sources(),
        "types_record": {"path": str(context.dependency_record), "sha256": sha(context.dependency_record_bytes)},
        "rlp_sources": {str(path): digest for path, digest in auth.expected.items()},
        "rlp_record": {"path": str(auth.record), "sha256": sha(auth.record_bytes)},
        "crypto_sources": {str(path): {"sha256": digest, "size": size} for path, (digest, size) in crypto_files.items()},
        "crypto_record": {"path": str(records[0]), "sha256": sha(crypto_record)},
    }

before = snapshot()
from ethereum_rlp import rlp
from ethereum_types.bytes import Bytes, Bytes32
from ethereum.forks.amsterdam import incremental_mpt as inc
from ethereum.crypto import hash as crypto
context.check_source(inc, "ethereum/forks/amsterdam/incremental_mpt.py")
context.check_source(crypto, "ethereum/crypto/hash.py")
context.check_source(rlp, "ethereum_rlp/rlp.py", dependency=True)
assert Bytes is bytes

def fq(cls):
    return cls.__module__ + "." + cls.__qualname__

def raw(value):
    cls = type(value)
    if cls in (bytes, bytearray, Bytes32):
        return {"class": fq(cls), "hex": value.hex(), "length": len(value)}
    if cls in (list, tuple):
        return {"class": fq(cls), "items": [raw(item) for item in value]}
    if cls is bool:
        return {"class": fq(cls), "value": value}
    if value is None:
        return {"class": fq(cls)}
    if cls in (inc.MutableLeafNode, inc.MutableExtensionNode, inc.MutableBranchNode, inc.HashedNode):
        return {"class": fq(cls), "fields": {name: raw(getattr(value, name)) for name in value.__dataclass_fields__}}
    raise TypeError("unclassified raw source class: " + fq(cls))

def error(exc):
    assert type(exc) in (AssertionError, IndexError, rlp.DecodingError)
    return {"class": fq(type(exc)), "message": str(exc), "args": [repr(a) for a in exc.args],
            "args_class": fq(type(exc.args)), "args_repr": repr(exc.args)}

functions = [inc._decode_witness_node, inc.compact_to_nibbles, inc._resolve_child_ref, rlp.decode]
saved = [(fn, fn.__code__) for fn in functions]
targets = {fn.__code__: fn.__qualname__ for fn in functions}
events = []
assert sys.gettrace() is None

def trace(frame, event, arg):
    if frame.f_code in targets:
        row = {"function": targets[frame.f_code], "event": event, "file": frame.f_code.co_filename,
               "line": frame.f_lineno}
        if event == "exception":
            row["error"] = error(arg[1])
        if event == "call":
            row["arguments"] = {key: raw(frame.f_locals[key]) for key in ("rlp_bytes", "compact", "child_ref", "encoded_data") if key in frame.f_locals}
        if event == "line":
            row["locals"] = {key: raw(frame.f_locals[key]) for key in ("decoded", "path_bytes", "nibbles", "is_leaf", "value") if key in frame.f_locals}
        if event == "return":
            row["result"] = raw(arg)
        events.append(row)
    return trace

def call(wire):
    try:
        return {"status": "ok", "raw_result": raw(inc._decode_witness_node({}, wire))}
    except (AssertionError, IndexError, rlp.DecodingError) as exc:
        return {"status": "error", "raw_error": error(exc)}

cases = []
def observe(name, wire, scope="wire"):
    assert type(wire) in (bytes, bytearray)
    events.clear()
    sys.settrace(trace)
    try:
        observed = call(wire)
    finally:
        sys.settrace(None)
    trace_rows = list(events)
    replay = call(wire)
    assert replay == observed
    try:
        decoded = {"status": "ok", "result": raw(rlp.decode(wire))}
    except rlp.DecodingError as exc:
        decoded = {"status": "error", "error": error(exc)}
    cases.append({"name": name, "scope": scope, "raw_input": raw(wire), "raw_rlp_decode": decoded,
                  "outcome": observed, "trace": trace_rows, "untraced_replay": replay})

observe("list_compact_path", bytes.fromhex("c2c0c0"))
observe("list_leaf_value", bytes.fromhex("c220c0"))
for path_name, path in [("empty", b""), ("extension_empty", b"\x00"), ("extension_odd", b"\x10"),
                        ("leaf_empty", b"\x20"), ("leaf_odd", b"\x30"),
                        ("empty_list", []), ("bytes_list", [b"\x20"]), ("nested_list", [[]])]:
    for value_name, value in [("empty_bytes", b""), ("bytes", b"\x7f"), ("empty_list", []), ("nested_list", [[]])]:
        observe(path_name + "_" + value_name, rlp.encode([path, value]))
for flag in range(16):
    for value_name, value in [("empty_bytes", b""), ("empty_list", [])]:
        observe(f"flag_{flag:x}_{value_name}", rlp.encode([bytes([flag << 4]), value]))
for path in [b"\x2f", b"\x6f\x12", b"\xf1\x23", b"\x4f", b"\xd1\x23"]:
    observe("lenient_path_" + path.hex() + "_list_value", rlp.encode([path, []]))

# Whole RLP parsing precedes both semantic assertions, including malformed second field.
for name, wire in [("path_list_second_bad_rlp", "c4c0810180"),
                   ("leaf_list_with_trailing", "c220c080"),
                   ("compact_empty_second_bad_rlp", "c3808101"),
                   ("list_path_bad_ref", "c2c078"),
                   ("leaf_bytes_bad_ref_is_value", "c22078"),
                   ("empty_extension_bad_ref", "c20078"),
                   ("odd_extension_bad_ref", "c21078"),
                   ("odd_extension_empty_inline", "c210c0"),
                   ("odd_extension_list_path_child", "c410c2c0c0"),
                   ("odd_extension_leaf_list_child", "c410c220c0")]:
    observe(name, bytes.fromhex(wire))
branch = [b"\x11" * 32, b"\x22" * 32] + [b""] * 14 + [[]]
observe("branch_list_value_adjacent_control", rlp.encode(branch), "adjacent branch-value control only")
for name, wire in [("list_path_mutable", "c2c0c0"), ("leaf_list_mutable", "c220c0"),
                   ("leaf_empty_mutable", "c22080")]:
    observe(name, bytearray.fromhex(wire), "direct mutable bytearray API control")

# Observation hooks must be restored, and no source callable was replaced.
assert sys.gettrace() is None
assert all(fn.__code__ is code for fn, code in saved)
assert [inc._decode_witness_node, inc.compact_to_nibbles, inc._resolve_child_ref, rlp.decode] == functions
after = snapshot()
assert before == after
result = {
    "scope": "two field-shape failures and bounded adjacent/order controls only",
    "environment": {"executable": sys.executable, "prefix": sys.prefix, "python": platform.python_version(),
                    "openssl": ssl.OPENSSL_VERSION, "isolated": sys.flags.isolated,
                    "dont_write_bytecode": sys.flags.dont_write_bytecode,
                    "recursion_limit": sys.getrecursionlimit(), "eels": str(context.eels),
                    "ethereum_types": context.version, "ethereum_rlp": "0.1.6", "pycryptodome": dist.version},
    "authentication_before": before, "authentication_after": after,
    "authentication_equal": before == after, "no_callable_substitution": True,
    "accepted_basis_head": subprocess.check_output(["git", "--no-replace-objects", "--no-optional-locks", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
    "trace_restored": sys.gettrace() is None, "cases": cases,
    "counts": {"cases": len(cases), "ok": sum(c["outcome"]["status"] == "ok" for c in cases),
               "error": sum(c["outcome"]["status"] == "error" for c in cases), "untraced_replays": len(cases)},
    "technical_helper_identities": {str(path): sha(path.read_bytes()) for path in [
        ROOT / "scripts/differential.py", ROOT / "STFSpec/Conformance/Codec/rlp_typed_differential.py",
        ROOT / "reference.toml", ROOT / "STFSpec/informal/CONTRACT.md", ROOT / "STFSpec/informal/DECISIONS.md",
        ROOT / "STFSpec/informal/modules/EthCommit.md", ROOT / "STFSpec/Commit/TrieError.lean", Path(__file__)]},
}
# Check the precise source exception/descendant order, independently of Lean dispatch.
expected_lines = {
    "list_compact_path": [("_decode_witness_node", 946)],
    "list_leaf_value": [("_decode_witness_node", 951)],
    "path_list_second_bad_rlp": [("decode", 153), ("decode", 156),
                                  ("_decode_witness_node", 936)],
    "leaf_list_with_trailing": [("decode", 156), ("_decode_witness_node", 936)],
    "empty_empty_list": [("compact_to_nibbles", 878), ("_decode_witness_node", 947)],
    "list_path_bad_ref": [("_decode_witness_node", 946)],
    "empty_extension_bad_ref": [("_decode_witness_node", 959)],
    "odd_extension_empty_inline": [("_decode_witness_node", 991),
                                    ("_resolve_child_ref", 914), ("_decode_witness_node", 960)],
    "odd_extension_list_path_child": [("_decode_witness_node", 946),
                                       ("_resolve_child_ref", 914), ("_decode_witness_node", 960)],
    "odd_extension_leaf_list_child": [("_decode_witness_node", 951),
                                       ("_resolve_child_ref", 914), ("_decode_witness_node", 960)],
}
for case in cases:
    if case["name"] in expected_lines:
        assert [(e["function"], e["line"]) for e in case["trace"]
                if e["event"] == "exception"] == expected_lines[case["name"]]
assert result["counts"] == {"cases": 85, "error": 70, "ok": 15, "untraced_replays": 85}

# Complete actual codec/compact outputs, no miniature node decoder or invented result.
def lean_bytes(hex_value):
    return "b [" + ", ".join(str(v) for v in bytes.fromhex(hex_value)) + "]"

def lean_item(value):
    if value["class"] in ("builtins.bytes", "builtins.bytearray"):
        return "(.bytes (" + lean_bytes(value["hex"]) + "))"
    assert value["class"] == "builtins.list"
    return "(.list [" + ", ".join(lean_item(v) for v in value["items"]) + "])"

guards = ["import STFSpec.Conformance.Commit.DecoderDiagnosticGuards",
          "open STFSpec.Codec STFSpec.Commit",
          "open STFSpec.Conformance.Commit.DecoderDiagnosticGuards"]
for case in cases:
    parsed = case["raw_rlp_decode"]
    if parsed["status"] == "ok":
        guards.append("#guard sameRlp (Rlp.decode (" + lean_bytes(case["raw_input"]["hex"]) +
                      ")) (.ok " + lean_item(parsed["result"]) + ")")
compact_outputs = {}
for case in cases:
    for event in case["trace"]:
        if event["function"] == "compact_to_nibbles" and event["event"] == "call":
            wire = event["arguments"]["compact"]
            assert wire["class"] == "builtins.bytes"
            compact_wire = bytes.fromhex(wire["hex"])
            try:
                decoded = inc.compact_to_nibbles(compact_wire)
                assert type(decoded) is tuple and len(decoded) == 2
                assert type(decoded[0]) is bytes and type(decoded[1]) is bool
                expected = ".ok (" + repr(list(decoded[0])) + ", " + str(decoded[1]).lower() + ")"
            except IndexError as exc:
                assert compact_wire == b"" and exc.args == ("index out of range",)
                expected = ".error (.malformed .compactEmpty)"
            compact_outputs[wire["hex"]] = expected
for hex_value, expected in compact_outputs.items():
    guards.append("#guard sameCompact (compactView (" + lean_bytes(hex_value) + ")) (" + expected + ")")
context.output.write_text("-- Generated finite seam observations; do not commit.\n" +
                          "\n".join(guards) + "\n")
compiled = subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", str(context.output)],
                          cwd=ROOT, capture_output=True)
result["lean_command"] = {"argv": compiled.args, "cwd": str(ROOT), "exit": compiled.returncode,
                          "stdout": compiled.stdout.decode(), "stderr": compiled.stderr.decode()}
result["seam_guards"] = len(guards) - 3
result["compact_full_values"] = compact_outputs
assert all(fn.__code__ is code for fn, code in saved)
assert [inc._decode_witness_node, inc.compact_to_nibbles, inc._resolve_child_ref, rlp.decode] == functions
assert sys.gettrace() is None
result["authentication_after"] = snapshot()
assert before == result["authentication_after"]
print(json.dumps(result, indent=2, sort_keys=True))
raise SystemExit(compiled.returncode)
