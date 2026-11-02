#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Observe complete prefixes from genuine authenticated pinned patricialize calls.

EELS/.venv/bin/python -I -B STFSpec/Conformance/Commit/root_prefix_differential.py \
  --eels EELS --output EXTERNAL.lean
The output must be outside both checkouts. A restored Python trace hook reads the
actual top frame after selection; no source function, recursion, encoding, hash or
class is replaced. Every traced result is also compared with a genuine untraced
call. Source/lock and installed types/RLP/crypto bytes are authenticated before and
after. Frozen installation/RECORD, interpreter/startup and host crypto remain trust
inputs. Emitted Lean guards compare the public List/drop reference expressions;
Root proves their all-input equality to its private packed implementation. The
driver elaborates those guards and supplies no compiled native execution. This
is finite pure-prefix evidence, not Lean constructor/root agreement
or an interpretation of host resources. No resource limits are changed manually.
"""
import base64
import hashlib
import importlib.metadata
import inspect
import json
from pathlib import Path
import subprocess
import sys
import tomllib

ROOT = Path(__file__).resolve().parents[3]
if not sys.flags.isolated or not sys.flags.dont_write_bytecode:
    raise SystemExit("run with the frozen EELS interpreter -I -B")
sys.path.insert(0, str(ROOT / "scripts"))
from differential import Driver, FreshSourceLoader, FreshSourceFinder


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def exact(value, cls):
    require(type(value) is cls, f"expected exact {cls}, got {type(value)}")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    context = Driver(__doc__, __file__, 42)
    pin = tomllib.loads((ROOT / "reference.toml").read_text())["release"]
    inventories = {}
    for name, package in (("ethereum-rlp", "ethereum_rlp"), ("pycryptodome", "Crypto")):
        dist = importlib.metadata.distribution(name)
        require(dist.version == pin["python_dependencies"][name], "locked version differs")
        hashes, records = {}, []
        for file in dist.files or []:
            relative = Path(file)
            path = Path(dist.locate_file(file)).absolute()
            if relative.name == "RECORD" and relative.parent.name.endswith(".dist-info"):
                records.append(path)
            if not relative.parts or relative.parts[0] != package:
                continue
            if relative.suffix not in (".py", ".so"):
                continue
            require(path.resolve() == path and path.is_relative_to(context.eels / ".venv"),
                    "installed source alias/outside venv")
            require(file.hash is not None and file.hash.mode == "sha256" and
                    file.size is not None, "installed file lacks RECORD hash")
            hashes[path] = (file.hash.value, file.size)
        require(len(records) == 1 and bool(hashes), "missing package RECORD/inventory")
        record = records[0]
        require(record.resolve() == record and record.is_relative_to(context.eels / ".venv"),
                "installed RECORD outside venv")
        inventories[package] = {"version": dist.version, "hashes": hashes,
                                "record": record, "record_bytes": record.read_bytes()}

    def matches(path, data, inventory):
        encoded = base64.urlsafe_b64encode(hashlib.sha256(data).digest()).decode().rstrip("=")
        return path.resolve() == path and inventory["hashes"].get(path) == (encoded, len(data))

    def check_installed():
        for inventory in inventories.values():
            require(inventory["record"].read_bytes() == inventory["record_bytes"],
                    "installed RECORD changed")
            for path in inventory["hashes"]:
                require(matches(path, path.read_bytes(), inventory), "installed bytes differ")

    class InstalledLoader(FreshSourceLoader):
        def get_code(self, fullname):
            path = Path(self.get_filename(fullname)).absolute()
            require(matches(path, self.get_data(str(path)),
                            inventories[fullname.split(".", 1)[0]]),
                    "import source differs from RECORD")
            return super().get_code(fullname)

    class InstalledFinder(FreshSourceFinder):
        def find_spec(self, fullname, path=None, target=None):
            package = fullname.split(".", 1)[0]
            if package not in inventories:
                return None
            spec = super().find_spec(fullname, path, target)
            require(spec is not None and isinstance(spec.loader, FreshSourceLoader),
                    "installed import must be fresh source")
            source = Path(spec.origin).absolute()
            require(source in inventories[package]["hashes"] and source.resolve() == source,
                    "installed import outside authenticated inventory")
            spec.loader = InstalledLoader(fullname, str(source), context)
            return spec

    check_installed()
    require(not any(n.split(".", 1)[0] in inventories for n in sys.modules),
            "dependency imported before authentication")
    sys.meta_path.insert(0, InstalledFinder(context))
    from ethereum import merkle_patricia_trie as mpt
    from ethereum.crypto import hash as hash_module
    from ethereum_rlp import rlp
    from ethereum_types.bytes import Bytes, Bytes32
    from ethereum_types.numeric import Uint
    require(Bytes is bytes, "locked Bytes alias differs")
    origins = {"mpt": str(context.check_source(mpt, "ethereum/merkle_patricia_trie.py")),
               "hash": str(context.check_source(hash_module, "ethereum/crypto/hash.py")),
               "rlp": str(context.check_source(rlp, "ethereum_rlp/rlp.py", dependency=True))}
    original = {name: getattr(mpt, name) for name in
                ("patricialize", "common_prefix_length", "encode_internal_node",
                 "LeafNode", "ExtensionNode", "BranchNode", "keccak256")}
    fn = original["patricialize"]
    require(inspect.isfunction(fn) and fn.__module__ == mpt.__name__ and
            Path(fn.__code__.co_filename).resolve() == Path(origins["mpt"]) and
            fn.__code__.co_firstlineno == 507, "actual callable/source identity differs")
    for name in ("LeafNode", "ExtensionNode", "BranchNode"):
        cls = original[name]
        require(type(cls) is type and cls.__module__ == mpt.__name__ and
                Path(inspect.getsourcefile(cls)).resolve() == Path(origins["mpt"]),
                "node class identity/source differs")

    def identities():
        context.check_clean()
        context.check_dependency()
        check_installed()
        return {"commit": context.head, "source_blobs": context.oracle_blobs,
                "source_sha256": {name: digest((context.eels / name).read_bytes())
                                  for name in context.oracle_blobs},
                "types_record": digest(context.dependency_record.read_bytes()),
                "types_sources": context.dependency_sources(),
                "installed": {name: {"version": inv["version"],
                    "record": str(inv["record"]), "record_sha256": digest(inv["record_bytes"]),
                    "files": {str(path): {"hash": h, "size": n} for path, (h, n)
                              in inv["hashes"].items()}} for name, inv in inventories.items()}}

    def extended(value):
        if type(value) in (bytes, Bytes32):
            return {"class": type(value).__module__ + "." + type(value).__qualname__,
                    "hex": value.hex()}
        require(type(value) in (tuple, list), "unexpected exact Extended container class")
        return {"class": "builtins." + type(value).__name__,
                "fields": [extended(v) for v in value]}

    def node_view(node):
        if node is None:
            return {"class": "builtins.NoneType"}
        require(type(node) in (mpt.LeafNode, mpt.ExtensionNode, mpt.BranchNode),
                "unexpected exact source node class")
        cls = type(node).__name__
        if type(node) is mpt.LeafNode:
            exact(node.rest_of_key, bytes)
            exact(node.value, bytes)
            return {"class": cls, "path": node.rest_of_key.hex(), "value": node.value.hex()}
        if type(node) is mpt.ExtensionNode:
            exact(node.key_segment, bytes)
            return {"class": cls, "path": node.key_segment.hex(), "child": extended(node.subnode)}
        exact(node.subnodes, tuple)
        require(len(node.subnodes) == 16, "branch must have sixteen complete children")
        exact(node.value, bytes)
        return {"class": cls, "children": [extended(v) for v in node.subnodes],
                "value": node.value.hex()}

    before = identities()
    recursion_before = sys.getrecursionlimit()
    observations = []
    emitted = ["import STFSpec.Conformance.Commit.RootPrefixGuards",
               "import STFSpec.Conformance.Fixtures.Hex",
               "open STFSpec.Commit STFSpec.Conformance.Commit.RootPrefixGuards",
               "private def raw (s : String) : ByteArray := "
               "(STFSpec.Conformance.Internal.decodeHex \"prefix differential\" s).toOption"
               ".getD ByteArray.empty",
               "private def path (s : String) : Nibbles := Nibbles.ofList "
               "((raw s).data.toList.map (fun b ↦ ⟨b.toNat % 16, by omega⟩))"]
    source_rows = []
    a = bytes([1, 2, 3, 4])
    b = bytes([1, 2, 3, 5, 6, 7])
    corpus = [("empty", [], 0), ("empty arbitrary depth", [], 99),
              ("empty singleton", [(b"", b"")], 0),
              ("singleton suffix", [(a, b"")], 2),
              ("singleton ending", [(a, b"\xff")], 4),
              ("odd unequal", [(a, b"\x07\x08"), (b, b"")], 0),
              ("odd unequal consumed", [(a, b"\x07\x08"), (b, b"")], 2),
              ("prefix relationship", [(b"\x00", b""), (b"\x00\x01", b"\xff")], 0),
              ("ending at depth", [(b"\x00", b""), (b"\x00\x01", b"\xff")], 1),
              ("empty key prefix", [(b"", b""), (b"\x0f", b"\x01")], 0),
              ("all16", [(bytes([7, 8, d]), bytes([d])) for d in range(16)], 2),
              ("long odd prefix related", [(b"\x03" * 257, b""),
                (b"\x03" * 257 + b"\x04\x05", b"\x07")], 0),
              ("long odd ending", [(b"\x03" * 257, b""),
                (b"\x03" * 257 + b"\x04\x05", b"\x07")], 257),
              ("long shared", [(b"\x03" * 4098, b""),
                (b"\x03" * 4097 + b"\x04" * 3, b"\x09\x0a")], 0),
              ("long consumed", [(b"\x03" * 4098, b""),
                (b"\x03" * 4097 + b"\x04" * 3, b"\x09\x0a")], 4096)]
    corpus += [(name + " reversed", list(reversed(entries)), level)
               for name, entries, level in list(corpus) if len(entries) > 1]
    for name, entries, level in corpus:
        exact(level, int)
        for key, value in entries:
            exact(key, bytes)
            exact(value, bytes)
            require(all(d < 16 for d in key), "unbounded digit input")
        obj = dict(entries)
        require(len(obj) == len(entries), "duplicate key input needs explicit replacement")
        require(all(len(k) >= level for k in obj), "wrong depth outside Q50 domain")
        require(not obj or len({k[:level] for k in obj}) == 1, "wrong consumed prefix")
        direct = fn(obj, Uint(level))
        direct_view = node_view(direct)
        old_trace = sys.gettrace()
        root_frame, locals_seen = None, None

        def trace(frame, event, arg):
            nonlocal root_frame, locals_seen
            if frame.f_code is fn.__code__:
                if event == "call" and root_frame is None:
                    root_frame = frame
                if frame is root_frame and event == "return":
                    locals_seen = dict(frame.f_locals)
            return trace

        try:
            sys.settrace(trace)
            traced = fn(obj, Uint(level))
        finally:
            sys.settrace(old_trace)
        require(sys.gettrace() is old_trace, "trace hook not restored")
        require(all(getattr(mpt, n) is value for n, value in original.items()),
                "source callable/class was replaced")
        require(node_view(traced) == direct_view, "tracing changed genuine source result")
        require(locals_seen is not None and locals_seen["obj"] is obj, "wrong top frame")
        map_expr = "(∅ : Std.ExtTreeMap Nibbles ByteArray)"
        for key, value in entries:
            map_expr = f'({map_expr}.insert (path "0x{key.hex()}") (raw "0x{value.hex()}"))'
        if not obj:
            require(traced is None, "empty source must return None")
            result = "none"
            amount, prefix, representative = None, None, None
        else:
            representative = locals_seen["arbitrary_key"]
            exact(representative, bytes)
            require(representative == entries[0][0], "source chose unexpected member")
            if type(traced) is mpt.LeafNode:
                prefix = traced.rest_of_key
                amount = len(prefix)
            else:
                amount = locals_seen["prefix_length"]
                exact(amount, int)
                prefix = representative[level:level + amount]
                if type(traced) is mpt.ExtensionNode:
                    require(prefix == traced.key_segment and amount > 0, "extension prefix differs")
                else:
                    require(type(traced) is mpt.BranchNode and amount == 0, "branch prefix differs")
            chosen = min(obj)
            prefix_expr = f'(path "0x{prefix.hex()}").toList.map Fin.val'
            chosen_expr = f'(path "0x{chosen.hex()}").toList.map Fin.val'
            result = f"some ({chosen_expr}, {amount}, {prefix_expr})"
            source_rows.append(f'("{name} alternative source member", '
                               f'some ([], prefixFrom {map_expr} {level} '
                               f'(path "0x{representative.hex()}"), []), some ([], {amount}, []))')
        source_rows.append(f'("{name}", selection {map_expr} {level}, {result})')
        observations.append({"name": name, "level": level,
            "entries": [{"key": k.hex(), "value": v.hex()} for k, v in entries],
            "chosen_source_member": None if representative is None else representative.hex(),
            "amount": amount, "complete_prefix": None if prefix is None else prefix.hex(),
            "complete_source_result": direct_view, "traced_equals_untraced": True,
            "trace_restored": True, "callables_unchanged": True})
    emitted.append("def sourceSelections : List (String × Option (List Nat × Nat × List Nat) ×\n"
                   "    Option (List Nat × Nat × List Nat)) := [\n  " + ",\n  ".join(source_rows) + "\n]")
    emitted += ["def allSourceSelections : Bool := sourceSelections.all "
                "(fun (_, actual, expected) ↦ actual == expected)", "#guard allSourceSelections"]
    after = identities()
    require(before == after, "source/lock/installation identity changed")
    context.output.write_text("-- Generated complete source-prefix evidence; do not commit.\n" +
                              "\n".join(emitted) + "\n")
    command = ["lake", "env", "lean", "-DwarningAsError=true", str(context.output)]
    checked = subprocess.run(command, cwd=ROOT)
    require(identities() == before, "identity changed during Lean validation")
    report = {"argv": sys.argv, "cwd": str(Path.cwd()), "executable": sys.executable,
              "isolated": sys.flags.isolated, "dont_write_bytecode": sys.flags.dont_write_bytecode,
              "origins": origins, "before": before, "after": after,
              "actual_callable": {"module": fn.__module__, "name": fn.__qualname__,
                  "source": fn.__code__.co_filename, "first_line": fn.__code__.co_firstlineno},
              "recursion_before": recursion_before, "recursion_after": sys.getrecursionlimit(),
              "manual_limit_changes": False, "replacement_callables": [],
              "source_calls": 2 * len(corpus), "observations": observations,
              "native_comparable_rows": len(source_rows), "lean_command": command,
              "lean_exit": checked.returncode, "claim": "finite complete pure prefix observations"}
    context.output.with_suffix(".json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"source_calls": report["source_calls"], "observations": len(observations),
                      "complete_rows": len(source_rows), "lean_exit": checked.returncode}))
    return checked.returncode


if __name__ == "__main__":
    raise SystemExit(main())
