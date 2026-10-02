#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Observe complete recursive construction from genuine authenticated pinned patricialize calls.

EELS/.venv/bin/python -I -B STFSpec/Conformance/Commit/root_construction_differential.py \
  --eels EELS --output EXTERNAL.lean
The output must be outside both checkouts. A restored Python trace hook reads the
actual top frame after selection; no source function, recursion, encoding, hash or
class is replaced. Every traced result is also compared with a genuine untraced
call. Source/lock and installed types/RLP/crypto bytes are authenticated before and
after. Frozen installation/RECORD, interpreter/startup and host crypto remain trust
inputs. This is finite C7 construction evidence, not C8/root agreement
or an interpretation of host resources. No resource limits are changed manually.
"""
import base64
import dataclasses
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



def qualified(value):
    cls = type(value)
    return cls.__module__ + "." + cls.__qualname__

def raw(value):
    cls = qualified(value)
    if value is None:
        return {"class": cls}
    if isinstance(value, bytes):
        return {"class": cls, "hex": value.hex(), "length": len(value)}
    if isinstance(value, int) or cls == "ethereum_types.numeric.Uint":
        return {"class": cls, "integer": int(value)}
    if isinstance(value, (tuple, list)):
        return {"class": cls, "items": [raw(v) for v in value]}
    if isinstance(value, dict):
        return {"class": cls, "entries": [[raw(k), raw(v)] for k, v in value.items()]}
    if dataclasses.is_dataclass(value):
        return {"class": cls, "fields": {f.name: raw(getattr(value, f.name))
                for f in dataclasses.fields(value)}}
    raise TypeError(type(value))

def fixtures():
    b = bytes
    prefix = b([i % 16 for i in range(129)])
    cases = [
        ("empty-zero", 0, []), ("empty-depth-19", 19, []),
        ("singleton-empty-key-empty-value", 0, [(b(), b())]),
        ("singleton-ending-depth", 3, [(b([2, 4, 6]), b("value", "ascii"))]),
        ("singleton-suffix-odd", 2, [(b([2, 4, 6, 8, 10]), b())]),
        ("empty-ending-and-continuing", 0, [(b(), b()), (b([0]), b())]),
        ("extension-empty-ending-and-continuing", 0,
            [(b([0]), b()), (b([0, 1]), b("x", "ascii"))]),
        ("ending-nonzero-depth-fullkeys", 2,
            [(b([9, 3]), b("end", "ascii")), (b([9, 3, 0]), b()),
             (b([9, 3, 15, 2]), b("long", "ascii"))]),
        ("all-sixteen-plus-ending", 0,
            [(b(), b("end", "ascii"))] + [(b([d]), b([d])) for d in range(16)]),
        ("all-sixteen-nonzero-fullkeys", 2,
            [(b([11, 4, d, d]), b([d]) * (d + 1)) for d in range(16)]),
        ("odd-shared-prefix", 0,
            [(b([1, 2, 3, 4, 5, 0]), b()), (b([1, 2, 3, 4, 5, 15, 2]), b("z", "ascii"))]),
        ("long-odd-shared-prefix", 0,
            [(prefix + b([0]), b("a", "ascii")), (prefix + b([15, 2]), b("b", "ascii"))]),
        ("shared-prefix-from-nonzero-depth", 3,
            [(b([6, 7, 8, 9, 10, 11, 0]), b("a", "ascii")),
             (b([6, 7, 8, 9, 10, 11, 15]), b("b", "ascii"))]),
        ("unequal-length-nested-prefixes", 0,
            [(b([4]), b("a", "ascii")), (b([4, 0]), b()),
             (b([4, 0, 3]), b("b", "ascii")), (b([4, 15]), b("c", "ascii"))]),
        ("leaf-child-31-32-33", 0,
            [(b([d]), b("B", "ascii") * (28 + d)) for d in range(3)]),
        ("extension-over-hashed-branch", 0,
            [(b([7, 8, d]), b([d + 1]) * (28 + d)) for d in range(3)]),
    ]
    for total in (9, 10, 11):
        cases.append((f"branch-child-{22 + total}", 0,
            [(b([5, 0]), b("A", "ascii") * 4),
             (b([5, 1]), b("B", "ascii") * (total - 4))]))
    # Additional deterministic bounded full-key maps; generated inputs, not acceptance caps.
    state = 4701
    for case in range(8):
        entries = {}
        for j in range(2 + case % 4):
            state = (1103515245 * state + 12345) % (1 << 31)
            length = 1 + state % 7
            key = b([(state >> (4 * (i % 7))) % 16 for i in range(length)])
            entries[key] = b([j + 1]) * (state % 36)
        cases.append((f"generated-{case}", 0, list(entries.items())))
    return cases

def main():
    context = Driver(__doc__, __file__, 48)
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
    recursion_before_imports = sys.getrecursionlimit()
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
    targets = {fn.__code__: "patricialize",
        original["encode_internal_node"].__code__: "encode_internal_node",
        original["keccak256"].__code__: "keccak256"}
    bindings = (hash_module.keccak256, hash_module._keccak256_digest, rlp.encode,
                Bytes, Bytes32, Uint)
    observations, source_rows, common = [], [], {}
    emitted = ["import STFSpec.Conformance.Commit.RootConstructionGuards",
        "import STFSpec.Conformance.Fixtures.Hex",
        "open STFSpec.Commit STFSpec.Codec STFSpec.Conformance.Commit.RootConstructionGuards",
        "private def sourceBytes (s : String) : ByteArray := "
        "(STFSpec.Conformance.Internal.decodeHex \"construction differential\" s).toOption"
        ".getD ByteArray.empty"]

    def lean_bytes(value):
        require(type(value) in (bytes, Bytes32), "unexpected byte class")
        return f'(sourceBytes "0x{value.hex()}")'

    def lean_path(value):
        exact(value, bytes)
        require(all(d < 16 for d in value), "source path digit outside nibble domain")
        return "(Nibbles.ofList [" + ", ".join(f"⟨{d}, by decide⟩" for d in value) + "])"

    def lean_item(value):
        if type(value) in (bytes, Bytes32):
            return "RlpItem.bytes " + lean_bytes(value)
        require(type(value) in (tuple, list), "unexpected Extended class")
        return "RlpItem.list [" + ", ".join(lean_item(v) for v in value) + "]"

    def lean_node(node):
        if node is None:
            return "none"
        if type(node) is mpt.LeafNode:
            return f'(some (InternalNode.leaf {lean_path(node.rest_of_key)} ({lean_item(node.value)})))'
        if type(node) is mpt.ExtensionNode:
            return f'(some (InternalNode.extension {lean_path(node.key_segment)} ({lean_item(node.subnode)})))'
        exact(node, mpt.BranchNode)
        require(len(node.subnodes) == 16, "branch arity differs")
        return "(some (InternalNode.branch #v[" + ", ".join(lean_item(v) for v in node.subnodes) + "] (" + lean_item(node.value) + ")))"

    corpus = fixtures()
    corpus += [("last-write-full-values", 0, [(b"", b"first"), (b"\x00", b"child"),
        (b"", b"last"), (b"\x00", b"")])]
    for name, level, writes in corpus:
        final = list(dict(writes).items())
        orders = [writes]
        for i in range(len(final)):
            rotated = final[i:] + final[:i]
            for order in [rotated, rotated[:1] + list(reversed(rotated[1:]))]:
                if order not in orders:
                    orders.append(order)
        for variant, entries in enumerate(orders):
            obj = dict(entries)
            require(all(type(k) is bytes and type(v) is bytes and all(d < 16 for d in k)
                        for k, v in obj.items()), "input classes/digits differ")
            require(all(level <= len(k) for k in obj) and len({k[:level] for k in obj}) <= 1,
                    "outside Q50 domain")
            original_obj = raw(obj)
            events, stack, active, consumed = [], [], {}, set()
            old_hook = sys.gettrace()

            def trace(frame, event, arg):
                consumed.add(frame.f_code.co_filename)
                kind = targets.get(frame.f_code)
                if kind is None:
                    return trace
                if event == "call":
                    index = len(events)
                    active[id(frame)] = index
                    parent = stack[-1] if stack else None
                    stack.append(index)
                    record = {"index": index, "event": "call", "operation": kind,
                        "parent_call": parent, "source": frame.f_code.co_filename,
                        "first_line": frame.f_code.co_firstlineno}
                    if kind == "patricialize":
                        record.update(obj=raw(frame.f_locals["obj"]), level=raw(frame.f_locals["level"]))
                    elif kind == "encode_internal_node":
                        record["node"] = raw(frame.f_locals["node"])
                    else:
                        record["preimage"] = raw(frame.f_locals["buffer"])
                    events.append(record)
                elif event == "return":
                    call = active.pop(id(frame))
                    require(stack.pop() == call, "call stack differs")
                    record = {"index": len(events), "event": "return", "operation": kind,
                        "call": call, "result": raw(arg)}
                    if kind == "patricialize":
                        record["selection"] = {k: raw(frame.f_locals[k]) for k in
                            ("arbitrary_key", "substring", "prefix_length", "prefix", "branches", "value")
                            if k in frame.f_locals}
                    elif kind == "encode_internal_node":
                        record.update(unencoded=raw(frame.f_locals["unencoded"]),
                                      rlp=raw(frame.f_locals["encoded"]))
                    events.append(record)
                elif event == "exception":
                    raise AssertionError((name, variant, kind, "source exception", repr(arg)))
                return trace

            try:
                sys.settrace(trace)
                result = fn(obj, Uint(level))
            finally:
                sys.settrace(old_hook)
            require(sys.gettrace() is old_hook and not stack and not active, "trace not restored")
            replay = fn(obj, Uint(level))
            require(raw(result) == raw(replay) and raw(obj) == original_obj, "trace/input effect")
            require(all(getattr(mpt, n) is value for n, value in original.items()), "source replaced")
            require(bindings == (hash_module.keccak256, hash_module._keccak256_digest,
                rlp.encode, Bytes, Bytes32, Uint), "dependency/class binding changed")
            query_calls = [e for e in events if e["event"] == "call" and e["operation"] == "keccak256"]
            returns = {e["call"]: e for e in events if e["event"] == "return"}
            queries = [(bytes.fromhex(e["preimage"]["hex"]),
                        bytes.fromhex(returns[e["index"]]["result"]["hex"])) for e in query_calls]
            for e in query_calls:
                require(events[e["parent_call"]]["operation"] == "encode_internal_node",
                        "unexpected parent query")
                require(len(bytes.fromhex(returns[e["index"]]["result"]["hex"])) == 32,
                        "answer width differs")
            signature = (raw(result), [(a.hex(), b.hex()) for a, b in queries])
            if name in common:
                require(common[name] == signature, "same final-map member/insertion variant differs")
            common[name] = signature
            map_expr = "(∅ : Std.ExtTreeMap Nibbles ByteArray)"
            for key, value in entries:
                map_expr = f'({map_expr}.insert {lean_path(key)} {lean_bytes(value)})'
            domain_expr = "PatricializeDomain.zero _" if level == 0 else \
                "(STFSpec.Conformance.Commit.RootDomainGuards.domainCheck_iff _ _).mp (by decide)"
            query_expr = "[" + ", ".join(f'(({lean_bytes(a)}).data.toList, ({lean_bytes(b)}).data.toList)'
                                       for a, b in queries) + "]"
            source_rows.append(f'("{name} variant{variant}", concreteTrace {map_expr} {level} ({domain_expr}), '
                f'(nodeView {lean_node(result)}, {query_expr}))')
            observations.append({"fixture": name, "variant": variant, "writes": raw(entries),
                "input": original_obj, "level": raw(Uint(level)), "traced_result": raw(result),
                "untraced_replay_result": raw(replay), "events": events,
                "consumed_trace_files": sorted(consumed)})
    row_type = ("String × (NodeView × List (List UInt8 × List UInt8)) × "
                "(NodeView × List (List UInt8 × List UInt8))")
    row_names = []
    # Keep every original full-value comparison while compiling and evaluating
    # one row at a time. A single large declaration/guard can exhaust the Lean
    # compiler's host resources; this changes neither inputs nor resource limits.
    for index, row in enumerate(source_rows):
        name = f"sourceConstructionRow{index}"
        row_names.append(name)
        emitted += [f"def {name} : {row_type} :=\n  {row}",
                    f"#guard let (_, actual, expected) := {name}; actual == expected",
                    f'#eval IO.println "complete source row {index}"']
    emitted.append(f"def sourceConstructions : List ({row_type}) := [\n  " +
                   ",\n  ".join(row_names) + "\n]")
    emitted += ["def allSourceConstructions : Bool := sourceConstructions.all "
                "(fun (_, actual, expected) ↦ actual == expected)"]
    after = identities()
    require(before == after, "source/lock/installation identity changed")
    context.output.write_text("-- Generated complete C7 source evidence; do not commit.\n" +
                              "\n".join(emitted) + "\n")
    command = ["lake", "env", "lean", "-DwarningAsError=true", "--root",
               str(context.output.parent), str(context.output)]
    checked = subprocess.run(command, cwd=ROOT)
    require(identities() == before, "identity changed during Lean validation")
    report = {"argv": sys.argv, "cwd": str(Path.cwd()), "executable": sys.executable,
        "isolated": sys.flags.isolated, "dont_write_bytecode": sys.flags.dont_write_bytecode,
        "origins": origins, "before": before, "after": after,
        "actual_callable": {"module": fn.__module__, "name": fn.__qualname__,
            "source": fn.__code__.co_filename, "first_line": fn.__code__.co_firstlineno},
        "recursion_before_imports": recursion_before_imports, "recursion_before": recursion_before,
        "recursion_after": sys.getrecursionlimit(), "manual_limit_changes": False,
        "replacement_callables": [], "source_calls": 2 * len(observations),
        "observations": observations, "native_comparable_rows": len(source_rows),
        "lean_command": command, "lean_exit": checked.returncode,
        "claim": "finite complete recursive C7 construction/query observations; no C8/root claim"}
    context.output.with_suffix(".json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"source_calls": report["source_calls"], "observations": len(observations),
                      "complete_rows": len(source_rows), "lean_exit": checked.returncode}))
    return checked.returncode


if __name__ == "__main__":
    raise SystemExit(main())
