#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Compare finite complete C8 roots with genuine authenticated pinned Trie/root calls.

EELS/.venv/bin/python -I -B STFSpec/Conformance/Commit/math_root_differential.py \
  --eels EELS --output EXTERNAL.lean
The destination must be outside both checkouts. Original Trie, trie_set, preparation,
packing, value encoding, patricialize, C6, RLP and hashing execute without replacement.
A restored trace hook captures actual prepared mappings and complete original query
values; every full call is replayed without tracing. Empty source roots query RLP80
once, acquiring the coherent supplied constant; approved local mathRoot then queries
zero times. Preparation queries are outside local C8. Invalid preparation fixtures
are source-only controls, with no typed-trie preparation implementation or policy claim.
Source/lock and installed types/RLP/crypto RECORD bytes are checked before/after.
Interpreter/startup, frozen installation/RECORD and host crypto remain trust inputs.
No manual resource limits, general source refinement, canonicality or EEST claim.
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


def raw(value):
    cls = type(value).__module__ + "." + type(value).__qualname__
    if value is None:
        return {"class": cls}
    if isinstance(value, bytes):
        return {"class": cls, "hex": value.hex(), "length": len(value)}
    if type(value) is bool:
        return {"class": cls, "boolean": value}
    if type(value) is int or cls == "ethereum_types.numeric.Uint":
        return {"class": cls, "integer": int(value)}
    if type(value) in (tuple, list):
        return {"class": cls, "items": [raw(v) for v in value]}
    if type(value) is dict:
        return {"class": cls, "entries": [[raw(k), raw(v)] for k, v in value.items()]}
    if dataclasses.is_dataclass(value):
        return {"class": cls, "fields": {f.name: raw(getattr(value, f.name))
                for f in dataclasses.fields(value)}}
    raise TypeError(type(value))


def fixtures(Uint, seed):
    cases = [
        ("empty", False, b"", [], None),
        ("erased-default-empty-value", False, b"", [(b"", b"x"), (b"", b"")], None),
        ("singleton-empty-packed-key", False, b"", [(b"", b"x")], None),
        ("packed-key-conversion", False, b"", [(b"\x12", b"x")], None),
        ("empty-key-ending-branch", False, b"", [(b"", b"end"), (b"\x00", b"a")], None),
        ("children-wire31-32-33", False, b"", [(bytes([d << 4]), b"A" * (28 + d))
            for d in range(3)], None),
        ("odd-extension-hashed-branch", False, b"", [(b"\x50", b"A" * 28),
            (b"\x51", b"B" * 29), (b"\x52", b"C" * 30)], None),
        ("nested-prefix-ending", False, b"", [(b"\x12", b"end"),
            (b"\x12\x30", b"a"), (b"\x12\x31", b"b"), (b"\x12\xff", b"c")], None),
        ("all-sixteen", False, b"", [(bytes([d << 4]), bytes([d + 1]))
            for d in range(16)], None),
        ("all-sixteen-thresholds", False, b"", [(bytes([d << 4]), bytes([d + 1]) *
            (28 + d % 3)) for d in range(16)], None),
        ("secured-two-prepared-keys", True, b"", [(b"alpha", b"a"), (b"beta", b"b")], None),
        ("typed-uint-prepared-values", False, Uint(0), [(b"\x01", Uint(1)),
            (b"\x02", Uint(256))], None),
        ("last-write-and-default-erasure", False, b"", [(b"\x12", b"first"),
            (b"\x13", b"child"), (b"\x12", b"last"), (b"\x13", b"")], None),
        ("empty-value-source-assert", False, None, [(b"\x12", b"")], "AssertionError"),
        ("none-value-source-assert", False, b"", [(b"\x12", None)], "AssertionError"),
        ("secured-preparation-failure-after-prior-query", True, None,
            [(b"alpha", b"a"), (b"beta", b"")], "AssertionError"),
    ]
    for width in (31, 32, 33):
        cases.append((f"top-wire{width}", False, b"", [(b"", b"A" * (width - 3))], None))
    state = seed
    for index in range(8):
        entries = {}
        for j in range(2 + index % 4):
            state = (1103515245 * state + 12345) % (1 << 31)
            key = bytes((state >> (8 * (i % 3))) % 256 for i in range(1 + state % 4))
            entries[key] = bytes([j + 1]) * (1 + state % 36)
        cases.append((f"generated-packed-{index}", False, b"", list(entries.items()), None))
    return cases


def main():
    context = Driver(__doc__, __file__, 51)
    require(Path(sys.executable).absolute() == context.eels / ".venv/bin/python",
            "use the original lexical EELS/.venv/bin/python path")
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
                                "record": record, "record_bytes": record.read_bytes(),
                                "package": Path(dist.locate_file(package)).absolute()}

    def matches(path, data, inventory):
        encoded = base64.urlsafe_b64encode(hashlib.sha256(data).digest()).decode().rstrip("=")
        return path.resolve() == path and inventory["hashes"].get(path) == (encoded, len(data))

    def check_installed():
        for inventory in inventories.values():
            require(inventory["record"].read_bytes() == inventory["record_bytes"],
                    "installed RECORD changed")
            require({p for p in inventory["package"].rglob("*") if p.suffix in (".py", ".so")}
                    == set(inventory["hashes"]), "installed source inventory changed")
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
                ("root", "_prepare_trie", "_prepare_data", "encode_node", "trie_set",
                 "bytes_to_nibble_list", "nibble_list_to_compact", "patricialize",
                 "common_prefix_length", "encode_internal_node", "Trie",
                 "LeafNode", "ExtensionNode", "BranchNode", "keccak256")}
    fn = original["root"]
    require(inspect.isfunction(fn) and fn.__module__ == mpt.__name__ and
            Path(fn.__code__.co_filename).resolve() == Path(origins["mpt"]) and
            fn.__code__.co_firstlineno == 478, "actual callable/source identity differs")
    for name in ("Trie", "LeafNode", "ExtensionNode", "BranchNode"):
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

    before = identities()
    recursion_before = sys.getrecursionlimit()
    operations = {original[name]: name for name in ("root", "_prepare_trie", "_prepare_data",
        "encode_node", "patricialize", "encode_internal_node", "keccak256")}
    operations[rlp.encode] = "rlp_encode"
    targets = {f.__code__: name for f, name in operations.items()}
    source_codes = {name: f.__code__ for f, name in operations.items()}
    bindings = (hash_module.keccak256, hash_module._keccak256_digest, rlp.encode,
                Bytes, Bytes32, Uint)
    observations, source_rows, common, top_widths = [], [], {}, set()
    emitted = ["import STFSpec.Conformance.Commit.MathRootGuards",
        "import STFSpec.Conformance.Fixtures.Hex",
        "open STFSpec.Base STFSpec.Commit STFSpec.Conformance.Commit.MathRootGuards",
        "private def sourceBytes (s : String) : ByteArray := "
        "(STFSpec.Conformance.Internal.decodeHex \"mathRoot differential\" s).toOption"
        ".getD ByteArray.empty"]

    def lean_bytes(value):
        require(type(value) in (bytes, Bytes32), "unexpected byte class")
        return f'(sourceBytes "0x{value.hex()}")'

    def lean_path(value):
        exact(value, bytes)
        require(all(d < 16 for d in value), "source path digit outside nibble domain")
        return "(Nibbles.ofList [" + ", ".join(f"⟨{d}, by decide⟩" for d in value) + "])"

    def invoke(trie):
        try:
            return {"ok": raw(fn(trie))}
        except Exception as error:
            return {"error": {"class": type(error).__module__ + "." + type(error).__qualname__,
                "message": str(error)}}

    def raw_bytes(value):
        require(value["class"] in ("builtins.bytes", "ethereum_types.bytes.Bytes32"),
                "unexpected source byte class")
        exact(value["length"], int)
        result = bytes.fromhex(value["hex"])
        require(len(result) == value["length"], "source byte length differs")
        if value["class"] == "ethereum_types.bytes.Bytes32":
            require(len(result) == 32, "source fixed hash width differs")
        return result

    for name, secured, default, writes, expected_error in fixtures(Uint, context.seed):
        orders = [writes]
        # Genuine trie_set retains erasure and last-write behavior on every order.
        # Only unique, non-default, successful fixtures have permutation variants.
        if expected_error is None and len({k for k, _ in writes}) == len(writes) and all(
                value != default for _, value in writes):
            for i in range(len(writes)):
                rotated = writes[i:] + writes[:i]
                for order in (rotated, rotated[:1] + list(reversed(rotated[1:]))):
                    if order not in orders:
                        orders.append(order)
        for variant, entries in enumerate(orders):
            trie = mpt.Trie(secured=secured, default=default)
            for key, value in entries:
                mpt.trie_set(trie, key, value)
            original_input = raw(trie)
            events, stack, active, consumed = [], [], {}, set()
            old_hook = sys.gettrace()
            argument_fields = {"root": ("trie", "get_storage_root"),
                "_prepare_trie": ("trie", "get_storage_root"),
                "_prepare_data": ("data", "secured", "get_storage_root"),
                "encode_node": ("node", "storage_root"), "patricialize": ("obj", "level"),
                "encode_internal_node": ("node",), "keccak256": ("buffer",),
                "rlp_encode": ("raw_data",)}

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
                    events.append({"index": index, "event": event, "operation": kind,
                        "parent_call": parent, "source": frame.f_code.co_filename,
                        "first_line": frame.f_code.co_firstlineno,
                        "arguments": {k: raw(frame.f_locals[k]) for k in argument_fields[kind]}})
                elif event == "return":
                    call = active.pop(id(frame))
                    require(stack.pop() == call, "source call stack differs")
                    fields = {"root": ("obj", "root_node"), "_prepare_trie": (),
                        "_prepare_data": ("mapped", "encoded_value", "key"), "encode_node": (),
                        "patricialize": ("arbitrary_key", "substring", "prefix_length", "prefix",
                            "branches", "value"), "encode_internal_node": ("unencoded", "encoded"),
                        "keccak256": (), "rlp_encode": ()}[kind]
                    events.append({"index": len(events), "event": event, "operation": kind,
                        "call": call, "result": raw(arg), "locals": {k: raw(frame.f_locals[k])
                            for k in fields if k in frame.f_locals}})
                elif event == "exception":
                    typ, error, tb = arg
                    events.append({"index": len(events), "event": event, "operation": kind,
                        "call": active[id(frame)], "error": {"class": typ.__module__ + "." +
                            typ.__qualname__, "message": str(error),
                            "source": tb.tb_frame.f_code.co_filename, "line": tb.tb_lineno}})
                return trace

            try:
                sys.settrace(trace)
                result = invoke(trie)
            finally:
                sys.settrace(old_hook)
            require(sys.gettrace() is old_hook and not stack and not active, "trace not restored")
            replay = invoke(trie)
            require(result == replay and raw(trie) == original_input, "trace/input effect")
            require(all(getattr(mpt, n) is value for n, value in original.items()), "source replaced")
            require(all(f.__code__ is source_codes[label] for f, label in operations.items()),
                    "source code object changed")
            require(bindings == (hash_module.keccak256, hash_module._keccak256_digest,
                rlp.encode, Bytes, Bytes32, Uint), "dependency/class binding changed")
            require(("error" in result) == (expected_error is not None), "unexpected source outcome")
            calls = [e for e in events if e["event"] == "call"]
            returns = {e["call"]: e for e in events if e["event"] == "return"}
            exceptions = [e for e in events if e["event"] == "exception"]
            require(calls[0]["operation"] == "root" and calls[0]["parent_call"] is None,
                    "source root dispatch differs")
            record = {"fixture": name, "variant": variant, "scope": "genuine original Trie/root",
                "writes": raw(entries), "input": original_input, "traced_result": result,
                "untraced_replay_result": replay, "events": events,
                "consumed_trace_files": sorted(consumed)}
            if expected_error is not None:
                require(result["error"]["class"] == "builtins." + expected_error,
                        "original preparation error differs")
                require(exceptions and not any(e["operation"] in ("patricialize",
                    "encode_internal_node") for e in calls), "invalid preparation reached C8")
                record["local_C8_comparison"] = False
                observations.append(record)
                continue
            require(not exceptions, "successful source call raised exception")
            prep = next(e for e in calls if e["operation"] == "_prepare_trie")
            prepared_raw = returns[prep["index"]]["result"]
            require(prepared_raw["class"] == "builtins.dict", "prepared map class differs")
            prepared = [(raw_bytes(k), raw_bytes(v)) for k, v in prepared_raw["entries"]]
            require(all(v and all(d < 16 for d in k) for k, v in prepared),
                    "original prepared domain differs")
            pat = next(e for e in calls if e["operation"] == "patricialize")
            require(pat["arguments"]["obj"] == prepared_raw and
                pat["arguments"]["level"] == raw(Uint(0)), "original full map/depth differs")
            enc = next(e for e in calls if e["operation"] == "encode_internal_node" and
                e["parent_call"] == calls[0]["index"])
            require(enc["arguments"]["node"] == returns[pat["index"]]["result"],
                    "original top construction/encoding differs")
            top_wire = raw_bytes(returns[enc["index"]]["locals"]["encoded"])
            top_widths.add(len(top_wire))
            query_calls = [e for e in calls if e["operation"] == "keccak256"]
            preparation_calls = [e for e in query_calls if e["index"] < pat["index"]]
            construction_calls = [e for e in query_calls if e["index"] >= pat["index"]]
            queries = [(raw_bytes(e["arguments"]["buffer"]),
                raw_bytes(returns[e["index"]]["result"])) for e in construction_calls]
            require(all(len(answer) == 32 for _, answer in queries), "original hash width differs")
            require(queries and queries[-1][0] == top_wire, "complete top query absent/out of order")
            root_bytes = raw_bytes(result["ok"])
            require(root_bytes == queries[-1][1], "original whole digest differs")
            if not prepared:
                require(not preparation_calls and queries == [(b"\x80", root_bytes)] and
                    root_bytes == bytes(mpt.EMPTY_TRIE_ROOT), "original empty acquisition differs")
                local_queries = []
            else:
                local_queries = queries
            signature = (root_bytes.hex(), [(a.hex(), b.hex()) for a, b in local_queries])
            if name in common:
                require(common[name] == signature, "same final-map insertion variant differs")
            common[name] = signature
            map_expr = "(∅ : Std.ExtTreeMap Nibbles ByteArray)"
            for key, value in prepared:
                map_expr = f'({map_expr}.insert {lean_path(key)} {lean_bytes(value)})'
            query_expr = "[" + ", ".join(f'(({lean_bytes(a)}).data.toList, ({lean_bytes(b)}).data.toList)'
                                       for a, b in local_queries) + "]"
            source_rows.append(f'("{name} variant{variant}", concreteTrace {map_expr} '
                f'HashConsts.literals.emptyTrieRoot, (({lean_bytes(root_bytes)}).data.toList, {query_expr}))')
            record.update(local_C8_comparison=True, prepared_mapping=prepared_raw,
                prepared_nonempty=bool(prepared), full_top_wire=raw(top_wire),
                source_preparation_queries=[e["index"] for e in preparation_calls],
                source_acquisition_queries=0 if prepared else 1,
                local_queries=[[a.hex(), b.hex()] for a, b in local_queries])
            observations.append(record)
    require({31, 32, 33} <= top_widths, "actual top wire31/32/33 missing")
    row_type = ("String × (List UInt8 × List (List UInt8 × List UInt8)) × "
                "(List UInt8 × List (List UInt8 × List UInt8))")
    row_names = []
    for index, row in enumerate(source_rows):
        name = f"sourceRootRow{index}"
        row_names.append(name)
        emitted += [f"def {name} : {row_type} :=\n  {row}",
                    f"#guard let (_, actual, expected) := {name}; actual == expected",
                    f'#eval IO.println "complete source root row {index}"']
    emitted.append(f"def sourceRoots : List ({row_type}) := [\n  " +
                   ",\n  ".join(row_names) + "\n]")
    emitted += ["def allSourceRoots : Bool := sourceRoots.all "
                "(fun (_, actual, expected) ↦ actual == expected)"]
    after = identities()
    require(before == after and recursion_before == sys.getrecursionlimit(),
            "source/lock/installation/limits changed")
    context.output.write_text("-- Generated complete finite C8 source evidence; do not commit.\n" +
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
        "source_callables": {name: {"source": f.__code__.co_filename,
            "first_line": f.__code__.co_firstlineno} for f, name in operations.items()},
        "recursion_before_imports": recursion_before_imports, "recursion_before": recursion_before,
        "recursion_after": sys.getrecursionlimit(), "manual_limit_changes": False,
        "trace_restored": True, "replacement_callables": [], "source_calls": 2 * len(observations),
        "observations": observations, "native_comparable_rows": len(source_rows),
        "source_only_preparation_failures": sum(not r["local_C8_comparison"] for r in observations),
        "top_widths": sorted(top_widths), "lean_command": command, "lean_exit": checked.returncode,
        "claim": "finite genuine original roots versus complete local C8 results/queries after actual "
            "prepared mapping; empty original acquisition excluded from approved zero-query local action; "
            "no typed-trie preparation or whole-source/secure-ordering/canonicality/EEST claim"}
    context.output.with_suffix(".json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"source_calls": report["source_calls"], "observations": len(observations),
        "complete_rows": len(source_rows), "source_only_failures": report["source_only_preparation_failures"],
        "lean_exit": checked.returncode}))
    return checked.returncode


if __name__ == "__main__":
    raise SystemExit(main())
