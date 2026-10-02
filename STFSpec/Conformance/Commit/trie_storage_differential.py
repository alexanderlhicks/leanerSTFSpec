#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Compare complete C11 storage observations with original authenticated pinned EELS.

Run EELS/.venv/bin/python -I -B with --eels EELS --output EXTERNAL.lean.
The driver calls genuine Trie/trie_set/trie_get/copy_trie without replacement or
tracing. Numeric Uint values/Bytes32 keys and optional Bytes values/bounded Bytes
keys are separate concrete interpretations. Equality agreement on these supplied
homogeneous default comparisons is checked as a concrete premise. Numeric-key
Bytes32 contents are observed as existing Lean U256 values; this finite
interpretation adds no key adapter instance. Lawful Lean
equality proves no arbitrary heterogeneous Python bridge. Test-local validity is
preparation-only instrumentation; this driver implements no preparation API and
calls no preparation/root/hash operation. Finite storage tests are distinct from
symbolic laws. Frozen interpreter/startup/RECORD and host remain trust inputs;
all source/lock and installed types/RLP/crypto bytes are authenticated before/after.
"""
import base64
import hashlib
import importlib.metadata
import inspect
import json
from pathlib import Path
import sys
import tomllib

ROOT = Path(__file__).resolve().parents[3]
if not sys.flags.isolated or not sys.flags.dont_write_bytecode:
    raise SystemExit("run with frozen EELS interpreter -I -B")
sys.path.insert(0, str(ROOT / "scripts"))
from differential import Driver, FreshSourceLoader, FreshSourceFinder


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def raw(v):
    cls = type(v).__module__ + "." + type(v).__qualname__
    if v is None:
        return {"class": cls}
    if isinstance(v, bytes):
        return {"class": cls, "hex": v.hex()}
    if isinstance(v, int) or cls.startswith("ethereum_types.numeric."):
        return {"class": cls, "integer": int(v)}
    if isinstance(v, list):
        return {"class": cls, "items": [raw(x) for x in v]}
    raise TypeError(type(v))


def main():
    context = Driver(__doc__, __file__, 56)
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
    from ethereum_types.numeric import Uint, U256
    from ethereum_types import bytes as bytes_module, numeric as numeric_module
    require(Bytes is bytes, "locked Bytes alias differs")
    origins = {"mpt": str(context.check_source(mpt, "ethereum/merkle_patricia_trie.py")),
               "hash": str(context.check_source(hash_module, "ethereum/crypto/hash.py")),
               "rlp": str(context.check_source(rlp, "ethereum_rlp/rlp.py", dependency=True))}
    original = {name: getattr(mpt, name) for name in ("Trie", "trie_set", "trie_get", "copy_trie")}
    for name, line in (("trie_set", 325), ("trie_get", 341), ("copy_trie", 315)):
        fn = original[name]
        require(inspect.isfunction(fn) and fn.__module__ == mpt.__name__ and
                Path(fn.__code__.co_filename).resolve() == Path(origins["mpt"]) and
                fn.__code__.co_firstlineno == line, "original callable identity differs")
    require(type(mpt.Trie) is type and mpt.Trie.__module__ == mpt.__name__ and
            Path(inspect.getsourcefile(mpt.Trie)).resolve() == Path(origins["mpt"]),
            "original Trie class identity differs")

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
    class_bindings = (mpt.Trie, bytes_module.Bytes, bytes_module.Bytes32,
                      numeric_module.Uint, numeric_module.U256)
    require(class_bindings == (original["Trie"], Bytes, Bytes32, Uint, U256),
            "nominal class bindings differ before observations")
    bindings = (hash_module.keccak256, rlp.encode)
    recursion_before = sys.getrecursionlimit()
    hook_before = sys.gettrace()
    rows, emissions, emitted = [], [], ["import STFSpec.Conformance.Commit.TrieGuards",
        "open STFSpec.Base STFSpec.Commit STFSpec.Conformance.Commit.TrieGuards"]

    def lean_list(xs, f):
        return "[" + ", ".join(f(x) for x in xs) + "]"

    def lean_value(v, family):
        if family == "numeric":
            require(type(v) is Uint, "numeric value nominal class differs")
            return str(int(v))
        require(v is None or type(v) is bytes, "optional value class differs")
        return "none" if v is None else "(some (Bytes.ofList " + lean_list(v, str) + "))"

    def lean_key(k, family):
        if family == "numeric":
            require(type(k) is Bytes32 and len(k) == 32, "numeric key nominal class differs")
            return "(U256.ofNat " + str(int.from_bytes(k, "big")) + ")"
        require(type(k) is bytes and all(d < 16 for d in k), "bounded key class/digits differ")
        return "(Nibbles.ofList " + lean_list(k, str) + ")"

    def observed_value(v, family):
        if family == "numeric":
            return lean_value(v, family)
        return "none" if v is None else "(some " + lean_list(v, str) + ")"

    def view(t, queries, family):
        require(type(t) is mpt.Trie and type(t.secured) is bool and type(t._data) is dict,
                "nominal Trie fields differ")
        entries = sorted(t._data.items())
        gets = [mpt.trie_get(t, k) for k in queries]
        for k, v in entries:
            lean_key(k, family)
            lean_value(v, family)
        lean_value(t.default, family)
        entries_term = lean_list(entries, lambda kv: "(" +
            (str(int.from_bytes(kv[0], "big")) if family == "numeric" else
             lean_list(kv[0], str)) + ", " + observed_value(kv[1], family) + ")")
        expected = ("(" + str(t.secured).lower() + ", " +
                    observed_value(t.default, family) + ", " + entries_term + ", " +
                    lean_list(gets, lambda v: observed_value(v, family)) + ")")
        raw_view = {"secured": raw(t.secured), "default": raw(t.default),
            "entries": [{"key": raw(k), "value": raw(v)} for k, v in entries],
            "queries": [raw(k) for k in queries], "results": [raw(v) for v in gets]}
        return expected, raw_view

    def observation(label, t, expr, queries, family):
        expected, full = view(t, queries, family)
        row = len(rows)
        snapshot = "numericSnapshot" if family == "numeric" else "bytesSnapshot"
        declaration = f"sourceRow{row}"
        emitted.extend([f"def {declaration} : Bool × String :=", f"  let actual := {snapshot} ({expr}) " +
            lean_list(queries, lambda k: lean_key(k, family)),
            f"  let expected := {expected}",
            f"  (actual == expected, reprStr ({json.dumps(label)}, actual))",
            f"#guard {declaration}.1", f"#eval IO.println {declaration}.2"])
        rows.append({"label": label, "family": family, "complete_observation": full,
                     "lean_expression": expr, "expected": expected})
        emissions.append(declaration)

    for family, defaults in (("numeric", [Uint(0), Uint(99), Uint(2**256 + 7)]),
            ("optional", [None, Bytes(b""), Bytes(b"\x07\x00\xff")])):
        keys = ([Bytes32(n.to_bytes(32, "big")) for n in (0, 1, 2**256 - 1)]
                if family == "numeric" else
                [Bytes(b""), Bytes(b"\x00\x01"), Bytes(b"\x0f\x02\x03")])
        nondefault = ([Uint(0), Uint(7), Uint(99), Uint(2**256 + 11)]
                      if family == "numeric" else
                      [None, Bytes(b""), Bytes(b"\x04"), Bytes(b"\x09\x00\xff")])
        for secured in (False, True):
            for di, default in enumerate(defaults):
                prefix = family + "-" + str(secured).lower() + "-default" + str(di)
                t = mpt.Trie(secured, default)
                K, V = ("U256", "Nat") if family == "numeric" else ("Nibbles", "(Option Bytes)")
                expr = ("(Trie.mk " + str(secured).lower() + " " +
                        lean_value(default, family) + f" (∅ : Std.ExtTreeMap {K} {V}))")
                observation(prefix + "-empty", t, expr, keys, family)
                writes = ([(keys[0], default)] +
                          [(keys[i % 3], v) for i, v in enumerate(nondefault)] +
                          [(keys[1], nondefault[-1]), (keys[0], default), (keys[2], default)])
                for wi, (k, v) in enumerate(writes):
                    # Homogeneous concrete equality interpretation is an explicit checked premise.
                    equality = ((int(v) == int(default)) if family == "numeric" else
                        ((v is None and default is None) or
                         (type(v) is bytes and type(default) is bytes and bytes(v) == bytes(default))))
                    require((v == default) is equality, "Python/default equality premise differs")
                    old = mpt.copy_trie(t)
                    require(old is not t and old._data is not t._data, "copy must own independent dict")
                    old_view = view(old, keys, family)
                    old_expr = "(copyTrie " + expr + ")"
                    before_gets = [mpt.trie_get(t, q) for q in keys]
                    mpt.trie_set(t, k, v)
                    expr = "(trieSet " + expr + " " + lean_key(k, family) + " " + lean_value(v, family) + ")"
                    require(mpt.trie_get(t, k) == v and (k not in t._data) == equality,
                            "changed-key source behavior differs")
                    require(view(old, keys, family) == old_view, "copied old observations changed")
                    for q, prior in zip(keys, before_gets):
                        if q != k:
                            require(mpt.trie_get(t, q) == prior, "distinct-key changed")
                    observation(prefix + f"-copy-before-{wi}", old, old_expr, keys, family)
                    observation(prefix + f"-write-{wi}", t, expr, keys, family)
                # Directly stored default: construction does not silently enforce NoDefault.
                direct = mpt.Trie(secured, default, {keys[1]: default})
                direct_expr = ("(Trie.mk " + str(secured).lower() + " " +
                    lean_value(default, family) + f" ((∅ : Std.ExtTreeMap {K} {V}).insert " +
                    lean_key(keys[1], family) + " " + lean_value(default, family) + "))")
                observation(prefix + "-direct-stored-default", direct, direct_expr, keys, family)

    require(all(getattr(mpt, n) is fn for n, fn in original.items()), "source bindings changed")
    require(class_bindings == (mpt.Trie, bytes_module.Bytes, bytes_module.Bytes32,
                              numeric_module.Uint, numeric_module.U256),
            "nominal module class bindings changed")
    require(bindings == (hash_module.keccak256, rlp.encode),
            "dependency/runtime bindings changed")
    require(sys.gettrace() is hook_before and sys.getrecursionlimit() == recursion_before,
            "trace/recursion configuration changed")
    after = identities()
    require(before == after, "authenticated inputs changed")
    emitted.append("def sourceRows : Array (Bool × String) := #[" + ", ".join(emissions) + "]")
    context.output.parent.mkdir(parents=True, exist_ok=True)
    context.output.write_text("\n".join(emitted) + "\n")
    report = {"pin": context.head, "lexical_python": sys.executable, "python": sys.version,
        "source_before": before, "source_after": after, "unchanged": before == after,
        "recursion_before_imports": recursion_before_imports, "recursion_after_imports": recursion_before,
        "trace_used": False, "rows": rows, "row_count": len(rows),
        "class_bindings_before_after": [cls.__module__ + "." + cls.__qualname__
                                       for cls in class_bindings],
        "equality_bridge": "checked homogeneous Uint and optional Bytes/None default comparisons only",
        "preparation_api_implemented": False, "emitted_sha256": digest(context.output.read_bytes())}
    context.output.with_suffix(".json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"complete_storage_rows": len(rows), "source_unchanged": True,
                      "lean_output": str(context.output)}, indent=2))


if __name__ == "__main__":
    main()
