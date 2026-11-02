#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Compare pure preparation with genuine authenticated pinned _prepare_trie calls.

EELS/.venv/bin/python -I -B STFSpec/Conformance/Commit/preparation_differential.py \
  --eels EELS --output EXTERNAL.lean
Complete maps and ordered failures are retained, together with traced/untraced
replays. No source callable, class, encoder, hash or recursion policy is replaced.
Source/lock and installed types/RLP/Crypto bytes are checked before and after.
Frozen installation/RECORD, interpreter/startup and host remain trust inputs.
Finite supported-value observations do not discharge consumer encodings, root,
secure-key or host-resource agreement. No limits are changed manually.
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

def main():
    context = Driver(__doc__, __file__, 61)
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
    from ethereum_types.bytes import Bytes, Bytes0, Bytes1, Bytes20, Bytes32
    from ethereum_types.numeric import Uint
    require(Bytes is bytes, "locked Bytes alias differs")
    origins = {"mpt": str(context.check_source(mpt, "ethereum/merkle_patricia_trie.py")),
               "hash": str(context.check_source(hash_module, "ethereum/crypto/hash.py")),
               "rlp": str(context.check_source(rlp, "ethereum_rlp/rlp.py", dependency=True))}
    original = {name: getattr(mpt, name) for name in
                ("_prepare_trie", "_prepare_data", "encode_node", "bytes_to_nibble_list",
                 "Trie", "Account", "keccak256")}
    fn = original["_prepare_trie"]
    require(inspect.isfunction(fn) and fn.__module__ == mpt.__name__ and
            Path(fn.__code__.co_filename).resolve() == Path(origins["mpt"]) and
            fn.__code__.co_firstlineno == 451, "actual callable/source identity differs")
    for name in ("Trie", "Account"):
        cls = original[name]
        require(type(cls) is type and
                (cls.__module__ == mpt.__name__ if name == "Trie" else
                 cls.__module__ == "ethereum.state") and
                (Path(inspect.getsourcefile(cls)).resolve() == Path(origins["mpt"])
                 if name == "Trie" else Path(inspect.getsourcefile(cls)).resolve() == context.eels / "src/ethereum/state.py"),
                "class identity/source differs")

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
    bindings = (hash_module.keccak256, hash_module._keccak256_digest, rlp.encode,
                Bytes, Bytes0, Bytes1, Bytes20, Bytes32, Uint, mpt.Trie.__init__)
    callable_info = {name: {"module": value.__module__, "name": value.__qualname__,
        "source": str(inspect.getsourcefile(value)),
        "first_line": value.__code__.co_firstlineno if inspect.isfunction(value) else None}
        for name, value in original.items()}

    def recipe(value):
        if value is None:
            return {"tag": "none"}
        if type(value) in (bytes, Bytes0, Bytes1, Bytes20, Bytes32):
            return {"tag": "raw", "bytes": list(value)}
        if type(value) is Uint:
            return {"tag": "integer", "number": int(value)}
        exact(value, tuple)
        return {"tag": "collection", "items": [recipe(v) for v in value]}

    def value_view(value):
        return {"class": qualified(value), "recipe": recipe(value)}

    def data_view(data):
        exact(data, dict)
        return [{"key": raw(k), "value": value_view(v)} for k, v in data.items()]

    def prepared_view(data):
        exact(data, dict)
        for key, value in data.items():
            exact(key, bytes)
            exact(value, bytes)
            require(all(d < 16 for d in key), "prepared nibble outside range")
        return [{"key": list(k), "value": list(v)} for k, v in sorted(data.items())]

    ordinal = [rlp.encode(Uint(i)) for i in (0, 1, 127, 128, 256)]
    synthetic_tuple = (Uint(3), Uint(4), Bytes20(bytes(range(20))), Uint(5))
    already_encoded = rlp.encode(synthetic_tuple)
    cases = [
        ("empty-none", None, []), ("empty-arbitrary-default", b"default", []),
        ("empty-key", None, [(b"", b"value")]),
        ("prefixes-leadingzeros", None, [(b"\xff", b"last"), (b"", b"empty"),
            (b"\x00\x01", b"two"), (b"\x00", b"one"), (b"\x01", b"other"),
            (b"\x01\xff", b"variable"), (b"\x02", b"mismatch")]),
        ("ordinal-raw-bytes", None, list(zip(ordinal,
            [b"\x02\xc0", b"\xc0", b"\x80", b"\x01", already_encoded]))),
        ("native-fixed-alias-last-write", None,
            [(Bytes1(b"\x01"), b"first"), (b"\x01", b"last"), (Bytes0(b""), b"empty")]),
        ("stored-valid-byte-default", b"\x07", [(b"\x00", b"\x07")]),
        ("stored-valid-int-default", Uint(0), [(b"\x00", Uint(0))]),
        ("empty-collection-zero", None,
            [(b"", ()), (b"\x00", Uint(0)), (b"\x00\x01", Uint(1)), (b"\xff", Uint(256))]),
        ("mixed-supported-values", None,
            [(b"\x10", (Uint(0), Uint(1), b"", (b"\x00", Uint(128)), ())),
             (b"\x11", b"\x02\xc0"), (b"\x12", already_encoded), (b"\x13", Uint(128))]),
        ("direct-none-invalid", b"default", [(b"\x00", None)]),
        ("empty-bytes-nondefault-invalid", None, [(b"\x00", b"")]),
        ("empty-bytes-default-invalid", b"", [(b"\x00", b"")]),
        ("none-fails-before-encoding-and-later-binding", None,
            [(b"\x02", b"first"), (b"\x01", None), (b"\x00", b"later")]),
        ("empty-fails-after-encoding-before-later-binding", None,
            [(b"\x02", b"first"), (b"\x01", b""), (b"\x00", b"later")]),
    ]
    long = bytes(range(129))
    cases += [("long-key-and-zero-prefix", None,
        [(long + b"\x00", b"one"), (long + b"\x01", b"two"), (b"\x00" * 33, b"zero")]),
        ("all-sixteen-first-nibbles", None, [(bytes([16 * d]), bytes([d])) for d in range(16)]),
        ("noninjective-values-retain-both-keys", None, [(b"\x00", b"\x80"), (b"\x01", Uint(0))])]
    targets = {original[name].__code__: name for name in
        ("_prepare_trie", "_prepare_data", "encode_node", "bytes_to_nibble_list", "keccak256")}
    observations, rows = [], []
    emitted = ["import STFSpec.Conformance.Commit.PreparationGuards",
        "open STFSpec.Commit STFSpec.Codec STFSpec.Conformance.Commit.PreparationGuards"]

    def lit(xs):
        return "[" + ", ".join(str(x) for x in xs) + "]"

    def lean_bytes(xs):
        return "(" + lit(xs) + ".toByteArray)"

    def lean_item(r):
        if r["tag"] == "raw":
            return "(.bytes " + lean_bytes(r["bytes"]) + ")"
        if r["tag"] == "integer":
            return "(Rlp.ofNat " + str(r["number"]) + ")"
        require(r["tag"] == "collection", "unsupported RLP item recipe")
        return "(.list [" + ", ".join(lean_item(x) for x in r["items"]) + "])"

    def lean_value(r):
        if r["tag"] == "none":
            return ".none"
        if r["tag"] == "raw":
            return "(.raw " + lean_bytes(r["bytes"]) + ")"
        if r["tag"] == "integer":
            return "(.integer " + str(r["number"]) + ")"
        require(r["tag"] == "collection", "unsupported sample value recipe")
        return "(.collection [" + ", ".join(lean_item(x) for x in r["items"]) + "])"

    def run(trie):
        try:
            result = fn(trie)
        except Exception as error:
            return {"error": {"class": qualified(error), "message": str(error),
                "args": list(error.args)}}
        return {"prepared": prepared_view(result)}

    for name, default, writes in cases:
        final = list(dict(writes).items())
        # Failure ordering is checked in original dictionary order. Successful maps
        # are also checked after reversed insertion of exactly the same final data.
        orders = [writes]
        if all(v is not None and not (isinstance(v, bytes) and not v) for _, v in final):
            reversed_final = list(reversed(final))
            if reversed_final != writes:
                orders.append(reversed_final)
        for variant, entries in enumerate(orders):
            trie = mpt.Trie(False, default, dict(entries))
            exact(trie, original["Trie"])
            stored_before = data_view(trie._data)
            events, consumed = [], set()
            old_hook = sys.gettrace()

            def trace(frame, event, arg):
                consumed.add(frame.f_code.co_filename)
                kind = targets.get(frame.f_code)
                if kind is not None:
                    record = {"operation": kind, "event": event,
                        "source": frame.f_code.co_filename, "line": frame.f_lineno}
                    if event == "call" and kind == "encode_node":
                        record["value"] = value_view(frame.f_locals["node"])
                    if event == "return" and kind in ("encode_node", "bytes_to_nibble_list"):
                        record["result"] = raw(arg)
                    if event == "exception":
                        record["exception"] = {"class": arg[0].__module__ + "." + arg[0].__qualname__,
                            "message": str(arg[1]), "args": list(arg[1].args)}
                    if event in ("call", "return", "exception"):
                        events.append(record)
                return trace

            try:
                sys.settrace(trace)
                result = run(trie)
            finally:
                sys.settrace(old_hook)
            replay = run(trie)
            require(sys.gettrace() is old_hook and result == replay, "trace/replay differs")
            require(data_view(trie._data) == stored_before, "stored data changed")
            require(all(getattr(mpt, n) is v for n, v in original.items()), "source replaced")
            require(bindings == (hash_module.keccak256, hash_module._keccak256_digest,
                rlp.encode, Bytes, Bytes0, Bytes1, Bytes20, Bytes32, Uint, mpt.Trie.__init__),
                "dependency/class binding changed")
            require(not any(e["operation"] == "keccak256" and e["event"] == "call"
                for e in events), "unsecured preparation queried")
            calls = [e["value"] for e in events if e["operation"] == "encode_node"
                and e["event"] == "call"]
            if "prepared" in result:
                require(len(result["prepared"]) == len(trie._data), "binding filtered or aliased")
                require(calls == [value_view(v) for v in trie._data.values()], "encode call order/count")
                require(all(row["value"] for row in result["prepared"]), "empty successful encoding")
                input_expr = "[" + ", ".join("(" + lit(list(k)) + ", " +
                    lean_value(recipe(v)) + ")" for k, v in entries) + "]"
                expected = "[" + ", ".join("(" + lit(r["key"]) + ", " + lit(r["value"]) + ")"
                    for r in result["prepared"]) + "]"
                row_name = "sourcePreparationRow" + str(len(rows))
                rows.append(row_name)
                emitted += [f"def {row_name} : String × List (List Nat × List UInt8) × "
                    "List (List Nat × List UInt8) :=\n  " +
                    f'("{name} variant{variant}", observePrepared {lean_value(recipe(default))} '
                    f"{input_expr}, {expected})",
                    f"#guard let (_, actual, expected) := {row_name}; actual == expected"]
            else:
                values = list(trie._data.values())
                first_invalid = next(i for i, v in enumerate(values)
                    if v is None or (isinstance(v, bytes) and not v))
                encoded_prefix = values[:first_invalid + (values[first_invalid] is not None)]
                require(calls == [value_view(v) for v in encoded_prefix], "failure encoding precedence")
                require(result["error"]["class"] == "builtins.AssertionError", "failure class differs")
                expected_message = "cannot encode `None`" if values[first_invalid] is None else ""
                require(result["error"]["message"] == expected_message, "failure message differs")
            observations.append({"name": name, "variant": variant,
                "default": value_view(default), "input_rows":
                [{"key": raw(k), "value": value_view(v)} for k, v in entries],
                "stored_before": stored_before, "stored_after": data_view(trie._data),
                "noDefault": all(v != default for v in trie._data.values()),
                "traced": result, "untraced_replay": replay,
                "events": events, "consumed_files": sorted(consumed)})

    emitted += ["def sourcePreparations : List (String × List (List Nat × List UInt8) × "
        "List (List Nat × List UInt8)) := [" + ", ".join(rows) + "]",
        "def allSourcePreparations : Bool := sourcePreparations.all "
        "(fun (_, actual, expected) ↦ actual == expected)",
        "def printSourcePreparations : IO Unit := do",
        "  for (name, actual, expected) in sourcePreparations do",
        "    IO.println (repr (name, actual, expected))",
        "  if !allSourcePreparations then throw (IO.userError \"prepared map mismatch\")"]
    after = identities()
    require(before == after and sys.getrecursionlimit() == recursion_before,
            "source/dependency/limit changed")
    context.output.write_text("-- Generated complete preparation evidence; do not commit.\n" +
                              "\n".join(emitted) + "\n")
    command = ["lake", "env", "lean", "-DwarningAsError=true", "--root",
               str(context.output.parent), str(context.output)]
    checked = subprocess.run(command, cwd=ROOT, capture_output=True)
    context.output.with_suffix(".lean.stdout").write_bytes(checked.stdout)
    context.output.with_suffix(".lean.stderr").write_bytes(checked.stderr)
    require(identities() == before, "identity changed during Lean validation")
    report = {"argv": sys.argv, "cwd": str(Path.cwd()), "executable": sys.executable,
        "isolated": sys.flags.isolated, "dont_write_bytecode": sys.flags.dont_write_bytecode,
        "origins": origins, "before": before, "after": after, "callables": callable_info,
        "synthetic_tuple": value_view(synthetic_tuple), "already_encoded": raw(already_encoded),
        "synthetic_scope": "supported tuple, not an actual Withdrawal instance",
        "recursion_before_imports": recursion_before_imports,
        "recursion_before": recursion_before, "recursion_after": sys.getrecursionlimit(),
        "manual_limit_changes": False, "replacement_callables": [],
        "source_calls": 2 * len(observations), "observations": observations,
        "native_comparable_rows": len(rows), "lean_command": command,
        "lean_exit": checked.returncode, "guest_records_executed": 0,
        "claim": "finite complete unsecured supported-value preparation maps and ordered failures"}
    context.output.with_suffix(".json").write_text(json.dumps(report, indent=2) + "\n")
    print(checked.stdout.decode(errors="replace"))
    print(checked.stderr.decode(errors="replace"), file=sys.stderr)
    print(json.dumps({"source_calls": report["source_calls"], "observations": len(observations),
        "complete_rows": len(rows), "lean_exit": checked.returncode}))
    return checked.returncode


if __name__ == "__main__":
    raise SystemExit(main())
