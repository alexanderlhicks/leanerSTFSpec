#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Observe actual pinned build_node_db using isolated, freshly compiled authenticated source.

Run EELS/.venv/bin/python -I -B STFSpec/Conformance/Commit/node_db_differential.py
--eels EELS --output OUTSIDE/NodeDBSource.lean.
Full concrete table observations and instrumented order/collision/failure controls
are retained alongside emitted guards. Loader/startup/installation/RECORD and the
host hash backend are trust premises; this is not guest/EEST or security evidence.
"""

import base64
import hashlib
import importlib.abc
import importlib.machinery
import importlib.metadata
import json
from pathlib import Path
import random
import sys
import tomllib

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "scripts"))
from differential import setup_driver


def sha(data):
    return hashlib.sha256(data).hexdigest()


def typename(value):
    cls = type(value)
    return cls.__module__ + "." + cls.__qualname__


class InstalledSources:
    """Validate every installed distribution's recorded Python sources before imports."""

    def __init__(self, eels):
        self.venv = eels / ".venv"
        self.sources, self.records, self.packages = {}, {}, {}
        for dist in importlib.metadata.distributions():
            selected = []
            for file in dist.files or []:
                path = Path(dist.locate_file(file)).absolute()
                if not path.is_relative_to(self.venv):
                    continue
                if file.name == "RECORD" and file.parent.name.endswith(".dist-info"):
                    self.records[path] = path.read_bytes()
                if file.suffix != ".py":
                    continue
                if path.resolve() != path or file.hash is None or file.hash.mode != "sha256":
                    raise ImportError(f"invalid source RECORD entry: {path}")
                data = path.read_bytes()
                value = (base64.urlsafe_b64encode(hashlib.sha256(data).digest())
                         .decode().rstrip("="))
                if (value, len(data)) != (file.hash.value, file.size):
                    raise ImportError(f"source differs from RECORD: {path}")
                self.sources[path] = (sha(data), len(data))
                selected.append(str(path))
            self.packages[dist.metadata["Name"]] = {"version": dist.version, "sources": selected}
        self.check()

    def verify(self, path, data):
        path = Path(path).absolute()
        if path.resolve() != path or self.sources.get(path) != (sha(data), len(data)):
            raise ImportError(f"unauthenticated installed source: {path}")

    def check(self):
        for path, raw in self.records.items():
            if path.read_bytes() != raw:
                raise ImportError(f"RECORD changed: {path}")
        for path in self.sources:
            self.verify(path, path.read_bytes())

    def metadata(self):
        sources = {str(p): {"sha256": h, "size": n} for p, (h, n) in self.sources.items()}
        return {"sources": sources,
                "records": {str(p): sha(b) for p, b in self.records.items()},
                "distributions": self.packages}


class InstalledLoader(importlib.machinery.SourceFileLoader):
    def __init__(self, name, path, auth):
        super().__init__(name, path)
        self.auth = auth

    def get_code(self, name):
        path = self.get_filename(name)
        data = self.get_data(path)
        self.auth.verify(path, data)
        return self.source_to_code(data, path)


class InstalledFinder(importlib.abc.MetaPathFinder):
    def __init__(self, auth):
        self.auth = auth

    def find_spec(self, name, path=None, target=None):
        spec = importlib.machinery.PathFinder.find_spec(name, path)
        if spec is None or spec.origin is None:
            return None
        origin = Path(spec.origin).absolute()
        if not origin.is_relative_to(self.auth.venv):
            return None
        if isinstance(spec.loader, importlib.machinery.SourceFileLoader):
            self.auth.verify(origin, origin.read_bytes())
            spec.loader = InstalledLoader(name, str(origin), self.auth)
        # Binary hash/curve backends remain the frozen-installation trust premise.
        return spec


def array(raw):
    return "⟨#[" + ", ".join(str(b) for b in raw) + "]⟩"


def callable_record(fn):
    code = getattr(fn, "__code__", None)
    return {"id": id(fn), "class": typename(fn), "module": getattr(fn, "__module__", None),
            "qualname": getattr(fn, "__qualname__", None),
            "filename": None if code is None else code.co_filename,
            "firstlineno": None if code is None else code.co_firstlineno}


def main():
    if not sys.flags.isolated or not sys.flags.dont_write_bytecode:
        raise RuntimeError("use isolated -I -B interpreter")
    # Snapshot installed sources before setup imports the authenticated numeric types.
    # setup_driver checks that --eels names this interpreter's required .venv.
    auth = InstalledSources(Path(sys.prefix).resolve().parent)
    context = setup_driver(__doc__, __file__, 39012)
    sys.meta_path.insert(0, InstalledFinder(auth))
    pin = tomllib.loads((context.root / "reference.toml").read_text())["release"]
    for name, version in pin["python_dependencies"].items():
        if importlib.metadata.version(name) != version:
            raise ImportError(f"dependency version differs: {name}")
    from ethereum.forks.amsterdam import witness_state as source
    from ethereum.crypto import hash as hash_source
    from ethereum_types.bytes import Bytes, Bytes32
    context.check_source(source, "ethereum/forks/amsterdam/witness_state.py")
    context.check_source(hash_source, "ethereum/crypto/hash.py")
    original, build = source.keccak256, source.build_node_db
    before = {"keccak": callable_record(original), "build": callable_record(build)}
    guards = ["import STFSpec.Commit", "open STFSpec.Base STFSpec.Hash STFSpec.Commit"]
    observations = []
    rng = random.Random(context.seed)
    cases = [[], [b""], [b"\xff"], [b"\x80\x00"], [b"", b""],
             [b"\xc0", b"\x80", b"\xff", b"\xc0"],
             [bytes(range(32)), bytes(reversed(range(32)))],
             [bytes(rng.randrange(256) for _ in range(n))
              for n in [1, 31, 32, 33, 135, 136, 137, 300]]]
    cases += [[bytes(rng.randrange(256) for _ in range(rng.randrange(48)))
               for _ in range(rng.randrange(1, 12))] for _ in range(20)]
    for index, values in enumerate(cases):
        entries = tuple(Bytes(b) for b in values)
        db = build(entries)
        raw = {"case": index, "input_class": typename(entries),
               "entry_classes": [typename(b) for b in entries],
               "entries": [bytes(b).hex() for b in entries],
               "result_class": typename(db),
               "items": [{"key_class": typename(k), "value_class": typename(v),
                           "key": bytes(k).hex(), "value": bytes(v).hex()} for k, v in db.items()]}
        observations.append(raw)
        expected = {}
        for b in entries:
            h = original(b)
            if len(h) != 32:
                raise AssertionError("digest width")
            expected[h] = b
        if db != expected:
            raise AssertionError("actual pinned table differs")
        name = f"case{index}"
        guards += [f"def {name} : NodeDB := NodeDB.build (m := Id) #[" +
                   ", ".join(array(v) for v in values) + "]",
                   f"#guard {name}.map.size == {len(db)}"]
        for k, v in db.items():
            guards.append(f"#guard match Hash32.ofBytes? (Bytes.ofByteArray {array(k)}) with\n"
                          f"  | some h => {name}.map[h]? == some {array(v)}\n  | none => false")
        miss = Bytes32(bytes(32))
        guards.append(f"#guard match Hash32.ofBytes? (Bytes.ofByteArray {array(miss)}) with\n"
                      f"  | some h => {name}.map[h]? == " +
                      ("none" if miss not in db else "some " + array(db[miss])) +
                      "\n  | none => false")
    controls = []
    values = (Bytes(b""), Bytes(b"\xff"), Bytes(b""), Bytes(b"\x80\x00"))
    for collide, fail_at in [(False, None), (True, None)] + [(False, i) for i in range(4)]:
        seen, answers = [], []

        def instrumented(entry):
            n = len(seen)
            seen.append({"class": typename(entry), "value": bytes(entry).hex()})
            if fail_at == n:
                raise RuntimeError(f"query-{n}")
            answer = (1 << 255) + 7 if collide else (1 << (64 * n)) + 7
            result = Bytes32(answer.to_bytes(32, "big"))
            answers.append({"class": typename(result), "value": bytes(result).hex()})
            return result

        patched = callable_record(instrumented)
        source.keccak256 = instrumented
        result, error = None, None
        try:
            result = build(values)
        except RuntimeError as exc:
            error = {"class": typename(exc), "message": str(exc)}
        finally:
            source.keccak256 = original
        if source.keccak256 is not original or source.build_node_db is not build:
            raise AssertionError("instrumentation did not restore source callable")
        if len(seen) != (len(values) if fail_at is None else fail_at + 1):
            raise AssertionError("query order/failure prefix differs")
        if [item["value"] for item in seen] != [bytes(v).hex() for v in values[:len(seen)]]:
            raise AssertionError("raw query bytes/order differs")
        if fail_at is None:
            expected = {Bytes32(bytes.fromhex(a["value"])): values[i]
                        for i, a in enumerate(answers)}
            if result != expected:
                raise AssertionError("arbitrary-answer last-write differs")
        elif error != {"class": "builtins.RuntimeError", "message": f"query-{fail_at}"}:
            raise AssertionError("failure differs")
        controls.append({"collision": collide, "fail_at": fail_at, "patched": patched,
                         "restored": callable_record(source.keccak256), "seen": seen,
                         "answers": answers, "error": error,
                         "result_class": None if result is None else typename(result),
                         "items": None if result is None else [
                             {"key_class": typename(k), "value_class": typename(v),
                              "key": bytes(k).hex(), "value": bytes(v).hex()}
                             for k, v in result.items()]})
    # Empty source input makes no query even if the control would throw on its first call.
    def forbidden(entry):
        raise AssertionError("empty input queried")
    source.keccak256 = forbidden
    try:
        if build(()) != {}:
            raise AssertionError("empty input table")
    finally:
        source.keccak256 = original
    after = {"keccak": callable_record(source.keccak256),
             "build": callable_record(source.build_node_db)}
    if before != after:
        raise AssertionError("source callable identity changed")
    context.check_clean()
    context.check_dependency()
    auth.check()
    report = {"before": before, "after": after, "concrete": observations,
              "controls": controls, "empty_control": "no query", "installed": auth.metadata(),
              "oracle_sources": context.oracle_blobs,
              "backend": "hashlib" if hash_source._USE_HASHLIB else "pycryptodome",
              "limits": ("instrumentation controls are arbitrary-answer controls, "
                         "not concrete hash collisions")}
    context.output.with_suffix(".observations.json").write_text(
        json.dumps(report, indent=2) + "\n")
    result = context.run(guards, concrete_cases=len(cases), controlled_cases=len(controls) + 1,
                         limitations=__doc__)
    auth.check()
    return result


if __name__ == "__main__":
    raise SystemExit(main())
