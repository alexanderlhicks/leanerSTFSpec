#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Compact decoder observations against actual authenticated pinned EELS.

From the repository root, run:
  EELS/.venv/bin/python -I -B STFSpec/Conformance/Commit/compact_differential.py \
    --eels EELS --output EXTERNAL.lean

Choose EXTERNAL.lean outside both repositories. Shared Driver/Fresh loaders
authenticate current pinned source/lock bytes and locked ethereum-types RECORD.
Exact input, pair, path, flag and empty exception classes/args are checked
before normalization. The frozen installation/startup/RECORD and interpreter
remain trusted inputs.
Only pure compact paths are covered; no node, root, guest or throughput claim.
"""
from pathlib import Path
import hashlib
import json
import random
import subprocess
import sys

if not sys.flags.isolated or not sys.flags.dont_write_bytecode:
    print("run with the frozen EELS .venv interpreter -I -B", file=sys.stderr)
    raise SystemExit(2)
sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "scripts"))
from differential import Driver, FreshSourceLoader


def exact(value, cls):
    if type(value) is not cls:
        raise TypeError(f"expected exact {cls.__module__}.{cls.__qualname__}, got {type(value)}")


def path_input(value):
    exact(value, bytes)
    if any(digit >= 16 for digit in value):
        raise ValueError("nibble paths require every digit below 16")


def pair_result(value):
    exact(value, tuple)
    if len(value) != 2:
        raise ValueError("compact decoder must return exactly two fields")
    path_input(value[0])
    exact(value[1], bool)


def empty_exception(error):
    exact(error, IndexError)
    exact(error.args, tuple)
    if len(error.args) != 1:
        raise ValueError("empty compact IndexError argument arity differs")
    exact(error.args[0], str)
    if error.args != ("index out of range",):
        raise ValueError("empty compact IndexError arguments differ")


def identity(context):
    paths = [context.eels / "uv.lock", context.dependency_record,
             context.root / "reference.toml", Path(__file__),
             context.root / "scripts/differential.py"]
    return {"head": context.git("rev-parse", "HEAD", text=True).strip(),
            "status": context.git("status", "--porcelain", "--untracked-files=all", text=True),
            "source_lock_blobs": context.oracle_blobs,
            "sha256": {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
            "dependency_sources": context.dependency_sources()}


def collect(context):
    """Collect real source results and emit expressions; do not run Lean or write files."""
    before = identity(context)
    recursion_before = sys.getrecursionlimit()
    from ethereum_types.bytes import Bytes
    from ethereum import merkle_patricia_trie as mpt
    from ethereum.forks.amsterdam import incremental_mpt as inc
    import ethereum_types.bytes as dependency_bytes
    if Bytes is not bytes:
        raise TypeError("locked ethereum-types Bytes alias differs")
    origins = {"mpt": str(context.check_source(mpt, "ethereum/merkle_patricia_trie.py")),
               "inc": str(context.check_source(
                   inc, "ethereum/forks/amsterdam/incremental_mpt.py")),
               "bytes": str(context.check_source(
                   dependency_bytes, "ethereum_types/bytes.py", dependency=True))}
    modules = {"mpt": mpt, "inc": inc, "bytes": dependency_bytes}
    for name, module in modules.items():
        if type(module.__loader__) is not FreshSourceLoader:
            raise TypeError(f"{name} was not freshly authenticated from source")
    guards = ["import STFSpec.Conformance.Commit.CompactGuards",
              "import STFSpec.Conformance.Fixtures.Hex",
              "open STFSpec.Commit STFSpec.Conformance.Commit.NibblesGuards "
              "STFSpec.Conformance.Commit.CompactGuards",
              "local instance {α : Type} [BEq α] : BEq (Except TrieError α) where\n"
              "  beq\n"
              "    | .error a, .error b => a == b\n"
              "    | .ok a, .ok b => a == b\n"
              "    | _, _ => false",
              "private def raw (text : String) : ByteArray := "
              "(STFSpec.Conformance.Internal.decodeHex \"differential\" text).toOption"
              ".getD ByteArray.empty",
              "private def pathHex (text : String) : Nibbles := "
              "Nibbles.ofList ((raw text).data.toList.map (fun b ↦ ⟨b.toNat % 16, by omega⟩))"]
    observations = []
    counts = {"leading_alone": 0, "leading_suffix": 0, "named": 0,
              "long_wire": 0, "canonical_singleton": 0, "canonical_pair": 0,
              "canonical_empty": 0, "canonical_long": 0, "seeded_wire": 0,
              "seeded_canonical": 0, "empty_failure": 0,
              "exact_class_negative": 0, "shape_negative": 0,
              "domain_negative": 0, "exception_negative": 0,
              "authentication_negative": 0}
    calls = {"compact_to_nibbles": 0, "nibble_list_to_compact": 0}
    controls = []

    def canonical_model(path, leaf):
        odd = len(path) % 2
        return bytes([16 * (2 * int(leaf) + odd) + (path[0] if odd else 0)] +
                     [16 * path[i] + path[i + 1] for i in range(odd, len(path), 2)])

    def decode(wire):
        exact(wire, Bytes)
        calls["compact_to_nibbles"] += 1
        result = inc.compact_to_nibbles(wire)
        pair_result(result)
        expected = ((bytes([wire[0] % 16]) if wire[0] & 16 else b"") +
                    bytes(n for byte in wire[1:] for n in (byte // 16, byte % 16)),
                    bool(wire[0] & 32))
        if result != expected:
            raise AssertionError(
                "actual compact decoder disagrees with ordered digit/flag equation")
        return result

    def encode(path, leaf):
        path_input(path)
        exact(leaf, bool)
        calls["nibble_list_to_compact"] += 1
        result = mpt.nibble_list_to_compact(path, leaf)
        exact(result, Bytes)
        if result != canonical_model(path, leaf):
            raise AssertionError("actual canonical encoder disagrees with bounded model")
        return result

    def note(group, wire, result, reencoded, **extra):
        path, leaf = result
        counts[group] += 1
        observations.append({"group": group, "input": wire.hex(), "path": path.hex(),
                             "leaf": leaf, "reencoded": reencoded.hex(),
                             "input_class": str(type(wire)), "pair_class": str(type(result)),
                             "path_class": str(type(path)), "flag_class": str(type(leaf)),
                             **extra})
        guards.append(f'#guard decodeView (raw "0x{wire.hex()}") == '
                      f'.ok (bytes (raw "0x{path.hex()}"), {str(leaf).lower()})')
        return path, leaf

    def wire_case(wire, group):
        result = decode(wire)
        reencoded = encode(*result)
        normalized = bytes([wire[0] & (0x3f if wire[0] & 16 else 0x20)]) + wire[1:]
        if reencoded != normalized:
            raise AssertionError("accepted wire normalization differs")
        note(group, wire, result, reencoded)
        guards.append(f'#guard reencodeView (raw "0x{wire.hex()}") == '
                      f'.ok (bytes (raw "0x{reencoded.hex()}"))')

    def canonical_case(path, leaf, group):
        encoded = encode(path, leaf)
        result = decode(encoded)
        if result != (path, leaf):
            raise AssertionError("canonical path/flag roundtrip differs")
        note(group, encoded, result, encoded, canonical_path=path.hex())
        guards.append(f'#guard bytes (nibbleListToCompact (pathHex "0x{path.hex()}") '
                      f'{str(leaf).lower()}) == bytes (raw "0x{encoded.hex()}")')
        guards.append(f'#guard roundtrip (pathHex "0x{path.hex()}") {str(leaf).lower()}')

    for first in range(256):
        wire_case(bytes([first]), "leading_alone")
        wire_case(bytes([first, 0x12, 0x34, 0x00, 0xff]), "leading_suffix")
    for wire in (b"\x00", b"\x0f", b"\x20", b"\x2f", b"\xf1\x23"):
        wire_case(wire, "named")
    for suffix in (b"\x00" * 4096, b"\xff" * 4097, bytes(range(256)) * 16):
        for first in (0x00, 0x10, 0x20, 0x30, 0xf1):
            wire_case(bytes([first]) + suffix, "long_wire")
    for digit in range(16):
        for leaf in (False, True):
            canonical_case(bytes([digit]), leaf, "canonical_singleton")
            for other in range(16):
                canonical_case(bytes([digit, other]), leaf, "canonical_pair")
    for leaf in (False, True):
        canonical_case(b"", leaf, "canonical_empty")
    for path in (b"\x00" * 4096, b"\x00" * 4097,
                 b"\x0f" * 4096, b"\x0f" * 4097,
                 bytes(range(16)) * 256, bytes(range(16)) * 256 + b"\x07"):
        for leaf in (False, True):
            canonical_case(path, leaf, "canonical_long")
    rng = random.Random(context.seed)
    for _ in range(128):
        wire_case(bytes(rng.randrange(256) for _ in range(rng.randrange(1, 130))), "seeded_wire")
        canonical_case(bytes(rng.randrange(16) for _ in range(rng.randrange(129))),
                       bool(rng.randrange(2)), "seeded_canonical")
    calls["compact_to_nibbles"] += 1
    try:
        inc.compact_to_nibbles(b"")
    except Exception as error:
        empty_exception(error)
        observations.append({"group": "empty_failure", "input": "",
                             "exception_class": "builtins.IndexError", "args": list(error.args),
                             "lean_error": "TrieError.malformed Malformed.compactEmpty"})
        counts["empty_failure"] += 1
        guards.append('#guard decodeView ByteArray.empty == .error (.malformed .compactEmpty)')
    else:
        raise AssertionError("empty compact input succeeded")

    def rejected(label, action, expected, count):
        try:
            action()
        except expected as error:
            counts[count] += 1
            controls.append({"label": label, "exception_class": str(type(error)),
                             "message": str(error)})
        else:
            raise AssertionError(f"negative control accepted: {label}")

    class ByteSubclass(bytes):
        pass

    class IndexSubclass(IndexError):
        pass

    for value, cls in [(ByteSubclass(), bytes), (bytearray(), bytes), (1, bool),
                       (True, int), ([b"", False], tuple), (IndexSubclass(), IndexError)]:
        rejected("exact " + repr((value, cls)), lambda value=value, cls=cls: exact(value, cls),
                 TypeError, "exact_class_negative")
    for value in ([b"", False], (bytearray(), False), (b"", 0)):
        rejected("decoder pair classes " + repr(value), lambda value=value: pair_result(value),
                 TypeError, "exact_class_negative")
    for value in ((), (b"",), (b"", False, None)):
        rejected("decoder pair arity " + repr(value), lambda value=value: pair_result(value),
                 ValueError, "shape_negative")
    for value in (b"\x10", b"\xff", b"\x00\x10"):
        rejected("path bound " + value.hex(), lambda value=value: path_input(value),
                 ValueError, "domain_negative")
    for error in (IndexSubclass("index out of range"), ValueError("index out of range"),
                  IndexError("different"), IndexError(), IndexError(1)):
        rejected("empty exception " + repr(error), lambda error=error: empty_exception(error),
                 (TypeError, ValueError), "exception_negative")
    dep = Path(origins["bytes"])
    if context.dependency_bytes_match(dep, dep.read_bytes() + b"\n"):
        raise AssertionError("changed dependency bytes accepted")
    counts["authentication_negative"] += 1
    controls.append({"label": "changed dependency bytes", "rejected": True})
    saved_hashes = context.dependency_hashes
    context.dependency_hashes = {**saved_hashes, dep: ("A" * 43, dep.stat().st_size)}
    try:
        rejected("wrong dependency RECORD hash", lambda: FreshSourceLoader(
            "ethereum_types.bytes", str(dep), context).get_code("ethereum_types.bytes"),
            ImportError, "authentication_negative")
    finally:
        context.dependency_hashes = saved_hashes
    saved_blobs = context.oracle_blobs
    try:
        for name, relative in (("inc", "src/ethereum/forks/amsterdam/incremental_mpt.py"),
                               ("mpt", "src/ethereum/merkle_patricia_trie.py")):
            context.oracle_blobs = {**saved_blobs, relative: "0" * 40}
            fullname = modules[name].__name__
            rejected("wrong pinned " + name + " blob", lambda name=name, fullname=fullname:
                     FreshSourceLoader(fullname, origins[name], context).get_code(fullname),
                     ImportError, "authentication_negative")
    finally:
        context.oracle_blobs = saved_blobs
    context.check_clean()
    context.check_dependency()
    after = identity(context)
    if before != after:
        raise RuntimeError("source/lock/dependency identity changed")
    report = {"source_commit": context.head, "ethereum_types": context.version,
              "argv": sys.argv, "cwd": str(Path.cwd()), "executable": sys.executable,
              "resolved_executable_for_identity_only": str(Path(sys.executable).resolve()),
              "prefix": sys.prefix, "isolated": sys.flags.isolated,
              "dont_write_bytecode": sys.flags.dont_write_bytecode,
              "recursion_before": recursion_before, "recursion_after": sys.getrecursionlimit(),
              "manual_limit_changes": False,
              "source_package_limit_policy":
                  "pinned ethereum/__init__.py:30 adjusts recursion limit on import",
              "origins": origins,
              "loader_classes": {name: str(type(module.__loader__))
                                 for name, module in modules.items()},
              "before": before, "after": after, "source_identity_preserved": before == after,
              "seed": context.seed, "counts": counts, "source_calls": calls,
              "source_call_count": sum(calls.values()), "observation_count": len(observations),
              "emitted_guards": sum(line.startswith("#guard ") for line in guards),
              "negative_controls": controls, "observations": observations}
    return guards, report


def main():
    context = Driver(__doc__, __file__, 3031)
    guards, report = collect(context)
    context.output.write_text(
        "-- Generated differential evidence; do not commit.\n" + "\n".join(guards) + "\n")
    command = ["lake", "env", "lean", "-DwarningAsError=true", str(context.output)]
    result = subprocess.run(command, cwd=context.root)
    context.check_clean()
    context.check_dependency()
    if identity(context) != report["before"]:
        raise RuntimeError("source identity changed during Lean check")
    report.update(lean_command=command, lean_exit=result.returncode)
    context.output.with_suffix(".json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n")
    summary_keys = ("source_commit", "source_identity_preserved", "counts", "source_calls",
                    "observation_count", "emitted_guards", "lean_exit")
    print(json.dumps({key: report[key] for key in summary_keys}, sort_keys=True))
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
