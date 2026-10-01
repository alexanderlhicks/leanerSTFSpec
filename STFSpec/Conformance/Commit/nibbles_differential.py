#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Pure path observations against actual authenticated pinned EELS expressions.

From the repository root, run:
  EELS/.venv/bin/python -I -B STFSpec/Conformance/Commit/nibbles_differential.py \
    --eels EELS --output EXTERNAL.lean

Choose EXTERNAL.lean outside both repositories. The shared Driver
authenticates current source/lock bytes and locked
ethereum-types RECORD and installs fresh source loaders. Inputs/results have exact
classes checked before normalization. Only bounded valid nibble paths are encoded.
No compact decoder, node, root, guest, throughput or host-resource claim is made.
The frozen interpreter, installation/startup and installed RECORD remain trusted.
"""
from pathlib import Path
import hashlib
import json
import random
import subprocess
import sys

# Require actual isolated startup and bytecode suppression before reference setup.
if not sys.flags.isolated or not sys.flags.dont_write_bytecode:
    print("run with the frozen EELS .venv interpreter -I -B", file=sys.stderr)
    raise SystemExit(2)
sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "scripts"))
from differential import Driver, FreshSourceLoader


def exact(value, cls):
    if type(value) is not cls:
        raise TypeError(f"expected exact {cls.__name__}, got {type(value).__name__}")


def path_input(value):
    exact(value, bytes)
    if any(digit >= 16 for digit in value):
        raise ValueError("nibble paths require every digit below 16")


def identity(context):
    paths = [context.eels / "uv.lock", context.dependency_record,
             context.root / "reference.toml", Path(__file__),
             context.root / "scripts/differential.py"]
    return {"head": context.git("rev-parse", "HEAD", text=True).strip(),
            "status": context.git("status", "--porcelain", "--untracked-files=all", text=True),
            "source_lock_blobs": context.oracle_blobs,
            "sha256": {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
            "dependency_sources": context.dependency_sources()}


def main():
    context = Driver(__doc__, __file__, 3030)
    before = identity(context)
    recursion_before = sys.getrecursionlimit()
    from ethereum_types.bytes import Bytes
    from ethereum import merkle_patricia_trie as mpt
    import ethereum_types.bytes as dependency_bytes
    if Bytes is not bytes:
        raise TypeError("locked ethereum-types Bytes alias differs")
    origins = {"mpt": str(context.check_source(mpt, "ethereum/merkle_patricia_trie.py")),
               "bytes": str(context.check_source(dependency_bytes, "ethereum_types/bytes.py", dependency=True))}
    guards = ["import STFSpec.Conformance.Commit.NibblesGuards",
              "import STFSpec.Conformance.Fixtures.Hex",
              "open STFSpec.Commit STFSpec.Conformance.Commit.NibblesGuards",
              "private def raw (text : String) : ByteArray := "
              "(STFSpec.Conformance.Internal.decodeHex \"differential\" text).toOption.getD ByteArray.empty",
              "private def pathHex (text : String) : Nibbles := "
              "Nibbles.ofList ((raw text).data.toList.map (fun b ↦ ⟨b.toNat % 16, by omega⟩))"]
    observations = []
    counts = {"split": 0, "compact": 0, "prefix": 0,
              "exact_class_negative": 0, "domain_negative": 0, "authentication_negative": 0}

    def observe_split(value):
        exact(value, Bytes)
        result = mpt.bytes_to_nibble_list(value)
        exact(result, Bytes)
        observations.append({"operation": "split", "input": value.hex(), "output": result.hex()})
        guards.append(f'#guard digits (bytesToNibbleList (raw "0x{value.hex()}")) == bytes (raw "0x{result.hex()}")')
        counts["split"] += 1

    def observe_compact(value, leaf):
        path_input(value)
        exact(leaf, bool)
        result = mpt.nibble_list_to_compact(value, leaf)
        exact(result, Bytes)
        observations.append({"operation": "compact", "input": value.hex(), "leaf": leaf, "output": result.hex()})
        guards.append(f'#guard decide (nibbleListToCompact (pathHex "0x{value.hex()}") '
                      f'{str(leaf).lower()} = raw "0x{result.hex()}")')
        counts["compact"] += 1

    def observe_prefix(a, b):
        path_input(a)
        path_input(b)
        result = mpt.common_prefix_length(a, b)
        exact(result, int)
        if result < 0:
            raise ValueError("negative source prefix length")
        observations.append({"operation": "prefix", "left": a.hex(), "right": b.hex(), "output": result})
        guards.append(f'#guard commonPrefixLength (pathHex "0x{a.hex()}") (pathHex "0x{b.hex()}") == {result}')
        counts["prefix"] += 1

    for value in range(256):
        observe_split(bytes([value]))
    for high in range(16):
        for leaf in (False, True):
            observe_compact(bytes([high]), leaf)
            for low in range(16):
                observe_compact(bytes([high, low]), leaf)
    long_paths = [b"", b"\x00", b"\x0f", bytes(range(16)), bytes(range(15)),
                  b"\x00" * 4096, b"\x0f" * 4097, bytes(range(16)) * 257]
    for value in long_paths:
        for leaf in (False, True):
            observe_compact(value, leaf)
    for value in (b"", b"\x12\x21\x00\xff", b"\x00" * 4096,
                  b"\xff" * 4097, bytes(range(256)) * 17):
        observe_split(value)
    prefix_paths = [b"", b"\x00", b"\x01", b"\x01\x02", b"\x01\x02\x03",
                    b"\x01\x03", b"\x02\x01", b"\x00" * 4096,
                    b"\x00" * 4096 + b"\x01", b"\x00" * 4095 + b"\x02"]
    for a in prefix_paths:
        for b in prefix_paths:
            observe_prefix(a, b)
    rng = random.Random(context.seed)
    for _ in range(128):
        observe_split(bytes(rng.randrange(256) for _ in range(rng.randrange(129))))
        a = bytes(rng.randrange(16) for _ in range(rng.randrange(129)))
        observe_compact(a, bool(rng.randrange(2)))
        i = rng.randrange(len(a) + 1)
        b = a[:i] + bytes(rng.randrange(16) for _ in range(rng.randrange(129)))
        observe_prefix(a, b)
        observe_prefix(b, a)

    class ByteSubclass(bytes):
        pass

    for value, cls in [(ByteSubclass(), bytes), (bytearray(), bytes), (1, bool),
                       (0, bool), (True, int), (1.0, int), ([b"", False], tuple)]:
        try:
            exact(value, cls)
        except TypeError:
            counts["exact_class_negative"] += 1
        else:
            raise AssertionError("exact-class negative control accepted")
    for value in (b"\x10", b"\xff", b"\x00\x10"):
        try:
            path_input(value)
        except ValueError:
            counts["domain_negative"] += 1
        else:
            raise AssertionError("out-of-domain path accepted")
    dep = Path(origins["bytes"])
    if context.dependency_bytes_match(dep, dep.read_bytes() + b"\n"):
        raise AssertionError("synthetic changed dependency bytes accepted")
    counts["authentication_negative"] += 1
    saved_blobs = context.oracle_blobs
    context.oracle_blobs = {**saved_blobs, "src/ethereum/merkle_patricia_trie.py": "0" * 40}
    try:
        FreshSourceLoader("ethereum.merkle_patricia_trie", origins["mpt"], context).get_code("ethereum.merkle_patricia_trie")
    except ImportError:
        counts["authentication_negative"] += 1
    else:
        raise AssertionError("synthetic wrong oracle blob accepted")
    finally:
        context.oracle_blobs = saved_blobs
    context.output.write_text("-- Generated differential evidence; do not commit.\n" + "\n".join(guards) + "\n")
    command = ["lake", "env", "lean", "-DwarningAsError=true", str(context.output)]
    result = subprocess.run(command, cwd=context.root)
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
              "manual_limit_changes": False, "origins": origins,
              "loader_classes": {"mpt": str(type(mpt.__loader__)), "bytes": str(type(dependency_bytes.__loader__))},
              "before": before, "after": after, "source_identity_preserved": before == after,
              "seed": context.seed, "counts": counts, "source_calls": len(observations),
              "emitted_guards": sum(line.startswith("#guard ") for line in guards),
              "lean_command": command, "lean_exit": result.returncode, "observations": observations}
    context.output.with_suffix(".json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: report[key] for key in ["source_commit", "source_identity_preserved", "counts",
                                                 "source_calls", "emitted_guards", "lean_exit"]}, sort_keys=True))
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
