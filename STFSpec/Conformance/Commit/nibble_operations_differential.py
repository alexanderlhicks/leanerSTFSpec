#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Bounded nibble sequence support checks against authenticated pinned Python.

From the repository root, run:
  EELS/.venv/bin/python -I -B STFSpec/Conformance/Commit/nibble_operations_differential.py \
    --eels EELS --output EXTERNAL.lean

Choose EXTERNAL.lean outside both repositories. Actual locked ethereum-types Bytes
and the expressions at mpt:538/543/547/556 supply slice semantics; Python bytes
supply lexicographic
ordering and bounded callback sequences. These are support helpers, not new EELS
functions or a patricialize/root/decoder implementation. The shared Driver checks
all pinned source/lock blobs and all installed ethereum-types Python RECORD rows,
then installs fresh source loaders. Exact classes are checked before normalization.
No manual Python/Lean limits, benchmark, host-resource or guest claim is made.
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
from differential import setup_driver, FreshSourceLoader


def exact(value, cls):
    if type(value) is not cls:
        raise TypeError(f"expected exact {cls.__name__}, got {type(value).__name__}")


def path_input(value):
    exact(value, bytes)
    if any(digit >= 16 for digit in value):
        raise ValueError("every nibble digit must be below 16")


def offset(value):
    exact(value, int)
    if value < 0:
        raise ValueError("natural offsets only")


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
    context = setup_driver(__doc__, __file__, 33033)
    before = identity(context)
    recursion_before = sys.getrecursionlimit()
    from ethereum_types.bytes import Bytes
    from ethereum_types.numeric import Uint
    from ethereum import merkle_patricia_trie as mpt
    import ethereum_types.bytes as dependency_bytes
    if Bytes is not bytes:
        raise TypeError("locked Bytes alias differs")
    origins = {"mpt": str(context.check_source(mpt, "ethereum/merkle_patricia_trie.py")),
               "bytes": str(context.check_source(
                   dependency_bytes, "ethereum_types/bytes.py", dependency=True))}
    guards = ["import STFSpec.Conformance.Commit.NibblesOperationsGuards",
              "import STFSpec.Conformance.Fixtures.Hex",
              "open STFSpec.Commit STFSpec.Conformance.Commit.NibblesOperationsGuards",
              'private def raw (text : String) : ByteArray := '
              '(STFSpec.Conformance.Internal.decodeHex "differential" text).toOption'
              '.getD ByteArray.empty',
              'private def pathHex (text : String) : Nibbles := '
              'Nibbles.ofList ((raw text).data.toList.map (fun b ↦ ⟨b.toNat % 16, by omega⟩))']
    observations = []
    counts = {"extract": 0, "take": 0, "drop": 0, "generate": 0, "compare": 0,
              "exact_class_negative": 0, "domain_negative": 0, "authentication_negative": 0}

    def slice_observation(operation, value, start, stop):
        path_input(value)
        offset(start)
        offset(stop)
        # Execute the typed-index expressions used by the pinned trie consumers.
        level = Uint(start)
        exact(level, Uint)
        if operation == "drop":
            result = value[level:]
            expr = f'(pathHex "0x{value.hex()}").drop {start}'
        elif operation == "take":
            result = value[:Uint(stop)]
            expr = f'(pathHex "0x{value.hex()}").take {stop}'
        else:
            result = value[int(level):int(Uint(stop))]
            expr = f'(pathHex "0x{value.hex()}").extract {start} {stop}'
        exact(result, Bytes)
        observations.append({"operation": operation, "input": value.hex(),
                             "start": start, "stop": stop, "output": result.hex()})
        guards.append(f'#guard digits ({expr}) == (raw "0x{result.hex()}")'
                      '.data.toList.map UInt8.toNat')
        guards.append(f'#guard ({expr}).size == {len(result)}')
        counts[operation] += 1

    def compare_observation(a, b):
        path_input(a)
        path_input(b)
        equal, smaller, larger = a == b, a < b, a > b
        for answer in (equal, smaller, larger):
            exact(answer, bool)
        if sum((equal, smaller, larger)) != 1:
            raise AssertionError("bytes order is not trichotomous")
        answer = "eq" if equal else "lt" if smaller else "gt"
        observations.append({"operation": "compare", "left": a.hex(), "right": b.hex(),
                             "output": answer, "equal": equal})
        guards.append(f'#guard compare (pathHex "0x{a.hex()}") '
                      f'(pathHex "0x{b.hex()}") == .{answer}')
        guards.append(f'#guard decide (pathHex "0x{a.hex()}" = pathHex "0x{b.hex()}") '
                      f'== {str(equal).lower()}')
        counts["compare"] += 1

    callback_specs = {"zero": (lambda i: 0, "fun _ ↦ 0"),
                      "fifteen": (lambda i: 15, "fun _ ↦ 15"),
                      "affine": (lambda i: (3*i+7)%16, "affine"),
                      "mixed": (lambda i: (i//7+5*i+i%3)%16, "mixed")}
    for name, (callback, lean_callback) in callback_specs.items():
        for n in (0, 1, 2, 15, 16, 64, 4096, 4097):
            visited = []
            def checked(i):
                offset(i)
                if i >= n:
                    raise AssertionError("callback out of range")
                visited.append(i)
                answer = callback(i)
                exact(answer, int)
                if not 0 <= answer < 16:
                    raise ValueError("callback out of nibble range")
                return answer
            result = Bytes(checked(i) for i in range(n))
            exact(result, Bytes)
            if visited != list(range(n)):
                raise AssertionError("support callback order differs")
            observations.append({"operation": "generate", "callback": name, "length": n,
                                 "visited": visited, "output": result.hex()})
            expr = f'Nibbles.generate {n} ({lean_callback})'
            guards.append(f'#guard digits ({expr}) == (raw "0x{result.hex()}")'
                          '.data.toList.map UInt8.toNat')
            guards.append(f'#guard ({expr}).size == {n}')
            counts["generate"] += 1

    for value in (b"", b"\x00", b"\x0f", bytes(range(16)), b"\x00\x0f\x00\x01\x0f"):
        offsets = list(range(len(value) + 3)) + [2**128, 2**1024]
        for start in offsets:
            slice_observation("drop", value, start, len(value))
            slice_observation("take", value, 0, start)
            for stop in offsets:
                slice_observation("extract", value, start, stop)
    for a in range(16):
        for b in range(16):
            compare_observation(Bytes([a]), Bytes([b]))
    long = Bytes((i//7+5*i+i%3)%16 for i in range(4096))
    paths = [b"", b"\x00", b"\x01", b"\x01\x00", b"\x00\x01", b"\x0f", b"\x00\x0f",
             b"\x01\x02\x03", b"\x01\x02\x04\x00", b"\x01\x03", long,
             long+b"\x01", long[:-1]+b"\x0f", b"\x0f"+long[1:]]
    for a in paths:
        for b in paths:
            compare_observation(a, b)
    for value in (long, long+b"\x01", b"\x00"*4096, b"\x0f"*4097):
        for start, stop in ((0, 64), (1, 4096), (4095, 2**1024), (4096, 4097),
                            (4097, 4096), (2**1024, 2**1024+1), (0, 2**1024)):
            slice_observation("extract", value, start, stop)
    rng = random.Random(context.seed)
    for _ in range(64):
        a = Bytes(rng.randrange(16) for _ in range(rng.randrange(129)))
        b = Bytes(rng.randrange(16) for _ in range(rng.randrange(129)))
        compare_observation(a, b)
        slice_observation("extract", a, rng.randrange(150), rng.randrange(150))

    class ByteSubclass(bytes):
        pass
    for value, cls in [(ByteSubclass(), bytes), (bytearray(), bytes), (True, int),
                       (1.0, int), (1, bool), (0, bool)]:
        try:
            exact(value, cls)
        except TypeError:
            counts["exact_class_negative"] += 1
        else:
            raise AssertionError("exact-class negative accepted")
    for value in (b"\x10", b"\xff", b"\x00\x10"):
        try:
            path_input(value)
        except ValueError:
            counts["domain_negative"] += 1
        else:
            raise AssertionError("invalid nibble negative accepted")
    try:
        offset(-1)
    except ValueError:
        counts["domain_negative"] += 1
    else:
        raise AssertionError("negative offset accepted")
    dep = Path(origins["bytes"])
    if context.dependency_bytes_match(dep, dep.read_bytes()+b"\n"):
        raise AssertionError("changed dependency bytes accepted")
    counts["authentication_negative"] += 1
    saved = context.oracle_blobs
    context.oracle_blobs = {**saved, "src/ethereum/merkle_patricia_trie.py": "0"*40}
    try:
        FreshSourceLoader("ethereum.merkle_patricia_trie", origins["mpt"], context).get_code(
            "ethereum.merkle_patricia_trie")
    except ImportError:
        counts["authentication_negative"] += 1
    else:
        raise AssertionError("changed oracle bytes accepted")
    finally:
        context.oracle_blobs = saved
    context.output.write_text(
        "-- Generated support differential evidence; do not commit.\n"+"\n".join(guards)+"\n")
    command = ["lake", "env", "lean", "-DwarningAsError=true", str(context.output)]
    result = subprocess.run(command, cwd=context.root)
    context.check_clean()
    context.check_dependency()
    after = identity(context)
    if before != after:
        raise RuntimeError("oracle/dependency/source identities changed")
    report = {"scope":
                  "typed-Bytes slice and Python sequence support semantics; no new EELS function",
              "source_commit": context.head, "ethereum_types": context.version,
              "argv": sys.argv, "cwd": str(Path.cwd()), "executable": sys.executable,
              "resolved_executable_for_identity_only": str(Path(sys.executable).resolve()),
              "prefix": sys.prefix, "isolated": sys.flags.isolated,
              "dont_write_bytecode": sys.flags.dont_write_bytecode,
              "recursion_before": recursion_before, "recursion_after": sys.getrecursionlimit(),
              "manual_limit_changes": False, "origins": origins,
              "loader_classes": {"mpt": str(type(mpt.__loader__)),
                                 "bytes": str(type(dependency_bytes.__loader__))},
              "before": before, "after": after, "source_identity_preserved": before == after,
              "seed": context.seed, "counts": counts, "observation_count": len(observations),
              "emitted_guards": sum(line.startswith("#guard ") for line in guards),
              "lean_command": command, "lean_exit": result.returncode,
              "observations": observations}
    context.output.with_suffix(".json").write_text(
        json.dumps(report, indent=2, sort_keys=True)+"\n")
    summary_keys = ("source_commit", "source_identity_preserved", "counts",
                    "observation_count", "emitted_guards", "lean_exit")
    print(json.dumps({key: report[key] for key in summary_keys}, sort_keys=True))
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
