#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Compare exact byte construction and lexical ordering with the pinned dependency.

Run with PYTHONDONTWRITEBYTECODE=1 using EELS/.venv/bin/python and:
  --eels <checkout> --output <outside-worktree>/fixed-bytes-differential.lean

The unchanged locked ethereum-types 0.4.1 FixedBytes constructor at bytes.py:29
and Python bytes comparison are the oracle. Address/Hash32/Root/VersionedHash/
Bloom/Hash64 are loaded from actual pinned EELS declarations. Numeric observations
are checked against the explicit big-endian int.from_bytes model, not a new EELS
integer API. Generated observations are uncommitted bug-finding evidence. No guest
records, codecs, masked addresses, integer encodings or hash acquisition are run.
Tuple comparisons test F19 ordered keys, not a BAL pair sort.
"""

from pathlib import Path
import random
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "scripts"))
from differential import setup_driver


def lean_bytes(value: bytes) -> str:
    return "(Bytes.ofList [" + ", ".join(str(x) for x in value) + "])"


def ordering(a, b) -> str:
    return "lt" if a < b else "gt" if a > b else "eq"


def main():
    context = setup_driver(__doc__, __file__, 2566)
    from ethereum_types import bytes as dependency_bytes
    from ethereum import state
    from ethereum.crypto import hash as crypto_hash
    from ethereum.forks.amsterdam import fork_types
    context.check_source(dependency_bytes, "ethereum_types/bytes.py", dependency=True)
    context.check_source(state, "ethereum/state.py")
    context.check_source(crypto_hash, "ethereum/crypto/hash.py")
    context.check_source(fork_types, "ethereum/forks/amsterdam/fork_types.py")
    if not (state.Address is dependency_bytes.Bytes20 and
            crypto_hash.Hash32 is dependency_bytes.Bytes32 and
            state.Root is crypto_hash.Hash32 and
            fork_types.VersionedHash is crypto_hash.Hash32 and
            fork_types.Bloom is dependency_bytes.Bytes256 and
            crypto_hash.Hash64 is dependency_bytes.Bytes64):
        raise RuntimeError("pinned byte aliases differ from this slice's source map")
    rng = random.Random(context.seed)
    # Keep the option in the two-entry header, so the shared guard count stays exact.
    guards = ["import STFSpec.Base", "open STFSpec.Base\nset_option maxRecDepth 4096"]
    counts = {"construction": 0, "byte_order": 0, "domain_conversions": 0, "pair_order": 0}
    length_rejections = 0
    equality_assertions = 0
    samples = {}
    widths = (0, 1, 4, 8, 20, 32, 48, 64, 96, 256)
    for n in widths:
        oracle = getattr(dependency_bytes, "Bytes" + str(n))
        patterns = [bytes(n), b"\xff" * n, bytes(x % 256 for x in range(n)),
                    bytes(255 - x % 256 for x in range(n)),
                    bytes(0 if x % 2 else 255 for x in range(n))]
        if n:
            patterns += [b"\x01" + bytes(n - 1), bytes(n - 1) + b"\x01",
                         b"\x80" + bytes(n - 1), bytes(n - 1) + b"\xff"]
        patterns = list(dict.fromkeys(patterns))
        values = patterns + [rng.randbytes(n) for _ in range(24)]
        samples[n] = patterns
        invalid = [bytes(n + 1), b"\xff" * (n + 1), bytes(n + 7)]
        if n:
            invalid += [bytes(n - 1), b"\xff" * (n - 1)]
        for value in values + invalid:
            b = lean_bytes(value)
            try:
                actual = oracle(value)
            except ValueError:
                if len(value) == n:
                    raise AssertionError("oracle rejected exact width")
                guards.append(f"#guard (FixedBytes.ofBytes? (n := {n}) ({b})) = none")
                length_rejections += 1
            else:
                if len(actual) != n or bytes(actual) != value:
                    raise AssertionError("oracle changed accepted contents")
                if not (actual == value and value == actual):
                    raise AssertionError("fixed/plain byte equality differs")
                equality_assertions += 2
                guards.append(f"#guard (FixedBytes.ofBytes? (n := {n}) ({b})).map "
                              f"FixedBytes.toBytes = some ({lean_bytes(bytes(actual))})")
                guards.append(f"#guard (FixedBytes.ofBytes? (n := {n}) ({b})).map "
                              f"FixedBytes.toNat = some {int.from_bytes(actual, 'big')}")
            counts["construction"] += 1
        pairs = [(a, b) for a in patterns for b in patterns]
        pairs += [(rng.randbytes(n), rng.randbytes(n)) for _ in range(32)]
        for a, b in pairs:
            expected = ordering(oracle(a), oracle(b))
            guards.append(f"#guard (do let x ← FixedBytes.ofBytes? (n := {n}) "
                          f"({lean_bytes(a)}); let y ← FixedBytes.ofBytes? (n := {n}) "
                          f"({lean_bytes(b)}); pure (compare x y)) = some .{expected}")
            counts["byte_order"] += 1
    for name, n, oracle in [("Address", 20, state.Address), ("Hash32", 32, crypto_hash.Hash32)]:
        values = samples[n] + [rng.randbytes(n) for _ in range(16)]
        for value in values + [bytes(n - 1), bytes(n + 1), b"\xff" * (n + 1)]:
            b = lean_bytes(value)
            try:
                actual = oracle(value)
            except ValueError:
                guards.append(f"#guard {name}.ofBytes? ({b}) = none")
                length_rejections += 1
            else:
                guards.append(f"#guard ({name}.ofBytes? ({b})).map {name}.toBytes = "
                              f"some ({lean_bytes(bytes(actual))})")
                guards.append(f"#guard ({name}.ofBytes? ({b})).map {name}.toNat = "
                              f"some {int.from_bytes(actual, 'big')}")
                if n == 32:
                    fixed = dependency_bytes.Bytes32(actual)
                    if fixed != actual or crypto_hash.Hash32(fixed) != actual:
                        raise AssertionError("hash/bytes domain content changed")
                    guards.append(f"#guard ((Hash32.ofBytes? ({b})).map Hash32.toBytes32).map "
                                  f"FixedBytes.toBytes = some ({b})")
                    guards.append(f"#guard ((FixedBytes.ofBytes? (n := 32) ({b})).map "
                                  f"Hash32.ofBytes32).map Hash32.toBytes = some ({b})")
                    counts["domain_conversions"] += 2
            counts["construction"] += 1
        for a in samples[n]:
            for b in samples[n]:
                expected = ordering(oracle(a), oracle(b))
                guards.append(f"#guard (do let x ← {name}.ofBytes? ({lean_bytes(a)}); "
                              f"let y ← {name}.ofBytes? ({lean_bytes(b)}); "
                              f"pure (compare x y)) = some .{expected}")
                counts["byte_order"] += 1
    pair_samples = [(samples[20][0], samples[32][-1]),
                    (samples[20][-1], samples[32][0]),
                    (samples[20][0], samples[32][0]),
                    (samples[20][0], samples[32][-2])]
    pair_samples += [(rng.randbytes(20), rng.randbytes(32)) for _ in range(12)]
    for a, b in pair_samples:
        for c, d in pair_samples:
            expected = ordering((state.Address(a), dependency_bytes.Bytes32(b)),
                                (state.Address(c), dependency_bytes.Bytes32(d)))
            guards.append(f"#guard (do let a ← Address.ofBytes? ({lean_bytes(a)}); "
                          f"let b ← FixedBytes.ofBytes? (n := 32) ({lean_bytes(b)}); "
                          f"let c ← Address.ofBytes? ({lean_bytes(c)}); "
                          f"let d ← FixedBytes.ofBytes? (n := 32) ({lean_bytes(d)}); "
                          f"pure (compare (a, b) (c, d))) = some .{expected}")
            counts["pair_order"] += 1
    return context.run(
        guards, widths=widths, operation_cases=counts, length_rejections=length_rejections,
        plain_fixed_equality_assertions=equality_assertions, source_alias_assertions=6,
        guest_records_executed=0)



if __name__ == "__main__":
    raise SystemExit(main())
