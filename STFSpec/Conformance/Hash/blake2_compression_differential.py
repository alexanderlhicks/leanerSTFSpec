#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Finite BLAKE2b G/compression comparison with actual authenticated pinned EELS.

Run EELS/.venv/bin/python -I -B THIS_FILE --eels EELS --output OUTSIDE/compression.lean.
The shared driver authenticates the unreplaced pin, current source bytes and frozen
ethereum-types 0.4.1 before/after observation. Exact Uint word domains and list
widths are enforced before calls. G observations include arbitrary index aliases.
An independent integer RFC7693 model is supplemental evidence, not the oracle.
Only bounded counts execute: maximum UInt32 remains parse-only in the raw parser
suite. No precompile gas, guest/EEST executions or security/performance claim.
Spec guidance: STFSpec/informal/modules/EthHash.md §§3–4.
"""

import hashlib
from itertools import product
from pathlib import Path
import random
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "scripts"))
from differential import setup_driver

MASK = 2**64 - 1
# RFC7693 §§2.6–2.7. Compared with the actual pinned fields before model use.
IV = [0x6A09E667F3BCC908, 0xBB67AE8584CAA73B, 0x3C6EF372FE94F82B,
      0xA54FF53A5F1D36F1, 0x510E527FADE682D1, 0x9B05688C2B3E6C1F,
      0x1F83D9ABFB41BD6B, 0x5BE0CD19137E2179]
SIGMA = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]
MIX = [(0, 4, 8, 12), (1, 5, 9, 13), (2, 6, 10, 14), (3, 7, 11, 15),
       (0, 5, 10, 15), (1, 6, 11, 12), (2, 7, 8, 13), (3, 4, 9, 14)]
# Selected primary EIP152 examples 4–7, https://eips.ethereum.org/EIPS/eip-152#test-cases.
PRIMARY_H = [0x6A09E667F2BDC948, *IV[1:]]
PRIMARY_M = [0x636261] + [0] * 15
PRIMARY = [
    (4, 0, True, "08c9bcf367e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5"
     "d282e6ad7f520e511f6c3e2b8c68059b9442be0454267ce079217e1319cde05b"),
    (5, 12, True, "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1"
     "7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923"),
    (6, 12, False, "75ab69d3190a562c51aef8d88f1c2775876944407270c42c9844252c26d28752"
     "98743e7f6d5ea2f2d3e8d226039cd31b4e426ac4f2d3d666a610c2116fde4735"),
    (7, 1, True, "b63a380cb2897d521994a85234ee2c181b5f844d2c624c002677e9703449d2fb"
     "a551b3a8333bcdf5f2f7e08993d53923de3d64fcc68c034e717b9293fed7a421")]


def require_uint(value, width, uint):
    if type(value) is not uint or not 0 <= int(value) < 2**width:
        raise RuntimeError(f"expected exact in-range Uint/{width}")


def require_words(values, length, uint):
    if type(values) is not list or len(values) != length:
        raise RuntimeError(f"expected list of exactly {length} words")
    for value in values:
        require_uint(value, 64, uint)
    return list(map(int, values))


def domain_regressions(uint):
    good = [uint(0)] * 16
    require_words(good, 16, uint)
    bad = [tuple(good), good[:-1], good + [uint(0)], [True] + good[1:],
           [0] + good[1:], [uint(2**64)] + good[1:]]
    for case in bad:
        try:
            require_words(case, 16, uint)
        except RuntimeError:
            continue
        raise RuntimeError("word-domain regression admitted invalid input")
    for value in (True, 0, uint(2**32)):
        try:
            require_uint(value, 32, uint)
        except RuntimeError:
            continue
        raise RuntimeError("round-domain regression admitted invalid input")
    return 1 + len(bad) + 3


def rotate(x, count):
    k = count % 64
    # Integer radix arithmetic, separate from Lean's native shifts.
    return x if not k else x // 2**k + (x % 2**k) * 2**(64 - k)


def integer_g(v, indices, x, y):
    v = v.copy()
    a, b, c, d = indices
    for word, rotation in ((x, 32), (y, 16)):
        v[a] = (v[a] + v[b] + word) % 2**64
        v[d] = rotate(v[d] ^ v[a], rotation)
        v[c] = (v[c] + v[d]) % 2**64
        v[b] = rotate(v[b] ^ v[c], 24 if rotation == 32 else 63)
    return v


def integer_rounds(m, v, count, start=0):
    for r in range(start, start + count):
        s = SIGMA[r % 10]
        for j, indices in enumerate(MIX):
            v = integer_g(v, indices, m[s[2*j]], m[s[2*j+1]])
    return v


def integer_compress(count, h, m, t0, t1, flag):
    v = h + IV.copy()
    v[12] ^= t0
    v[13] ^= t1
    if flag:
        v[14] ^= MASK
    v = integer_rounds(m, v, count)
    return b"".join((h[i] ^ v[i] ^ v[i+8]).to_bytes(8, "little") for i in range(8))


def vec(words):
    return "#v[" + ",".join(map(str, words)) + "]"


def byte_array(data):
    return "#[" + ",".join(map(str, data)) + "]"


def main():
    context = setup_driver(__doc__, __file__, 18018)
    from ethereum.crypto import blake2
    from ethereum_types.numeric import Uint
    source = context.check_source(blake2, "ethereum/crypto/blake2.py")
    oracle = blake2.Blake2b()
    regressions = domain_regressions(Uint)
    if (list(map(int, oracle.IV)) != IV or [list(row) for row in oracle.sigma] != SIGMA
            or [tuple(map(int, row)) for row in oracle.MIX_TABLE] != MIX
            or tuple(map(int, (oracle.R1, oracle.R2, oracle.R3, oracle.R4))) != (32, 24, 16, 63)):
        raise RuntimeError("actual pinned constants differ from RFC model literals")
    rng = random.Random(context.seed)
    guards = ["import STFSpec.Hash.Blake2Compression", "open STFSpec.Hash.Blake2b"]
    counts = {}
    observations = hashlib.sha256()

    def add(group, guard):
        guards.append(guard)
        counts[group] = counts.get(group, 0) + 1
        observations.update(guard.encode())

    add("iv", f"#guard IV = {vec(IV)}")
    for r, row in enumerate(SIGMA):
        add("sigma_rows", f"#guard sigma[{r}] = {vec(row)}")
    tuples = ",".join("(" + ",".join(map(str, row)) + ")" for row in MIX)
    add("mix_table", f"#guard MIX_TABLE = #v[{tuples}]")

    def actual_g(v, indices, x, y):
        values = [Uint(word) for word in v]
        require_words(values, 16, Uint)
        for i in indices:
            if type(i) is not int or not 0 <= i < 16:
                raise RuntimeError("G index outside Fin16")
        xx, yy = Uint(x), Uint(y)
        require_uint(xx, 64, Uint)
        require_uint(yy, 64, Uint)
        result = oracle.G(values, *(Uint(i) for i in indices), xx, yy)
        if result is not values:
            raise RuntimeError("pinned G did not return its mutated list")
        result = require_words(result, 16, Uint)
        if result != integer_g(v, indices, x, y):
            raise RuntimeError("pinned G differs from independent integer model")
        if any(result[i] != v[i] for i in range(16) if i not in indices):
            raise RuntimeError("G altered an untouched index")
        return result

    # All fifteen equivalence relations on four index positions (including all
    # six single-pair aliases, three double-pairs, four triples, same and distinct).
    partitions = [p for p in product(range(4), repeat=4)
                  if p[0] == 0 and all(p[i] <= max(p[:i]) + 1 for i in range(1, 4))]
    if len(partitions) != 15:
        raise RuntimeError("alias partition enumeration incomplete")
    states = [[0]*16, [MASK]*16,
              [(0x8000000000000001 + i * 0x0102030405060708) & MASK for i in range(16)]]
    states.extend([[rng.getrandbits(64) for _ in range(16)] for _ in range(24)])
    for v in states:
        for p in partitions:
            indices = tuple((0, 5, 10, 15)[i] for i in p)
            x, y = rng.getrandbits(64), rng.getrandbits(64)
            result = actual_g(v, indices, x, y)
            args = " ".join(map(str, indices))
            add("g_alias_partitions", f"#guard G {vec(v)} {args} {x} {y} = {vec(result)}")
    # Move distinct and same-index writes through every storage coordinate.
    for i in range(16):
        v = states[2]
        for indices in ((i, i, i, i), tuple((i + j) % 16 for j in range(4))):
            result = actual_g(v, indices, MASK, 0x8000000000000000)
            args = " ".join(map(str, indices))
            add("g_positions", f"#guard G {vec(v)} {args} {MASK} 9223372036854775808 = {vec(result)}")
    for x in (0, 1, 2**63, 2**63+1, MASK, 0x0102030405060708):
        for r in (0, 1, 16, 24, 32, 63, 64, 65, 128, 129, 2**32+1):
            add("rotation", f"#guard rotr {x} {r} = {rotate(x, r)}")

    compression_calls = 0

    def actual_compress(count, h, m, t0, t1, flag):
        nonlocal compression_calls
        # This is a test workload bound, not a semantic acceptance bound.
        if type(count) is not int or count not in (0, 1, 2, 9, 10, 11, 12, 20, 21):
            raise RuntimeError("unbounded runtime compression count")
        if type(flag) is not bool:
            raise RuntimeError("compress requires an exact Boolean flag")
        hh, mm, rr, tt0, tt1 = ([Uint(x) for x in h], [Uint(x) for x in m],
                                Uint(count), Uint(t0), Uint(t1))
        require_words(hh, 8, Uint)
        require_words(mm, 16, Uint)
        require_uint(rr, 32, Uint)
        require_uint(tt0, 64, Uint)
        require_uint(tt1, 64, Uint)
        result = oracle.compress(rr, hh, mm, tt0, tt1, flag)
        compression_calls += 1
        if type(result) is not bytes or len(result) != 64:
            raise RuntimeError("compress must return exactly 64 native bytes")
        if result != integer_compress(count, h, m, t0, t1, flag):
            raise RuntimeError("pinned compression differs from supplemental RFC integer model")
        return result

    for identifier, count, flag, expected in PRIMARY:
        observed = actual_compress(count, PRIMARY_H, PRIMARY_M, 3, 0, flag)
        if observed.hex() != expected:
            raise RuntimeError(f"pinned source differs from primary EIP152 example {identifier}")
        add("primary_eip152_4_7", f"#guard (compress {count} {vec(PRIMARY_H)} {vec(PRIMARY_M)} "
            f"3 0 {str(flag).lower()}).data = {byte_array(observed)}")
    for case in range(15):
        if case == 0:
            h, m, t0, t1 = [0]*8, [0]*16, 0, 0
        elif case == 1:
            h, m, t0, t1 = [MASK]*8, [MASK]*16, MASK, MASK
        elif case == 2:
            h, m, t0, t1 = states[2][:8], states[2], 2**63, MASK
        else:
            h = [rng.getrandbits(64) for _ in range(8)]
            m = [rng.getrandbits(64) for _ in range(16)]
            t0, t1 = rng.getrandbits(64), rng.getrandbits(64)
        for count in (0, 1, 2, 9, 10, 11, 12, 20, 21):
            for flag in (False, True):
                observed = actual_compress(count, h, m, t0, t1, flag)
                add("compression_boundaries", f"#guard (compress {count} {vec(h)} {vec(m)} "
                    f"{t0} {t1} {str(flag).lower()}).data = {byte_array(observed)}")
        # Compare arbitrary-start prefixes with actual pinned G calls; EELS
        # compress itself always starts at zero, so label these observations separately.
        for start in (0, 9, 10, 11, 20):
            count = 2
            work = m.copy()
            result = work.copy()
            for r in range(start, start + count):
                s = oracle.sigma[r % oracle.sigma_len]
                for j, indices in enumerate(MIX):
                    result = actual_g(result, indices, m[s[2*j]], m[s[2*j+1]])
            if result != integer_rounds(m, work, count, start):
                raise RuntimeError("arbitrary-start prefix mismatch")
            add("prefixes_actual_g", f"#guard rounds {vec(m)} {count} {start} {vec(work)} = {vec(result)}")
    return context.run(
        guards, cases=counts, alias_partitions=partitions, result_domain_regressions=regressions,
        compression_calls=compression_calls, maximum_rounds_executed=21,
        maximum_uint32_compression_calls=0, guest_executions=0,
        supplemental_model="independent RFC7693 integer radix rotation/sequential G model",
        oracle_operations=["Blake2b().G", "Blake2b().compress"],
        observations_sha256=observations.hexdigest(), python=sys.version,
        oracle_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        uv_lock_sha256=hashlib.sha256((context.eels / "uv.lock").read_bytes()).hexdigest(),
        dependency_sha256=hashlib.sha256(context.dependency.read_bytes()).hexdigest())


if __name__ == "__main__":
    raise SystemExit(main())
