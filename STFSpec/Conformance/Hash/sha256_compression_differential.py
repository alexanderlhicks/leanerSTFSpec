#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Finite SHA-256 compression differential and test-only block composition.

Run with EELS/.venv/bin/python -I, --eels EELS --output /tmp/sha256-compression.lean.
Keep generated output outside both checkouts. Fixed-word
compression is compared with an independent readable FIPS 180-4 integer model,
NOT an EELS compression oracle (EELS exposes hashlib digests). Test-only Python
padding/parsing composes Lean compression against hashlib observed through the
authenticated pinned precompile module. It is not a production digest API test.
No guest, precompile gas/effect or unrestricted huge-input correspondence is claimed.
Spec guidance: STFSpec/informal/modules/EthHash.md §§3–4.
"""

from pathlib import Path
import random
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "scripts"))
from differential import setup_driver

MASK = (1 << 32) - 1
# FIPS 180-4 §§4.2.2, 5.3.3, https://doi.org/10.6028/NIST.FIPS.180-4.
K = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
    0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
    0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
    0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
    0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
    0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]
IV = [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
      0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]


def rotr(x, n):
    return ((x >> n) | (x << (32 - n))) & MASK


def expand(block):
    w = list(block)
    for t in range(16, 64):
        s0 = rotr(w[t - 15], 7) ^ rotr(w[t - 15], 18) ^ (w[t - 15] >> 3)
        s1 = rotr(w[t - 2], 17) ^ rotr(w[t - 2], 19) ^ (w[t - 2] >> 10)
        w.append((w[t - 16] + s0 + w[t - 7] + s1) & MASK)
    return w


def trace(state, w):
    states = [list(state)]
    for t in range(64):
        a, b, c, d, e, f, g, h = states[-1]
        ch = (e & f) ^ ((~e & MASK) & g)
        maj = (a & b) ^ (a & c) ^ (b & c)
        s1 = rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25)
        s0 = rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22)
        t1 = (h + s1 + ch + K[t] + w[t]) & MASK
        t2 = (s0 + maj) & MASK
        states.append([(t1 + t2) & MASK, a, b, c, (d + t1) & MASK, e, f, g])
    return states


def vector(words):
    return "#v[" + ", ".join(f"0x{x:08x}" for x in words) + "]"


def padded_blocks(message):
    """Test harness only: ordinary finite FIPS-domain inputs, no production padding."""
    if len(message) * 8 >= 1 << 64:
        raise ValueError("test composition requires the FIPS domain")
    padded = message + b"\x80"
    padded += bytes((56 - len(padded) % 64) % 64)
    padded += (8 * len(message)).to_bytes(8, "big")
    return [[int.from_bytes(padded[t + j:t + j + 4], "big")
             for j in range(0, 64, 4)] for t in range(0, len(padded), 64)]


def main():
    context = setup_driver(__doc__, __file__, 12012)
    from ethereum.forks.amsterdam.vm.precompiled_contracts import sha256 as source
    context.check_source(source, "ethereum/forks/amsterdam/vm/precompiled_contracts/sha256.py")
    rng = random.Random(context.seed)
    cases = [([0] * 8, [0] * 16), ([MASK] * 8, [MASK] * 16),
             (IV, [0x80000000] + [0] * 15), (IV, [0x61626380] + [0] * 14 + [24]),
             ([i for i in range(8)], [i * 0x1020304 for i in range(16)]),
             ([1 << (31 - i) for i in range(8)], [1 << (31 - i) for i in range(16)])]
    # Every input position is exercised independently; asymmetry detects indexing errors.
    for i in range(16):
        block = [0] * 16
        block[i] = MASK if i % 2 else 0x80000001
        cases.append(([MASK, 0, 1, 0x80000000, 0x12345678, 0x87654321, 3, 7], block))
    cases += [([rng.getrandbits(32) for _ in range(8)],
               [rng.getrandbits(32) for _ in range(16)]) for _ in range(64)]
    guards = ["import STFSpec.Hash", "open STFSpec.Hash STFSpec.Hash.Sha256"]
    for state, block in cases:
        w = expand(block)
        states = trace(state, w)
        s, b = vector(state), vector(block)
        guards.append(f"#guard schedule {b} = {vector(w)}")
        for prefix in (0, 1, 2, 17, 64):
            guards.append(f"#guard rounds (schedule {b}) {s} {prefix} (by decide) = "
                          f"{vector(states[prefix])}")
        final = [(x + y) & MASK for x, y in zip(state, states[-1])]
        guards.append(f"#guard sha256Compress {s} {b} = {vector(final)}")
    lengths = [0, 1, 3, 31, 55, 56, 63, 64, 65, 119, 120, 127, 128, 129, 255, 256, 257]
    messages = [bytes((17 * i + 131) % 256 for i in range(n)) for n in lengths]
    messages += [rng.randbytes(rng.randrange(513)) for _ in range(8)]
    blocks_total = 0
    for msg in messages:
        expression = "initialState"
        model_state = IV
        for block in padded_blocks(msg):
            expression = f"(sha256Compress {expression} {vector(block)})"
            work = trace(model_state, expand(block))[-1]
            model_state = [(x + y) & MASK for x, y in zip(model_state, work)]
            blocks_total += 1
        digest = source.hashlib.sha256(msg).digest()
        host_words = [int.from_bytes(digest[i:i + 4], "big") for i in range(0, 32, 4)]
        if model_state != host_words:
            raise AssertionError("independent model disagrees with pinned module's host digest")
        guards.append(f"#guard {expression} = {vector(host_words)}")
    return context.run(guards, fixed_word_cases=len(cases), random_fixed_word_cases=64,
        schedule_words_checked=64 * len(cases), round_prefixes=[0, 1, 2, 17, 64],
        compression_oracle="independent FIPS 180-4 integer model, not EELS",
        test_only_composition_messages=len(messages), test_only_composition_blocks=blocks_total,
        test_only_message_lengths=[len(m) for m in messages],
        digest_oracle="hashlib alias from authenticated pinned precompile source",
        limitations="finite tests; harness padding/parsing only; no production digest, gas/effects or guest")


if __name__ == "__main__":
    raise SystemExit(main())
