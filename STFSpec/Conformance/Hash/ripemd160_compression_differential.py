#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""RIPEMD-160 compression: independent integer model and finite EELS composition.

The model is newly written from the authors' corrected pseudocode, not EELS raw
compression (none exists) or another implementation. Primary digest facts:
https://homes.esat.kuleuven.be/~bosselae/ripemd160.html
Algorithm: https://homes.esat.kuleuven.be/~bosselae/ripemd/rmd160.txt
MD4 padding: RFC 1320 §§3.1–3.2. No production digest/parser is exercised.

Run with frozen EELS/.venv/bin/python -I -B, --eels EELS and --output outside
both checkouts. The shared Driver authenticates pinned source/current bytes and
ethereum-types RECORD. Actual pinned ripemd160 precompile execution observes
hashlib.new("ripemd160") on this supported host. Gas setup below is a test adapter,
not a Lean precompile/gas claim. Source/interpreter/driver identities are recorded
before/after. No all-host/resource, guest, security or performance claim follows.
Spec guidance: STFSpec/informal/modules/EthHash.md §§3–4.
"""

import hashlib
import json
from pathlib import Path
import random
import ssl
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts"))
from differential import setup_driver

MASK = (1 << 32) - 1
IV = [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0]
# Independently transcribed standard data, grouped by the five branch functions.
ORDERS = (
    ((0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15),
     (7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8),
     (3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12),
     (1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2),
     (4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13)),
    ((5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12),
     (6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2),
     (15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13),
     (8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14),
     (12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11)))
ROTATIONS = (
    ((11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8),
     (7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12),
     (11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5),
     (11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12),
     (9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6)),
    ((8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6),
     (9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11),
     (9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5),
     (15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8),
     (8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11)))
CONSTANTS = ((0, 0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xa953fd4e),
             (0x50a28be6, 0x5c4dd124, 0x6d703ef3, 0x7a6d76e9, 0))
PRIMARY = (
    (b"", "9c1185a5c5e9fc54612808977ee8f548b2258d31"),
    (b"a", "0bdc9d2d256b3ee9daae347be6f4dc835a467ffe"),
    (b"abc", "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc"),
    (b"message digest", "5d0689ef49d2fae572b881b123a85ffa21595f36"),
    (b"abcdefghijklmnopqrstuvwxyz", "f71c27109c692c1b56bbdceb5b9d2865b3708dbc"),
    (b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
     "12a053384a9c0c88e405a06c27dcf49ada62eb2b"),
    (b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789",
     "b0e20b6e3116640286ed3a87a5713079b21f5189"),
    (b"1234567890" * 8, "9b752e45573d4b39f4dbd3323cab82bf63326bfb"),
    (b"a" * 1_000_000, "52783243c1697bdbe16d37f97f68f08325dc1528"))


def rotate(x, s):
    s %= 32
    return ((x << s) | (x >> ((32 - s) % 32))) & MASK


def boolean(group, x, y, z):
    return (x ^ y ^ z, (x & y) | (~x & z), (x | ~y) ^ z,
            (x & z) | (y & ~z), x ^ (y | ~z))[group] & MASK


def step(q, group, x, k, s):
    a, b, c, d, e = q
    t = (rotate((a + boolean(group, b, c, d) + x + k) & MASK, s) + e) & MASK
    return [e, t, b, rotate(c, 10), d]


def dual_round(left, right, block, j):
    group, position = divmod(j, 16)
    return tuple(step(q, fgroup, block[ORDERS[branch][group][position]],
                      CONSTANTS[branch][group], ROTATIONS[branch][group][position])
                 for branch, (q, fgroup) in enumerate(((left, group), (right, 4 - group))))


def feedforward(h, left, right):
    # Cyclic indexing is independently arranged from the explicit Lean expressions.
    return [(h[(i + 1) % 5] + left[(i + 2) % 5] + right[(i + 3) % 5]) & MASK
            for i in range(5)]


def compress(h, block):
    left, right = h.copy(), h.copy()
    for j in range(80):
        left, right = dual_round(left, right, block, j)
    return feedforward(h, left, right)


def padded_blocks(message):
    # Finite test adapter only; the MD4 low-64-bit length rule is explicit.
    padded = message + b"\x80"
    padded += b"\0" * ((56 - len(padded)) % 64)
    padded += ((8 * len(message)) % (1 << 64)).to_bytes(8, "little")
    return [[int.from_bytes(padded[k + i:k + i + 4], "little")
             for i in range(0, 64, 4)] for k in range(0, len(padded), 64)]


def vector(words):
    return "#v[" + ", ".join(f"0x{x:08x}" for x in words) + "]"


def work(left, right):
    return f"(⟨{vector(left)}, {vector(right)}⟩ : Ripemd160Work)"


def digest_words(digest):
    raw = bytes.fromhex(digest)
    return [int.from_bytes(raw[i:i + 4], "little") for i in range(0, 20, 4)]


def identity(paths):
    return {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}


def main():
    context = setup_driver(__doc__, __file__, 170160)
    if not sys.flags.isolated or not sys.flags.dont_write_bytecode:
        context.parser.error("use the frozen interpreter with -I -B")
    from ethereum.forks.amsterdam.vm.precompiled_contracts import ripemd160 as oracle
    from ethereum.forks.amsterdam.fork_types import ExecutionGas, StateGas
    from ethereum.forks.amsterdam.vm.gas import GasMeter
    from ethereum_types.numeric import Uint
    from ethereum_types.bytes import Bytes
    from ethereum.trace import discard_evm_trace, set_evm_trace
    set_evm_trace(discard_evm_trace)
    source = context.check_source(oracle,
        "ethereum/forks/amsterdam/vm/precompiled_contracts/ripemd160.py")
    paths = [Path(__file__), ROOT / "scripts/differential.py", ROOT / "reference.toml",
             ROOT / "lean-toolchain", ROOT / "lakefile.toml", ROOT / "lake-manifest.json",
             ROOT / "STFSpec/Hash.lean", ROOT / "STFSpec/Conformance.lean",
             ROOT / "STFSpec/Hash/Ripemd160Compression.lean",
             ROOT / "STFSpec/Conformance/Hash/Ripemd160CompressionGuards.lean",
             ROOT / "STFSpec/Conformance/Hash/Ripemd160CompressionCallerProofs.lean",
             Path(sys.executable).resolve(), source, context.eels / "uv.lock",
             context.dependency_record]
    before = identity(paths)
    build = subprocess.run(["lake", "build", "EthHash", "EthConformance", "--wfail"], cwd=ROOT)
    if build.returncode:
        return build.returncode
    guards = ["import STFSpec.Hash", "open STFSpec.Hash"]
    counts = {}

    def guard(kind, expression):
        counts[kind] = counts.get(kind, 0) + 1
        guards.append("#guard " + expression)

    rng = random.Random(context.seed)
    states = [[0] * 5, [MASK] * 5, IV, [1, 10, 100, 1000, 10000]]
    states += [[1 << (i * 7 % 32) if i == k else 0 for i in range(5)] for k in range(5)]
    states += [[rng.getrandbits(32) for _ in range(5)] for _ in range(32)]
    for case, h in enumerate(states):
        block = ([0] * 16 if case == 0 else [MASK] * 16 if case == 1 else
                 list(range(16)) if case == 2 else [rng.getrandbits(32) for _ in range(16)])
        left, right = h.copy(), h.copy()
        if case < 8:
            guard("Prefix", f"ripemd160Rounds {work(h, h)} {vector(block)} 0 (by decide) = {work(h, h)}")
        for j in range(80):
            old_left, old_right = left, right
            left, right = dual_round(left, right, block, j)
            if case < 8 or j in (0, 15, 16, 31, 32, 47, 48, 63, 64, 79):
                guard("Round", f"ripemd160Round {work(old_left, old_right)} {vector(block)} {j} = {work(left, right)}")
            if case < 8:
                guard("Prefix", f"ripemd160Rounds {work(h, h)} {vector(block)} {j + 1} (by decide) = {work(left, right)}")
        guard("Compress", f"ripemd160Compress {vector(h)} {vector(block)} = {vector(feedforward(h, left, right))}")
        arbitrary_left = [rng.getrandbits(32) for _ in range(5)]
        arbitrary_right = [rng.getrandbits(32) for _ in range(5)]
        guard("Feedforward", f"ripemd160Feedforward {vector(h)} {work(arbitrary_left, arbitrary_right)} = {vector(feedforward(h, arbitrary_left, arbitrary_right))}")
        for j in (0, 15, 16, 31, 32, 47, 48, 63, 64, 79):
            l, r = dual_round(arbitrary_left, arbitrary_right, block, j)
            guard("AsymmetricRound", f"ripemd160Round {work(arbitrary_left, arbitrary_right)} {vector(block)} {j} = {work(l, r)}")
    for branch, name in enumerate(("Left", "Right")):
        for j in range(80):
            group, position = divmod(j, 16)
            guard("Order", f"ripemd160{name}Order[{j}] = {ORDERS[branch][group][position]}")
            guard("RotationTable", f"ripemd160{name}Rotations[{j}] = {ROTATIONS[branch][group][position]}")
        for group in range(5):
            guard("Constant", f"ripemd160{name}Constants[{group}] = {CONSTANTS[branch][group]}")
    for j in range(80):
        guard("Group", f"ripemd160Group {j} = {j // 16}")
        guard("Reverse", f"ripemd160Reverse {j} = {79 - j}")
        x, y, z = [rng.getrandbits(32) for _ in range(3)]
        guard("Boolean", f"ripemd160F {j} {x} {y} {z} = {boolean(j // 16, x, y, z)}")
    for x in (0, 1, 1 << 31, MASK, 0x01234567):
        for s in (0, 1, 10, 15, 31, 32, 33, 63, 64, 65, 4096):
            guard("Rotation", f"ripemd160Rotl {x} {s} = {rotate(x, s)}")
    guards.append("def wi017Blocks (blocks : Array (Vector UInt32 16)) : Vector UInt32 5 :=\n  blocks.foldl ripemd160Compress ripemd160IV")
    messages = list(PRIMARY)
    for length in (1, 31, 32, 55, 56, 57, 63, 64, 65, 119, 120, 127, 128, 129, 255, 256, 4096):
        messages += [(bytes(rng.getrandbits(8) for _ in range(length)), None),
                     (b"\xff" * length, None), (b"\0" * length, None)]
    messages += [(bytes(rng.getrandbits(8) for _ in range(rng.randrange(4097))), None)
                 for _ in range(32)]
    observations = []
    for case, (message, primary) in enumerate(messages):
        cost = 600 + 120 * ((len(message) + 31) // 32)
        frame = context.frame([])
        frame.call_data = Bytes(message)
        frame.gas_meter = GasMeter(ExecutionGas(Uint(cost + 1)), StateGas(Uint(0)), StateGas(Uint(0)))
        oracle.ripemd160(frame)
        output = bytes(frame.output)
        if len(output) != 32 or output[:12] != b"\0" * 12 or int(frame.gas_meter.gas_left) != 1:
            raise RuntimeError("actual precompile adapter output/gas mismatch")
        digest = output[12:].hex()
        if primary is not None and digest != primary:
            raise RuntimeError("pinned hashlib disagrees with the primary published fact")
        blocks = padded_blocks(message)
        h = IV.copy()
        for block in blocks:
            h = compress(h, block)
        if h != digest_words(digest):
            raise RuntimeError("independent integer model disagrees with pinned hashlib")
        if len(message) == 1_000_000:
            # A finite repeated-block test avoids a multi-megabyte literal program.
            if blocks[:-1] != [blocks[0]] * 15625:
                raise RuntimeError("million-a repeated-block construction mismatch")
            guards.append("def wi017Million : Vector UInt32 5 := Id.run do\n"
                          "  let mut h := ripemd160IV\n"
                          "  for _ in [0:15625] do\n"
                          f"    h := ripemd160Compress h {vector(blocks[0])}\n"
                          f"  return ripemd160Compress h {vector(blocks[-1])}")
            guard("PrimaryComposition", f"wi017Million = {vector(h)}")
        else:
            block_array = "#[" + ", ".join(vector(b) for b in blocks) + "]"
            guard("PrimaryComposition" if primary else "EelsComposition",
                  f"wi017Blocks {block_array} = {vector(h)}")
        observations.append({"case": case, "bytes": len(message), "blocks": len(blocks),
                             "message_sha256": hashlib.sha256(message).hexdigest(),
                             "digest": digest, "primary": primary is not None})
    declarations = [g for g in guards[2:] if g.startswith("def ")]
    guards = guards[:2] + [g for g in guards[2:] if g.startswith("#guard ")]
    guards[1] += "\n" + "\n".join(declarations)
    result = context.run(guards, cases=counts, model="independent corrected-author integer model",
                         oracle="actual pinned ripemd160.py:26–54 precompile invoking hashlib.new")
    after = identity(paths)
    report = {"before": before, "after": after, "unchanged": before == after,
              "counts": counts, "guards": sum(counts.values()), "states": len(states),
              "seed": context.seed, "eels_commit": context.head,
              "python": sys.version, "openssl": ssl.OPENSSL_VERSION,
              "ripemd160_capability": "ripemd160" in hashlib.algorithms_available,
              "isolated": sys.flags.isolated, "no_bytecode_writes": sys.flags.dont_write_bytecode,
              "source": str(source), "source_blob": context.oracle_blobs[str(source.relative_to(context.eels))],
              "lean_version": subprocess.check_output(["lake", "env", "lean", "--version"], cwd=ROOT, text=True).strip(),
              "parent": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
              "generated_sha256": hashlib.sha256(context.output.read_bytes()).hexdigest(),
              "composition": observations, "lean_exit": result,
              "limitations": "finite supported-host composition; no raw EELS compression oracle, production digest/parser, all-host/resources, guest/security/performance claim"}
    context.output.with_suffix(".json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"guards": report["guards"], "counts": counts, "unchanged": report["unchanged"],
                      "composition_messages": len(messages), "lean_exit": result}), flush=True)
    return result or int(before != after)


if __name__ == "__main__":
    raise SystemExit(main())
