#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Finite Keccak-f[1600] comparison against an independent standard model.

This model implements FIPS 202 §§3.2–3.3 using forward pi placement, rho offsets
computed by its coordinate walk, and iota constants computed by Algorithm 5's
LFSR. It does not read Lean's constants or use EELS/pycryptodome. The pinned EELS
hash module has no raw permutation surface. Generated observations are finite
bug-finding evidence, never normative committed known answers.

Run from the repository root:
  python3 STFSpec/Conformance/Hash/keccak_permutation_differential.py \
    --output /tmp/keccak-permutation-differential.lean

Spec guidance: STFSpec/informal/modules/EthHash.md §§3–4.
"""

import argparse
import hashlib
import json
from pathlib import Path
import random
import subprocess
import sys

sys.dont_write_bytecode = True
MASK = (1 << 64) - 1
MODEL = "FIPS 202 coordinate/LFSR Python model; not pinned EELS execution"


def rotate(lane, amount):
    amount %= 64
    return ((lane << amount) | (lane >> ((64 - amount) % 64))) & MASK


def offsets():
    result = [0] * 25
    x, y = 1, 0
    for t in range(24):
        result[x + 5 * y] = ((t + 1) * (t + 2) // 2) % 64
        x, y = y, (2 * x + 3 * y) % 5
    return result


def rc(t):
    # FIPS 202 Algorithm 5, r[0] first: shifting multiplies by x;
    # reduction uses x^8 + x^6 + x^5 + x^4 + 1.
    register = 1
    for _ in range(t % 255):
        register <<= 1
        if register & 0x100:
            register ^= 0x171
    return register & 1


def round_constant(round_index):
    return sum(rc(j + 7 * round_index) << ((1 << j) - 1) for j in range(7))


def theta(a):
    columns = [a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20]
               for x in range(5)]
    return [a[x + 5 * y] ^ columns[(x - 1) % 5] ^ rotate(columns[(x + 1) % 5], 1)
            for y in range(5) for x in range(5)]


def rho(a):
    return [rotate(lane, amount) for lane, amount in zip(a, offsets())]


def pi(a):
    result = [0] * 25
    for y in range(5):
        for x in range(5):
            result[y + 5 * ((2 * x + 3 * y) % 5)] = a[x + 5 * y]
    return result


def chi(a):
    return [(a[x + 5 * y] ^ ((~a[(x + 1) % 5 + 5 * y]) &
                             a[(x + 2) % 5 + 5 * y])) & MASK
            for y in range(5) for x in range(5)]


def iota(a, round_index):
    result = a.copy()
    result[0] ^= round_constant(round_index)
    return result


def steps(a, round_index):
    result = []
    for name, step in [("Theta", theta), ("Rho", rho), ("Pi", pi), ("Chi", chi),
                       ("Iota", lambda lanes: iota(lanes, round_index))]:
        before = a
        a = step(a)
        result.append((name, before, a))
    return result


def vector(a):
    return "#v[" + ", ".join(f"0x{lane:016x}" for lane in a) + "]"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--seed", type=int, default=1101600)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[3]
    args.output = args.output.resolve()
    if args.output.is_relative_to(root):
        parser.error("generated observations must be outside the implementation checkout")
    build_command = ["lake", "build", "EthHash", "--wfail"]
    build = subprocess.run(build_command, cwd=root)
    if build.returncode:
        return build.returncode
    rng = random.Random(args.seed)
    states = [[0] * 25, [MASK] * 25, list(range(25))]
    states += [[(1 << (i * 7 % 64)) if j == i else 0 for j in range(25)]
               for i in range(25)]
    states += [[rng.getrandbits(64) for _ in range(25)] for _ in range(32)]
    guards = ["import STFSpec.Hash", "open STFSpec.Hash"]
    counts = {name: 0 for name in ["Theta", "Rho", "Pi", "Chi", "Iota", "Round",
                                  "Prefix", "F1600", "Rotation", "RhoOffset",
                                  "RoundConstant"]}
    for index, initial in enumerate(states):
        a = initial
        if index < 8:
            guards.append(f"#guard keccakRounds {vector(initial)} 0 (by decide) = {vector(a)}")
            counts["Prefix"] += 1
        for r in range(24):
            snapshots = steps(a, r)
            if r in [0, 1, 11, 23]:
                for name, before, after in snapshots:
                    extra = f" {r}" if name == "Iota" else ""
                    guards.append(f"#guard keccak{name} {vector(before)}{extra} = {vector(after)}")
                    counts[name] += 1
                guards.append(f"#guard keccakRound {vector(a)} {r} = {vector(snapshots[-1][2])}")
                counts["Round"] += 1
            a = snapshots[-1][2]
            if index < 8:
                guards.append(f"#guard keccakRounds {vector(initial)} {r + 1} (by decide) = {vector(a)}")
                counts["Prefix"] += 1
        guards.append(f"#guard keccakF1600 {vector(initial)} = {vector(a)}")
        counts["F1600"] += 1
    for lane in [0, 1, 1 << 63, MASK, 0x0123456789abcdef]:
        for amount in [0, 1, 7, 8, 31, 32, 63, 64, 65, 127, 128, 129, 4096]:
            guards.append(f"#guard keccakRotl {lane} {amount} = {rotate(lane, amount)}")
            counts["Rotation"] += 1
    for index, amount in enumerate(offsets()):
        guards.append(f"#guard keccakRhoOffsets[{index}] = {amount}")
        counts["RhoOffset"] += 1
    for r in range(24):
        guards.append(f"#guard keccakRoundConstants[{r}] = {round_constant(r)}")
        counts["RoundConstant"] += 1
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("\n".join(guards) + "\n")
    report = {"model": MODEL, "seed": args.seed, "states": len(states),
              "operation_cases": counts, "guards": sum(counts.values()),
              "driver_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "lean_version": subprocess.check_output(["lake", "env", "lean", "--version"],
                                                       text=True).strip(),
              "source_sha256": {str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                                for p in [Path("STFSpec/Hash.lean"),
                                          Path("STFSpec/Hash/KeccakPermutation.lean")]},
              "generated_sha256": hashlib.sha256(args.output.read_bytes()).hexdigest(),
              "source_parent_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
              "build_command": build_command, "build_exit": build.returncode,
              "command": ["lake", "env", "lean", str(args.output)]}
    completed = subprocess.run(report["command"], cwd=root)
    report["sources_unchanged"] = all(
        hashlib.sha256(Path(p).read_bytes()).hexdigest() == digest
        for p, digest in report["source_sha256"].items())
    report["exit"] = completed.returncode
    args.output.with_suffix(".json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, sort_keys=True), flush=True)
    return completed.returncode or int(not report["sources_unchanged"])


if __name__ == "__main__":
    raise SystemExit(main())
