#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Generate and run U256 guards against the pinned ethereum-types implementation.

Run with the frozen EELS venv's Python, for example:
  EELS/.venv/bin/python STFSpec/Conformance/Base/u256_differential.py \
    --eels EELS --output /tmp/u256-differential.lean

Generated observations are bug-finding evidence, never committed normative fixtures.
Spec guidance: STFSpec/informal/modules/EthBase.md §§3–4. The constructor and signed
conversion sources are ethereum_types/numeric.py:44,594,611,675 (locked dependency).
The output contains only public U256 API calls and is checked by ordinary Lean guards.
"""

import argparse
import importlib.metadata
import json
from pathlib import Path
import random
import subprocess
import tomllib


def lean_int(value):
    """Use parentheses so a negative value is parsed as one Lean argument."""
    return f"({value} : Int)"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--eels", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[3]
    pin = tomllib.loads((root / "reference.toml").read_text())["release"]
    eels = args.eels.resolve()
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=eels, text=True).strip()
    if head != pin["commit"]:
        parser.error("EELS checkout does not match reference.toml")
    version = importlib.metadata.version("ethereum-types")
    if version != pin["python_dependencies"]["ethereum-types"]:
        parser.error("ethereum-types version does not match reference.toml")
    from ethereum_types import numeric
    from ethereum_types.numeric import U256
    dependency = Path(numeric.__file__).resolve()
    if not dependency.is_relative_to(eels / ".venv"):
        parser.error("ethereum-types must be loaded from the frozen EELS venv")
    output = args.output.resolve()
    if output.is_relative_to(root) or output.is_relative_to(eels):
        parser.error("generated evidence must be outside the repository and EELS checkout")
    rng = random.Random(256)
    modulus, half = 2**256, 2**255
    unsigned = [0, 1, half - 1, half, half + 1, modulus - 1, modulus, modulus + 1]
    unsigned += [rng.getrandbits(257) for _ in range(64)]
    signed = [-half - 1, -half, -half + 1, -1, 0, 1, half - 1, half, half + 1]
    signed += [rng.getrandbits(256) - half for _ in range(64)]
    guards = ["import STFSpec.Base", "open STFSpec.Base"]
    failures = {"unsigned": 0, "signed": 0}
    for n in unsigned:
        try:
            word = U256(n)
        except OverflowError:
            failures["unsigned"] += 1
            guards.append(f"#guard U256.ofNat? {n} = none")
        else:
            guards.append(f"#guard (U256.ofNat? {n}).map U256.toNat = some {int(word)}")
            guards.append(
                f"#guard (U256.ofNat? {n}).map U256.toInt = some {lean_int(word.to_signed())}"
            )
        # The wrapping helper's oracle is the checked library constructor after masking;
        # ofNat's modular model is separately proved by U256.toNat_ofNat.
        wrapped = U256(n & int(U256.MAX_VALUE))
        guards.append(f"#guard (U256.ofNat {n}).toNat = {int(wrapped)}")
        guards.append(f"#guard (U256.ofNat {n}).toInt = {lean_int(wrapped.to_signed())}")
    for i in signed:
        try:
            word = U256.from_signed(i)
        except OverflowError:
            failures["signed"] += 1
            guards.append(f"#guard U256.ofInt? {lean_int(i)} = none")
        else:
            guards.append(f"#guard (U256.ofInt? {lean_int(i)}).map U256.toNat = some {int(word)}")
            guards.append(
                f"#guard (U256.ofInt? {lean_int(i)}).map U256.toInt = "
                f"some {lean_int(word.to_signed())}"
            )
    pairs = [(unsigned[i] % modulus, unsigned[(i + 1) % len(unsigned)] % modulus)
             for i in range(len(unsigned))]
    pairs += [(0, 0), (modulus - 1, modulus - 1), (half, half - 1)]
    for a, b in pairs:
        left, right = U256(a), U256(b)
        ordering = "lt" if left < right else "gt" if left > right else "eq"
        guards.append(f"#guard compare (U256.ofNat {a}) (U256.ofNat {b}) = .{ordering}")
    for b in [False, True]:
        guards.append(f"#guard (U256.ofBool {str(b).lower()}).toNat = {int(U256(b))}")
    guards.append(f"#guard U256.max.toNat = {int(U256.MAX_VALUE)}")
    guards.append(f"#guard U256.max.toInt = {lean_int(U256.MAX_VALUE.to_signed())}")
    output.write_text(
        "-- Generated differential evidence; do not commit.\n" + "\n".join(guards) + "\n"
    )
    result = subprocess.run(["lake", "env", "lean", str(output)], cwd=root)
    print(json.dumps({"eels_commit": head, "ethereum_types": version,
                      "dependency": str(dependency), "unsigned_cases": len(unsigned),
                      "signed_cases": len(signed), "comparison_cases": len(pairs),
                      "rejected": failures, "guards": len(guards) - 2,
                      "lean_exit": result.returncode, "generated": str(output)}, sort_keys=True))
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
