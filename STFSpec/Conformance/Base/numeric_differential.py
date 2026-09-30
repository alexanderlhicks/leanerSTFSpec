#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Generate and run Uint.sub?/ceil32 guards against the pinned Python source.

Run with the frozen EELS venv's Python:
  EELS/.venv/bin/python STFSpec/Conformance/Base/numeric_differential.py \
    --eels EELS --output SCRATCH/numeric-differential.lean

Spec guidance: STFSpec/informal/modules/EthBase.md §§3–4. Sources are EELS
src/ethereum/utils/numeric.py:43 and locked ethereum_types/numeric.py:103,517,539.
Calls unchanged EELS ceil32 and actual Uint subtraction directly; no handler
abstraction. Generated oracle observations are uncommitted bug-finding evidence.
"""

import argparse
import importlib.metadata
import json
from pathlib import Path
import random
import subprocess
import sys
import tomllib


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
    # Keep the read-only reference checkout free of Python cache writes.
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(eels / "src"))
    from ethereum_types import numeric
    from ethereum_types.numeric import Uint
    from ethereum.utils import numeric as helpers
    dependency = Path(numeric.__file__).resolve()
    source = Path(helpers.__file__).resolve()
    if not dependency.is_relative_to(eels / ".venv"):
        parser.error("ethereum-types must be loaded from the frozen EELS venv")
    if source != eels / "src/ethereum/utils/numeric.py":
        parser.error("ceil32 must be loaded from the pinned EELS source")
    output = args.output.resolve()
    if output.is_relative_to(root) or output.is_relative_to(eels):
        parser.error("generated evidence must be outside the worktree and EELS checkout")
    rng = random.Random(4001)
    widths = [0, 1, 5, 64, 256, 512, 4096]
    boundaries = [0, 1, 31, 32, 33, 2**64 - 1, 2**64, 2**256 - 1,
                  2**256, 2**4096, 2**4096 + 33]
    pairs = [(n, m) for n in boundaries for m in boundaries]
    pairs += [(rng.getrandbits(rng.choice(widths) + rng.randrange(7)),
               rng.getrandbits(rng.choice(widths) + rng.randrange(7))) for _ in range(64)]
    for i in range(64):
        base = 2 ** rng.choice([256, 512, 4096]) + rng.getrandbits(128)
        delta = rng.randrange(1, 65)
        pairs.append((base + delta, base) if i % 2 == 0 else (base, base + delta))
    rounding = boundaries + [scale * 32 + residue
                             for scale in [0, 1, 31, 2**64, 2**256, 2**4096]
                             for residue in range(32)]
    rounding += [rng.getrandbits(rng.choice(widths) + rng.randrange(7)) for _ in range(64)]
    guards = ["import STFSpec.Base", "open STFSpec.Base"]
    rejected = 0
    for n, m in pairs:
        try:
            result = Uint(n) - Uint(m)
        except OverflowError:
            rejected += 1
            guards.append(f"#guard Uint.sub? {n} {m} = none")
        else:
            guards.append(f"#guard Uint.sub? {n} {m} = some {int(result)}")
    for n in rounding:
        result = helpers.ceil32(Uint(n))
        guards.append(f"#guard ceil32 {n} = {int(result)}")
    output.write_text(
        "-- Generated differential evidence; do not commit.\n" + "\n".join(guards) + "\n"
    )
    result = subprocess.run(["lake", "env", "lean", str(output)], cwd=root)
    max_bits = max(n.bit_length() for pair in pairs for n in pair)
    max_bits = max(max_bits, max(n.bit_length() for n in rounding))
    print(json.dumps({"eels_commit": head, "ethereum_types": version,
                      "dependency": str(dependency), "source": str(source), "seed": 4001,
                      "subtraction_cases": len(pairs), "ceil32_cases": len(rounding),
                      "underflow_rejections": rejected, "max_input_bits": max_bits,
                      "guards": len(guards) - 2, "lean_exit": result.returncode,
                      "generated": str(output)}, sort_keys=True))
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
