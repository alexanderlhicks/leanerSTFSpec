#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Generate and run Uint.sub?/ceil32 guards against the pinned Python source.

Run with the frozen EELS venv's Python:
  EELS/.venv/bin/python -I STFSpec/Conformance/Base/numeric_differential.py \
    --eels EELS --output /tmp/numeric-differential.lean

Spec guidance: STFSpec/informal/modules/EthBase.md §§3–4. Sources are EELS
src/ethereum/utils/numeric.py:43 and locked ethereum_types/numeric.py:103,517,539.
Calls unchanged EELS ceil32 and actual Uint subtraction directly; no handler
abstraction. Generated oracle observations are uncommitted bug-finding evidence.
"""

from pathlib import Path
import random
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "scripts"))
from differential import setup_driver


def main():
    context = setup_driver(__doc__, __file__, 4001)
    from ethereum_types.numeric import Uint
    from ethereum.utils import numeric as helpers
    source = context.check_source(helpers, "ethereum/utils/numeric.py")
    rng = random.Random(context.seed)
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
    max_bits = max(n.bit_length() for pair in pairs for n in pair)
    max_bits = max(max_bits, max(n.bit_length() for n in rounding))
    return context.run(guards, source=str(source), subtraction_cases=len(pairs),
                       ceil32_cases=len(rounding), underflow_rejections=rejected,
                       max_input_bits=max_bits)


if __name__ == "__main__":
    raise SystemExit(main())
