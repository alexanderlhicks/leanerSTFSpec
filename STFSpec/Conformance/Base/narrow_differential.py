#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Compare narrow unsigned values with locked ethereum-types 0.4.1.

Run with the pinned EELS virtual environment's Python:
  EELS/.venv/bin/python STFSpec/Conformance/Base/narrow_differential.py \
    --eels EELS --output SCRATCH/narrow-differential.lean

Sources: ethereum_types/numeric.py:44,91,103,131,321,325,357,364,611,614,625,636;
width classes/constants at :716,738–739,743,765–766,770,792–793,797,819–820. Invoke actual checked
constructors/operators, wrapping methods, equality and unsigned comparisons.
Generated oracle observations are uncommitted bug-finding evidence, not fixtures.
Spec guidance: STFSpec/informal/modules/EthBase.md §§3–4.
"""

import itertools
import operator
from pathlib import Path
import random
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "scripts"))
from differential import setup_driver


def main():
    context = setup_driver(__doc__, __file__, 4002)
    from ethereum_types import numeric
    guards = ["import STFSpec.Base", "open STFSpec.Base"]
    counts = {}
    rejected = {}
    seed = context.seed
    for width in (8, 16, 32, 64):
        name = f"U{width}"
        cls = getattr(numeric, name)
        modulus = 2**width
        bounds = [0, 1, 2, modulus // 2 - 1, modulus // 2,
                  modulus // 2 + 1, modulus - 2, modulus - 1]
        rng = random.Random(seed + width)
        constructors = bounds + [modulus, modulus + 1, 2 * modulus - 1,
                                  2**4096, 2**4096 + 17]
        constructors += [rng.getrandbits(rng.choice([width - 1, width, width + 1, 512]))
                         for _ in range(64)]
        pairs = list(itertools.product(bounds, repeat=2))
        pairs += [(rng.getrandbits(width), rng.getrandbits(width)) for _ in range(128)]
        counts[name] = {"constructors": len(constructors), "pairs": len(pairs)}
        rejected[name] = {"ofNat?": 0, "checkedAdd": 0, "checkedSub": 0, "checkedMul": 0}
        guards.append(f"#guard {name}.max.toNat = {int(cls.MAX_VALUE)}")
        for n in constructors:
            # The source constructor is checked; mask only for the separate wrapping model.
            wrapped = cls(n & int(cls.MAX_VALUE))
            guards.append(f"#guard ({name}.ofNat {n}).toNat = {int(wrapped)}")
            guards.append(f"#guard ({name}.ofNat {n}).toBitVec.toNat = {int(wrapped)}")
            try:
                value = cls(n)
            except OverflowError:
                rejected[name]["ofNat?"] += 1
                guards.append(f"#guard {name}.ofNat? {n} = none")
            else:
                guards.append(f"#guard ({name}.ofNat? {n}).map {name}.toNat = some {int(value)}")
        for a, b in pairs:
            left, right = cls(a), cls(b)
            for lean_name, method in (("wrappingAdd", "wrapping_add"),
                                      ("wrappingSub", "wrapping_sub"),
                                      ("wrappingMul", "wrapping_mul")):
                value = getattr(left, method)(right)
                call = f"{name}.{lean_name} ({name}.ofNat {a}) ({name}.ofNat {b})"
                guards.append(f"#guard ({call}).toNat = {int(value)}")
            for lean_name, operation in (("checkedAdd", operator.add),
                                         ("checkedSub", operator.sub),
                                         ("checkedMul", operator.mul)):
                call = f"{name}.{lean_name} ({name}.ofNat {a}) ({name}.ofNat {b})"
                try:
                    value = operation(left, right)
                except OverflowError:
                    rejected[name][lean_name] += 1
                    guards.append(f"#guard {call} = none")
                else:
                    guards.append(f"#guard ({call}).map {name}.toNat = some {int(value)}")
            ordering = ".lt" if left < right else ".gt" if left > right else ".eq"
            guards.append(f"#guard compare ({name}.ofNat {a}) ({name}.ofNat {b}) = {ordering}")
            equal = "true" if left == right else "false"
            guards.append(f"#guard decide (({name}.ofNat {a}) = ({name}.ofNat {b})) = {equal}")
    return context.run(guards, cases=counts, rejections=rejected)


if __name__ == "__main__":
    raise SystemExit(main())
