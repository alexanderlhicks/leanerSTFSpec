#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Compare nested and combined shifts with actual pinned EELS handlers.

Run with EELS/.venv/bin/python -I and --eels EELS --output /tmp/u256-shift.lean.
Only operation values are compared; no Lean opcode effects or guest conformance
are claimed. Generated observations must stay outside both repositories.
Spec guidance: STFSpec/informal/modules/EthBase.md §§3–4.
"""

from pathlib import Path
import random
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "scripts"))
from differential import setup_driver


def main():
    context = setup_driver(__doc__, __file__, 3003)
    from ethereum_types.numeric import U256
    from ethereum.forks.amsterdam.vm import gas
    from ethereum.forks.amsterdam.vm.instructions import bitwise
    context.check_source(bitwise, "ethereum/forks/amsterdam/vm/instructions/bitwise.py")
    context.check_source(gas, "ethereum/forks/amsterdam/vm/gas.py")
    modulus, half = 2**256, 2**255
    rng = random.Random(context.seed)
    words = [0, 1, half - 1, half, half + 1, modulus - 3, modulus - 1, 0xaa55aa55]
    amounts = [(0, 0), (0, 1), (1, 0), (0, 255), (255, 0), (1, 254),
               (254, 1), (127, 128), (128, 127)]
    cases = [(s, t, v) for s, t in amounts for v in words]
    for _ in range(128):
        s = rng.randrange(256)
        cases.append((s, rng.randrange(256 - s), rng.getrandbits(256)))
    # Saturation still composes; wrapping amounts are counterexamples.
    outside = [(1, 255), (255, 1), (256, 0), (0, 256), (modulus - 1, 1),
               (1, modulus - 1), (half, half), (modulus - 1, modulus - 1)]
    cases += [(s, t, v) for s, t in outside for v in words]
    guards = ["import STFSpec.Base", "open STFSpec.Base"]
    counts = {}
    for name, handler in [("shl", bitwise.bitwise_shl), ("shr", bitwise.bitwise_shr),
                          ("sar", bitwise.bitwise_sar)]:
        differences = 0
        for s, t, v in cases:
            first = context.run_opcode(handler, [s, v])
            nested_value = int(context.run_opcode(handler, [t, int(first)]))
            combined_amount = U256(s).wrapping_add(U256(t))
            combined_value = int(context.run_opcode(handler, [int(combined_amount), v]))
            if s + t < modulus and nested_value != combined_value:
                raise AssertionError("pinned handlers violate the nonwrapping sum equation")
            differences += nested_value != combined_value
            a, b, x = (f"(U256.ofNat {n})" for n in (s, t, v))
            guards.append(f"#guard (U256.{name} {b} (U256.{name} {a} {x})).toNat = "
                          f"{nested_value}")
            guards.append(f"#guard (U256.{name} (U256.add {a} {b}) {x}).toNat = "
                          f"{combined_value}")
        counts[name] = {"sequences": len(cases), "outside_premise_differences": differences}
    return context.run(guards, operation_cases=counts,
        nonwrapping_cases_per_operation=sum(s + t < modulus for s, t, _ in cases),
        wrapping_cases_per_operation=sum(s + t >= modulus for s, t, _ in cases))


if __name__ == "__main__":
    raise SystemExit(main())
