#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Compare U256 EXP values with the actual pinned EELS EXP handler.

Run with the pinned EELS checkout at /tmp/eels:
  /tmp/eels/.venv/bin/python -I STFSpec/Conformance/Base/u256_exp_differential.py \
    --eels /tmp/eels --output /tmp/u256-exp-differential.lean

Source: src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py:297,326;
locked ethereum-types 0.4.1 supplies unsigned conversions. The unchanged handler
executes pop/push, charging and PC code using a real funded GasMeter and discard
tracer. Adapter assertions check those oracle effects; only result values and
checked word construction are compared with Lean. This does not establish Lean
opcode failure/effect or guest conformance. Generated observations are bug-finding evidence, never normative fixtures.
Spec guidance: STFSpec/informal/modules/EthBase.md §§3–4.
"""

import itertools
from pathlib import Path
import random
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "scripts"))
from differential import setup_driver


def main():
    context = setup_driver(__doc__, __file__, 2564)
    from ethereum_types.numeric import U256
    from ethereum.forks.amsterdam.vm import gas
    from ethereum.forks.amsterdam.vm.instructions import arithmetic
    context.check_source(arithmetic, "ethereum/forks/amsterdam/vm/instructions/arithmetic.py")
    context.check_source(gas, "ethereum/forks/amsterdam/vm/gas.py")
    modulus, half = 2**256, 2**255
    bases = [0, 1, 2, 3, 7, 255, 256, 2**128 - 1, 2**128, 2**128 + 1,
             half - 1, half, half + 1, modulus - 1]
    exponents = [0, 1, 2, 3, 7, 8, 254, 255, 256, 257, 2**128, half,
                 modulus - 2, modulus - 1]
    pairs = list(itertools.product(bases, exponents))
    rng = random.Random(context.seed)
    pairs += [(rng.getrandbits(256), rng.getrandbits(256)) for _ in range(128)]
    pairs += [(rng.getrandbits(256), rng.randrange(258)) for _ in range(64)]
    for bit in range(256):
        pairs.extend([(3, 1 << bit), (modulus - 1, (1 << bit) - 1)])
    guards = ["import STFSpec.Base", "open STFSpec.Base"]
    for a, b in pairs:
        charge = int(gas.GasCosts.OPCODE_EXP_BASE) + (
            int(gas.GasCosts.OPCODE_EXP_PER_BYTE) * ((b.bit_length() + 7) // 8))
        value = int(context.run_opcode(arithmetic.exp, [a, b], cost=charge))
        call = f"U256.exp (U256.ofNat {a}) (U256.ofNat {b})"
        guards.append(f"#guard ({call}).toNat = {value}")
        guards.append(f"#guard U256.ofNat? {value} = some ({call})")
    return context.run(guards, operation_cases={"exp": len(pairs)})


if __name__ == "__main__":
    raise SystemExit(main())
