#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Compare signed U256 operation values with the actual pinned EELS handlers.

Run with the frozen EELS venv's Python:
  EELS/.venv/bin/python -I STFSpec/Conformance/Base/u256_signed_differential.py \
    --eels EELS --output /tmp/signed-differential.lean

Sources: EELS src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py:142,205;
locked ethereum-types 0.4.1 numeric.py:594,675. A minimal funded frame supplies a
valid stack, pc and real GasMeter; handlers execute their actual pop/push, gas charge
and pc code with the discard tracer. Only word values and their checked signed
construction are compared with Lean. This is not whole-opcode or guest conformance.
Generated observations are bug-finding evidence, never normative fixtures.
Spec guidance: STFSpec/informal/modules/EthBase.md §§3–4.
"""

from pathlib import Path
import random
import sys
import itertools

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "scripts"))
from differential import setup_driver


def main():
    context = setup_driver(__doc__, __file__, 2563)
    from ethereum_types.numeric import U256
    from ethereum.forks.amsterdam.vm.instructions import arithmetic
    context.check_source(arithmetic, "ethereum/forks/amsterdam/vm/instructions/arithmetic.py")
    modulus, half = 2**256, 2**255
    bounds = [-half, -half + 1, -half // 2, -7, -3, -2, -1, 0, 1, 2, 3, 7,
              half - 2, half - 1]
    pairs = [(a % modulus, b % modulus) for a, b in itertools.product(bounds, repeat=2)]
    rng = random.Random(context.seed)
    pairs += [(rng.getrandbits(256), rng.getrandbits(256)) for _ in range(128)]
    small = [-17, -7, -3, -2, -1, 0, 1, 2, 3, 7, 17]
    pairs += [(rng.getrandbits(256), rng.choice(small) % modulus) for _ in range(64)]
    guards = ["import STFSpec.Base", "open STFSpec.Base"]
    counts = {}
    for name in ("sdiv", "smod"):
        for a, b in pairs:
            value = context.run_opcode(getattr(arithmetic, name), (a, b))
            signed = value.to_signed()
            call = f"U256.{name} (U256.ofNat {a}) (U256.ofNat {b})"
            guards.append(f"#guard ({call}).toNat = {int(value)}")
            guards.append(f"#guard ({call}).toInt = ({signed} : Int)")
            guards.append(f"#guard U256.ofInt? ({signed} : Int) = some ({call})")
        counts[name] = len(pairs)
    return context.run(guards, operation_cases=counts)


if __name__ == "__main__":
    raise SystemExit(main())
