#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Compare unsigned U256 arithmetic with pinned EELS handlers and ethereum-types.

Run with the pinned EELS checkout at /tmp/eels:
  /tmp/eels/.venv/bin/python -I STFSpec/Conformance/Base/u256_arithmetic_differential.py \
    --eels /tmp/eels --output /tmp/u256-arithmetic-differential.lean

Spec guidance: STFSpec/informal/modules/EthBase.md §§3–4. The seven EVM handlers
are imported unchanged from the pinned arithmetic.py. A minimal frame adapter supplies
only stack, pc and the actual GasMeter, with sufficient gas and default discarded tracing;
real stack pop/push and charge_gas execute. Frame construction and gas/stack failure paths
are outside this value comparison. Checked operations invoke the actual locked
ethereum-types Python operators. Generated observations are uncommitted bug-finding
evidence, never normative fixtures or a whole-guest conformance claim.
"""

from pathlib import Path
import random
import sys
import itertools
import operator

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "scripts"))
from differential import setup_driver


def main():
    context = setup_driver(__doc__, __file__, 2562)
    from ethereum_types.numeric import U256
    from ethereum.forks.amsterdam.vm.gas import GasCosts
    from ethereum.forks.amsterdam.vm.instructions import arithmetic
    source = context.check_source(arithmetic, "ethereum/forks/amsterdam/vm/instructions/arithmetic.py")
    rng = random.Random(context.seed)
    modulus, half = 2**256, 2**255
    boundaries = [0, 1, 2, 12, half - 1, half, half + 1, modulus - 1]
    pairs = list(itertools.product(boundaries, repeat=2))
    pairs += [(2**128, 2**128), (2**128 - 1, 2**128 + 1)]
    pairs += [(rng.getrandbits(256), rng.getrandbits(256)) for _ in range(64)]
    triples = [(a, b, boundaries[i % len(boundaries)]) for i, (a, b) in enumerate(pairs)]
    triples += [(modulus - 1, 1, modulus - 1), (modulus - 1, modulus - 1, 12)]
    triples += [(rng.getrandbits(256), rng.getrandbits(256), rng.getrandbits(256))
                for _ in range(64)]
    guards = ["import STFSpec.Base", "open STFSpec.Base"]
    evm_ops = ["add", "sub", "mul", "div", "mod", "addmod", "mulmod"]
    checked_ops = {"checkedAdd": operator.add, "checkedSub": operator.sub,
                   "checkedMul": operator.mul, "checkedDiv": operator.floordiv,
                   "checkedMod": operator.mod}
    failures = {name: {} for name in checked_ops}
    counts = {name: 0 for name in evm_ops + list(checked_ops)}
    for name in evm_ops:
        cases = triples if name in {"addmod", "mulmod"} else pairs
        for values in cases:
            cost = int(getattr(GasCosts, "OPCODE_" + name.upper()))
            value = context.run_opcode(getattr(arithmetic, name), values, cost=cost)
            args_lean = " ".join(f"(U256.ofNat {n})" for n in values)
            guards.append(f"#guard (U256.{name} {args_lean}).toNat = {int(value)}")
            counts[name] += 1
    for name, operation in checked_ops.items():
        for a, b in pairs:
            args_lean = f"(U256.ofNat {a}) (U256.ofNat {b})"
            try:
                value = operation(U256(a), U256(b))
            except (OverflowError, ZeroDivisionError) as failure:
                kind = type(failure).__name__
                failures[name][kind] = failures[name].get(kind, 0) + 1
                guards.append(f"#guard U256.{name} {args_lean} = none")
            else:
                guards.append(
                    f"#guard (U256.{name} {args_lean}).map U256.toNat = some {int(value)}"
                )
            counts[name] += 1
    return context.run(guards, source=str(source), executed=counts, rejected=failures)


if __name__ == "__main__":
    raise SystemExit(main())
