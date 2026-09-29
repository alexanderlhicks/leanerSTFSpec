#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Compare unsigned U256 arithmetic with pinned EELS handlers and ethereum-types.

Run with the frozen EELS venv's Python:
  EELS/.venv/bin/python STFSpec/Conformance/Base/u256_arithmetic_differential.py \
    --eels EELS --output /tmp/u256-arithmetic-differential.lean

Spec guidance: STFSpec/informal/modules/EthBase.md §§3–4. The seven EVM handlers
are imported unchanged from the pinned arithmetic.py. A minimal frame adapter supplies
only stack, pc and the actual GasMeter, with sufficient gas and default discarded tracing;
real stack pop/push and charge_gas execute. Frame construction and gas/stack failure paths
are outside this value-slice comparison. Checked operations invoke the actual locked
ethereum-types Python operators. Generated observations are uncommitted bug-finding
evidence, never normative fixtures or a whole-guest conformance claim.
"""

import argparse
import importlib.metadata
import itertools
import json
import operator
from pathlib import Path
import random
import subprocess
import sys
import tomllib
from types import SimpleNamespace


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
    sys.path.insert(0, str(eels / "src"))
    from ethereum_types import numeric
    from ethereum_types.numeric import U256, Uint
    from ethereum.forks.amsterdam.fork_types import ExecutionGas, StateGas
    from ethereum.forks.amsterdam.vm.gas import GasCosts, GasMeter
    from ethereum.forks.amsterdam.vm.instructions import arithmetic
    dependency = Path(numeric.__file__).resolve()
    if not dependency.is_relative_to(eels / ".venv"):
        parser.error("ethereum-types must be loaded from the frozen EELS venv")
    source = Path(arithmetic.__file__).resolve()
    if source != eels / "src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py":
        parser.error("opcode handlers must be loaded from the pinned EELS checkout")
    output = args.output.resolve()
    if output.is_relative_to(root) or output.is_relative_to(eels):
        parser.error("generated evidence must be outside the repository and EELS checkout")
    rng = random.Random(2562)
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
            gas_before = 100000
            frame = SimpleNamespace(
                stack=[U256(n) for n in reversed(values)], pc=Uint(0),
                gas_meter=GasMeter(ExecutionGas(Uint(gas_before)),
                                   StateGas(Uint(0)), StateGas(Uint(0)))
            )
            getattr(arithmetic, name)(frame)
            cost = int(getattr(GasCosts, "OPCODE_" + name.upper()))
            assert len(frame.stack) == 1 and frame.pc == Uint(1)
            assert int(frame.gas_meter.gas_left) == gas_before - cost
            args_lean = " ".join(f"(U256.ofNat {n})" for n in values)
            guards.append(f"#guard (U256.{name} {args_lean}).toNat = {int(frame.stack[0])}")
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
    output.write_text(
        "-- Generated differential evidence; do not commit.\n" + "\n".join(guards) + "\n"
    )
    result = subprocess.run(["lake", "env", "lean", str(output)], cwd=root)
    print(json.dumps({"eels_commit": head, "ethereum_types": version,
                      "source": str(source), "dependency": str(dependency), "seed": 2562,
                      "executed": counts, "rejected": failures, "guards": len(guards) - 2,
                      "lean_exit": result.returncode, "generated": str(output)}, sort_keys=True))
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
