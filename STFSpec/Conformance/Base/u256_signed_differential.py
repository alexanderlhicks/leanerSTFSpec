#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Compare signed U256 operation values with the actual pinned EELS handlers.

Run with the frozen EELS venv's Python:
  EELS/.venv/bin/python STFSpec/Conformance/Base/u256_signed_differential.py \
    --eels EELS --output <ignored-evidence>/signed-differential.lean

Sources: EELS src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py:142,205;
locked ethereum-types 0.4.1 numeric.py:594,675. A minimal funded frame supplies a
valid stack, pc and real GasMeter; handlers execute their actual pop/push, gas charge
and pc code with the discard tracer. Only word values and their checked signed
construction are compared with Lean. This is not whole-opcode or guest conformance.
Generated observations are scratch bug-finding evidence, never normative fixtures.
Spec guidance: STFSpec/informal/modules/EthBase.md §§3–4.
"""

import argparse
import importlib.metadata
import itertools
import json
from pathlib import Path
import random
import subprocess
import sys
import tomllib
from types import SimpleNamespace

# Keep the pinned source and frozen dependency environment read-only.
sys.dont_write_bytecode = True


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
    if subprocess.run(["git", "diff", "--quiet", "HEAD", "--", "src/ethereum", "uv.lock"],
                      cwd=eels).returncode:
        parser.error("EELS source or lock has tracked changes from the pin")
    version = importlib.metadata.version("ethereum-types")
    if version != pin["python_dependencies"]["ethereum-types"]:
        parser.error("ethereum-types version does not match reference.toml")
    sys.path.insert(0, str(eels / "src"))
    from ethereum_types import numeric
    from ethereum_types.numeric import U256, Uint
    from ethereum.forks.amsterdam.fork_types import ExecutionGas, StateGas
    from ethereum.forks.amsterdam.vm.gas import GasMeter
    from ethereum.forks.amsterdam.vm.instructions import arithmetic
    from ethereum.trace import discard_evm_trace, set_evm_trace
    if not Path(numeric.__file__).resolve().is_relative_to(eels / ".venv"):
        parser.error("ethereum-types must be loaded from the frozen EELS venv")
    if not Path(arithmetic.__file__).resolve().is_relative_to(eels / "src"):
        parser.error("arithmetic handlers must be loaded from the pinned checkout")
    output = args.output.resolve()
    if output.is_relative_to(root) or output.is_relative_to(eels):
        parser.error("generated evidence must be outside the worktree and EELS checkout")
    modulus, half = 2**256, 2**255
    bounds = [-half, -half + 1, -half // 2, -7, -3, -2, -1, 0, 1, 2, 3, 7,
              half - 2, half - 1]
    pairs = [(a % modulus, b % modulus) for a, b in itertools.product(bounds, repeat=2)]
    rng = random.Random(2563)
    pairs += [(rng.getrandbits(256), rng.getrandbits(256)) for _ in range(128)]
    small = [-17, -7, -3, -2, -1, 0, 1, 2, 3, 7, 17]
    pairs += [(rng.getrandbits(256), rng.choice(small) % modulus) for _ in range(64)]
    guards = ["import STFSpec.Base", "open STFSpec.Base"]
    counts = {}
    set_evm_trace(discard_evm_trace)
    for name in ("sdiv", "smod"):
        for a, b in pairs:
            frame = SimpleNamespace(
                stack=[U256(b), U256(a)], pc=Uint(0),
                gas_meter=GasMeter(ExecutionGas(Uint(100000)),
                                   StateGas(Uint(0)), StateGas(Uint(0))))
            getattr(arithmetic, name)(frame)
            if len(frame.stack) != 1:
                raise AssertionError("handler did not return one word")
            value = frame.stack[0]
            signed = value.to_signed()
            call = f"U256.{name} (U256.ofNat {a}) (U256.ofNat {b})"
            guards.append(f"#guard ({call}).toNat = {int(value)}")
            guards.append(f"#guard ({call}).toInt = ({signed} : Int)")
            guards.append(f"#guard U256.ofInt? ({signed} : Int) = some ({call})")
        counts[name] = len(pairs)
    output.write_text("-- Generated differential evidence; do not commit.\n" +
                      "\n".join(guards) + "\n")
    result = subprocess.run(["lake", "env", "lean", str(output)], cwd=root)
    print(json.dumps({"eels_commit": head, "ethereum_types": version, "seed": 2563,
                      "operation_cases": counts, "guards": len(guards) - 2,
                      "lean_exit": result.returncode, "generated": str(output)}, sort_keys=True))
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
