#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Run public U256 guards generated from actual pinned EELS opcode handlers.

Invoke with the frozen EELS venv's Python:
  EELS/.venv/bin/python STFSpec/Conformance/Base/u256_bitwise_differential.py \
    --eels EELS --output /tmp/u256-bitwise-differential.lean

A SimpleNamespace supplies a valid stack, pc and funded gas meter. The actual
handlers execute their own stack, gas and pc code, with the default discard tracer.
Only resulting operation values are compared: this is not a claim about Lean
opcode gas, stack faults, tracing, pc behavior, or guest/EEST conformance.
The generated observations are scratch bug-finding evidence, never committed
normative values. Spec guidance: STFSpec/informal/modules/EthBase.md §§3–4.
"""

import argparse
import importlib.metadata
import json
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
    from ethereum.forks.amsterdam.vm import ExecutionGas
    from ethereum.forks.amsterdam.vm.instructions import arithmetic, bitwise, comparison
    from ethereum.trace import discard_evm_trace, set_evm_trace
    if not Path(numeric.__file__).resolve().is_relative_to(eels / ".venv"):
        parser.error("ethereum-types must be loaded from the frozen EELS venv")
    for module in (arithmetic, bitwise, comparison):
        if not Path(module.__file__).resolve().is_relative_to(eels / "src"):
            parser.error("instruction modules must be loaded from the pinned checkout")
    output = args.output.resolve()
    if output.is_relative_to(root) or output.is_relative_to(eels):
        parser.error("generated evidence must be outside the repository and EELS checkout")
    rng = random.Random(7939)
    modulus, half = 2**256, 2**255
    bounds = [0, 1, half - 1, half, half + 1, modulus - 1, 0x7f, 0x80]
    words = bounds + [rng.getrandbits(256) for _ in range(64)]
    pairs = [(a, b) for a in bounds for b in bounds]
    pairs += [(rng.getrandbits(256), rng.getrandbits(256)) for _ in range(64)]
    shifts = [(s, x) for s in [0, 1, 7, 8, 127, 128, 254, 255, 256, 257, half, modulus - 1]
              for x in bounds]
    shifts += [(rng.randrange(258), rng.getrandbits(256)) for _ in range(64)]
    shifts += [(rng.getrandbits(256), rng.getrandbits(256)) for _ in range(16)]
    # Every byte/sign index, endpoint sign bits, and huge word indices.
    byte_pairs = [(i, x) for i in [*range(34), half, modulus - 1] for x in bounds]
    byte_pairs += [(i, int.from_bytes(bytes(range(32)), "big")) for i in range(32)]
    byte_pairs += [(rng.randrange(34), rng.getrandbits(256)) for _ in range(64)]
    sign_pairs = [(i, x) for i in [*range(34), half, modulus - 1] for x in bounds]
    for i in range(32):
        sign = 1 << (8 * (i + 1) - 1)
        sign_pairs += [(i, sign - 1), (i, sign), (i, sign + 1)]
    sign_pairs += [(rng.randrange(34), rng.getrandbits(256)) for _ in range(64)]
    guards = ["import STFSpec.Base", "open STFSpec.Base"]
    counts = {}
    set_evm_trace(discard_evm_trace)

    def run(name, handler, cases):
        for operands in cases:
            # pop order is first argument first, whereas stack storage has top at the end.
            frame = SimpleNamespace(stack=[U256(x) for x in reversed(operands)],
                                    pc=Uint(0), gas_meter=SimpleNamespace(
                                        gas_left=ExecutionGas(Uint(100000))))
            handler(frame)
            if len(frame.stack) != 1:
                raise AssertionError("handler did not produce one result")
            expected = int(frame.stack[0])
            args_lean = " ".join(f"(U256.ofNat {x})" for x in operands)
            guards.append(f"#guard (U256.{name} {args_lean}).toNat = {expected}")
        counts[name] = len(cases)

    for name, handler in [("lt", comparison.less_than), ("gt", comparison.greater_than),
                          ("slt", comparison.signed_less_than),
                          ("sgt", comparison.signed_greater_than), ("eq", comparison.equal),
                          ("and", bitwise.bitwise_and), ("or", bitwise.bitwise_or),
                          ("xor", bitwise.bitwise_xor)]:
        run(name, handler, pairs)
    for name, handler in [("iszero", comparison.is_zero), ("not", bitwise.bitwise_not),
                          ("clz", bitwise.count_leading_zeros)]:
        run(name, handler, [(x,) for x in words])
    for name, handler in [("shl", bitwise.bitwise_shl), ("shr", bitwise.bitwise_shr),
                          ("sar", bitwise.bitwise_sar)]:
        run(name, handler, shifts)
    run("byte", bitwise.get_byte, byte_pairs)
    run("signextend", arithmetic.signextend, sign_pairs)
    for a, b in pairs:
        left, right = U256(a), U256(b)
        for name, expected in [("ult", left < right), ("ule", left <= right),
                               ("slt'", left.to_signed() < right.to_signed())]:
            guards.append(f"#guard U256.{name} (U256.ofNat {a}) (U256.ofNat {b}) = "
                          f"{str(expected).lower()}")
    for x in words:
        guards.append(f"#guard U256.bitLength (U256.ofNat {x}) = {int(U256(x).bit_length())}")
    counts.update({"ult": len(pairs), "ule": len(pairs), "slt'": len(pairs),
                   "bitLength": len(words)})
    output.write_text("-- Generated differential evidence; do not commit.\n" +
                      "\n".join(guards) + "\n")
    result = subprocess.run(["lake", "env", "lean", str(output)], cwd=root)
    print(json.dumps({"eels_commit": head, "ethereum_types": version, "seed": 7939,
                      "operation_cases": counts, "guards": len(guards) - 2,
                      "lean_exit": result.returncode, "generated": str(output)}, sort_keys=True))
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
