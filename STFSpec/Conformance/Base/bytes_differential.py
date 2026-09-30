#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Compare padding and padded reads with actual pinned EELS functions.

Run with the pinned EELS checkout at /tmp/eels:
  /tmp/eels/.venv/bin/python -I STFSpec/Conformance/Base/bytes_differential.py \
    --eels /tmp/eels --output /tmp/bytes-differential.lean

Sources: utils/byte.py:18,40; forks/amsterdam/vm/memory.py:63,82–83
(buffer_read). CALLDATALOAD/CALLDATACOPY consume this exact helper at
vm/instructions/environment.py:177,239. memory_read_bytes (:39,60) is unpadded;
we compare it only for windows wholly inside existing memory. This driver runs
helpers, not whole opcode handlers or guest executions. Host resource/size failures
and their consumer mapping remain open. Generated observations are bug-finding
evidence, never committed normative fixtures.
"""

from pathlib import Path
import random
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "scripts"))
from differential import setup_driver


def lean_bytes(value: bytes) -> str:
    return "Bytes.ofList [" + ", ".join(str(x) for x in value) + "]"


def main():
    context = setup_driver(__doc__, __file__, 2565)
    from ethereum_types import bytes as dependency_bytes
    from ethereum_types.numeric import U256, Uint
    from ethereum.utils import byte
    from ethereum.forks.amsterdam.vm import memory
    context.check_source(dependency_bytes, "ethereum_types/bytes.py", dependency=True)
    context.check_source(byte, "ethereum/utils/byte.py")
    context.check_source(memory, "ethereum/forks/amsterdam/vm/memory.py")
    rng = random.Random(context.seed)
    values = [b"", b"\x00", b"\xff", b"\x01\x80\xff", bytes(range(21)),
              bytes(range(32)), bytes(range(256))]
    values += [rng.randbytes(rng.randrange(65)) for _ in range(32)]
    guards = ["import STFSpec.Base.Bytes", "open STFSpec.Base"]
    counts = {"leftPadZero": 0, "rightPadZero": 0, "extractPadded": 0}
    in_bounds_memory = 0
    partial_memory_distinctions = 0
    for value in values:
        source = lean_bytes(value)
        widths = sorted({0, 1, 2, 3, 20, 21, 31, 32, 33, len(value),
                         max(0, len(value) - 1), len(value) + 1, len(value) + 17})
        for width in widths:
            for name, helper in [("leftPadZero", byte.left_pad_zero_bytes),
                                 ("rightPadZero", byte.right_pad_zero_bytes)]:
                # All three supported nonnegative source parameter types are checked.
                expected = helper(value, width)
                if expected != helper(value, Uint(width)) or expected != helper(value, U256(width)):
                    raise AssertionError("padding parameter types disagree")
                guards.append(f"#guard Bytes.{name} ({source}) {width} = {lean_bytes(expected)}")
                counts[name] += 1
        starts = sorted({0, 1, 2, max(0, len(value) - 1), len(value), len(value) + 1,
                         2**64, 2**255, 2**256 - 1})
        for start in starts:
            for length in (0, 1, 2, 3, 32, 65):
                expected = memory.buffer_read(value, U256(start), U256(length))
                if len(expected) != length:
                    raise AssertionError("oracle padded result length mismatch")
                raw = memory.memory_read_bytes(bytearray(value), U256(start), U256(length))
                if start + length <= len(value):
                    if raw != expected:
                        raise AssertionError("in-bounds memory/read helper mismatch")
                    in_bounds_memory += 1
                elif length and len(raw) < length:
                    if raw == expected:
                        raise AssertionError("unpadded memory helper unexpectedly pads")
                    partial_memory_distinctions += 1
                guards.append(f"#guard Bytes.extractPadded ({source}) {start} {length} = {lean_bytes(expected)}")
                counts["extractPadded"] += 1
        for _ in range(8):
            start = rng.randrange(len(value) + 65)
            length = rng.randrange(66)
            expected = memory.buffer_read(value, U256(start), U256(length))
            guards.append(f"#guard Bytes.extractPadded ({source}) {start} {length} = {lean_bytes(expected)}")
            counts["extractPadded"] += 1
    return context.run(
        guards, operation_cases=counts,
        in_bounds_memory_read_comparisons=in_bounds_memory,
        unpadded_memory_distinctions=partial_memory_distinctions,
        padding_parameter_type_assertions=2 * (counts["leftPadZero"] + counts["rightPadZero"]),
        guest_records_executed=0)



if __name__ == "__main__":
    raise SystemExit(main())
