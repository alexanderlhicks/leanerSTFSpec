#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Compare integer byte APIs with locked ethereum-types and actual EELS masking.

Run with the pinned EELS checkout at /tmp/eels:
  /tmp/eels/.venv/bin/python -I STFSpec/Conformance/Base/integer_bytes_differential.py \
    --eels /tmp/eels --output /tmp/integer-bytes.lean
Generated evidence must be outside both repositories. Reference caches are bypassed.
Spec guidance: STFSpec/informal/modules/EthBase.md §§3–4.
"""

from pathlib import Path
import random
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "scripts"))
from differential import setup_driver


def main():
    context = setup_driver(__doc__, __file__, 5003)
    from ethereum_types.numeric import U256, U64, Uint
    from ethereum.forks.amsterdam.utils import address
    context.check_source(address, "ethereum/forks/amsterdam/utils/address.py")
    rng = random.Random(context.seed)
    guards = ["import STFSpec.Base", "open STFSpec.Base"]
    counts = {"fixed_outputs": 0, "minimal_outputs": 0, "bounded_decodes": 0,
              "unbounded_decodes": 0, "uint_fixed32_outputs": 0, "masked_addresses": 0,
              "length_rejections": 0, "output_overflows": 0}

    def lean_bytes(data):
        return f"(Bytes.ofList ({list(data)} : List UInt8))"

    for cls, width in [(U256, 32), (U64, 8)]:
        values = sorted({0, 1, 255, 256, 2**(8*width)-1,
                         *[min(2**(8*width)-1, 2**bit+delta)
                           for bit in range(0, 8*width, 8) for delta in [-1, 0, 1]],
                         *[rng.getrandbits(8*width) for _ in range(48)]})
        for n in values:
            x = cls(n)
            for endian in ["be", "le"]:
                result = getattr(x, f"to_{endian}_bytes{width}")()
                operation = f"{cls.__name__}.to{endian.title()}Bytes{width}"
                guards.append(f"#guard Bytes.toList ({operation} "
                              f"({cls.__name__}.ofNat {n})).toBytes = {list(result)}")
                counts["fixed_outputs"] += 1
            guards.append(f"#guard Bytes.toList ({cls.__name__}.toBeBytes "
                          f"({cls.__name__}.ofNat {n})) = {list(x.to_be_bytes())}")
            counts["minimal_outputs"] += 1
            if cls is U256:
                result = address.to_address_masked(x)
                guards.append(f"#guard Bytes.toList (Address.ofU256Masked "
                              f"(U256.ofNat {n})).toBytes = {list(result)}")
                counts["masked_addresses"] += 1
        for length in sorted({0, 1, width-1, width, width+1, width+2, 64, 65}):
            arrays = [bytes(length), bytes([255])*length,
                      bytes(rng.randrange(256) for _ in range(length)),
                      bytes(length-1)+b"\x01" if length else b""]
            for data in arrays:
                for endian in (["be", "le"] if cls is U64 else ["be"]):
                    try:
                        result = getattr(cls, f"from_{endian}_bytes")(data)
                    except ValueError:
                        expected = "none"
                        counts["length_rejections"] += 1
                    else:
                        expected = f"some {int(result)}"
                    guards.append(f"#guard ({cls.__name__}.of{endian.title()}Bytes? "
                                  f"{lean_bytes(data)}).map {cls.__name__}.toNat = {expected}")
                    counts["bounded_decodes"] += 1
    values = sorted({0, 1, 255, 256, 2**64-1, 2**64, 2**256-1, 2**256, 2**4096,
                     *[rng.getrandbits(rng.choice([8, 64, 256, 512, 4096]))
                       for _ in range(48)]})
    for n in values:
        x = Uint(n)
        guards.append(f"#guard Bytes.toList (Uint.toBeBytes {n}) = {list(x.to_be_bytes())}")
        counts["minimal_outputs"] += 1
        try:
            result = x.to_be_bytes32()
        except OverflowError:
            expected = "none"
            counts["output_overflows"] += 1
        else:
            expected = f"some {list(result)}"
        guards.append(f"#guard (Uint.toBeBytes32? {n}).map "
                      f"(fun x ↦ Bytes.toList x.toBytes) = {expected}")
        counts["uint_fixed32_outputs"] += 1
    for length in [0, 1, 7, 8, 9, 31, 32, 33, 64, 65, 256, 512]:
        for data in [bytes(length), bytes([255])*length,
                     bytes(rng.randrange(256) for _ in range(length))]:
            for endian in ["be", "le"]:
                result = getattr(Uint, f"from_{endian}_bytes")(data)
                guards.append(f"#guard Uint.of{endian.title()}Bytes "
                              f"{lean_bytes(data)} = {int(result)}")
                counts["unbounded_decodes"] += 1
    return context.run(guards, counts=counts, oracle_sources=context.oracle_blobs,
                       dependency_sources=context.dependency_sources(),
                       dependency_record=str(context.dependency_record))


if __name__ == "__main__":
    raise SystemExit(main())
