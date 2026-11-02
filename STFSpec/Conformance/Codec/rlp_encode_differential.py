#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Bounded raw RLP encoding observations against locked ethereum-rlp 0.1.6.

Run EELS/.venv/bin/python -I -B with --eels EELS --output SCRATCH/observations.lean.
Reuse the typed driver's authenticated current-source loader and trusted RECORD
checks. Inputs are exactly bytes or nested exact lists of those bytes, plus the
fixed 22-case Nat handoff through exact source Uint. Results must be exact bytes,
before any Lean observation is emitted. Interpreter, startup,
frozen installation and RECORD remain trust inputs. No huge/deep host claim follows.
"""
from pathlib import Path
import hashlib
import random
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
from rlp_typed_differential import setup_driver, RlpSourceAuth, RlpFreshFinder


def require_model(value):
    """Exact raw model classes; bool/int/bytearray/subclasses are outside this probe."""
    if type(value) is bytes:
        return
    if type(value) is not list:
        raise TypeError("raw RLP observation input must be exact bytes or list")
    for child in value:
        require_model(child)


def require_bytes(value):
    """Python equality cannot distinguish bool/int or bytes-like return classes."""
    if type(value) is not bytes:
        raise TypeError("raw RLP encoder returned a non-bytes result")


def require_nat(value):
    """Only exact nonnegative Python integers enter the Nat-to-Uint handoff."""
    if type(value) is not int or value < 0:
        raise TypeError("Nat observation requires an exact nonnegative int")


def require_uint(value, uint_class):
    """Require the original authenticated Uint class before oracle encoding."""
    if type(value) is not uint_class:
        raise TypeError("Nat encoding requires exact source Uint")


def lean_list(value):
    """Keep the same bytes while bounding literal depth and repeated numeral work."""
    chunks, literal = [], []

    def flush():
        if literal:
            chunks.append(str(literal))
            literal.clear()

    i = 0
    while i < len(value):
        end = i + 1
        while end < len(value) and value[end] == value[i]:
            end += 1
        if end - i >= 4:
            flush()
            chunks.append(f"(List.replicate {end-i} ({value[i]} : UInt8))")
        else:
            for byte in value[i:end]:
                literal.append(byte)
                if len(literal) == 256:
                    flush()
        i = end
    flush()
    return "(" + " ++ ".join(chunks or ["[]"]) + ")"


def lean_bytes(value):
    require_bytes(value)
    return f"(ByteArray.mk ({lean_list(value)} : List UInt8).toArray)"


def lean_item(value):
    if type(value) is bytes:
        return f"(RlpItem.bytes {lean_bytes(value)})"
    return f"(RlpItem.list [{', '.join(map(lean_item, value))}])"


def main():
    context = setup_driver(__doc__, __file__, 5023)
    if not sys.flags.isolated or not sys.flags.dont_write_bytecode:
        context.parser.error("use the frozen interpreter -I -B")
    if any(name.split(".", 1)[0] == "ethereum_rlp" for name in sys.modules):
        raise ImportError("ethereum_rlp imported before authentication")
    auth = RlpSourceAuth(context)
    sys.meta_path.insert(0, RlpFreshFinder(auth))
    from ethereum_rlp import rlp
    from ethereum_types.numeric import Uint, U64
    from ethereum_types import numeric
    context.check_source(rlp, "ethereum_rlp/rlp.py", dependency=True)
    source_uint, source_encode = Uint, rlp.encode
    rng = random.Random(context.seed)
    guards = ["import STFSpec.Codec", "open STFSpec.Codec STFSpec.Codec.Rlp STFSpec.Base"]
    counts = {"items": 0, "bytes": 0, "list_payloads": 0, "integers": 0,
              "shape_negative_controls": 0, "nat_negative_controls": 0,
              "typed_integer_encodings": 0}
    for wrong in [True, 1, bytearray(b"x"), memoryview(b"x"), [False], (b"x",)]:
        try:
            require_model(wrong)
        except TypeError:
            counts["shape_negative_controls"] += 1
        else:
            raise AssertionError("model exact-type negative control accepted")
    for wrong in [True, 1, bytearray(b"x"), memoryview(b"x"), [120]]:
        try:
            require_bytes(wrong)
        except TypeError:
            counts["shape_negative_controls"] += 1
        else:
            raise AssertionError("result exact-type negative control accepted")
    for wrong in [True, -1, 1.0, "1", b"1", Uint(1), U64(1)]:
        try:
            require_nat(wrong)
        except TypeError:
            counts["nat_negative_controls"] += 1
        else:
            raise AssertionError("Nat input negative control accepted")
    for wrong in [True, -1, 1, 1.0, "1", b"1", U64(1)]:
        try:
            require_uint(wrong, source_uint)
        except TypeError:
            counts["nat_negative_controls"] += 1
        else:
            raise AssertionError("Uint input negative control accepted")

    def observe(value):
        require_model(value)
        result = rlp.encode(value)
        require_bytes(result)
        guards.append(f"#guard encode {lean_item(value)} = {lean_bytes(result)}")
        counts["items"] += 1
        if type(value) is bytes:
            direct = rlp.encode_bytes(value)
            require_bytes(direct)
            if direct != result:
                raise AssertionError("encode dispatch and encode_bytes disagree")
            guards.append(f"#guard encodeBytes {lean_bytes(value)} = {lean_bytes(direct)}")
            counts["bytes"] += 1
        else:
            direct = rlp.encode_sequence(value)
            payload = rlp.join_encodings(value)
            require_bytes(direct)
            require_bytes(payload)
            if direct != result:
                raise AssertionError("encode dispatch and encode_sequence disagree")
            guards.append(f"#guard encodePayloadModel [{', '.join(map(lean_item, value))}] = {lean_list(payload)}")
            counts["list_payloads"] += 1

    for value in [b"", b"\x00", b"\x7f", b"\x80", b"\xff", [], [b""], [[]],
                  [b"\x00", b"", [b"\x80", [], b"\x01\x00"], b"\xff"]]:
        observe(value)
    for width in [2, 3, 31, 32, 54, 55, 56, 57, 127, 128, 254, 255, 256, 257, 1024]:
        observe(bytes(rng.randrange(256) for _ in range(width)))
    for width in [0, 1, 54, 55, 56, 57, 255, 256]:
        observe([b""] * width)
    for width in [53, 54, 55]:
        observe([bytes(width)])
    for depth in [1, 2, 8, 24, 32]:
        value = b"\x00\x80\x01"
        for _ in range(depth):
            value = [value]
        observe(value)
    observe([bytes([i])*300 for i in range(16)])

    def sample(depth):
        if depth == 0 or rng.randrange(4) == 0:
            width = rng.choice([0, 1, 2, 3, 31, 55, 56, 57, 255, 256])
            return bytes(rng.randrange(256) for _ in range(width))
        return [sample(depth-1) for _ in range(rng.randrange(4))]

    for _ in range(100):
        observe(sample(rng.randrange(1, 6)))
    for n in [0, 1, 2, 127, 128, 129, 255, 256, 257, 1024, 0x01000203,
              2**64-1, 2**64, 2**64+1, 2**256-1, 2**256, 2**256+1,
              2**(8*54)+0x010003, 2**(8*55)+0x010003,
              2**(8*254)+0x010003, 2**(8*255)+0x010003, 2**(8*256)+0x010003]:
        require_nat(n)
        if (Uint is not source_uint or numeric.Uint is not source_uint or
                rlp.Uint is not source_uint or rlp.encode is not source_encode):
            raise AssertionError("authenticated Uint/encode identity changed")
        value = source_uint(n)
        require_uint(value, source_uint)
        result = source_encode(value)
        require_bytes(result)
        guards.append(f"#guard encode (ofNat {n}) = {lean_bytes(result)}")
        guards.append(f"#guard encodeOf ({n} : Nat) = {lean_bytes(result)}")
        counts["integers"] += 1
        counts["typed_integer_encodings"] += 1
    if (Uint is not source_uint or numeric.Uint is not source_uint or
            rlp.Uint is not source_uint or rlp.encode is not source_encode):
        raise AssertionError("authenticated Uint/encode identity changed")
    auth.check()
    result = context.run(guards, counts=counts, ethereum_rlp="0.1.6",
                         rlp_sources={str(p): h for p, h in auth.expected.items()},
                         rlp_record_sha256=hashlib.sha256(auth.record_bytes).hexdigest(),
                         domain="bounded exact raw bytes/list trees and 22 exact Uint/Nat encodings")
    auth.check()
    return result


if __name__ == "__main__":
    raise SystemExit(main())
