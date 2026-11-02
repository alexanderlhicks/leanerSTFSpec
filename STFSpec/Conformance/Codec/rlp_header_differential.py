#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Bounded cursor RLP item-length observations against locked ethereum-rlp 0.1.6.

Run EELS/.venv/bin/python -I -B with --eels EELS --output SCRATCH/observations.lean.
The shared driver authenticates pinned EELS/lock and ethereum-types. RlpSourceAuth
and RlpFreshFinder authenticate RECORD/current source/origins and bypass cached code.
Success must be an exact plain int; failure must be the exact DecodingError class.
Interpreter, frozen installation/startup and RECORD remain trusted inputs. These
finite header observations do not establish raw decoding, host-depth or guest claims.
"""
from pathlib import Path
import hashlib
import random
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
from rlp_typed_differential import setup_driver, RlpSourceAuth, RlpFreshFinder


def require_input(data, pos):
    """Exact bytes and nonnegative plain integer cursor, before source invocation."""
    if type(data) is not bytes or type(pos) is not int or pos < 0:
        raise TypeError("expected exact bytes and nonnegative plain int cursor")


def require_observation(value):
    """Validate the entire observation before generating a Lean expression."""
    if type(value) is not tuple or len(value) != 2 or type(value[0]) is not str:
        raise TypeError("expected exact tagged observation tuple")
    kind, result = value
    if kind == "ok":
        if type(result) is not int or result <= 0:
            raise TypeError("item-length success must be a positive exact plain int")
    elif kind == "error":
        if result is not None:
            raise TypeError("DecodingError observation has no result")
    else:
        raise TypeError("unknown observation kind")


def lean_observation(value):
    """All diagnostics map to the source's single DecodingError failure channel."""
    require_observation(value)
    return "none" if value[0] == "error" else f"some {value[1]}"


def main():
    context = setup_driver(__doc__, __file__, 5024)
    if not sys.flags.isolated or not sys.flags.dont_write_bytecode:
        context.parser.error("use the frozen interpreter -I -B")
    if any(name.split(".", 1)[0] == "ethereum_rlp" for name in sys.modules):
        raise ImportError("ethereum_rlp imported before authentication")
    auth = RlpSourceAuth(context)
    sys.meta_path.insert(0, RlpFreshFinder(auth))
    from ethereum_rlp import rlp
    context.check_source(rlp, "ethereum_rlp/rlp.py", dependency=True)
    rng = random.Random(context.seed)
    guards = ["import STFSpec.Codec", "open STFSpec.Codec STFSpec.Codec.Rlp STFSpec.Base"]
    counts = {"source_calls": 0, "accepted": 0, "rejected": 0,
              "all_tags": 0, "long_fields": 0, "random_cursors": 0,
              "conceptual_offsets": 0, "domain_negative_controls": 0}
    for data, pos in [(bytearray(), 0), (b"", True), (b"", 0.0), (b"", -1)]:
        try:
            require_input(data, pos)
        except TypeError:
            counts["domain_negative_controls"] += 1
        else:
            raise AssertionError("input domain negative control accepted")
    for value in [True, 1, 1.0, None, ["ok", 1], (True, 1), ("ok", True),
                  ("ok", 1.0), ("ok", 0), ("ok", -1), ("error", False), ("bad", 1)]:
        try:
            lean_observation(value)
        except TypeError:
            counts["domain_negative_controls"] += 1
        else:
            raise AssertionError("observation domain negative control accepted")

    def observe(data, pos=0):
        require_input(data, pos)
        counts["source_calls"] += 1
        try:
            value = rlp.decode_item_length(data[pos:])
        except rlp.DecodingError as error:
            if type(error) is not rlp.DecodingError:
                raise TypeError("unexpected DecodingError subclass") from error
            result = ("error", None)
            counts["rejected"] += 1
        else:
            result = ("ok", value)
            counts["accepted"] += 1
        expected = lean_observation(result)
        literal = f"(ByteArray.mk ({list(data)} : List UInt8).toArray)"
        guards.append(f"#guard (decodeItemLength {literal} {pos}).toOption = {expected}")

    observe(b"")
    for tag in range(256):
        observe(bytes([tag]))
        observe(bytes([tag, 1, 2, 3, 4, 5, 6, 7, 8, 99]))
        counts["all_tags"] += 1
    for base in [183, 247]:
        for width in range(1, 9):
            tag = base + width
            fields = [bytes([1]) + bytes(width - 1), bytes([255]) * width,
                      bytes(range(1, width + 1)), bytes(width)]
            if width == 1:
                fields += [b"\x01", b"\x05", b"\x37", b"\x38"]
            for digits in fields:
                for suffix in [b"", b"\x00", b"\x7f\x80\xc0"]:
                    observe(bytes([tag]) + digits + suffix)
                    observe(b"\xff\x00" + bytes([tag]) + digits + suffix, 2)
                    counts["long_fields"] += 2
            for available in range(width):
                # Truncation must precede the simultaneous zero-first-digit condition.
                observe(bytes([tag]) + bytes(available))
                counts["long_fields"] += 1
    for data in [b"\x81\x05", b"\xc1", b"\x05\x06", b"\xc0\x00",
                 b"\xb8\x05", b"\xf8\x05", b"\xbf" + b"\xff" * 8]:
        observe(data)
    for _ in range(256):
        data = bytes(rng.randrange(256) for _ in range(rng.randrange(25)))
        pos = rng.randrange(len(data) + 3)
        observe(data, pos)
        counts["random_cursors"] += 1
    for pos in [2**64, 2**128, 2**256 + 1]:
        observe(b"\xb8\x01", pos)
        counts["conceptual_offsets"] += 1
    auth.check()
    result = context.run(guards, counts=counts, ethereum_rlp="0.1.6",
                         rlp_sources={str(p): h for p, h in auth.expected.items()},
                         rlp_record_sha256=hashlib.sha256(auth.record_bytes).hexdigest(),
                         domain="bounded exact bytes/nonnegative plain int cursors; header observations only")
    auth.check()
    return result


if __name__ == "__main__":
    raise SystemExit(main())
