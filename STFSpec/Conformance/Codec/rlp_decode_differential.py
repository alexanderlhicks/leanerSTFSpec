#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Bounded raw RLP decoding against authenticated locked ethereum-rlp 0.1.6.

Use EELS/.venv/bin/python -I -B --eels EELS --output SCRATCH/observations.lean.
The shared loader verifies current source/origins/RECORD and bypasses .pyc.
Success is recursively exact bytes/list, checked before any observation. Failures
must be exact DecodingError. The first authenticated source raise line determines
the Lean diagnostic, retaining precedence when several conditions fail together.
Other exceptions, including RecursionError, are not protocol rejection evidence.
Interpreter/startup/frozen installation/RECORD remain trust inputs. This bounded
corpus establishes no universal canonicality, Python/host-depth or guest theorem.
"""
from pathlib import Path
import hashlib
import random
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
from rlp_typed_differential import setup_driver, RlpSourceAuth, RlpFreshFinder
from rlp_encode_differential import require_model, require_bytes, lean_bytes, lean_item


# Actual raise sites in authenticated rlp.py, not an independent reject parser.
DIAGNOSTICS = {
    149: (".empty", ("Cannot decode empty bytestring",)),
    397: ('(.nonCanonical "negative length")', ("negative length",)),
    399: (".truncated", ("truncated",)),
    401: (".trailing", ("trailing bytes",)),
    404: ('(.nonCanonical "prefixed single byte")', ()),
    411: (".truncated", ("truncated",)),
    413: ('(.nonCanonical "leading zero length")', ()),
    418: ('(.nonCanonical "long form for short payload")', ()),
    421: (".truncated", ("truncated",)),
    423: (".trailing", ("trailing bytes",)),
    435: (".truncated", ("truncated",)),
    437: (".trailing", ("trailing bytes",)),
    442: (".truncated", ("truncated",)),
    444: ('(.nonCanonical "leading zero length")', ()),
    449: ('(.nonCanonical "long form for short payload")', ()),
    454: (".truncated", ("truncated",)),
    456: (".trailing", ("trailing bytes",)),
    477: (".truncated", ("truncated",)),
    520: (".truncated", ("truncated",)),
    522: ('(.nonCanonical "leading zero length")', ()),
    536: (".truncated", ("truncated",)),
    538: ('(.nonCanonical "leading zero length")', ()),
}

# Manual structural recursion: no nested deriving and no re-encoding-only comparison.
LEAN_HELPERS = """open STFSpec.Codec STFSpec.Codec.Rlp STFSpec.Base
mutual
  private def sameItem : RlpItem → RlpItem → Bool
    | .bytes a, .bytes b => decide (a = b)
    | .list xs, .list ys => sameItems xs ys
    | _, _ => false
  private def sameItems : List RlpItem → List RlpItem → Bool
    | [], [] => true
    | x :: xs, y :: ys => sameItem x y && sameItems xs ys
    | _, _ => false
end
private def sameResult : Except RlpError RlpItem → Except RlpError RlpItem → Bool
  | .ok x, .ok y => sameItem x y
  | .error e, .error f => decide (e = f)
  | _, _ => false"""


def main():
    context = setup_driver(__doc__, __file__, 5025)
    if not sys.flags.isolated or not sys.flags.dont_write_bytecode:
        context.parser.error("use the frozen interpreter -I -B")
    if any(name.split(".", 1)[0] == "ethereum_rlp" for name in sys.modules):
        raise ImportError("ethereum_rlp imported before authentication")
    auth = RlpSourceAuth(context)
    sys.meta_path.insert(0, RlpFreshFinder(auth))
    from ethereum_rlp import rlp
    context.check_source(rlp, "ethereum_rlp/rlp.py", dependency=True)
    source = str(Path(rlp.__file__).resolve())
    counts = {"inputs": 0, "accepted": 0, "rejected": 0,
              "all_tags": 0, "mutations": 0, "negative_controls": 0}
    raises = {}
    guards = ["import STFSpec.Codec", LEAN_HELPERS]
    rng = random.Random(context.seed)

    class BytesSubclass(bytes):
        pass

    class ListSubclass(list):
        pass

    for wrong in [True, 0, bytearray(b"x"), memoryview(b"x"), BytesSubclass(b"x")]:
        try:
            require_bytes(wrong)
        except TypeError:
            counts["negative_controls"] += 1
        else:
            raise AssertionError("wire exact-class control accepted")
    for wrong in [False, 1, bytearray(b"x"), memoryview(b"x"), [False], (b"",),
                  BytesSubclass(b"x"), ListSubclass([]), [ListSubclass([])]]:
        try:
            require_model(wrong)
        except TypeError:
            counts["negative_controls"] += 1
        else:
            raise AssertionError("result exact recursive-class control accepted")

    def observe(data):
        require_bytes(data)
        events = []

        def trace(frame, event, arg):
            if event == "exception" and frame.f_code.co_filename == source:
                exception_type, exception, _ = arg
                if exception_type is rlp.DecodingError:
                    events.append((frame.f_lineno, exception))
            return trace

        if sys.gettrace() is not None:
            raise RuntimeError("an existing trace would invalidate raise-site evidence")
        sys.settrace(trace)
        try:
            value = rlp.decode(data)
        except rlp.DecodingError as error:
            if type(error) is not rlp.DecodingError:
                raise TypeError("unexpected DecodingError subclass") from error
            if not events or events[0][1] is not error:
                raise AssertionError("missing authenticated first raise event") from error
            line = events[0][0]
            diagnostic, args = DIAGNOSTICS[line]
            if type(error.args) is not tuple or error.args != args:
                raise AssertionError("unexpected source diagnostic payload") from error
            raises[str(line)] = raises.get(str(line), 0) + 1
            expected = f"(.error {diagnostic})"
            counts["rejected"] += 1
        else:
            require_model(value)
            expected = f"(.ok {lean_item(value)})"
            counts["accepted"] += 1
        finally:
            sys.settrace(None)
        guards.append(f"#guard sameResult (decode {lean_bytes(data)}) {expected}")
        counts["inputs"] += 1

    for data in [b"", b"\x00", b"\x7f", b"\x80", b"\x81", b"\xff", b"\x81\x05",
                 b"\x05\x06", b"\xc0\x00", b"\xc1", b"\xc2\x82\x00",
                 b"\xc3\x81\x00", b"\xc2\x81\x00\x00", b"\xc4\x81\x00\x81\x00",
                 b"\xc4\x00\x81\x00\x81", b"\xc2\xb8\x05",
                 b"\xc7\xb8\x05" + bytes(5), b"\xc3\xb9\x00\x38",
                 b"\xc1\xb8", b"\xc1\xf8", b"\xc3\xf9\x00\x38"]:
        observe(data)
    for tag in range(256):
        observe(bytes([tag]))
        observe(bytes([tag, 0, 1, 2]))
        counts["all_tags"] += 1
    for base in [183, 247]:
        for width in range(1, 9):
            tag = base + width
            for available in range(width):
                observe(bytes([tag]) + bytes(available))
            for digits in [bytes(width), bytes([1]) + bytes(width - 1), bytes([255]) * width]:
                observe(bytes([tag]) + digits)
                observe(bytes([tag]) + digits + b"\x00")
    models = [b"", b"\x00", b"\x7f", b"\x80", [], [b""], [[]],
              [b"\x00", b"", [b"\x80", [], b"\x00\x01"], b"\xff"]]
    for width in [2, 3, 31, 32, 54, 55, 56, 57, 127, 128, 254, 255, 256, 257, 1024]:
        models.append(bytes(rng.randrange(256) for _ in range(width)))
    for width in [0, 1, 54, 55, 56, 57, 255, 256, 512]:
        models.append([b""] * width)
    for depth in [1, 2, 8, 24, 32]:
        value = b"\x00\x80\x01"
        for _ in range(depth):
            value = [value]
        models.append(value)

    def sample(depth):
        if depth == 0 or rng.randrange(4) == 0:
            return bytes(rng.randrange(256) for _ in range(rng.choice([0, 1, 2, 55, 56, 255, 256])))
        return [sample(depth - 1) for _ in range(rng.randrange(4))]

    models.extend(sample(rng.randrange(1, 5)) for _ in range(80))
    for model in models:
        require_model(model)
        data = rlp.encode(model)
        require_bytes(data)
        observe(data)
        observe(data + b"\x00")
        observe(data[:-1])
        if data:
            changed = bytearray(data)
            changed[rng.randrange(len(changed))] ^= 1 << rng.randrange(8)
            observe(bytes(changed))
            counts["mutations"] += 1
    for _ in range(128):
        observe(bytes(rng.randrange(256) for _ in range(rng.randrange(13))))
    auth.check()
    result = context.run(guards, counts=counts, raise_sites=raises,
                         python_recursion_limit=sys.getrecursionlimit(), ethereum_rlp="0.1.6",
                         rlp_sources={str(p): h for p, h in auth.expected.items()},
                         rlp_record_sha256=hashlib.sha256(auth.record_bytes).hexdigest(),
                         domain="bounded exact bytes and recursively exact bytes/list results; source raise-site diagnostics")
    auth.check()
    return result


if __name__ == "__main__":
    raise SystemExit(main())
