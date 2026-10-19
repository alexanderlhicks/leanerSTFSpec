#!/usr/bin/env python3
"""Complete padded-buffer frames and source-independent public-import observations.

Reproduce from the repository root with fresh output paths:
  DRIVER=STFSpec/Conformance/Vm/Core/buffer_read_differential.py
  python3 -B "$DRIVER" --self-test
  python3 -B -O "$DRIVER" --self-test
  python3 -B "$DRIVER" --emit-lean > /tmp/Buffer.lean
  lake env lean --run /tmp/Buffer.lean > /tmp/buffer.ndjson
  python3 -B "$DRIVER" --check-frames /tmp/buffer.ndjson
  python3 -B -O "$DRIVER" --check-frames /tmp/buffer.ndjson

The emitter defines main; plain Lean without --run produces no observations.
This comparator has no source mode and imports no external oracle.
"""
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys

PIN = "e1a316a06fc3d3e0a5da36fdc78580811e9d8a36"
CONTROL_SHA256 = "e65112fae1e815306c339208666e2dbb2b508726d09716de47a1f0fa4a9b0e71"
CATALOG = {
  "status": "PREPARE literal planned expectations; no target or source execution",
  "date": "2026-10-17",
  "eels_pin": "e1a316a06fc3d3e0a5da36fdc78580811e9d8a36",
  "cases": [
    {
      "id": "empty-zero",
      "input_hex": "",
      "start": 0,
      "size": 0,
      "output_hex": ""
    },
    {
      "id": "empty-one",
      "input_hex": "",
      "start": 0,
      "size": 1,
      "output_hex": "00"
    },
    {
      "id": "empty-four",
      "input_hex": "",
      "start": 1,
      "size": 4,
      "output_hex": "00000000"
    },
    {
      "id": "empty-huge-zero",
      "input_hex": "",
      "start": 115792089237316195423570985008687907853269984665640564039457584007913129639935,
      "size": 0,
      "output_hex": ""
    },
    {
      "id": "one-zero-byte",
      "input_hex": "00",
      "start": 0,
      "size": 1,
      "output_hex": "00"
    },
    {
      "id": "one-high-byte",
      "input_hex": "ff",
      "start": 0,
      "size": 1,
      "output_hex": "ff"
    },
    {
      "id": "one-high-tail",
      "input_hex": "ff",
      "start": 0,
      "size": 4,
      "output_hex": "ff000000"
    },
    {
      "id": "one-exact-end",
      "input_hex": "ff",
      "start": 1,
      "size": 1,
      "output_hex": "00"
    },
    {
      "id": "zero-prefix",
      "input_hex": "00017f80ff",
      "start": 0,
      "size": 2,
      "output_hex": "0001"
    },
    {
      "id": "whole-mixed",
      "input_hex": "00017f80ff",
      "start": 0,
      "size": 5,
      "output_hex": "00017f80ff"
    },
    {
      "id": "contained-mixed",
      "input_hex": "00017f80ff",
      "start": 1,
      "size": 3,
      "output_hex": "017f80"
    },
    {
      "id": "contained-high-end",
      "input_hex": "00017f80ff",
      "start": 3,
      "size": 2,
      "output_hex": "80ff"
    },
    {
      "id": "partial-last-byte",
      "input_hex": "00017f80ff",
      "start": 4,
      "size": 4,
      "output_hex": "ff000000"
    },
    {
      "id": "partial-two-bytes",
      "input_hex": "00017f80ff",
      "start": 3,
      "size": 4,
      "output_hex": "80ff0000"
    },
    {
      "id": "whole-plus-zero",
      "input_hex": "00017f80ff",
      "start": 0,
      "size": 6,
      "output_hex": "00017f80ff00"
    },
    {
      "id": "exact-end-padding",
      "input_hex": "00017f80ff",
      "start": 5,
      "size": 4,
      "output_hex": "00000000"
    },
    {
      "id": "beyond-end-padding",
      "input_hex": "00017f80ff",
      "start": 6,
      "size": 4,
      "output_hex": "00000000"
    },
    {
      "id": "zero-inside",
      "input_hex": "00017f80ff",
      "start": 2,
      "size": 0,
      "output_hex": ""
    },
    {
      "id": "zero-at-end",
      "input_hex": "00017f80ff",
      "start": 5,
      "size": 0,
      "output_hex": ""
    },
    {
      "id": "zero-beyond-end",
      "input_hex": "00017f80ff",
      "start": 9,
      "size": 0,
      "output_hex": ""
    },
    {
      "id": "interior-zero",
      "input_hex": "ff008001",
      "start": 0,
      "size": 4,
      "output_hex": "ff008001"
    },
    {
      "id": "interior-zero-window",
      "input_hex": "ff008001",
      "start": 1,
      "size": 2,
      "output_hex": "0080"
    },
    {
      "id": "u64-before",
      "input_hex": "00017f80ff",
      "start": 18446744073709551615,
      "size": 4,
      "output_hex": "00000000"
    },
    {
      "id": "u64-at",
      "input_hex": "00017f80ff",
      "start": 18446744073709551616,
      "size": 4,
      "output_hex": "00000000"
    },
    {
      "id": "u64-after",
      "input_hex": "00017f80ff",
      "start": 18446744073709551617,
      "size": 4,
      "output_hex": "00000000"
    },
    {
      "id": "u64-after-nonzero-prefix",
      "input_hex": "ff008001",
      "start": 18446744073709551617,
      "size": 2,
      "output_hex": "0000"
    },
    {
      "id": "u256-max-zero",
      "input_hex": "ff008001",
      "start": 115792089237316195423570985008687907853269984665640564039457584007913129639935,
      "size": 0,
      "output_hex": ""
    },
    {
      "id": "u256-max-one",
      "input_hex": "ff008001",
      "start": 115792089237316195423570985008687907853269984665640564039457584007913129639935,
      "size": 1,
      "output_hex": "00"
    },
    {
      "id": "u256-max-three",
      "input_hex": "ff008001",
      "start": 115792089237316195423570985008687907853269984665640564039457584007913129639935,
      "size": 3,
      "output_hex": "000000"
    },
    {
      "id": "word-full",
      "input_hex": "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "start": 0,
      "size": 32,
      "output_hex": "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
    },
    {
      "id": "word-last-high-tail",
      "input_hex": "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e80",
      "start": 30,
      "size": 4,
      "output_hex": "1e800000"
    },
    {
      "id": "word-plus-one",
      "input_hex": "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "start": 0,
      "size": 33,
      "output_hex": "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f00"
    }
  ]
}
ROW_FIELDS = {"kind", "id", "input_hex", "start", "size", "output_hex", "output_size"}


class FrameError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise FrameError(message)


def pairs(items):
    result = {}
    for key, value in items:
        require(key not in result, "duplicate JSON key: " + key)
        result[key] = value
    return result


def bad_constant(value):
    raise FrameError("non-JSON numeric constant: " + value)


def load(text):
    return json.loads(text, object_pairs_hook=pairs, parse_constant=bad_constant)


def integer(value):
    return type(value) is int and value >= 0


def whole_hex(value):
    return (type(value) is str and len(value) % 2 == 0 and
            all(c in "0123456789abcdef" for c in value))


def catalog(path=None):
    if path is None:
        obj = copy.deepcopy(CATALOG)
    else:
        raw = path.read_bytes()
        require(hashlib.sha256(raw).hexdigest() == CONTROL_SHA256, "changed frozen controls")
        obj = load(raw.decode("utf-8"))
    require(type(obj) is dict and set(obj) == {"status", "date", "eels_pin", "cases"},
            "control schema")
    require(obj["eels_pin"] == PIN and type(obj["cases"]) is list, "control pin/list")
    cases = obj["cases"]
    require(len(cases) == 32, "control count")
    ids = set()
    for row in cases:
        require(type(row) is dict and set(row) ==
                {"id", "input_hex", "start", "size", "output_hex"}, "control fields")
        require(type(row["id"]) is str and row["id"] and row["id"] not in ids, "control id")
        ids.add(row["id"])
        require(integer(row["start"]) and row["start"] < 2**256, "control start")
        require(integer(row["size"]) and row["size"] <= 33, "control width")
        require(whole_hex(row["input_hex"]) and whole_hex(row["output_hex"]), "control hex")
        require(len(row["output_hex"]) == 2 * row["size"], "control output width")
    return cases


def frames_from_literals(cases):
    """Format preexisting literals; this computes no semantic expected output."""
    return ([{"kind": "begin", "version": 1, "count": len(cases)}] +
            [dict(row, kind="buffer_read", output_size=len(row["output_hex"]) // 2)
             for row in cases] +
            [{"kind": "end", "version": 1, "count": len(cases)}])


def stream(rows):
    return "".join(json.dumps(row, separators=(",", ":")) + "\n" for row in rows)


def parse_frames(text, cases):
    require(type(text) is str and text.endswith("\n"), "missing final newline")
    lines = text.split("\n")
    require(lines[-1] == "" and len(lines) == len(cases) + 3, "frame row count/trailing data")
    rows = [load(line) for line in lines[:-1]]
    for index, kind in [(0, "begin"), (len(rows) - 1, "end")]:
        row = rows[index]
        require(type(row) is dict and set(row) == {"kind", "version", "count"}, "marker fields")
        require(row["kind"] == kind and type(row["version"]) is int and row["version"] == 1,
                "marker kind/version")
        require(type(row["count"]) is int and row["count"] == len(cases), "marker count")
    ids = set()
    for index in range(len(cases)):
        row, expected = rows[index + 1], cases[index]
        require(type(row) is dict and set(row) == ROW_FIELDS, "result row fields")
        require(row["kind"] == "buffer_read", "result kind")
        require(type(row["id"]) is str and row["id"] not in ids and
                row["id"] == expected["id"], "result id/order")
        ids.add(row["id"])
        for field in ["start", "size", "output_size"]:
            require(integer(row[field]), "result integer: " + field)
        require(whole_hex(row["input_hex"]) and whole_hex(row["output_hex"]), "result hex")
        require(len(row["output_hex"]) == 2 * row["output_size"], "result byte length")
        require(row["output_size"] == expected["size"], "requested output width")
        for field in ["id", "input_hex", "start", "size", "output_hex"]:
            require(row[field] == expected[field], "whole result differs: " + field)
    return rows


def self_test(cases):
    rows = frames_from_literals(cases)
    good = stream(rows)
    parse_frames(good, cases)
    bad = ["", good[:-1], good[:-2], good + "\n", good + good, good + "{}\n",
           good.replace('"version":1', '"version":1,"version":1', 1),
           good.replace('"start":0', '"start":0,"start":0', 1),
           good.replace('"start":0', '"start":NaN', 1)]

    def mutate(index, field, value, remove=False):
        changed = copy.deepcopy(rows)
        if remove:
            del changed[index][field]
        else:
            changed[index][field] = value
        bad.append(stream(changed))

    for index in [0, len(rows) - 1]:
        for field in ["version", "count"]:
            for value in [True, False, 1.0, -1, "1", None]:
                mutate(index, field, value)
        mutate(index, "extra", 0)
        mutate(index, "kind", "wrong")
        mutate(index, "kind", None, remove=True)
    for field in ["start", "size", "output_size"]:
        for value in [True, False, 0.0, -1, "0", None]:
            mutate(1, field, value)
    for field in ROW_FIELDS:
        mutate(1, field, None, remove=True)
    mutate(1, "extra", 0)
    mutate(1, "id", rows[2]["id"])
    mutate(1, "id", "unknown")
    mutate(1, "kind", "wrong")
    mutate(1, "start", 1)
    mutate(1, "size", 1)
    mutate(1, "output_size", 1)
    mutate(1, "input_hex", "00")
    for field in ["input_hex", "output_hex"]:
        for value in ["0", "gg", "AA", " 00", "0x00", [], False]:
            mutate(1, field, value)
    changed = copy.deepcopy(rows)
    changed[1], changed[2] = changed[2], changed[1]
    bad.append(stream(changed))
    bad.append(stream(rows[:1] + rows[2:]))
    bad.append(stream(rows[:1] + [rows[1]] + rows[1:]))
    for case_id in ["whole-mixed", "word-full"]:
        index = next(i for i, row in enumerate(rows) if row.get("id") == case_id)
        value = rows[index]["output_hex"]
        middle = (len(value) // 4) * 2
        replacement = "ff" if value[middle:middle + 2] != "ff" else "00"
        mutate(index, "output_hex", value[:middle] + replacement + value[middle + 2:])
    rejected = 0
    for text in bad:
        try:
            parse_frames(text, cases)
        except (FrameError, json.JSONDecodeError, UnicodeError):
            rejected += 1
        else:
            raise FrameError("parser accepted mutation " + str(rejected))
    print(json.dumps({"status": "strict parser controls passed", "rejected": rejected,
                      "optimize": sys.flags.optimize, "literal_cases": len(cases)}))


def lean_bytes(hexadecimal):
    return "[" + ", ".join(str(b) for b in bytes.fromhex(hexadecimal)) + "]"


def emit_lean(cases):
    """Emit public-import observations; every output is computed by actual bufferRead."""
    print("""/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Vm.Core
import Lean
open STFSpec.Vm.Core STFSpec.Base Lean

private def digit (n : Nat) : Char :=
  Char.ofNat (if n < 10 then 48 + n else 87 + n)

private def hex (b : Bytes) : String :=
  String.ofList (b.toList.flatMap fun byte ↦
    [digit (byte.toNat / 16), digit (byte.toNat % 16)])

private def observe (id : String) (input : List UInt8) (s k : Nat) : Json :=
  let b := Bytes.ofList input
  let start := U256.ofNat s
  let size := U256.ofNat k
  let result := bufferRead b start size
  Json.mkObj [("kind", toJson "buffer_read"), ("id", toJson id),
    ("input_hex", toJson (hex b)), ("start", toJson start.toNat),
    ("size", toJson size.toNat), ("output_hex", toJson (hex result)),
    ("output_size", toJson result.size)]

def main : IO Unit := do""")
    begin = '{"kind":"begin","version":1,"count":' + str(len(cases)) + '}'
    print("  IO.println " + json.dumps(begin))
    for row in cases:
        print("  IO.println ((observe " + json.dumps(row["id"]) + " " +
              lean_bytes(row["input_hex"]) + " " + str(row["start"]) + " " +
              str(row["size"]) + ").compress)")
    end = '{"kind":"end","version":1,"count":' + str(len(cases)) + '}'
    print("  IO.println " + json.dumps(end))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--controls", type=Path, help="optional exact frozen catalog override")
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--self-test", action="store_true")
    modes.add_argument("--emit-lean", action="store_true")
    modes.add_argument("--check-frames", type=Path)
    args = parser.parse_args()
    cases = catalog(args.controls)
    if args.self_test:
        self_test(cases)
    elif args.emit_lean:
        emit_lean(cases)
    else:
        parse_frames(args.check_frames.read_text(), cases)
        print(json.dumps({"status": "complete literal frames agree", "cases": len(cases),
                          "optimize": sys.flags.optimize}))


if __name__ == "__main__":
    main()
