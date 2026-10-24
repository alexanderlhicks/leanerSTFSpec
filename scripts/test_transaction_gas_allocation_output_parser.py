#!/usr/bin/env python3
"""Closed WI302 parser regressions. Never import or invoke original EELS."""
import copy
import importlib.util
import json
from pathlib import Path
import sys

HELPER = Path(__file__).resolve().parents[1] / "STFSpec/Conformance/Vm/Core/transaction_gas_allocation_differential.py"
spec = importlib.util.spec_from_file_location("allocation_parser", HELPER)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


def frame(mode="target"):
    return module.encode_frame(module.expected_records(mode), mode)


def reject(name, reason, action):
    try:
        action()
    except module.AdmissionError as error:
        if error.reason != reason:
            raise RuntimeError(f"{name}: expected {reason}, got {error.reason}") from error
    else:
        raise RuntimeError(f"{name}: incorrectly accepted")


def main():
    positives = [lambda: module.parse_frame(frame(), "target"),
                 lambda: module.parse_frame(frame("source"), "source")]
    for value in ("0", "1", "16777216", "4294967296", "18446744073709551616",
                  "115792089237316195423570985008687907853269984665640564039457584007913129639945"):
        positives.append(lambda value=value: module.nat(value))
    for value in ("0", "1", "-1", "-31"):
        positives.append(lambda value=value: module.integer(value))
    for pair in (("0", "0"), ("5", "2"), ("7", "0"), ("1", "0"), ("0", "1")):
        positives.append(lambda pair=pair: module.allocation(dict(zip(("executionGas", "stateGasReservoir"), pair))))
    for flag in (True, False):
        positives.append(lambda flag=flag: module.boolean(flag))
    positives.extend([
        lambda: module.meter(dict(zip(module.METER_FIELDS, ("5", "2", "2", "0", "0", "0")))),
        lambda: module.success({"status": "ok", "meter": dict(zip(module.METER_FIELDS, ("2", "2", "2", "0", "0", "0"))), "phi": "2"}),
        lambda: module.failure({"status": "error", "error": "outOfGas"}),
        lambda: module.source_error({"class": "builtins.OverflowError", "message": "", "args": []}),
        lambda: module.end_record({"end": True, "count": 36}, 36),
    ])
    if len(positives) != 24:
        raise RuntimeError("positive catalog size")
    for action in positives:
        action()

    negatives = []
    for value in (0, False, 1.0, "-1", "+1", "01", " 1", ""):
        negatives.append(("Nat lexical/type", "scalar", lambda value=value: module.nat(value)))
    for value in ("-0", True, "1.0"):
        negatives.append(("Int lexical/type", "scalar", lambda value=value: module.integer(value)))
    negatives.extend([
        ("duplicate key", "json", lambda: module.parse_frame(frame().replace(b'"mode":"target"', b'"mode":"target","mode":"target"', 1), "target")),
        ("NaN", "json", lambda: module.parse_frame(frame().replace(b'"count":36', b'"count":NaN', 1), "target")),
    ])
    def mutate(index, change, mode="target"):
        rows = [json.loads(line) for line in frame(mode).splitlines()]
        change(rows[index])
        return ("\n".join(json.dumps(row, separators=(",", ":")) for row in rows) + "\n").encode()
    def add_mutation(name, reason, index, change, mode="target"):
        negatives.append((name, reason, lambda: module.parse_frame(mutate(index, change, mode), mode)))
    add_mutation("unknown key", "shape", 1, lambda r: r.update(extra="0"))
    add_mutation("missing key", "shape", 1, lambda r: r.pop("kind"))
    add_mutation("missing coordinate", "shape", 1, lambda r: r["payload"]["allocation"].pop("executionGas"))
    add_mutation("swapped coordinates", "value", 18, lambda r: r["payload"]["allocation"].update(executionGas="2", stateGasReservoir="5"))
    add_mutation("refund sign", "value", 31, lambda r: r["payload"]["meter"].update(refundCounter="-1"))
    add_mutation("committed spill", "value", 31, lambda r: r["payload"]["meter"].update(stateGasCommittedSpill="1"))
    add_mutation("unknown error", "error", 35, lambda r: r["payload"].update(error="other"))
    add_mutation("error with meter", "shape", 35, lambda r: r["payload"].update(meter=dict(zip(module.METER_FIELDS, ("0",)*6))))
    add_mutation("success with error", "shape", 33, lambda r: r["payload"].update(error="outOfGas"))
    add_mutation("wrong case", "order", 1, lambda r: r.update(id="Z01"))
    add_mutation("duplicate case", "order", 2, lambda r: r.update(id="P01"))
    def rearrange(which):
        rows = frame().splitlines(keepends=True)
        if which == "order": rows[1], rows[2] = rows[2], rows[1]
        if which == "missing": rows.pop(2)
        if which == "extra": rows.insert(2, rows[1])
        return b"".join(rows)
    for kind in ("order", "missing", "extra"):
        negatives.append((kind, "order" if kind == "order" else "count", lambda kind=kind: module.parse_frame(rearrange(kind), "target")))
    add_mutation("header version", "header", 0, lambda r: r.update(schema="v0"))
    negatives.append(("missing end", "count", lambda: module.parse_frame(b"\n".join(frame().splitlines()[:-1])+b"\n", "target")))
    add_mutation("end count", "end", 37, lambda r: r.update(count=35))
    negatives.extend([
        ("trailing", "json", lambda: module.parse_frame(frame()+b"x", "target")),
        ("truncated", "json", lambda: module.parse_frame(frame()[:-3], "target")),
        ("line limit", "line-limit", lambda: module.parse_frame(b" "*32769+b"\n", "target")),
        ("scalar limit", "scalar", lambda: module.nat("1"*1025)),
        ("frame limit", "frame-limit", lambda: module.parse_frame(b" "*262145, "target")),
    ])
    add_mutation("source numeric class", "class", 1, lambda r: r["payload"].update(numericClass="builtins.int"), "source")
    if len(negatives) != 36:
        raise RuntimeError(f"negative catalog size: {len(negatives)}")
    for index, (name, reason, action) in enumerate(negatives, 1):
        reject(f"N{index:02}: {name}", reason, action)
    if any(name == "ethereum" or name.startswith(("ethereum.", "ethereum_types")) for name in sys.modules):
        raise RuntimeError("target/parser loaded original dependency")
    print("PASS allocation parser: 24 positive, 36 negative; original imports/calls 0")


if __name__ == "__main__":
    main()
