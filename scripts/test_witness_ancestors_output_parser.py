#!/usr/bin/env python3
"""Frozen complete-output controls, including nullable Nat/bool distinctions."""

import copy
import importlib.util
import json
from pathlib import Path
import sys

path = (Path(__file__).resolve().parents[1]
        / "STFSpec/Conformance/State/witness_ancestors_differential.py")
spec = importlib.util.spec_from_file_location("ancestors_reader", path)
reader = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reader)


def encode(rows):
    return ("\n".join(json.dumps(row, separators=(",", ":")) for row in rows) + "\n").encode()


def fixtures():
    rows = reader.expected_frames()
    good = encode(rows)
    yield "complete", good, True
    yield "no-final-newline", good[:-1], True
    for name, data in [
        ("empty", b""), ("missing", encode(rows[:-1])),
        ("extra", good + b"{}\n"), ("blank", good + b"\n"),
        ("truncated", good[:-3]), ("oversize", b" " * 1048577),
        ("duplicate-key", good.replace(b'"offset":null', b'"offset":null,"offset":null', 1)),
        ("nonfinite", good.replace(b'"offset":null', b'"offset":NaN', 1)),
    ]:
        yield name, data, False

    def change(index, field, value, delete=False):
        changed = copy.deepcopy(rows)
        if delete:
            del changed[index][field]
        else:
            changed[index][field] = value
        return encode(changed)

    for index in [0, 1, 2, 3, 6, 7, 9, 17, 27, 47]:
        # None, zero, one, two and huge values must never normalize across types.
        for name, bad in [("false", False), ("true", True), ("floatzero", 0.0),
                          ("floatone", 1.0), ("null", None), ("negative", -1),
                          ("string", "0"), ("array", [])]:
            if type(bad) is type(rows[index]["offset"]) and bad == rows[index]["offset"]:
                continue
            yield f"offset-{index}-{name}", change(index, "offset", bad), False
    for field in ["id", "headers", "offset", "result"]:
        yield "missing-" + field, change(17, field, None, True), False
    yield "unknown", change(17, "extra", 0), False
    yield "duplicate-id", change(17, "id", rows[16]["id"]), False
    for field in ["headers", "result"]:
        for name, bad in [("null", None), ("boolean", False), ("flatten", ""),
                          ("byte-types", [0]), ("changed-byte", ["ff"])]:
            yield field + "-" + name, change(27, field, bad), False
        changed = copy.deepcopy(rows)
        changed[27][field] = list(reversed(changed[27][field]))
        yield field + "-order", encode(changed), False
        changed = copy.deepcopy(rows)
        changed[27][field] += [changed[27][field][0]]
        yield field + "-duplicate", encode(changed), False
    changed = copy.deepcopy(rows)
    changed[0], changed[1] = changed[1], changed[0]
    yield "case-order", encode(changed), False
    yield "null-versus-empty", change(0, "result", None), False
    # Single-byte change at the last byte of case 47's final (four-byte) header.
    changed = copy.deepcopy(rows)
    value = changed[47]["result"][-1]
    changed[47]["result"][-1] = value[:-2] + ("00" if value[-2:] != "00" else "01")
    yield "last-byte", encode(changed), False


def main():
    count = 0
    for name, data, valid in fixtures():
        count += 1
        try:
            reader.parse_target(data)
        except reader.AdmissionError:
            if valid:
                raise RuntimeError("rejected valid fixture: " + name)
        else:
            if not valid:
                raise RuntimeError("accepted invalid fixture: " + name)
    if any(name == "ethereum" or name.startswith(("ethereum.", "ethereum_types"))
           for name in sys.modules):
        raise RuntimeError("source imported by parser controls")
    print(f"PASS ancestors parser: {count} frozen frames; source imports/calls 0")


if __name__ == "__main__":
    main()
