# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Strict complete KZG input/result comparison against frozen, pre-target bytes.

Source mode admits the exact adopted full observation rows and their supplied
sidecar byte binding. It does not re-execute or authenticate the Python runtime,
loaded code or environment. That source authentication remains a separate gate.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

SCHEMA = "kzg-versioned-hash-v1"
COUNT = 926
SOURCE_COUNT = 917
PIN = "e1a316a06fc3d3e0a5da36fdc78580811e9d8a36"
CATALOG = Path(__file__).with_name("kzg-versioned-hash-cases.json")
CATALOG_SHA256 = "fe529aae14ec2d4cab81093e2b0dab6745df1cf6c0296cd89efd84e03659e3f3"
INPUT_SHA256 = "0de804ea1fe753d030de5ab61f512a38836eef37708054f4fd3982c30ed626a4"
EXPECTED_SHA256 = "738907519c5b855a0e972eee2a31c7beff54e003e969bef18ffe4863375566a2"
ROWS_SHA256 = "32191f97de635e14e33e5b8dc52f8ed25357bab87cac9875bb0d723a6bc5001a"
PRODUCER_SHA256 = "0dd868b4f5625083f80067b5122cacc908de385763c3d03f3c34dbc0f406f755"
IDENTITY_SHA256 = "74213eb3ab4ab474d6da6bdb0109fa7ad27776c917dfeb2dc3e023c23caa1747"
MAX_BYTES = 32 * 1024 * 1024


class AdmissionError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise AdmissionError(message)


def pairs(items):
    result = {}
    for key, value in items:
        require(key not in result, "duplicate JSON member")
        result[key] = value
    return result


def decode(data):
    require(len(data) <= MAX_BYTES, "file bound")
    try:
        return json.loads(data, object_pairs_hook=pairs,
                          parse_constant=lambda _: require(False, "nonfinite JSON"))
    except (ValueError, UnicodeError) as error:
        raise AdmissionError(str(error)) from error


def keys(value, expected):
    require(type(value) is dict and set(value) == set(expected), "exact object keys")


def integer(value, expected):
    require(type(value) is int and value == expected, "exact integer excluding bool")


def hex_bytes(value, width=None):
    require(type(value) is str and re.fullmatch(r"(?:[0-9a-f]{2})*", value) is not None,
            "canonical complete hex")
    if width is not None:
        require(len(value) == 2 * width, "exact hex width")


def canonical(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def catalog():
    raw = CATALOG.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == CATALOG_SHA256, "frozen catalog identity")
    obj = decode(raw)
    keys(obj, ("schema", "pin", "provenance", "source_count", "count", "cases"))
    require(obj["schema"] == "kzg-versioned-hash-cases-v1" and obj["pin"] == PIN, "catalog schema/pin")
    integer(obj["count"], COUNT)
    integer(obj["source_count"], SOURCE_COUNT)
    require(type(obj["provenance"]) is str and obj["provenance"], "catalog provenance")
    require(type(obj["cases"]) is list and len(obj["cases"]) == COUNT, "catalog cases")
    for i, case in enumerate(obj["cases"]):
        keys(case, ("id", "case", "labels", "length", "hex", "sha256", "versioned_hash"))
        expected_id = f"c{i:04d}" if i < SOURCE_COUNT else f"own{i - SOURCE_COUNT:04d}"
        require(type(case["id"]) is str and case["id"] == expected_id, "catalog ID/order")
        require(type(case["length"]) is int and 0 <= case["length"] <= 2048, "catalog length")
        hex_bytes(case["hex"], case["length"])
        hex_bytes(case["sha256"], 32)
        hex_bytes(case["versioned_hash"], 32)
        require(case["versioned_hash"] == "01" + case["sha256"][2:], "catalog substitution")
    return obj["cases"]


def expected_rows():
    return [dict(id=c["id"], input_hex=c["hex"], length=c["length"],
                 actual_hex=c["versioned_hash"]) for c in catalog()]


def frame(data, count):
    require(len(data) <= MAX_BYTES, "file bound")
    require(data.endswith(b"\n"), "complete newline framing")
    lines = data.splitlines()
    require(len(lines) == count + 2, "exact frame record count")
    return [decode(line) for line in lines]


def parse_target(data):
    values = frame(data, COUNT)
    keys(values[0], ("schema", "count"))
    require(values[0]["schema"] == SCHEMA, "target schema")
    integer(values[0]["count"], COUNT)
    keys(values[-1], ("end", "count"))
    require(values[-1]["end"] is True, "target footer")
    integer(values[-1]["count"], COUNT)
    rows = values[1:-1]
    for row, expected in zip(rows, expected_rows()):
        keys(row, ("id", "input_hex", "length", "actual_hex"))
        require(type(row["id"]) is str and row["id"] == expected["id"], "row ID/order")
        integer(row["length"], expected["length"])
        hex_bytes(row["input_hex"], expected["length"])
        hex_bytes(row["actual_hex"], 32)
        require(row == expected, "complete input/result bytes")
    return rows


def parse_source(data, sidecar, mode):
    """Adopted-row identity and byte projection; not runtime/environment authentication."""
    values = frame(data, SOURCE_COUNT)
    head = values[0]
    keys(head, ("record", "schema", "count", "mode", "input_sha256", "expected_sha256",
                "producer_sha256", "identity_sha256", "provenance_sha256"))
    require(head["record"] == "header" and head["schema"] == "wi503-source-v1", "source schema")
    integer(head["count"], SOURCE_COUNT)
    require(type(mode) is str and mode in ("normal", "optimized") and head["mode"] == mode,
            "source mode")
    require(head["input_sha256"] == INPUT_SHA256 and
            head["expected_sha256"] == EXPECTED_SHA256 and
            head["producer_sha256"] == PRODUCER_SHA256 and
            head["identity_sha256"] == IDENTITY_SHA256, "adopted source identities")
    hex_bytes(head["provenance_sha256"], 32)
    require(len(sidecar) <= MAX_BYTES and hashlib.sha256(sidecar).hexdigest() ==
            head["provenance_sha256"], "sidecar complete byte binding")
    body = values[1:-1]
    digest = hashlib.sha256(b"".join(canonical(row) for row in body)).hexdigest()
    require(digest == ROWS_SHA256, "all adopted complete observation rows")
    tail = values[-1]
    keys(tail, ("record", "count", "rows_sha256"))
    require(tail["record"] == "footer" and tail["rows_sha256"] == digest, "source footer binding")
    integer(tail["count"], SOURCE_COUNT)
    result = []
    for row, case in zip(body, catalog()[:SOURCE_COUNT]):
        require(row["input"] == {k: case[k] for k in ("id", "case", "labels", "length", "hex")},
                "source complete input identity")
        value = row["result"]
        keys(value, ("type", "hex", "length"))
        require(value["type"] == "ethereum.crypto.kzg.VersionedHash", "source result class")
        integer(value["length"], 32)
        hex_bytes(value["hex"], 32)
        require(value["hex"] == case["versioned_hash"], "source all output bytes")
        result.append(dict(id=case["id"], input_hex=case["hex"], length=case["length"],
                           actual_hex=value["hex"]))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-target", type=Path, required=True)
    parser.add_argument("--check-source-normal", type=Path, nargs=2, metavar=("STREAM", "SIDECAR"))
    parser.add_argument("--check-source-optimized", type=Path, nargs=2, metavar=("STREAM", "SIDECAR"))
    args = parser.parse_args()
    require(bool(args.check_source_normal) == bool(args.check_source_optimized),
            "both source modes required together")
    target = parse_target(args.check_target.read_bytes())
    if args.check_source_normal:
        normal = parse_source(*(p.read_bytes() for p in args.check_source_normal), "normal")
        optimized = parse_source(*(p.read_bytes() for p in args.check_source_optimized), "optimized")
        require(target[:SOURCE_COUNT] == normal == optimized, "target/both-source full bytes")
    print("PASS KZG: 926 complete raw input/result rows (917 frozen, nine own boundary cases)" +
          ("; both adopted source modes agree" if args.check_source_normal else ""))


if __name__ == "__main__":
    try:
        main()
    except (AdmissionError, OSError) as error:
        raise SystemExit("REJECT: " + str(error))
