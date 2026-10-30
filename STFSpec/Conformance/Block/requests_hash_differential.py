# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Strict full request/digest observations against the independent frozen catalog.

Source mode consumes both original-source observations from the independently
sealed packet. It admits an observation projection, not runtime/seal authenticity.
Expected values preceded EELS/Lean and used OpenSSL CLI composition plus fixed
empty/abc anchors; CLI and hashlib share OpenSSL, not independent crypto code.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

PIN = "e1a316a06fc3d3e0a5da36fdc78580811e9d8a36"
SCHEMA = "requests-hash-v1"
COUNT = 298
CATALOG = Path(__file__).with_name("requests-hash-cases.json")
CATALOG_SHA256 = "98796c0f42b6672d35b706372f4af409e0197ea98f1fa35bda8660ac23e43be2"
MAX_BYTES = 8 * 1024 * 1024


class AdmissionError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise AdmissionError(message)


def object_pairs(pairs):
    value = {}
    for key, item in pairs:
        require(key not in value, "duplicate JSON key")
        value[key] = item
    return value


def decode(data):
    require(len(data) <= MAX_BYTES, "oversize output")
    try:
        return json.loads(data, object_pairs_hook=object_pairs,
                          parse_constant=lambda _: (_ for _ in ()).throw(AdmissionError("nonfinite JSON")))
    except (ValueError, UnicodeError) as error:
        raise AdmissionError(str(error)) from error


def keys(value, expected):
    require(type(value) is dict and set(value) == set(expected), "unexpected object keys")


def natural(value):
    require(type(value) is int and value >= 0, "expected JSON natural, excluding bool")


def hex_bytes(value, digest=False):
    require(type(value) is str and re.fullmatch(r"(?:[0-9a-f]{2})*", value) is not None,
            "noncanonical complete hex")
    if digest:
        require(len(value) == 64, "complete 32-byte digest")


def request_list(value):
    require(type(value) is list, "ordered requests list")
    for text in value:
        hex_bytes(text)


def catalog():
    data = CATALOG.read_bytes()
    require(hashlib.sha256(data).hexdigest() == CATALOG_SHA256, "catalog identity")
    rows = decode(data)
    require(type(rows) is list and len(rows) == COUNT, "catalog count")
    seen = set()
    for row in rows:
        keys(row, ("id", "requests_hex", "inner_expected_hex", "outer_input_hex",
                   "expected_hex", "coverage"))
        require(type(row["id"]) is str and row["id"] and row["id"] not in seen, "catalog id")
        seen.add(row["id"])
        require(type(row["coverage"]) is str and row["coverage"], "coverage description")
        request_list(row["requests_hex"])
        require(type(row["inner_expected_hex"]) is list and
                len(row["inner_expected_hex"]) == len(row["requests_hex"]), "inner digest count")
        for inner in row["inner_expected_hex"]:
            hex_bytes(inner, digest=True)
        hex_bytes(row["outer_input_hex"])
        require(row["outer_input_hex"] == "".join(row["inner_expected_hex"]), "ordered outer preimage")
        hex_bytes(row["expected_hex"], digest=True)
    return rows


def check_rows(rows):
    expected = catalog()
    require(type(rows) is list and len(rows) == COUNT, "row count")
    for row, case in zip(rows, expected):
        keys(row, ("id", "requests_hex", "actual_hex"))
        require(type(row["id"]) is str and row["id"] == case["id"], "row id/order")
        request_list(row["requests_hex"])
        require(row["requests_hex"] == case["requests_hex"], "complete ordered request bytes")
        hex_bytes(row["actual_hex"], digest=True)
        require(row["actual_hex"] == case["expected_hex"], "complete digest")
    return rows


def parse_target(data):
    require(len(data) <= MAX_BYTES, "oversize output")
    lines = data.splitlines()
    require(len(lines) == COUNT + 2, "frame length")
    frame = [decode(line) for line in lines]
    keys(frame[0], ("schema", "count"))
    require(type(frame[0]["schema"]) is str and frame[0]["schema"] == SCHEMA, "schema")
    natural(frame[0]["count"])
    require(frame[0]["count"] == COUNT, "header count")
    keys(frame[-1], ("end", "count"))
    require(frame[-1]["end"] is True, "footer end")
    natural(frame[-1]["count"])
    require(frame[-1]["count"] == COUNT, "footer count")
    return check_rows(frame[1:-1])


def parse_source(data, optimize):
    """Admit complete observations; attached environment manifests are a separate gate."""
    value = decode(data)
    require(type(value) is dict and value.get("head") == PIN, "source pin")
    require(value.get("status") == "all 298 source cases passed", "source status")
    require(value.get("case_file_before_sha256") == CATALOG_SHA256 and
            value.get("case_file_after_sha256") == CATALOG_SHA256, "source catalog identity")
    runtime = value.get("runtime")
    require(type(runtime) is dict and type(runtime.get("isolated")) is int and
            runtime["isolated"] == 1 and runtime.get("dont_write_bytecode") is True and
            runtime.get("cache_prefix_empty_at_start_and_end") is True, "source isolation")
    natural(runtime.get("optimize"))
    require(runtime["optimize"] == optimize, "source optimization mode")
    function = value.get("function")
    require(type(function) is dict and function.get("module") == "ethereum.forks.amsterdam.requests"
            and function.get("qualname") == "compute_requests_hash", "source function binding")
    natural(function.get("firstlineno"))
    require(function["firstlineno"] == 307, "source line")
    rows = value.get("rows")
    require(type(rows) is list and len(rows) == COUNT, "source row count")
    output = []
    for row, case in zip(rows, catalog()):
        keys(row, set(case) | {"actual_hex", "input_type", "request_types", "request_bytes",
                               "return_type", "return_bytes"})
        for field in case:
            require(type(row[field]) is type(case[field]) and row[field] == case[field],
                    "source complete case identity: " + field)
        request_list(row["requests_hex"])
        require(row["input_type"] == "builtins.list", "source input list type")
        require(type(row["request_types"]) is list and
                row["request_types"] == ["builtins.bytes"] * len(case["requests_hex"]),
                "source request types")
        require(type(row["request_bytes"]) is list and
                len(row["request_bytes"]) == len(case["requests_hex"]), "source request lengths")
        for length, text in zip(row["request_bytes"], case["requests_hex"]):
            natural(length)
            require(2 * length == len(text), "source complete request lengths")
        natural(row["return_bytes"])
        require(row["return_type"] == "builtins.bytes" and row["return_bytes"] == 32,
                "source complete return type/length")
        hex_bytes(row["actual_hex"], digest=True)
        require(row["actual_hex"] == case["expected_hex"], "source complete digest")
        output.append({"id": row["id"], "requests_hex": row["requests_hex"],
                       "actual_hex": row["actual_hex"]})
    return check_rows(output)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-target", type=Path, required=True)
    parser.add_argument("--check-source-normal", type=Path)
    parser.add_argument("--check-source-optimized", type=Path)
    args = parser.parse_args()
    require(bool(args.check_source_normal) == bool(args.check_source_optimized),
            "supply both source modes")
    target = parse_target(args.check_target.read_bytes())
    if args.check_source_normal:
        normal = parse_source(args.check_source_normal.read_bytes(), 0)
        optimized = parse_source(args.check_source_optimized.read_bytes(), 1)
        require(target == normal == optimized, "target/both-source complete rows")
    print("PASS requests hash: 298 complete ordered request/digest rows" +
          (" coupled to both original source modes" if args.check_source_normal else " against frozen catalog"))


if __name__ == "__main__":
    main()
