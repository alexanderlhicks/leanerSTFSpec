# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Strict complete deposit observations against an independent frozen catalog.

Source mode consumes original-helper observations from the independently sealed
source packet. It checks every byte, constructor and exact original raise-site
message. Packet/environment authentication is a separate gate; parser admission
alone is not a runtime or host authentication claim. No EELS imports occur here.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

PIN = "e1a316a06fc3d3e0a5da36fdc78580811e9d8a36"
SCHEMA = "deposit-data-v1"
COUNT = 142
CATALOG = Path(__file__).with_name("deposit_cases.json")
CATALOG_SHA256 = "1d1388e3d29c39e373fbcb7c423e744d3badfd97de7facb5e4593c571c717b85"
MESSAGES = {
    "length": "Invalid deposit event data length",
    "pubkeyOffset": "Invalid pubkey offset in deposit log",
    "wcOffset": "Invalid withdrawal credentials offset in deposit log",
    "amountOffset": "Invalid amount offset in deposit log",
    "signatureOffset": "Invalid signature offset in deposit log",
    "indexOffset": "Invalid index offset in deposit log",
    "pubkeySize": "Invalid pubkey size in deposit log",
    "wcSize": "Invalid withdrawal credentials size in deposit log",
    "amountSize": "Invalid amount size in deposit log",
    "signatureSize": "Invalid signature size in deposit log",
    "indexSize": "Invalid index size in deposit log",
}


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
    require(len(data) <= 8 * 1024 * 1024, "oversize output")
    try:
        return json.loads(data, object_pairs_hook=object_pairs,
                          parse_constant=lambda _: (_ for _ in ()).throw(AdmissionError("nonfinite JSON")))
    except (ValueError, UnicodeError) as error:
        raise AdmissionError(str(error)) from error


def keys(value, expected):
    require(type(value) is dict and set(value) == set(expected), "unexpected object keys")


def natural(value):
    require(type(value) is int and value >= 0, "expected JSON natural, excluding bool")


def hex_bytes(value):
    require(type(value) is str and re.fullmatch(r"(?:[0-9a-f]{2})*", value) is not None,
            "noncanonical complete hex")


def result(value, source=False):
    require(type(value) is dict, "result object")
    if set(value) == {"ok"}:
        hex_bytes(value["ok"])
        require(len(value["ok"]) == 384, "complete 192-byte result")
    else:
        keys(value, ("error", "message") if source else ("error",))
        require(type(value["error"]) is str and value["error"] in MESSAGES, "error identity")
        if source:
            require(type(value["message"]) is str and value["message"] == MESSAGES[value["error"]],
                    "exact original raise-site message")
    return value


def projection(value):
    return {"ok": value["ok"]} if "ok" in value else {"error": value["error"]}


def catalog():
    data = CATALOG.read_bytes()
    require(hashlib.sha256(data).hexdigest() == CATALOG_SHA256, "catalog identity")
    rows = decode(data)
    require(type(rows) is list and len(rows) == COUNT, "catalog count")
    seen = set()
    for row in rows:
        keys(row, ("id", "hex", "expected", "coverage"))
        require(type(row["id"]) is str and row["id"] not in seen, "catalog id")
        seen.add(row["id"])
        require(type(row["coverage"]) is str and row["coverage"], "coverage description")
        hex_bytes(row["hex"])
        result(row["expected"], source=True)
    return rows


def check_rows(rows):
    expected = catalog()
    require(type(rows) is list and len(rows) == COUNT, "row count")
    for row, case in zip(rows, expected):
        keys(row, ("id", "hex", "actual"))
        require(type(row["id"]) is str and row["id"] == case["id"], "row id/order")
        hex_bytes(row["hex"])
        require(row["hex"] == case["hex"], "complete input hex")
        result(row["actual"])
        require(row["actual"] == projection(case["expected"]), "complete result")
    return rows


def parse_target(data):
    require(len(data) <= 8 * 1024 * 1024, "oversize output")
    lines = data.splitlines()
    require(len(lines) == COUNT + 2, "frame length")
    frame = [decode(line) for line in lines]
    keys(frame[0], ("schema", "count"))
    require(frame[0]["schema"] == SCHEMA, "schema")
    natural(frame[0]["count"])
    require(frame[0]["count"] == COUNT, "header count")
    keys(frame[-1], ("end", "count"))
    require(frame[-1]["end"] is True, "footer end")
    natural(frame[-1]["count"])
    require(frame[-1]["count"] == COUNT, "footer count")
    return check_rows(frame[1:-1])


def parse_source(data):
    """Validate the source packet's complete observations, preserving raw diagnostics.

    Environment manifests remain attached to the independently authenticated
    packet. This projection checks the declared source binding and local rows;
    it does not claim that arbitrary supplied metadata authenticates a runtime.
    """
    value = decode(data)
    require(type(value) is dict and value.get("head") == PIN, "source pin")
    require(value.get("status") == "all 142 source cases passed", "source status")
    require(value.get("case_file_before_sha256") == CATALOG_SHA256 and
            value.get("case_file_after_sha256") == CATALOG_SHA256, "source catalog identity")
    runtime = value.get("runtime")
    require(type(runtime) is dict and type(runtime.get("isolated")) is int and
            runtime["isolated"] == 1 and runtime.get("dont_write_bytecode") is True and
            runtime.get("cache_prefix_empty_at_start_and_end") is True, "source isolation")
    natural(runtime.get("optimize"))
    require(runtime["optimize"] in (0, 1), "source optimization")
    function = value.get("function")
    require(type(function) is dict and function.get("module") == "ethereum.forks.amsterdam.requests"
            and function.get("qualname") == "extract_deposit_data", "source function binding")
    natural(function.get("firstlineno"))
    require(function["firstlineno"] == 170, "source line")
    rows = value.get("rows")
    require(type(rows) is list and len(rows) == COUNT, "source row count")
    output = []
    for row, case in zip(rows, catalog()):
        base = {"id", "hex", "expected", "coverage", "actual", "input_type", "input_bytes",
                "return_type", "exception_type", "exception_args"}
        success = "ok" in case["expected"]
        keys(row, base | ({"return_bytes"} if success else set()))
        require(row["id"] == case["id"] and row["coverage"] == case["coverage"], "source case identity")
        hex_bytes(row["hex"])
        require(row["hex"] == case["hex"], "source full input")
        result(row["expected"], source=True)
        result(row["actual"], source=True)
        require(row["expected"] == case["expected"] and row["actual"] == case["expected"],
                "source complete result/message")
        natural(row["input_bytes"])
        require(row["input_type"] == "builtins.bytes" and row["input_bytes"] * 2 == len(row["hex"]),
                "source input type/length")
        if success:
            natural(row["return_bytes"])
            require(row["return_type"] == "builtins.bytes" and row["return_bytes"] == 192 and
                    row["exception_type"] is None and row["exception_args"] is None, "source return")
        else:
            require(row["return_type"] is None and
                    row["exception_type"] == "ethereum.exceptions.InvalidBlock" and
                    row["exception_args"] == [MESSAGES[row["actual"]["error"]]], "source exact exception")
        output.append({"id": row["id"], "hex": row["hex"], "actual": projection(row["actual"])})
    return check_rows(output)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-target", type=Path, required=True)
    parser.add_argument("--check-source", type=Path)
    args = parser.parse_args()
    target = parse_target(args.check_target.read_bytes())
    if args.check_source:
        source = parse_source(args.check_source.read_bytes())
        require(target == source, "target/source complete rows")
    print("PASS deposit data: 142 complete byte/error rows" +
          (" coupled to original source" if args.check_source else " against frozen catalog"))


if __name__ == "__main__":
    main()
