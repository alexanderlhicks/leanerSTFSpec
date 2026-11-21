#!/usr/bin/env python3
"""Check complete transient-storage read observations against an integer model."""

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
INPUTS = HERE / "transient_storage_inputs.json"
INPUT_SHA256 = "c6e92e058fbd845a982485d6ba0015d6214ea680a749296bfc0c7556c6c1a8b7"

strict = importlib.util.spec_from_file_location(
    "transient_storage_strict_reader", HERE / "account_optional_differential.py")
READER = importlib.util.module_from_spec(strict)
exec(compile(Path(strict.origin).read_bytes(), strict.origin, "exec"), READER.__dict__)


def inputs():
    data = INPUTS.read_bytes()
    if hashlib.sha256(data).hexdigest() != INPUT_SHA256:
        raise READER.AdmissionError("transient storage input identity mismatch")
    return READER.decode(data)


def account(salt):
    return [2**180 + salt, 2**200 + salt, 2**255 + salt]


def overlay(address, slot, salt):
    return {
        "accountWrites": sorted([[address, account(salt)], [salt + 1, None]]),
        "storageWrites": sorted([[address, [[slot, 2**170 + salt]]], [salt + 3, []]]),
        "codeWrites": [[2**153 + salt, [0, salt, 255]]],
        "storageClears": [salt + 1],
        "accountReads": [salt + 2],
        "storageReads": [[salt + 2, 2**155 + salt]],
        "codeReads": [2**154 + salt],
    }


def order(address, slot, salt):
    def index(key, offset):
        return [2**190 + offset, [[key, 3]], [[5, key]]]

    return [index(address, salt), index(address, salt + 1),
            [[address, index(slot, salt + 2)]]]


def expected_rows(source=False):
    rows = []
    for case in inputs():
        address, slot = case["address"], case["slot"]
        transient = sorted(case["transient"])
        value = next((word for a, k, word in transient if (a, k) == (address, slot)), 0)
        frame = {
            "block": overlay(address, slot, 40) | {"oldestAncestorOffset": 2**140 + 13},
            "tx": overlay(address, slot, 80) | {"createdAccounts": [97], "transient": transient},
        }
        if not source:
            frame |= {
                "consts": [2**220 + i for i in range(1, 5)],
                "blockOrder": order(address, slot, 40),
                "txOrder": order(address, slot, 80),
                "provider": [account(120), 2**230 + 2, [120, 0, 255], 2**231 + 4],
            }
        repeat = case["repeat"]
        rows.append({"id": case["id"], "answers": [value] * repeat, "calls": [],
                     "frames": [frame] * (repeat + 1)})
    return rows


def parse_rows(data, source=False):
    if type(data) is not bytes or len(data) > 2**16:
        raise READER.AdmissionError("invalid or oversized transient storage stream")
    expected = expected_rows(source)
    lines = data.splitlines()
    if len(lines) != len(expected):
        raise READER.AdmissionError("missing, duplicate or extra transient storage rows")
    rows = [READER.decode(line) for line in lines]
    READER.strict_equal(rows, expected)
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-target", required=True, type=Path)
    args = parser.parse_args()
    rows = parse_rows(args.check_target.read_bytes())
    calls = sum(len(row["answers"]) for row in rows)
    print(f"PASS transient storage: {len(rows)} complete target cases and {calls} reads")


if __name__ == "__main__":
    main()
