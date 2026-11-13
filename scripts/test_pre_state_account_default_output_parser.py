#!/usr/bin/env python3
"""Adversarial strict-reader regressions, valid in both Python optimization modes."""

import copy
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "defaulted_account_reader", ROOT / "STFSpec/Conformance/State/pre_state_account_default_differential.py")
READER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(READER)


def stream(rows):
    return b"\n".join(json.dumps(row, separators=(",", ":")).encode() for row in rows) + b"\n"


class ReaderTests(unittest.TestCase):
    def setUp(self):
        self.rows = READER.expected_frames()

    def rejects(self, rows):
        with self.assertRaises(READER.AdmissionError):
            READER.parse_target(stream(rows))

    def test_complete(self):
        self.assertEqual(READER.parse_target(stream(self.rows)), self.rows)

    def test_missing_extra_reordered(self):
        self.rejects(self.rows[:-1])
        self.rejects(self.rows + self.rows[:1])
        self.rejects(self.rows[1:] + self.rows[:1])

    def test_missing_extra_duplicate_key(self):
        row = copy.deepcopy(self.rows)
        del row[0]["frames"]
        self.rejects(row)
        row = copy.deepcopy(self.rows)
        row[0]["extra"] = 0
        self.rejects(row)
        data = stream(self.rows).replace(b'"case":0', b'"case":0,"case":0', 1)
        with self.assertRaises(READER.AdmissionError):
            READER.parse_target(data)

    def test_exact_numeric_types(self):
        for value in [False, 0.0, "0", None]:
            row = copy.deepcopy(self.rows)
            row[0]["case"] = value
            self.rejects(row)

    def test_default_and_full_payload(self):
        row = copy.deepcopy(self.rows)
        row[0]["answers"][0] = [0, 0, 0, 0]
        self.rejects(row)
        for index in range(4):
            row = copy.deepcopy(self.rows)
            row[2]["answers"][0][index] += 1
            self.rejects(row)

    def test_exact_error_and_no_failed_state(self):
        row = copy.deepcopy(self.rows)
        row[3]["answers"][0][-1] += 1
        self.rejects(row)
        for key in ["frames", "readStates"]:
            row = copy.deepcopy(self.rows)
            row[3][key][0] = []
            self.rejects(row)

    def test_calls_order_repetition_and_membership(self):
        for index, key, value in [(2, "calls", []), (2, "calls", [1, 0]),
                                  (3, "calls", [0, 0]), (4, "calls", [0]),
                                  (0, "readStates", [[]]), (2, "readStates", [[0], [0]])]:
            row = copy.deepcopy(self.rows)
            row[index][key] = value
            self.rejects(row)

    def test_every_frame_scalar(self):
        # Covers every frame field, complete keys/payloads and all order metadata.
        for index in range(len(self.rows[0]["frames"][0])):
            row = copy.deepcopy(self.rows)
            row[0]["frames"][0][index] += 1
            self.rejects(row)

    def test_unbounded_nonce(self):
        row = copy.deepcopy(self.rows)
        row[60]["answers"][0][1] %= 2**256
        self.rejects(row)

    def test_raw_constant_defaults_and_present_hashes(self):
        for index in range(66, 81):
            changed = copy.deepcopy(self.rows)
            changed[index]["answers"][0][-1] ^= 1
            self.rejects(changed)

    def test_invalid_numbers_encoding_and_size(self):
        data = stream(self.rows)
        for replacement in [b"NaN", b"Infinity", b"-Infinity", b"0.0"]:
            with self.assertRaises(READER.AdmissionError):
                READER.parse_target(data.replace(b'"case":0', b'"case":' + replacement, 1))
        for bad in [b"\xff" + data[1:], b" " * 1048577, data + b"\n", data + b"{}\n"]:
            with self.assertRaises(READER.AdmissionError):
                READER.parse_target(bad)


if __name__ == "__main__":
    unittest.main()
