#!/usr/bin/env python3
"""Strict complete raw-model stream regressions, also under Python -O."""

import copy
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "transaction_view_reader", ROOT / "STFSpec/Conformance/State/transaction_view_model.py")
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

    def test_framing(self):
        self.rejects(self.rows[:-1])
        self.rejects(self.rows + self.rows[:1])
        self.rejects(self.rows[1:] + self.rows[:1])
        for suffix in [b"\n", b"junk\n"]:
            with self.assertRaises(READER.AdmissionError):
                READER.parse_target(stream(self.rows) + suffix)
        for data in [stream(self.rows)[:-1], stream(self.rows).replace(b"\n", b"\r\n")]:
            with self.assertRaises(READER.AdmissionError):
                READER.parse_target(data)
        duplicate = stream(self.rows).replace(b'"case":0', b'"case":0,"case":0', 1)
        with self.assertRaises(READER.AdmissionError):
            READER.parse_target(duplicate)

    def test_schema_and_full_fields(self):
        for field in ["schema", "case", "blockView", "view"]:
            rows = copy.deepcopy(self.rows)
            del rows[0][field]
            self.rejects(rows)
        for view in ["blockView", "view"]:
            for field in ["accounts", "storage", "code"]:
                rows = copy.deepcopy(self.rows)
                del rows[0][view][field]
                self.rejects(rows)
        rows = copy.deepcopy(self.rows)
        rows[0]["view"]["extra"] = []
        self.rejects(rows)

    def test_numeric_types(self):
        for value in [False, 0.0, "0", None, -1]:
            rows = copy.deepcopy(self.rows)
            rows[0]["case"] = value
            self.rejects(rows)
            rows = copy.deepcopy(self.rows)
            rows[0]["view"]["accounts"][0][1][0] = value
            self.rejects(rows)
        raw = stream(self.rows)
        for number in [b"NaN", b"Infinity", b"-Infinity", b"0.0"]:
            with self.assertRaises(READER.AdmissionError):
                READER.parse_target(raw.replace(b'"case":0', b'"case":' + number, 1))

    def test_raw_missing_empty_zero_and_code(self):
        # Case zero is unchanged raw input with empty, zero and orphan storage.
        for view in ["blockView", "view"]:
            for index in range(len(self.rows[0][view]["storage"])):
                rows = copy.deepcopy(self.rows)
                del rows[0][view]["storage"][index]
                self.rejects(rows)
            rows = copy.deepcopy(self.rows)
            rows[0][view]["storage"][0][1][1][1] = 1
            self.rejects(rows)
            for index in range(len(self.rows[0][view]["code"])):
                rows = copy.deepcopy(self.rows)
                rows[0][view]["code"][index][1].append(1)
                self.rejects(rows)

    def test_full_account_payload_and_key(self):
        for view in ["blockView", "view"]:
            for index in range(3):
                rows = copy.deepcopy(self.rows)
                rows[0][view]["accounts"][1][1][index] += 1
                self.rejects(rows)
            rows = copy.deepcopy(self.rows)
            rows[0][view]["accounts"][1][0] += 1
            self.rejects(rows)

    def test_every_result_scalar(self):
        # Every numeric leaf and every byte in a varied complete result is checked.
        paths = []
        def visit(node, path):
            if type(node) is int:
                paths.append(path)
            elif type(node) is list:
                for index, value in enumerate(node):
                    visit(value, path + [index])
            elif type(node) is dict:
                for key, value in node.items():
                    visit(value, path + [key])
        visit(self.rows[-1], [])
        for path in paths:
            rows = copy.deepcopy(self.rows)
            node = rows[-1]
            for key in path[:-1]:
                node = node[key]
            node[path[-1]] += 1
            self.rejects(rows)

    def test_encoding_and_limit(self):
        for data in [b"\xff", b"x" * 2097153, b"[]\n"]:
            with self.assertRaises(READER.AdmissionError):
                READER.parse_target(data)


if __name__ == "__main__":
    unittest.main()
