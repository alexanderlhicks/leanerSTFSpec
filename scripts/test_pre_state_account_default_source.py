#!/usr/bin/env python3
"""Bounded source-reader/authentication regressions without an EELS installation.

Synthetic frames test admission and framing only. Actual original-source comparisons
require pre_state_account_default_source.py --eels and its separately authenticated runtime.
"""

import copy
import base64
import importlib.util
import json
from pathlib import Path
import subprocess
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "defaulted_account_source", ROOT / "STFSpec/Conformance/State/pre_state_account_default_source.py")
SOURCE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SOURCE)


def stream(rows):
    return b"\n".join(json.dumps(row, separators=(",", ":")).encode() for row in rows) + b"\n"


def rows():
    result = []
    for expected, case in zip(SOURCE.READER.expected_frames()[:66], SOURCE.inputs(), strict=True):
        frame = {"block": {key: {"set": []} for key in SOURCE.BLOCK_FIELDS},
                 "tx": {key: {"map": []} for key in SOURCE.TX_FIELDS}}
        result.append({key: copy.deepcopy(expected[key]) for key in
                       ["case", "answers", "calls", "readStates"]} |
                      {"providerObservedReads": [True] * len(expected["calls"]),
                       "failedSourceReads": sorted({case["address"], case["otherAddress"]})
                       if expected["answers"][0][0] else None,
                       "sourceFrameBefore": frame, "sourceFrameAfter": copy.deepcopy(frame)})
    return result


def authentication(mode):
    return {"executable": {"sha256": "same interpreter"}, "version": "same version",
            "optimize": mode, "isolated": 1, "dont_write_bytecode": True,
            "operation_source": "same pinned operation", "imported_files": ["same files"],
            "uv_lock": "same lock", "dependencies": ["same installed bytes"], "limit": "same"}


class SourceReaderTests(unittest.TestCase):
    def setUp(self):
        self.rows = rows()

    def rejects(self, data):
        with self.assertRaises(SOURCE.READER.AdmissionError):
            SOURCE.parse_source(data)

    def test_complete_projection(self):
        self.assertEqual(SOURCE.parse_source(stream(self.rows)), self.rows)

    def test_stream_count_order_and_encoding(self):
        for invalid in [stream(self.rows[:-1]), stream(self.rows + self.rows[:1]),
                        stream(self.rows[::-1]), stream(self.rows) + b"\n",
                        b"\xff" + stream(self.rows)[1:], b" " * (2**21 + 1)]:
            self.rejects(invalid)

    def test_fields_and_duplicate_keys(self):
        for key in self.rows[0]:
            changed = copy.deepcopy(self.rows)
            del changed[0][key]
            self.rejects(stream(changed))
        changed = copy.deepcopy(self.rows)
        changed[0]["extra"] = 0
        self.rejects(stream(changed))
        self.rejects(stream(self.rows).replace(b'"case":0', b'"case":0,"case":0', 1))

    def test_exact_answer_calls_reads_and_types(self):
        for key, value in [("case", False), ("case", 0.0), ("answers", [[0, 0, 0, 0]]),
                           ("calls", [1]), ("readStates", [[]])]:
            changed = copy.deepcopy(self.rows)
            changed[0][key] = value
            self.rejects(stream(changed))
        for token in [b"NaN", b"Infinity", b"-Infinity"]:
            self.rejects(stream(self.rows).replace(b'"case":0', b'"case":' + token, 1))

    def test_order_observation_and_separate_failed_read(self):
        for key, value in [("providerObservedReads", [False]),
                           ("providerObservedReads", [1]), ("failedSourceReads", None),
                           ("readStates", [[0, 1]])]:
            changed = copy.deepcopy(self.rows)
            changed[3][key] = value
            self.rejects(stream(changed))

    def test_full_source_field_presence_and_retention(self):
        for part, fields in [("block", SOURCE.BLOCK_FIELDS), ("tx", SOURCE.TX_FIELDS)]:
            for field in fields:
                changed = copy.deepcopy(self.rows)
                del changed[0]["sourceFrameBefore"][part][field]
                del changed[0]["sourceFrameAfter"][part][field]
                self.rejects(stream(changed))
                changed = copy.deepcopy(self.rows)
                changed[0]["sourceFrameAfter"][part][field] = {"changed": 1}
                self.rejects(stream(changed))

    def test_error_constructor_payload_and_huge_nonce(self):
        changed = copy.deepcopy(self.rows)
        changed[3]["answers"][0][-1] += 1
        self.rejects(stream(changed))
        changed = copy.deepcopy(self.rows)
        changed[60]["answers"][0][1] %= 2**256
        self.rejects(stream(changed))


class AuthenticationTests(unittest.TestCase):
    def test_actual_modes_and_unchanged_identity(self):
        SOURCE.check_authentication(authentication(0), authentication(1))
        for key in authentication(1):
            changed = authentication(1)
            changed[key] = "changed"
            with self.assertRaises(ValueError):
                SOURCE.check_authentication(authentication(0), changed)
        for key, value in [("optimize", True), ("isolated", True),
                           ("dont_write_bytecode", 1)]:
            changed = authentication(1)
            changed[key] = value
            with self.assertRaises(ValueError):
                SOURCE.check_authentication(authentication(0), changed)

    def test_wrong_pin_stops_before_imports(self):
        report = {"executions": []}
        with patch.object(SOURCE, "run_child", return_value=b"wrong head\n") as child:
            with self.assertRaises(ValueError):
                SOURCE.source_identity(Path("unused-clone"), report)
            self.assertEqual(child.call_count, 1)

    def test_failed_child_retains_original_wait_and_streams(self):
        report = {"executions": []}
        with patch.object(SOURCE.subprocess, "run", return_value=
                          subprocess.CompletedProcess(["probe"], 7, b"out", b"error")):
            with self.assertRaises(ValueError):
                SOURCE.run_child(["probe"], report)
        self.assertEqual(len(report["executions"]), 1)
        receipt = report["executions"][0]
        self.assertIs(receipt["wait_consumed"], True)
        self.assertEqual((receipt["returncode"], receipt["stdout"], receipt["stderr"]),
                         (7, "out", "error"))
        self.assertEqual(base64.b64decode(receipt["stdout_base64"]), b"out")
        self.assertEqual(base64.b64decode(receipt["stderr_base64"]), b"error")


if __name__ == "__main__":
    unittest.main()
