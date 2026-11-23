#!/usr/bin/env python3
"""Bounded source-reader/authentication regressions without an EELS installation.

Synthetic frames test admission and framing only. Actual original-source comparisons
require pre_state_account_source.py --eels and its separately authenticated runtime.
"""

import copy
import base64
import importlib.util
import json
import os
import py_compile
import runpy
import sys
import tempfile
from pathlib import Path
import subprocess
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "optional_account_source", ROOT / "STFSpec/Conformance/State/pre_state_account_source.py")
SOURCE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SOURCE)


def stream(rows):
    return b"\n".join(json.dumps(row, separators=(",", ":")).encode() for row in rows) + b"\n"


def rows():
    result = []
    for expected, case in zip(SOURCE.READER.expected_frames(), SOURCE.inputs(), strict=True):
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
            "uv_lock": "same lock", "dependencies": ["same installed bytes"],
            "source_loading": {"policy": "compile-source-without-bytecode-cache",
                               "compiled_sources": {}}, "limit": "same"}


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
        for key, value in [("case", False), ("case", 0.0), ("answers", [[0, 1, 0, 0, 0]]),
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
        changed[60]["answers"][0][2] %= 2**256
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

    def test_source_status_preserves_index_and_refuses_dirty_checkout(self):
        git_env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
        git_env.update(GIT_OPTIONAL_LOCKS="1", GIT_CONFIG_GLOBAL=os.devnull,
                       GIT_CONFIG_SYSTEM=os.devnull)
        for name in ["pre_state_account_source", "pre_state_account_default_source",
                     "account_optional_source", "account_default_source"]:
            with self.subTest(driver=name), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                eels = root / "eels"
                eels.mkdir()

                def git(*args):
                    return subprocess.run(["git", *args], cwd=eels, check=True,
                                          capture_output=True, text=True, timeout=10).stdout

                with patch.dict(os.environ, git_env, clear=True):
                    git("init", "--quiet", "--template=")
                    tracker = eels / "src/ethereum/forks/amsterdam/state_tracker.py"
                    state = eels / "src/ethereum/state.py"
                    tracker.parent.mkdir(parents=True)
                    for path in [tracker, state, eels / "uv.lock"]:
                        path.write_text("\n")
                    git("add", ".")
                    git("-c", "user.name=Source test", "-c", "user.email=source@example.invalid",
                        "commit", "--quiet", "-m", "Add source fixture")
                    head = git("rev-parse", "HEAD").strip()
                    (root / "reference.toml").write_text(f'[release]\ncommit = "{head}"\n')
                    index = eels / ".git/index"
                    before = index.read_bytes()
                    stamp = tracker.stat()
                    os.utime(tracker, ns=(stamp.st_atime_ns, stamp.st_mtime_ns - 2_000_000_000))

                    driver = runpy.run_path(str(Path(SPEC.origin).with_name(name + ".py")))
                    source_identity = driver["source_identity"]
                    clean = {"executions": []}
                    dirty = {"executions": []}
                    with patch.dict(source_identity.__globals__, {"ROOT": root}):
                        self.assertEqual(source_identity(eels, clean)["head"], head)
                        self.assertEqual(index.read_bytes(), before)
                        tracker.write_text("dirty\n")
                        with self.assertRaisesRegex(ValueError, "clean checkout of the exact pin"):
                            source_identity(eels, dirty)
                        self.assertEqual(index.read_bytes(), before)

                    status_argv = ["git", "--no-replace-objects", "-C", str(eels),
                                   "--no-optional-locks", "status", "--porcelain"]
                    self.assertEqual(clean["executions"][1]["argv"], status_argv)
                    self.assertEqual(clean["executions"][1]["stdout"], "")
                    self.assertEqual(dirty["executions"][1]["argv"], status_argv)
                    self.assertEqual(dirty["executions"][1]["stdout"],
                                     f" M {tracker.relative_to(eels).as_posix()}\n")

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


class SourceLoadingTests(unittest.TestCase):
    def test_timestamp_valid_caches_never_supply_executed_code(self):
        # Both bytecode modes contain a changed answer outside the bounded catalogue.
        # The original filename, source size and timestamp remain valid for CPython.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            module = root / "cached_tracker.py"
            original = "def read(address):\n    return 111 if address == 42 else 0\n"
            altered = original.replace("111", "999")
            module.write_text(altered)
            stamp = module.stat()
            caches = []
            for optimize in [0, 1]:
                cache = Path(py_compile.compile(
                    str(module), doraise=True, optimize=optimize,
                    invalidation_mode=py_compile.PycInvalidationMode.TIMESTAMP))
                caches.append((cache, cache.read_bytes()))
            module.write_text(original)
            os.utime(module, ns=(stamp.st_atime_ns, stamp.st_mtime_ns))
            for optimize in [[], ["-O"]]:
                common = [sys.executable, "-I", "-B", *optimize, "-c"]
                setup = "import sys; sys.path.insert(0, " + repr(directory) + "); "
                control = subprocess.run(common + [setup +
                    "import cached_tracker; print(cached_tracker.read(42))"],
                    check=True, capture_output=True, text=True)
                self.assertEqual(control.stdout, "999\n")
                # Drive the actual worker entry point; stubs isolate source loading
                # from EELS installation and finite observation/authentication content.
                code = ("import runpy, json; driver=runpy.run_path(" + repr(str(SPEC.origin)) +
                        "); namespace=driver['main'].__globals__; " + setup +
                        "namespace['probe']=lambda: print(__import__('cached_tracker').read(42)); "
                        "namespace['authenticate']=lambda eels, policy: "
                        "policy.compiled_sources['cached_tracker']; "
                        "sys.argv=['source', '--worker', 'probe', '--eels', " +
                        repr(directory) + "]; driver['main']()")
                checked = subprocess.run(common + [code], check=True,
                                         capture_output=True, text=True)
                envelope = json.loads(checked.stdout)
                self.assertEqual(envelope["observations"], "111\n")
                self.assertEqual(envelope["authentication"], SOURCE.file_identity(module))
            for cache, original_bytes in caches:
                self.assertEqual(cache.read_bytes(), original_bytes)
            self.assertEqual(module.read_text(), original)

    def test_sourceless_bytecode_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            module = Path(directory) / "cached_only.py"
            module.write_text("answer = 999\n")
            py_compile.compile(str(module), cfile=str(module.with_suffix('.pyc')), doraise=True)
            module.unlink()
            code = ("import runpy, sys; driver=runpy.run_path(" + repr(str(SPEC.origin)) +
                    "); driver['install_source_only_imports'](); sys.path.insert(0, " +
                    repr(directory) + "); import cached_only")
            result = subprocess.run([sys.executable, "-I", "-B", "-c", code],
                                    capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("sourceless bytecode", result.stderr)


if __name__ == "__main__":
    unittest.main()
