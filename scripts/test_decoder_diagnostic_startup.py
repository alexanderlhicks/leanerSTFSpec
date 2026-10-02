#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Regression controls for decoder diagnostic driver startup before oracle activity."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
DRIVER = ROOT / "STFSpec/Conformance/Commit/decoder_diagnostic_differential.py"


class StartupTests(unittest.TestCase):
    def launch(self, script, flags, arguments=()):
        environment = dict(os.environ)
        for name in ("PYTHONOPTIMIZE", "PYTHONDONTWRITEBYTECODE"):
            environment.pop(name, None)
        return subprocess.run(
            [sys.executable, *flags, str(script), *map(str, arguments)],
            cwd=ROOT, env=environment, capture_output=True, timeout=30,
        )

    def test_flags_before_helper_import(self):
        # The real startup source must reject unsupported modes before importing
        # even the helper. A marker at import detects premature oracle setup.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            script = root / "STFSpec/Conformance/Commit" / DRIVER.name
            script.parent.mkdir(parents=True)
            script.write_bytes(DRIVER.read_bytes())
            helper = root / "STFSpec/Conformance/Codec/rlp_typed_differential.py"
            helper.parent.mkdir(parents=True)
            marker = root / "helper-import.json"
            helper.write_text(
                "import json, sys\nfrom pathlib import Path\n"
                f"Path({str(marker)!r}).write_text(json.dumps({{"
                "'isolated': sys.flags.isolated, "
                "'dont_write_bytecode': sys.flags.dont_write_bytecode, "
                "'optimize': sys.flags.optimize}))\n"
                "raise SystemExit(73)\n"
            )
            for flags in ([], ["-B"], ["-I"], ["-I", "-B", "-O"],
                          ["-I", "-B", "-OO"]):
                with self.subTest(flags=flags):
                    result = self.launch(script, flags)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn(b"unoptimized lexical EELS", result.stderr)
                    self.assertEqual(result.stdout, b"")
                    self.assertFalse(marker.exists())
            result = self.launch(script, ["-I", "-B"])
            self.assertEqual(result.returncode, 73)
            self.assertEqual(result.stdout, b"")
            self.assertEqual(result.stderr, b"")
            self.assertEqual(json.loads(marker.read_text()),
                             {"isolated": 1, "dont_write_bytecode": 1, "optimize": 0})

    def test_missing_arguments_before_oracle_or_output(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "observations.lean"
            for arguments in ([], ["--output", output]):
                with self.subTest(arguments=arguments):
                    result = self.launch(DRIVER, ["-I", "-B"], arguments)
                    self.assertEqual(result.returncode, 2)
                    self.assertIn(b"the following arguments are required", result.stderr)
                    self.assertEqual(result.stdout, b"")
                    self.assertFalse(output.exists())

    def test_missing_oracle_before_output(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            output = root / "observations.lean"
            result = self.launch(
                DRIVER, ["-I", "-B"],
                ["--eels", root / "missing-eels", "--output", output],
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(b"FileNotFoundError", result.stderr)
            self.assertEqual(result.stdout, b"")
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
