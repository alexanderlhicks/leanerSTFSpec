#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Exact-byte freshness CLI regressions; mutate only independent temporary copies."""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
GENERATOR = Path("scripts/gen_packed_keccak.py")
TARGET = Path("STFSpec/Hash/PackedKeccakPermutation.lean")


class PackedKeccakGeneratorChecks(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="stfspec-packed-keccak-generator-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / "repository"
        self.external = Path(self.temp.name) / "external"
        self.external.mkdir()
        for relative in (GENERATOR, TARGET):
            target = self.root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / relative, target)
        self.target = self.root / TARGET
        self.lf = self.target.read_bytes()
        self.assertIn(b"\n", self.lf)
        self.assertNotIn(b"\r", self.lf)

    def check(self, fresh):
        for cwd in (self.root, self.external):
            with self.subTest(cwd=cwd.name):
                before = self.target.read_bytes() if self.target.exists() else None
                result = subprocess.run(
                    [sys.executable, str(self.root / GENERATOR), "--check"],
                    cwd=cwd, capture_output=True, text=True,
                )
                after = self.target.read_bytes() if self.target.exists() else None
                self.assertEqual(after, before, "--check changed the target bytes or existence")
                self.assertEqual(result.returncode, 0 if fresh else 1,
                                 result.stdout + result.stderr)
                self.assertEqual(result.stdout, "")
                self.assertEqual(result.stderr, "" if fresh else
                                 "generated packed Keccak permutation is stale\n")

    def test_exact_lf(self):
        self.check(fresh=True)

    def test_crlf(self):
        crlf = self.lf.replace(b"\n", b"\r\n")
        self.assertNotEqual(crlf, self.lf)
        self.assertEqual(crlf.decode("utf-8").replace("\r\n", "\n"),
                         self.lf.decode("utf-8"))
        self.target.write_bytes(crlf)
        self.check(fresh=False)

    def test_changed_coordinate(self):
        old = b"keccakLane a 0 0"
        self.assertIn(old, self.lf)
        self.target.write_bytes(self.lf.replace(old, b"keccakLane a 0 1", 1))
        self.check(fresh=False)

    def test_missing_target(self):
        self.target.unlink()
        self.check(fresh=False)


if __name__ == "__main__":
    unittest.main()
