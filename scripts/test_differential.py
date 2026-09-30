# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Offline regressions for frozen-source differential imports and Git safeguards."""

import argparse
from contextlib import redirect_stderr
import importlib.machinery
import io
import os
from pathlib import Path
import py_compile
import subprocess
import tempfile
import unittest

from differential import Driver, FreshSourceFinder, FreshSourceLoader


class DifferentialTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.source = self.root / "src/ethereum/__init__.py"
        self.source.parent.mkdir(parents=True)
        self.source.write_text("VALUE = 1\n")
        (self.root / "uv.lock").write_text("locked\n")
        (self.root / ".gitignore").write_text("__pycache__/\n.venv/\n")
        self.git("init", "--quiet")
        self.git("add", ".")
        self.git("-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                 "commit", "--quiet", "-m", "test oracle")
        self.driver = Driver.__new__(Driver)
        self.driver.eels = self.root
        self.driver.head = self.git("rev-parse", "HEAD").strip()
        self.driver.parser = argparse.ArgumentParser()
        self.driver.check_clean()

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.root, text=True)

    def assert_dirty(self):
        with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as raised:
            self.driver.check_clean()
        self.assertEqual(raised.exception.code, 2)

    def test_hidden_source_edits(self):
        for flag in ("assume-unchanged", "skip-worktree"):
            with self.subTest(flag=flag):
                self.git("update-index", "--" + flag, "src/ethereum/__init__.py")
                self.source.write_text("VALUE = 9\n")
                self.assertEqual(self.git("status", "--porcelain"), "")
                self.assert_dirty()
                self.source.write_text("VALUE = 1\n")
                self.git("update-index", "--no-" + flag, "src/ethereum/__init__.py")

    def test_hidden_lock_edit(self):
        self.git("update-index", "--assume-unchanged", "uv.lock")
        (self.root / "uv.lock").write_text("changed\n")
        self.assertEqual(self.git("status", "--porcelain"), "")
        self.assert_dirty()

    def test_same_stat_source_edit(self):
        self.git("config", "core.trustctime", "false")
        self.git("status", "--porcelain")
        stat = self.source.stat()
        self.source.write_text("VALUE = 9\n")
        os.utime(self.source, ns=(stat.st_atime_ns, stat.st_mtime_ns))
        self.assert_dirty()

    def test_file_modes_and_symlinks(self):
        self.source.chmod(0o755)
        self.assert_dirty()
        self.source.chmod(0o644)
        copy = self.root / "copy.py"
        copy.write_bytes(self.source.read_bytes())
        self.source.unlink()
        self.source.symlink_to(copy)
        self.assert_dirty()

    def test_head_change(self):
        self.git("-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                 "commit", "--allow-empty", "--quiet", "-m", "different head")
        self.assert_dirty()

    def cache_control(self, source, fullname):
        # A timestamp-valid cache containing different, same-length code.
        os.utime(source, (1_700_000_000, 1_700_000_000))
        source.write_text("VALUE = 9\n")
        os.utime(source, (1_700_000_000, 1_700_000_000))
        py_compile.compile(str(source), doraise=True,
                           invalidation_mode=py_compile.PycInvalidationMode.TIMESTAMP)
        source.write_text("VALUE = 1\n")
        os.utime(source, (1_700_000_000, 1_700_000_000))
        old = {}
        exec(importlib.machinery.SourceFileLoader(fullname, str(source)).get_code(fullname), old)
        self.assertEqual(old["VALUE"], 9, "negative control must read the poisoned cache")
        fresh = {}
        exec(FreshSourceLoader(fullname, str(source), self.driver).get_code(fullname), fresh)
        self.assertEqual(fresh["VALUE"], 1)

    def test_ignored_oracle_bytecode(self):
        self.cache_control(self.source, "ethereum")
        self.assertEqual(self.git("status", "--porcelain"), "")
        self.driver.check_clean()

    def test_dependency_bytecode(self):
        source = self.root / ".venv/lib/sample.py"
        source.parent.mkdir(parents=True)
        source.write_text("VALUE = 1\n")
        self.cache_control(source, "sample")

    def test_import_source_revalidated(self):
        self.source.write_text("VALUE = 9\n")
        with self.assertRaisesRegex(ImportError, "import bytes differ"):
            FreshSourceLoader("ethereum", str(self.source), self.driver).get_code("ethereum")

    def test_finder_installs_source_loader(self):
        spec = FreshSourceFinder(self.driver).find_spec("ethereum", [str(self.root / "src")])
        self.assertIsInstance(spec.loader, FreshSourceLoader)

    def test_finder_rejects_sourceless_oracle(self):
        py_compile.compile(str(self.source), cfile=str(self.source.parent / "__init__.pyc"),
                           doraise=True)
        self.source.unlink()
        with self.assertRaisesRegex(ImportError, "not Python source"):
            FreshSourceFinder(self.driver).find_spec("ethereum", [str(self.root / "src")])


if __name__ == "__main__":
    unittest.main()
