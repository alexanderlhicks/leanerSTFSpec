# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Offline regressions for frozen-source differential imports and Git safeguards."""

import argparse
import base64
import hashlib
from contextlib import redirect_stderr
import importlib.machinery
import importlib.metadata
import importlib
import io
import os
from pathlib import Path
import py_compile
import shutil
import subprocess
import sys
from types import ModuleType
import tempfile
import unittest
from unittest.mock import patch

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

    def test_pinned_forks_namespace(self):
        # EELS has ethereum/__init__.py but no ethereum/forks/__init__.py.
        fork = self.source.parent / "forks/amsterdam/__init__.py"
        fork.parent.mkdir(parents=True)
        fork.write_text("VALUE = 1\n")
        self.git("add", ".")
        self.git("-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                 "commit", "--quiet", "-m", "pinned namespace")
        self.driver.head = self.git("rev-parse", "HEAD").strip()
        self.driver.check_clean()
        package = ModuleType("ethereum")
        package.__path__ = [str(self.source.parent)]
        with patch.dict(sys.modules, {"ethereum": package}):
            spec = FreshSourceFinder(self.driver).find_spec(
                "ethereum.forks", package.__path__)
            self.assertIsNone(spec.loader)
            self.assertEqual(list(spec.submodule_search_locations),
                             [str(self.source.parent / "forks")])

    def test_namespace_rejects_foreign_search_location(self):
        for root in (self.source.parent, self.root / "foreign/ethereum"):
            (root / "forks").mkdir(parents=True)
        package = ModuleType("ethereum")
        package.__path__ = [str(self.source.parent), str(self.root / "foreign/ethereum")]
        with patch.dict(sys.modules, {"ethereum": package}), \
                self.assertRaisesRegex(ImportError, "namespace search"):
            FreshSourceFinder(self.driver).find_spec("ethereum.forks", package.__path__)

    def test_replace_refs_do_not_replace_pin(self):
        pinned = self.driver.head
        self.source.write_text("VALUE = 9\n")
        self.git("add", ".")
        self.git("-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                 "commit", "--quiet", "-m", "replacement oracle")
        replacement = self.git("rev-parse", "HEAD").strip()
        self.git("replace", pinned, replacement)
        self.git("reset", "--hard", pinned)
        self.assertEqual(self.git("status", "--porcelain"), "")
        self.assert_dirty()

    def test_inherited_git_environment_is_ignored(self):
        foreign = self.root / ".venv/foreign"
        foreign.mkdir(parents=True)
        subprocess.check_call(["git", "init", "--quiet", str(foreign)])
        with patch.dict(os.environ, {"GIT_DIR": str(foreign / ".git"),
                                    "GIT_INDEX_FILE": str(foreign / "index"),
                                    "GIT_OBJECT_DIRECTORY": str(foreign / ".git/objects"),
                                    "GIT_CONFIG_COUNT": "1", "GIT_CONFIG_KEY_0": "core.bare",
                                    "GIT_CONFIG_VALUE_0": "true"}):
            self.driver.check_clean()

    def test_dependency_record_rejects_changed_source(self):
        source, _ = self.install_dependency_fixture()
        source.write_text("VALUE = 9\n")
        with self.assertRaisesRegex(ImportError, "dependency source bytes"):
            FreshSourceLoader("ethereum_types.numeric", str(source), self.driver).get_code(
                "ethereum_types.numeric")

    def install_dependency_fixture(self):
        package = self.root / ".venv/lib/site-packages/ethereum_types"
        package.mkdir(parents=True)
        source = package / "numeric.py"
        source.write_text("VALUE = 1\n")
        metadata = package.parent / "types.dist-info"
        metadata.mkdir()
        digest = base64.urlsafe_b64encode(hashlib.sha256(source.read_bytes()).digest()).decode().rstrip("=")
        (metadata / "RECORD").write_text(
            f"ethereum_types/numeric.py,sha256={digest},{source.stat().st_size}\n"
            "types.dist-info/RECORD,,\n")
        distribution = importlib.metadata.PathDistribution(metadata)
        self.driver.load_dependency_hashes(distribution)
        return source, distribution

    def test_dependency_unloaded_source_revalidated(self):
        source, _ = self.install_dependency_fixture()
        source.write_text("VALUE = 9\n")
        with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            self.driver.check_dependency()

    def test_dependency_unlisted_source_rejected(self):
        source, _ = self.install_dependency_fixture()
        extra = source.parent / "extra.py"
        extra.write_text("VALUE = 1\n")
        with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            self.driver.check_dependency()
        with self.assertRaisesRegex(ImportError, "dependency source bytes"):
            FreshSourceLoader("ethereum_types.extra", str(extra), self.driver).get_code(
                "ethereum_types.extra")

    def test_dependency_record_change_rejected(self):
        _, distribution = self.install_dependency_fixture()
        (distribution._path / "RECORD").write_text("changed\n")
        with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            self.driver.check_dependency()

    def test_dependency_missing_hash_rejected(self):
        _, distribution = self.install_dependency_fixture()
        (distribution._path / "RECORD").write_text(
            "ethereum_types/numeric.py,,10\n" + "types.dist-info/RECORD,,\n")
        with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            self.driver.load_dependency_hashes(distribution)

    def test_dependency_symlink_rejected(self):
        source, _ = self.install_dependency_fixture()
        copy = source.parent / "numeric-copy"
        source.rename(copy)
        source.symlink_to(copy)
        with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            self.driver.check_dependency()

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

    def import_package(self, fullname, finder):
        with patch.dict(sys.modules), \
                patch.object(sys, "path", [str(self.root / "src"), *sys.path]), \
                patch.object(sys, "meta_path", [finder, *sys.meta_path]):
            sys.modules.pop(fullname, None)
            return importlib.import_module(fullname)

    def checkout_package(self, fullname):
        package = self.root / "src" / fullname
        package.mkdir()
        with (self.root / ".git/info/exclude").open("a") as stream:
            stream.write(f"\nsrc/{fullname}/\n")
        marker = package / "executed"
        source = package / "__init__.py"
        source.write_text(f"from pathlib import Path\nPath({str(marker)!r}).touch()\nVALUE = 0\n")
        return package, source, marker

    def test_non_oracle_sourceless_checkout_package(self):
        fullname = "wi010_checkout_bytecode"
        package, source, marker = self.checkout_package(fullname)
        py_compile.compile(str(source), cfile=str(package / "__init__.pyc"), doraise=True)
        source.unlink()
        # Real import machinery executes the unexpected package, despite clean Git.
        self.driver.check_clean()
        control = self.import_package(fullname, importlib.machinery.PathFinder)
        self.assertEqual(control.VALUE, 0)
        self.assertTrue(marker.exists())
        marker.unlink()
        self.driver.check_clean()
        with self.assertRaisesRegex(ImportError, "not Python source"):
            self.import_package(fullname, FreshSourceFinder(self.driver))
        self.assertFalse(marker.exists())

    def test_non_oracle_sourceless_checkout_alias(self):
        fullname = "wi010_checkout_alias"
        package, source, marker = self.checkout_package(fullname)
        external = self.root / ".venv/package.pyc"
        external.parent.mkdir()
        py_compile.compile(str(source), cfile=str(external), doraise=True)
        source.unlink()
        (package / "__init__.pyc").symlink_to(external)
        self.driver.check_clean()
        with self.assertRaisesRegex(ImportError, "not Python source"):
            self.import_package(fullname, FreshSourceFinder(self.driver))
        self.assertFalse(marker.exists())

    def test_non_oracle_nested_git_package(self):
        fullname = "wi010_checkout_source"
        package, _, marker = self.checkout_package(fullname)
        subprocess.check_call(["git", "init", "--quiet", str(package)])
        self.driver.check_clean()
        with self.assertRaisesRegex(ImportError, "import bytes differ from the pin"):
            self.import_package(fullname, FreshSourceFinder(self.driver))
        self.assertFalse(marker.exists())

    def test_non_oracle_checkout_source_alias(self):
        fullname = "wi010_checkout_source_alias"
        _, source, marker = self.checkout_package(fullname)
        external = self.root / ".venv/package.py"
        external.parent.mkdir()
        source.rename(external)
        source.symlink_to(external)
        self.driver.check_clean()
        with self.assertRaisesRegex(ImportError, "source alias"):
            self.import_package(fullname, FreshSourceFinder(self.driver))
        self.assertFalse(marker.exists())

    def test_installed_native_dependency_preserved(self):
        spec = importlib.machinery.PathFinder.find_spec("_json")
        self.assertIsInstance(spec.loader, importlib.machinery.ExtensionFileLoader)
        installed = self.root / ".venv/lib"
        installed.mkdir(parents=True)
        shutil.copy2(spec.origin, installed / Path(spec.origin).name)
        self.assertIsNone(FreshSourceFinder(self.driver).find_spec("_json", [str(installed)]))


if __name__ == "__main__":
    unittest.main()
