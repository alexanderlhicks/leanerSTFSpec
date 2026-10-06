# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Offline regressions for frozen-source differential imports and Git safeguards."""

import argparse
import base64
import hashlib
from contextlib import contextmanager, redirect_stderr
import importlib.machinery
import importlib.metadata
import importlib.util
import io
import os
from pathlib import Path
import py_compile
import shutil
import subprocess
import sys
from types import CodeType, FunctionType, ModuleType, SimpleNamespace
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
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

    def prepare_initializer(self):
        source, distribution = self.install_dependency_fixture()
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.spec = Path(temp.name) / "spec"
        self.spec.mkdir()
        self.script = self.spec / "STFSpec/Conformance/Base/example.py"
        (self.spec / "reference.toml").write_text(
            f'[release]\ncommit = "{self.driver.head}"\n'
            '[release.python_dependencies]\nethereum-types = "1.0"\n')
        self.argv = [str(self.script), "--eels", str(self.root),
                     "--output", str(self.spec.parent / "evidence.lean")]
        return source, distribution

    @contextmanager
    def initializer_environment(self, distribution):
        flags = SimpleNamespace(**{name: getattr(sys.flags, name)
                                   for name in dir(sys.flags) if not name.startswith("_")})
        flags.isolated = 1
        package_path = distribution.locate_file("")
        with patch.dict(sys.modules), patch.object(sys, "flags", flags), \
                patch.object(sys, "path", [str(package_path)]), \
                patch.object(sys, "meta_path", list(sys.meta_path)), \
                patch.object(sys, "prefix", str(self.root / ".venv")), \
                patch.object(sys, "argv", self.argv):
            for name in list(sys.modules):
                if name.split(".", 1)[0] in ("ethereum", "ethereum_types"):
                    sys.modules.pop(name)
            yield

    def test_initializer_installs_finder_before_reference_import(self):
        source, distribution = self.prepare_initializer()
        # A successful real initializer must install the loader before importing
        # numeric, not merely return a finder object that a test invokes directly.
        self.driver.load_dependency_hashes(distribution)
        self.cache_control(source, "ethereum_types.numeric")
        with self.initializer_environment(distribution):
            driver = Driver("test", self.script, 7)
            self.assertIsInstance(sys.meta_path[0], FreshSourceFinder)
            self.assertIs(sys.meta_path[0].driver, driver)
            numeric = sys.modules["ethereum_types.numeric"]
            self.assertEqual(numeric.VALUE, 1)
            self.assertIsInstance(numeric.__loader__, FreshSourceLoader)
            self.assertEqual(driver.dependency, source)
            self.assertEqual(driver.seed, 7)

    def test_initializer_rejects_wrong_prefix(self):
        _, distribution = self.prepare_initializer()
        with self.initializer_environment(distribution), \
                patch.object(sys, "prefix", str(self.spec)), \
                redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as raised:
            Driver("test", self.script, 7)
        self.assertEqual(raised.exception.code, 2)

    def test_initializer_rejects_wrong_pin(self):
        _, distribution = self.prepare_initializer()
        pin = self.spec / "reference.toml"
        pin.write_text(pin.read_text().replace(self.driver.head, "0" * 40))
        with self.initializer_environment(distribution), \
                redirect_stderr(io.StringIO()) as errors, \
                self.assertRaises(SystemExit) as raised:
            Driver("test", self.script, 7)
        self.assertEqual(raised.exception.code, 2)
        self.assertIn("EELS checkout does not match reference.toml", errors.getvalue())

    def test_initializer_rejects_wrong_dependency_version(self):
        _, distribution = self.prepare_initializer()
        Path(distribution.locate_file("ethereum_types-1.0.dist-info/METADATA")).write_text(
            "Name: ethereum-types\nVersion: 2.0\n")
        with self.initializer_environment(distribution), \
                redirect_stderr(io.StringIO()) as errors, \
                self.assertRaises(SystemExit) as raised:
            Driver("test", self.script, 7)
        self.assertEqual(raised.exception.code, 2)
        self.assertIn("ethereum-types version does not match reference.toml", errors.getvalue())

    def test_initializer_rejects_dependency_export_from_wrong_source(self):
        source, distribution = self.prepare_initializer()
        # Every installed byte has a valid RECORD hash. Importing the requested
        # attribute still yields another source file, so RECORD checking alone
        # cannot establish the source-to-observation mapping.
        alternative = source.with_name("alternative.py")
        alternative.write_text("VALUE = 9\n")
        source.with_name("__init__.py").write_text("from . import alternative as numeric\n")
        records = []
        for file in sorted(source.parent.glob("*.py")):
            data = file.read_bytes()
            digest = base64.urlsafe_b64encode(hashlib.sha256(data).digest()).decode().rstrip("=")
            records.append(f"ethereum_types/{file.name},sha256={digest},{len(data)}")
        records.append("ethereum_types-1.0.dist-info/RECORD,,")
        Path(distribution.locate_file("ethereum_types-1.0.dist-info/RECORD")).write_text(
            "\n".join(records) + "\n")
        with self.initializer_environment(distribution), \
                redirect_stderr(io.StringIO()) as errors, \
                self.assertRaises(SystemExit) as raised:
            Driver("test", self.script, 7)
        self.assertEqual(raised.exception.code, 2)
        self.assertIn("ethereum_types/numeric.py was imported outside", errors.getvalue())

    def test_initializer_rejects_internal_output(self):
        _, distribution = self.prepare_initializer()
        for output in (self.spec / "evidence.lean", self.root / ".venv/evidence.lean"):
            with self.subTest(output=output), self.initializer_environment(distribution), \
                    patch.object(sys, "argv", self.argv[:-1] + [str(output)]), \
                    redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as raised:
                Driver("test", self.script, 7)
            self.assertEqual(raised.exception.code, 2)
            self.assertFalse(output.exists())

    def test_initializer_rejects_preloaded_reference(self):
        _, distribution = self.prepare_initializer()
        for name in ("ethereum", "ethereum_types.numeric"):
            with self.subTest(name=name), self.initializer_environment(distribution), \
                    patch.dict(sys.modules, {name: ModuleType(name)}), \
                    redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as raised:
                Driver("test", self.script, 7)
            self.assertEqual(raised.exception.code, 2)

    def test_initializer_rejects_unisolated_interpreter(self):
        _, distribution = self.prepare_initializer()
        with self.initializer_environment(distribution), \
                patch.object(sys.flags, "isolated", 0), redirect_stderr(io.StringIO()), \
                self.assertRaises(SystemExit) as raised:
            Driver("test", self.script, 7)
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
        metadata = package.parent / "ethereum_types-1.0.dist-info"
        metadata.mkdir()
        digest = base64.urlsafe_b64encode(
            hashlib.sha256(source.read_bytes()).digest()).decode().rstrip("=")
        (package / "__init__.py").write_text("")
        empty_digest = base64.urlsafe_b64encode(hashlib.sha256(b"").digest()).decode().rstrip("=")
        (metadata / "METADATA").write_text("Name: ethereum-types\nVersion: 1.0\n")
        (metadata / "RECORD").write_text(
            f"ethereum_types/numeric.py,sha256={digest},{source.stat().st_size}\n"
            f"ethereum_types/__init__.py,sha256={empty_digest},0\n"
            "ethereum_types-1.0.dist-info/RECORD,,\n")
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
            "ethereum_types/numeric.py,,10\n" + "ethereum_types-1.0.dist-info/RECORD,,\n")
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

    def test_finder_rejects_oracle_package_in_dependency_directory(self):
        finder = FreshSourceFinder(self.driver)
        pinned = finder.find_spec("ethereum", [str(self.root / "src")])
        namespace = {}
        exec(pinned.loader.get_code("ethereum"), namespace)
        self.assertEqual(namespace["VALUE"], 1)
        installed = self.root / ".venv/lib/site-packages"
        counterfeit = installed / "ethereum/__init__.py"
        counterfeit.parent.mkdir(parents=True)
        counterfeit.write_text("VALUE = 9\n")
        control = importlib.machinery.PathFinder.find_spec("ethereum", [str(installed)])
        self.assertEqual(Path(control.origin), counterfeit)
        # A Python source file inside the frozen venv is not thereby the pinned
        # ethereum package. The finder rejects the path before loading its code.
        with self.assertRaisesRegex(ImportError, "outside the frozen environment"):
            finder.find_spec("ethereum", [str(installed)])

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
        fullname = "checkout_bytecode"
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
        fullname = "checkout_alias"
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
        fullname = "checkout_source"
        package, _, marker = self.checkout_package(fullname)
        subprocess.check_call(["git", "init", "--quiet", str(package)])
        self.driver.check_clean()
        with self.assertRaisesRegex(ImportError, "import bytes differ from the pin"):
            self.import_package(fullname, FreshSourceFinder(self.driver))
        self.assertFalse(marker.exists())

    def test_non_oracle_checkout_source_alias(self):
        fullname = "checkout_source_alias"
        _, source, marker = self.checkout_package(fullname)
        external = self.root / ".venv/package.py"
        external.parent.mkdir()
        source.rename(external)
        source.symlink_to(external)
        self.driver.check_clean()
        with self.assertRaisesRegex(ImportError, "source alias"):
            self.import_package(fullname, FreshSourceFinder(self.driver))
        self.assertFalse(marker.exists())

    def test_sourceless_external_path_resolves_into_checkout(self):
        fullname = "checkout_resolved_bytecode"
        package, source, marker = self.checkout_package(fullname)
        py_compile.compile(str(source), cfile=str(package / "__init__.pyc"), doraise=True)
        source.unlink()
        external = self.root / ".venv/checkout-alias"
        external.parent.mkdir()
        external.symlink_to(self.root / "src", target_is_directory=True)
        with patch.dict(sys.modules), patch.object(sys, "path", [str(external), *sys.path]), \
                patch.object(sys, "meta_path", [FreshSourceFinder(self.driver), *sys.meta_path]), \
                self.assertRaisesRegex(ImportError, "not Python source"):
            sys.modules.pop(fullname, None)
            importlib.import_module(fullname)
        self.assertFalse(marker.exists())
        # Removing the resolve() arm admits this same package and runs its code.
        with patch.dict(sys.modules), patch.object(sys, "path", [str(external), *sys.path]):
            sys.modules.pop(fullname, None)
            control = importlib.import_module(fullname)
        self.assertEqual(control.VALUE, 0)
        self.assertTrue(marker.exists())

    def test_isolated_startup_ignores_python_environment(self):
        startup = self.root / ".venv/startup"
        startup.mkdir(parents=True)
        marker = self.root / ".venv/startup-executed"
        (startup / "sitecustomize.py").write_text(
            f"from pathlib import Path\nPath({str(marker)!r}).touch()\n")
        env = dict(os.environ, PYTHONPATH=str(startup))
        control = subprocess.run([sys.executable, "-c", "pass"], env=env,
                                 capture_output=True, text=True)
        self.assertEqual(control.returncode, 0, control.stderr)
        self.assertTrue(marker.exists(), "unisolated startup must execute the control")
        marker.unlink()
        isolated = subprocess.run([sys.executable, "-I", "-c", "pass"], env=env,
                                  capture_output=True, text=True)
        self.assertEqual(isolated.returncode, 0, isolated.stderr)
        self.assertFalse(marker.exists())
        # -I also ignores a bad PYTHONHOME before any driver or site code runs.
        env["PYTHONHOME"] = str(startup / "missing-python-home")
        isolated = subprocess.run([sys.executable, "-I", "-c", "pass"], env=env,
                                  capture_output=True, text=True)
        self.assertEqual(isolated.returncode, 0, isolated.stderr)
        self.assertFalse(marker.exists())

    def test_harness_disables_ordinary_import_cache_writes(self):
        source = self.root / ".venv/review_cache_control.py"
        source.parent.mkdir()
        source.write_text("VALUE = 1\n")
        scripts = Path(__file__).resolve().parent
        probe = (
            "import importlib,sys\n"
            "sys.path.insert(0,sys.argv[1])\n"
            "if sys.argv[3] == 'harness':\n"
            "    import differential\n"
            "sys.path.insert(0,sys.argv[2])\n"
            "module=importlib.import_module('review_cache_control')\n"
            "if module.VALUE != 1: raise RuntimeError('wrong import result')\n"
            "print(module.__cached__)\n"
        )
        for mode in ("ordinary", "harness"):
            with self.subTest(mode=mode):
                result = subprocess.run(
                    [sys.executable, "-I", "-c", probe, str(scripts), str(source.parent), mode],
                    capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                cache = Path(result.stdout.strip())
                self.assertEqual(cache.exists(), mode == "ordinary")
                cache.unlink(missing_ok=True)

    def test_installed_native_dependency_preserved(self):
        spec = importlib.machinery.PathFinder.find_spec("_json")
        self.assertIsInstance(spec.loader, importlib.machinery.ExtensionFileLoader)
        installed = self.root / ".venv/lib"
        installed.mkdir(parents=True)
        shutil.copy2(spec.origin, installed / Path(spec.origin).name)
        self.assertIsNone(FreshSourceFinder(self.driver).find_spec("_json", [str(installed)]))


class CodeIdentityTests(unittest.TestCase):
    """Offline code-content checks; no oracle imports or Git fixture setup."""

    @classmethod
    def setUpClass(cls):
        path = (Path(__file__).resolve().parents[1] /
                "STFSpec/Conformance/Commit/incremental_root_differential.py")
        spec = importlib.util.spec_from_file_location("incremental_root_identity_tests", path)
        cls.driver = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.driver)

    def function(self):
        scope = {}
        exec(compile("def target(x=5):\n"
                     "    return (x, (938271, 813791), 'long-synthetic-constant-abcdef')\n",
                     "<code identity fixture>", "exec"), scope)
        return scope["target"]

    def code(self):
        module = compile("def outer(x=5, *, y=6):\n"
                         "    def nested(z):\n"
                         "        return (z, (747481, 813791))\n"
                         "    return (x, y, nested)\n",
                         "<nested identity fixture>", "exec")
        return next(value for value in module.co_consts if type(value) is CodeType)

    def test_unchanged_constants_reference(self):
        function = self.function()
        code = function.__code__
        before = self.driver._code_digest(code)
        held = code.co_consts
        self.assertEqual(before, self.driver._code_digest(code))
        self.assertIs(function.__code__, code)
        self.assertIs(held, code.co_consts)

    def test_unchanged_result_reference(self):
        function = self.function()
        code = function.__code__
        before = self.driver._code_digest(code)
        function(8)  # Discarded result.
        self.assertEqual(before, self.driver._code_digest(code))
        held = function(8)
        self.assertEqual(before, self.driver._code_digest(code))
        self.assertIs(function.__code__, code)
        self.assertEqual(held[0], 8)
        held = None
        self.assertEqual(before, self.driver._code_digest(code))

    def test_unchanged_constructor_reference(self):
        scope = {}
        exec(compile("class Fixture:\n"
                     "    def __init__(self):\n"
                     "        self.value = (938271, 813791)\n",
                     "<constructor identity fixture>", "exec"), scope)
        constructor = scope["Fixture"].__init__
        code = constructor.__code__
        before = self.driver._code_digest(code)
        instance = scope["Fixture"]()
        self.assertEqual(before, self.driver._code_digest(code))
        self.assertIs(constructor.__code__, code)
        self.assertEqual(instance.value, (938271, 813791))

    def test_changed_code_fields(self):
        code = self.code()
        changes = [
            dict(co_argcount=0), dict(co_posonlyargcount=1), dict(co_kwonlyargcount=0),
            dict(co_nlocals=code.co_nlocals + 1, co_varnames=code.co_varnames + ("extra",)),
            dict(co_stacksize=code.co_stacksize + 1), dict(co_flags=code.co_flags ^ 64),
            dict(co_code=code.co_code + code.co_code[-2:]),
            dict(co_consts=code.co_consts + (938271,)),
            dict(co_names=code.co_names + ("new_name",)),
            dict(co_varnames=("renamed",) + code.co_varnames[1:]),
            dict(co_freevars=("new_free",)), dict(co_cellvars=("new_cell",)),
            dict(co_filename=code.co_filename + "x"), dict(co_name=code.co_name + "x"),
            dict(co_qualname=code.co_qualname + "x"), dict(co_firstlineno=code.co_firstlineno + 1),
            dict(co_linetable=code.co_linetable + bytes([0])),
            dict(co_exceptiontable=code.co_exceptiontable + bytes([0])),
        ]
        before = self.driver._code_digest(code)
        for change in changes:
            with self.subTest(fields=tuple(change)):
                self.assertNotEqual(before, self.driver._code_digest(code.replace(**change)))

    def test_changed_nested_code(self):
        code = self.code()
        nested = next(value for value in code.co_consts if type(value) is CodeType)
        changed = nested.replace(co_consts=nested.co_consts + ("changed",))
        outer = code.replace(co_consts=tuple(
            changed if value is nested else value for value in code.co_consts))
        self.assertNotEqual(self.driver._code_digest(code), self.driver._code_digest(outer))

    def test_typed_constants(self):
        code = self.code()
        for left, right in [(False, 0), (True, 1), (1, 1.0), (b"abc", "abc"),
                            ((1, 2), frozenset((1, 2)))]:
            with self.subTest(left=type(left), right=type(right)):
                self.assertNotEqual(
                    self.driver._code_digest(code.replace(co_consts=(None, left))),
                    self.driver._code_digest(code.replace(co_consts=(None, right))))

    def test_supported_constants_roundtrip(self):
        import marshal
        import struct
        code = self.code()
        values = [frozenset(("abc", "def", 3)), -0.0, float("inf"),
                  complex(2.5, -0.0), b"\x00\xff"]
        for value in values:
            with self.subTest(kind=type(value)):
                original = code.replace(co_consts=(None, value))
                restored = marshal.loads(marshal.dumps(original, 2))
                self.assertEqual(self.driver._code_digest(original),
                                 self.driver._code_digest(restored))
                self.assertIs(type(value), type(restored.co_consts[1]))
                if type(value) is float:
                    self.assertEqual(struct.pack(">d", value),
                                     struct.pack(">d", restored.co_consts[1]))
                elif type(value) is complex:
                    self.assertEqual(
                        struct.pack(">dd", value.real, value.imag),
                        struct.pack(">dd", restored.co_consts[1].real, restored.co_consts[1].imag))
                else:
                    self.assertEqual(value, restored.co_consts[1])

    def test_content_clone_keeps_distinct_live_identity(self):
        function = self.function()
        code = function.__code__
        clone = code.replace()
        self.assertEqual(self.driver._code_digest(code), self.driver._code_digest(clone))
        self.assertIsNot(code, clone)
        replacement = FunctionType(
            clone, function.__globals__, function.__name__, function.__defaults__)
        self.assertNotEqual((id(function), id(code)),
                            (id(replacement), id(replacement.__code__)))


if __name__ == "__main__":
    unittest.main()
