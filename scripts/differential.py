# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Shared safeguards for value differential drivers against the pinned EELS.

Create a fresh reference clone, check out reference.toml's release.commit, and run
`uv sync --frozen --no-dev` there. Invoke each driver with EELS/.venv/bin/python,
--eels EELS and --output pointing outside both repositories. Drivers compile current
source bytes without cached code. EELS bytes are compared with the unreplaced pin;
ethereum-types Python bytes are compared with the installed distribution RECORD.
The interpreter, frozen installation and its RECORD remain trusted inputs (this
is not an authentication of a hostile host). Observations are bug-finding evidence.
"""

import argparse
import base64
import hashlib
import importlib.abc
import importlib.machinery
import importlib.metadata
import json
import os
from pathlib import Path
import subprocess
import sys
import tomllib
from types import SimpleNamespace

# Set before any reference imports, including imports performed by driver setup.
sys.dont_write_bytecode = True

FRAME_GAS = 1_000_000


class FreshSourceLoader(importlib.machinery.SourceFileLoader):
    """Compile source bytes directly; Python's -B still permits reading cached code."""

    def __init__(self, fullname, path, driver):
        super().__init__(fullname, path)
        self.driver = driver

    def get_code(self, fullname):
        source = self.get_filename(fullname)
        data = self.get_data(source)
        relative = Path(source).resolve().relative_to(self.driver.eels)
        if fullname.split(".", 1)[0] == "ethereum" or relative.parts[0] == "src":
            expected = self.driver.oracle_blobs.get(relative.as_posix())
            observed = self.driver.git("hash-object", "--stdin", "--no-filters",
                                       input=data).decode().strip()
            if expected is None or observed != expected:
                raise ImportError(f"oracle import bytes differ from the pin: {relative}")
        if fullname.split(".", 1)[0] == "ethereum_types":
            if not self.driver.dependency_bytes_match(Path(source), data):
                raise ImportError(f"dependency source bytes differ from installed RECORD: {source}")
        return self.source_to_code(data, source)


class FreshSourceFinder(importlib.abc.MetaPathFinder):
    """Bypass .pyc files for reference and frozen-venv Python source imports."""

    def __init__(self, driver):
        self.driver = driver

    def find_spec(self, fullname, path=None, target=None):
        spec = importlib.machinery.PathFinder.find_spec(fullname, path)
        oracle = fullname.split(".", 1)[0] in ("ethereum", "ethereum_types")
        if spec is None:
            return None
        if spec.loader is None and spec.submodule_search_locations is not None:
            if not oracle:
                return None
            expected = self.driver.eels / "src" / Path(*fullname.split("."))
            locations = list(spec.submodule_search_locations)
            # A namespace contains no code. Admit only directories whose tracked
            # descendants belong to this exact pinned ethereum package path.
            prefix = expected.relative_to(self.driver.eels).as_posix() + "/"
            if (fullname.split(".", 1)[0] != "ethereum" or not locations or
                    any(Path(location).resolve() != expected for location in locations) or
                    not expected.is_relative_to(self.driver.eels / "src/ethereum") or
                    not any(name.startswith(prefix) for name in self.driver.oracle_blobs)):
                raise ImportError(f"oracle namespace search is outside the pin: {fullname}")
            # Freeze the validated paths: _NamespacePath can otherwise recalculate
            # from a subsequently changed parent package search path.
            spec.submodule_search_locations = locations
            return spec
        if not isinstance(spec.loader, importlib.machinery.SourceFileLoader):
            if oracle:
                raise ImportError(f"oracle module is not Python source: {fullname}")
            return None
        source = Path(spec.origin).resolve()
        within = (source.is_relative_to(self.driver.eels / "src") or
                  source.is_relative_to(self.driver.eels / ".venv"))
        if oracle and (not within or
                       (fullname.split(".", 1)[0] == "ethereum" and
                        not source.is_relative_to(self.driver.eels / "src/ethereum"))):
            raise ImportError(f"oracle module is outside the frozen environment: {fullname}")
        if not within:
            return None
        spec.loader = FreshSourceLoader(fullname, str(source), self.driver)
        return spec


class Driver:
    """A validated reference environment and external Lean evidence destination."""

    def __init__(self, description, script, seed):
        self.root = Path(script).resolve().parents[3]
        self.parser = argparse.ArgumentParser(description=description)
        self.parser.add_argument("--eels", required=True, type=Path)
        self.parser.add_argument("--output", required=True, type=Path)
        self.parser.add_argument("--seed", type=int, default=seed,
                                 help="deterministic input seed (default: %(default)s)")
        args = self.parser.parse_args()
        self.seed = args.seed
        self.eels = args.eels.resolve()
        self.output = args.output.resolve()
        pin = tomllib.loads((self.root / "reference.toml").read_text())["release"]
        self.head = self.git("rev-parse", "HEAD", text=True).strip()
        if self.head != pin["commit"]:
            self.parser.error("EELS checkout does not match reference.toml")
        self.check_clean()
        if Path(sys.prefix).resolve() != self.eels / ".venv":
            self.parser.error("run with the EELS .venv interpreter (uv sync --frozen --no-dev)")
        distribution = importlib.metadata.distribution("ethereum-types")
        self.version = distribution.version
        if self.version != pin["python_dependencies"]["ethereum-types"]:
            self.parser.error("ethereum-types version does not match reference.toml")
        self.load_dependency_hashes(distribution)
        if self.output.is_relative_to(self.root) or self.output.is_relative_to(self.eels):
            self.parser.error("generated evidence must be outside both repositories")
        if any(name.split(".", 1)[0] in ("ethereum", "ethereum_types")
               for name in sys.modules):
            self.parser.error("reference modules must not be imported before driver setup")
        sys.path.insert(0, str(self.eels / "src"))
        sys.meta_path.insert(0, FreshSourceFinder(self))
        from ethereum_types import numeric
        self.dependency = self.check_source(numeric, "ethereum_types/numeric.py", dependency=True)

    def git(self, *args, input=None, text=False):
        """Read this checkout without inherited Git overrides or replacement objects."""
        env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
        return subprocess.check_output(
            ["git", "--no-replace-objects", "--no-optional-locks", *args],
            cwd=self.eels, env=env, input=input, text=text)

    def load_dependency_hashes(self, distribution):
        """Snapshot installed RECORD hashes; the frozen installation is a trust input."""
        self.dependency_hashes = {}
        records = []
        for file in distribution.files or []:
            path = Path(file)
            source = Path(distribution.locate_file(file)).absolute()
            if path.name == "RECORD" and path.parent.name.endswith(".dist-info"):
                records.append(source)
            if not path.parts or path.parts[0] != "ethereum_types" or path.suffix != ".py":
                continue
            if (source.resolve() != source or not source.is_relative_to(self.eels / ".venv") or
                    not source.is_file() or file.hash is None or file.hash.mode != "sha256" or
                    file.size is None):
                self.parser.error(f"dependency source lacks a valid installed RECORD entry: {path}")
            self.dependency_hashes[source] = (file.hash.value, file.size)
        if (len(records) != 1 or records[0].resolve() != records[0] or
                not records[0].is_relative_to(self.eels / ".venv") or
                not self.dependency_hashes):
            self.parser.error("ethereum-types installed RECORD is missing or outside the venv")
        self.dependency_record = records[0]
        self.dependency_record_bytes = records[0].read_bytes()
        self.dependency_package = Path(distribution.locate_file("ethereum_types")).absolute()
        self.check_dependency()

    def dependency_bytes_match(self, source, data):
        expected = self.dependency_hashes.get(source)
        digest = base64.urlsafe_b64encode(hashlib.sha256(data).digest()).decode().rstrip("=")
        return (source.resolve() == source and expected == (digest, len(data)))

    def check_dependency(self):
        """Recheck all installed package Python files, including modules not imported."""
        if (self.dependency_record.read_bytes() != self.dependency_record_bytes or
                set(self.dependency_package.rglob("*.py")) != set(self.dependency_hashes)):
            self.parser.error("dependency RECORD or Python source inventory changed")
        for source in self.dependency_hashes:
            if not source.is_file() or not self.dependency_bytes_match(source, source.read_bytes()):
                self.parser.error(f"dependency source bytes differ from installed RECORD: {source}")

    def check_clean(self):
        """Require a clean checkout and actual source/lock bytes at the unreplaced pin."""
        head = self.git("rev-parse", "HEAD", text=True).strip()
        if head != self.head:
            self.parser.error("EELS checkout HEAD changed during the driver run")
        status = self.git("status", "--porcelain", "--untracked-files=all", text=True)
        if status:
            self.parser.error("EELS checkout must be clean")
        # Git's index flags/stat cache can hide changed oracle bytes from status.
        tree = self.git("ls-tree", "-rz", self.head, "--", "src/ethereum", "uv.lock")
        expected, paths = [], []
        for entry in tree.split(b"\0"):
            if not entry:
                continue
            header, raw_path = entry.split(b"\t", 1)
            mode, kind, blob = header.split()
            path = raw_path.decode()
            source = self.eels / path
            if (kind != b"blob" or mode not in (b"100644", b"100755") or
                    source.is_symlink() or not source.is_file() or
                    bool(source.stat().st_mode & 0o111) != (mode == b"100755")):
                self.parser.error(f"oracle file kind/mode differs from the pin: {path}")
            expected.append(blob.decode())
            paths.append(path)
        if not paths:
            self.parser.error("pinned oracle source inventory is empty")
        observed = self.git("hash-object", "--no-filters", "--", *paths, text=True).splitlines()
        if observed != expected:
            self.parser.error("oracle source or lock bytes differ from the pin")
        self.oracle_blobs = dict(zip(paths, expected))

    def check_source(self, module, relative_path, *, dependency=False):
        """Require the exact pinned source path, or the locked dependency's venv path."""
        source = Path(module.__file__).resolve()
        if dependency:
            valid = source.is_relative_to(self.eels / ".venv") and (
                source.parts[-len(Path(relative_path).parts):] == Path(relative_path).parts)
        else:
            valid = source == self.eels / "src" / relative_path
        if not valid:
            self.parser.error(f"{relative_path} was imported outside the pinned environment")
        return source

    def frame(self, values):
        """Fund a minimal frame whose stack pops operands in argument order."""
        from ethereum_types.numeric import U256, Uint
        from ethereum.forks.amsterdam.fork_types import ExecutionGas, StateGas
        from ethereum.forks.amsterdam.vm.gas import GasMeter
        return SimpleNamespace(
            stack=[U256(value) for value in reversed(values)], pc=Uint(0),
            gas_meter=GasMeter(ExecutionGas(Uint(FRAME_GAS)),
                               StateGas(Uint(0)), StateGas(Uint(0))))

    def run_opcode(self, handler, values, *, cost=None):
        """Run a pinned handler, checking the adapter postconditions even under -O."""
        from ethereum.trace import discard_evm_trace, set_evm_trace
        set_evm_trace(discard_evm_trace)
        frame = self.frame(values)
        handler(frame)
        if len(frame.stack) != 1 or int(frame.pc) != 1:
            raise RuntimeError("handler must return one word and advance pc once")
        if cost is not None and int(frame.gas_meter.gas_left) != FRAME_GAS - cost:
            raise RuntimeError("handler gas charge disagrees with the pinned cost")
        for field in ("state_gas_left", "state_gas_baseline", "state_gas_spilled",
                      "state_gas_committed_spill"):
            if int(getattr(frame.gas_meter, field)) != 0:
                raise RuntimeError(f"value handler changed {field}")
        return frame.stack[0]

    def run(self, guards, **metadata):
        """Emit guards, execute Lean and report reproducible reference metadata."""
        self.output.write_text(
            "-- Generated differential evidence; do not commit.\n" + "\n".join(guards) + "\n")
        result = subprocess.run(["lake", "env", "lean", str(self.output)], cwd=self.root)
        self.check_clean()
        self.check_dependency()
        print(json.dumps({**metadata, "eels_commit": self.head,
                          "ethereum_types": self.version, "dependency": str(self.dependency),
                          "seed": self.seed, "guards": len(guards) - 2,
                          "lean_exit": result.returncode, "generated": str(self.output)},
                         sort_keys=True))
        return result.returncode


def setup_driver(description, script, seed):
    """Parse the common CLI and validate its reference before the driver imports EELS."""
    return Driver(description, script, seed)
