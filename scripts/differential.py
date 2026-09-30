# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Shared safeguards for value differential drivers against the pinned EELS.

Create a fresh reference clone, check out reference.toml's release.commit, and run
`uv sync --frozen --no-dev` there. Invoke each driver with EELS/.venv/bin/python,
--eels EELS and --output pointing outside both repositories. Drivers execute actual
Python sources and emit ordinary Lean guards; observations are bug-finding evidence.
"""

import argparse
import importlib.metadata
import json
from pathlib import Path
import subprocess
import sys
import tomllib
from types import SimpleNamespace

# Set before any reference imports, including imports performed by driver setup.
sys.dont_write_bytecode = True

FRAME_GAS = 1_000_000


class Driver:
    """A validated reference environment and external Lean evidence destination."""

    def __init__(self, description, script, seed):
        self.root = Path(script).resolve().parents[3]
        self.seed = seed
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
        self.head = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=self.eels, text=True).strip()
        if self.head != pin["commit"]:
            self.parser.error("EELS checkout does not match reference.toml")
        self.check_clean()
        if Path(sys.prefix).resolve() != self.eels / ".venv":
            self.parser.error("run with the EELS .venv interpreter (uv sync --frozen --no-dev)")
        self.version = importlib.metadata.version("ethereum-types")
        if self.version != pin["python_dependencies"]["ethereum-types"]:
            self.parser.error("ethereum-types version does not match reference.toml")
        if self.output.is_relative_to(self.root) or self.output.is_relative_to(self.eels):
            self.parser.error("generated evidence must be outside both repositories")
        sys.path.insert(0, str(self.eels / "src"))
        from ethereum_types import numeric
        self.dependency = self.check_source(numeric, "ethereum_types/numeric.py", dependency=True)

    def check_clean(self):
        """Reject tracked changes and untracked files in the reference source tree."""
        status = subprocess.check_output(
            ["git", "status", "--porcelain", "--untracked-files=all"],
            cwd=self.eels, text=True)
        if status:
            self.parser.error("EELS checkout must be clean")

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
        print(json.dumps({**metadata, "eels_commit": self.head,
                          "ethereum_types": self.version, "dependency": str(self.dependency),
                          "seed": self.seed, "guards": len(guards) - 2,
                          "lean_exit": result.returncode, "generated": str(self.output)},
                         sort_keys=True))
        return result.returncode


def setup_driver(description, script, seed):
    """Parse the common CLI and validate its reference before the driver imports EELS."""
    return Driver(description, script, seed)
