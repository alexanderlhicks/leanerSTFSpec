#!/usr/bin/env python3
"""Actual positive and malformed full-value budget CLI regressions, including -O."""

import copy
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
DRIVER = ROOT / "STFSpec/Conformance/Vm/Runner/budget_policy_model.py"
SPEC = importlib.util.spec_from_file_location("budget_model", DRIVER)
MODEL = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODEL)


def encode(frames):
    return "".join(json.dumps(frame, separators=(",", ":")) + "\n" for frame in frames)


def main():
    frames = MODEL.expected()
    good = encode(frames)
    cases = [("positive", good, None)]
    for label, mutate, reason in [
        ("bool-natural", lambda f: f[1].__setitem__("phi", True), "exact type"),
        ("float-natural", lambda f: f[1].__setitem__("phiBudget", 1.0), "exact type"),
        ("bool-signed", lambda f: f[1]["meter"].__setitem__("refundCounter", False), "exact type"),
        ("negative-natural", lambda f: f[1].__setitem__("constBudget", -1), "value mismatch"),
        ("missing", lambda f: f[1]["meter"].pop("stateGasBaseline"), "missing or extra"),
        ("extra", lambda f: f[1]["meter"].__setitem__("extra", 0), "missing or extra"),
        ("wrong-id", lambda f: f[1].__setitem__("id", "other"), "value mismatch"),
        ("count", lambda f: f[0].__setitem__("count", 63), "value mismatch"),
        ("order", lambda f: f.__setitem__(slice(1, 3), f[1:3][::-1]), "value mismatch"),
        ("payload", lambda f: f[2].__setitem__("phiBudget", 999), "value mismatch"),
        ("end", lambda f: f[-1].__setitem__("end", False), "value mismatch"),
    ]:
        bad = copy.deepcopy(frames)
        mutate(bad)
        cases.append((label, encode(bad), reason))
    cases += [
        ("duplicate", good.replace('"phi":0', '"phi":0,"phi":0', 1), "duplicate key"),
        ("nan", good.replace('"phi":0', '"phi":NaN', 1), "nonfinite"),
        ("infinity", good.replace('"phi":0', '"phi":Infinity', 1), "nonfinite"),
        ("float-overflow", good.replace('"phi":0', '"phi":1e999', 1), "exact type"),
        ("truncated", "\n".join(good.splitlines()[:-1]) + "\n", "framing/count"),
        ("extra-frame", good + "{}\n", "framing/count"),
        ("missing-newline", good[:-1], "framing/count"),
        ("blank-frame", good.replace("\n", "\n\n", 1), "framing/count"),
    ]
    executions = 0
    base = Path(os.environ.get("BUDGET_POLICY_PARSER_EVIDENCE", str(ROOT / ".lake")))
    # One fixed evidence directory, replaced on each run: the latest receipts are kept
    # without accumulating a new directory per invocation.
    evidence = base / "budget-parser"
    if evidence.exists():
        shutil.rmtree(evidence)
    evidence.mkdir(parents=True)
    for flags in ([], ["-O"]):
        for label, raw, reason in cases:
            stem = evidence / (("optimized-" if flags else "normal-") + label)
            path = stem.with_suffix(".jsonl")
            path.write_text(raw, encoding="utf-8")
            argv = [sys.executable, "-B", *flags, str(DRIVER), "--check-target", str(path)]
            result = subprocess.run(argv, capture_output=True, text=True)
            stem.with_suffix(".stdout").write_text(result.stdout, encoding="utf-8")
            stem.with_suffix(".stderr").write_text(result.stderr, encoding="utf-8")
            stem.with_suffix(".receipt.json").write_text(json.dumps({
                "argv": argv, "returncode": result.returncode, "intended_reason": reason,
            }, indent=2) + "\n", encoding="utf-8")
            if reason is None:
                if result.returncode != 0 or "PASS 64" not in result.stdout:
                    raise RuntimeError(f"positive CLI failed: {result}")
            elif result.returncode != 1 or reason not in result.stderr:
                raise RuntimeError(f"{label} wrong rejection: {result}")
            executions += 1
    print(f"PASS {executions} actual budget parser CLIs; normal and optimized")
    return 0


if __name__ == "__main__":
    sys.exit(main())
