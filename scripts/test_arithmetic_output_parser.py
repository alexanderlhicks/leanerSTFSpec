#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""ADD/SUB framing and actual CLI regressions, under normal Python and -O."""

import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "STFSpec/Conformance/Vm/Instructions/arithmetic_differential.py"
spec = importlib.util.spec_from_file_location("arithmetic_differential", SCRIPT)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


def wire(rows):
    return "".join(json.dumps(row) + "\n" for row in rows)


class ArithmeticParserTests(unittest.TestCase):
    def test_complete_catalogue(self):
        rows = module.expected_frames()
        self.assertEqual(module.compare_frames(wire(rows)), rows)

    def test_reject_changed_complete_fields(self):
        rows = module.expected_frames()
        for key in rows[0]["before"]:
            bad = copy.deepcopy(rows)
            bad[0]["before"][key] = None
            with self.subTest(key=key), self.assertRaises(module.FrameError):
                module.compare_frames(wire(bad))
        for path in [("case",), ("after", "pc"), ("after", "meter"),
                     ("error",), ("tag",), ("cost",), ("otherCost",), ("phiAfter",), ("worldAfter", "storageProviderSample")]:
            bad = copy.deepcopy(rows)
            target = bad[0]
            for key in path[:-1]:
                target = target[key]
            target[path[-1]] = None
            with self.subTest(path=path), self.assertRaises(module.FrameError):
                module.compare_frames(wire(bad))

    def test_reject_bool_as_integer_and_float(self):
        for path in [("case",), ("before", "pc"), ("after", "pc"),
                     ("worldBefore", "blockAccountOrder")]:
            for value in [False, 0.0]:
                bad = module.expected_frames()
                target = bad[0]
                for key in path[:-1]:
                    target = target[key]
                target[path[-1]] = value
                with self.subTest(path=path, value=value), self.assertRaises(module.FrameError):
                    module.compare_frames(wire(bad))
        bad = module.expected_frames()
        bad[0]["after"]["meter"][0] = False
        with self.assertRaises(module.FrameError):
            module.compare_frames(wire(bad))

    def test_reject_wrong_results_with_valid_shapes(self):
        rows = module.expected_frames()
        probes = []
        for error in ["stackUnderflow", "outOfGas"]:
            i = next(i for i, r in enumerate(rows) if r["error"] == error and r["before"]["stack"])
            bad = copy.deepcopy(rows)
            bad[i]["after"]["stack"] = bad[i]["before"]["stack"]
            probes.append(bad)
        i = next(i for i, r in enumerate(rows) if r["op"] == "sub" and
                 r["tag"] == "continue" and r["before"]["stack"][:2] == [9, 2])
        bad = copy.deepcopy(rows)
        bad[i]["after"]["stack"][0] = (2 - 9) % 2**256
        probes.append(bad)
        i = next(i for i, r in enumerate(rows) if r["cost"] == 0 and r["tag"] == "continue")
        bad = copy.deepcopy(rows)
        bad[i]["phiAfter"] += 1
        probes.append(bad)
        for bad in probes:
            with self.assertRaises(module.FrameError):
                module.compare_frames(wire(bad))

    def test_framing(self):
        rows = module.expected_frames()
        valid = wire(rows)
        for bad in ["", valid + "\n", valid + "{}\n", wire(rows[:-1]), wire(rows[::-1]),
                    valid.replace('"case": 0', '"case": 0, "case": 0', 1),
                    valid.replace('"pc": 0', '"pc": NaN', 1),
                    valid.replace('"pc": 0', '"pc": Infinity', 1),
                    valid.replace('"pc": 0', '"pc": -1', 1),
                    valid.replace('"schema": "arithmetic-v1"', '"schema": "arithmetic-v2"', 1),
                    valid + "x" * 3000001]:
            with self.subTest(length=len(bad)), self.assertRaises(module.FrameError):
                module.compare_frames(bad)

    def test_cli(self):
        with tempfile.TemporaryDirectory(prefix="arithmetic-parser-") as temporary:
            frame = Path(temporary) / "frames.jsonl"
            frame.write_text(wire(module.expected_frames()))
            command = [sys.executable, "-B", *(["-O"] if sys.flags.optimize else []),
                       str(SCRIPT), "--check-target", str(frame)]
            result = subprocess.run(command, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads(result.stdout)["arithmetic_frames"], len(module.cases()))
            frame.write_text(frame.read_text().replace('"case": 0', '"case": false', 1))
            result = subprocess.run(command, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")


if __name__ == "__main__":
    unittest.main()
