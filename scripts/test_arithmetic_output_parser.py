#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""ADD/SUB/MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND framing and actual CLI regressions, under normal Python and -O."""

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
        i = next(i for i, r in enumerate(rows) if r["op"] == "mul" and
                 r["tag"] == "continue" and r["before"]["stack"][:2] == [2**255, 2])
        bad = copy.deepcopy(rows)
        bad[i]["after"]["stack"][0] = 1
        probes.append(bad)
        i = next(i for i, r in enumerate(rows) if r["op"] == "div" and
                 r["tag"] == "continue" and r["before"]["stack"][:2] == [9, 2])
        bad = copy.deepcopy(rows)
        bad[i]["after"]["stack"][0] = 2 // 9
        probes.append(bad)
        i = next(i for i, r in enumerate(rows) if r["op"] == "div" and
                 r["error"] == "outOfGas" and r["before"]["stack"][1] == 0)
        bad = copy.deepcopy(rows)
        bad[i]["tag"], bad[i]["error"] = "continue", None
        bad[i]["after"]["stack"].insert(0, 0)
        bad[i]["after"]["pc"] += 1
        probes.append(bad)
        for op in ["mul", "div"]:
            i = next(i for i, r in enumerate(rows) if r["op"] == op and
                     r["cost"] == 5 and r["tag"] == "continue")
            bad = copy.deepcopy(rows)
            bad[i]["after"]["meter"][0] -= 1
            bad[i]["phiAfter"] -= 1
            probes.append(bad)
            bad = copy.deepcopy(rows)
            bad[i]["otherCost"] += 1
            probes.append(bad)
        for bad in probes:
            with self.assertRaises(module.FrameError):
                module.compare_frames(wire(bad))

    def test_signed_and_unsigned_controls(self):
        rows = module.expected_frames()
        probes = []
        def result(op, words, tag="continue"):
            return next(i for i, r in enumerate(rows) if r["op"] == op and
                        r["tag"] == tag and r["before"]["stack"][:len(words)] == words)
        modulus = 2**256
        # Signed floor quotients, unsigned quotients and reversed operands differ.
        for words, alternatives in [([modulus - 7, 2], [-4, (modulus - 7) // 2, 0]),
                                    ([7, modulus - 2], [-4, 0]),
                                    ([2, 7], [3]),
                                    ([2**255, modulus - 1], [2**255 - 1, 0])]:
            i = result("sdiv", words)
            for value in alternatives:
                bad = copy.deepcopy(rows)
                bad[i]["after"]["stack"][0] = value % modulus
                probes.append(bad)
        # Remainder follows the dividend sign, independently of the divisor sign.
        for words, alternatives in [([modulus - 7, 2], [1]),
                                    ([7, modulus - 2], [-1, 7]),
                                    ([modulus - 7, modulus - 2], [1]),
                                    ([2**255, 3], [1, 2])]:
            i = result("smod", words)
            for value in alternatives:
                bad = copy.deepcopy(rows)
                bad[i]["after"]["stack"][0] = value % modulus
                probes.append(bad)
        for words, value in [([modulus - 1, 0], modulus - 1),
                             ([modulus - 1, 2**255], modulus - 1),
                             ([2, 7], 1), ([2**255, 3], 1)]:
            i = result("mod", words)
            bad = copy.deepcopy(rows)
            bad[i]["after"]["stack"][0] = value
            probes.append(bad)
        for op in ["sdiv", "mod", "smod"]:
            i = result(op, [2**255, 0, 17], "halt")
            bad = copy.deepcopy(rows)
            bad[i]["tag"], bad[i]["error"] = "continue", None
            bad[i]["after"]["stack"].insert(0, 0)
            bad[i]["after"]["pc"] += 1
            probes.append(bad)
            i = result(op, [7, 2])
            for amount in [1, rows[i]["veryLow"], rows[i]["otherCost"]]:
                bad = copy.deepcopy(rows)
                if amount > rows[i]["before"]["meter"][0]:
                    bad[i]["after"] = copy.deepcopy(rows[i]["before"])
                    bad[i]["after"]["stack"] = bad[i]["after"]["stack"][2:]
                    bad[i]["tag"], bad[i]["error"] = "halt", "outOfGas"
                else:
                    bad[i]["after"]["meter"][0] = rows[i]["before"]["meter"][0] - amount
                bad[i]["phiAfter"] = bad[i]["after"]["meter"][0] + 16
                probes.append(bad)
            for key in rows[i]["after"]:
                bad = copy.deepcopy(rows)
                bad[i]["after"][key] = None
                probes.append(bad)
            for key in rows[i]["worldAfter"]:
                bad = copy.deepcopy(rows)
                bad[i]["worldAfter"][key] = None
                probes.append(bad)
        for bad in probes:
            with self.subTest(case=next(r["case"] for r, good in zip(bad, rows) if r != good)), \
                    self.assertRaises(module.FrameError):
                module.compare_frames(wire(bad))

    def test_signextend_controls(self):
        rows = module.expected_frames()
        modulus = 2**256
        def result(words, tag="continue"):
            return next(i for i, r in enumerate(rows) if r["op"] == "signextend" and
                        r["cost"] == 5 and r["tag"] == tag and
                        r["before"]["stack"][:len(words)] == words)
        def reject(i, path, value):
            bad = copy.deepcopy(rows)
            target = bad[i]
            for key in path[:-1]:
                target = target[key]
            target[path[-1]] = value
            with self.subTest(case=i, path=path, value=value), self.assertRaises(module.FrameError):
                module.compare_frames(wire(bad))
        # Each retained sign boundary distinguishes masking, a wrong sign bit and shift substitutes.
        for k in range(32):
            threshold = 2**(8*k + 7)
            i = result([k, threshold])
            for value in [0, threshold - 1, threshold >> (8*k),
                          (threshold + modulus - 2**(8*(k + 1)) + 1) % modulus]:
                if value != rows[i]["after"]["stack"][0]:
                    reject(i, ("after", "stack", 0), value)
            i = result([k, threshold - 1])
            reject(i, ("after", "stack", 0), modulus - 1)
        # Guard uses the full unsigned index, and both identity branches still charge.
        for k, x in [(31, 128), (32, 128), (2**255, 128), (modulus - 1, 128),
                     (modulus - 1, 0)]:
            i = result([k, x])
            reject(i, ("after", "stack", 0), (modulus - 128 if x else modulus - 1))
            reject(i, ("after", "meter", 0), rows[i]["before"]["meter"][0])
        for k, x in [(32, modulus - 1), (modulus - 1, 0)]:
            i = result([k, x, 17], "halt")
            reject(i, ("tag",), "continue")
            reject(i, ("after", "stack"), [x, 17])
        # Reversing the index/value arguments is observable, including a discarded high byte.
        i = result([0, 128]); reject(i, ("after", "stack", 0), 0)
        i = result([0, 384]); reject(i, ("after", "stack", 0), 384)
        i = result([0, 0]); reject(i, ("after", "stack", 0), modulus - 1)
        i = result([0, 128])
        for key in rows[i]["after"]:
            reject(i, ("after", key), None)
        for key in rows[i]["worldAfter"]:
            reject(i, ("worldAfter", key), None)
        for path in [("case",), ("after", "pc"), ("after", "meter", 0),
                     ("after", "stack", 0), ("worldAfter", "blockAccountOrder")]:
            for value in [False, 0.0]:
                reject(i, path, value)
        for key in ["cost", "otherCost", "veryLow", "phiAfter"]:
            reject(i, (key,), rows[i][key] + 1)
        reject(i, ("after", "stack"), rows[i]["before"]["stack"][1:])
        # Wrong tier or sibling prices give different shortage or quantitative results.
        for amount in [rows[i]["veryLow"], rows[i]["otherCost"], 1]:
            bad = copy.deepcopy(rows)
            if amount > rows[i]["before"]["meter"][0]:
                bad[i]["after"] = copy.deepcopy(rows[i]["before"])
                bad[i]["after"]["stack"] = bad[i]["after"]["stack"][2:]
                bad[i]["tag"], bad[i]["error"] = "halt", "outOfGas"
            else:
                bad[i]["after"]["meter"][0] = rows[i]["before"]["meter"][0] - amount
            bad[i]["phiAfter"] = bad[i]["after"]["meter"][0] + 16
            with self.subTest(amount=amount), self.assertRaises(module.FrameError):
                module.compare_frames(wire(bad))
        valid = wire(rows)
        for bad in [wire(rows[:400] + rows[401:]), wire(rows + [rows[-1]]),
                    wire(rows[:400] + rows[400:][::-1]),
                    valid.replace('"case": 400', '"case": 400, "case": 400', 1),
                    valid.replace('"op": "signextend"', '"op": "signextend", "extra": 0', 1)]:
            with self.assertRaises(module.FrameError):
                module.compare_frames(bad)

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
