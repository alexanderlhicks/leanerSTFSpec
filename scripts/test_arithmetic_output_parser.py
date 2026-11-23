#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""ADD/SUB/MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND/ADDMOD/MULMOD/EXP framing and actual CLI regressions, under normal Python and -O."""

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


class FrameFixture:
    def __init__(self, rows):
        self.rows = rows
        self.lines = [json.dumps(row) + "\n" for row in rows]

    def replace(self, index, row):
        lines = self.lines.copy()
        lines[index] = json.dumps(row) + "\n"
        return "".join(lines)

    def with_value(self, index, path, value):
        row = self.rows[index].copy()
        if len(path) > 1:
            # The expected rows share a world dictionary between both world fields.
            branch = path[0]
            row[branch] = copy.deepcopy(row[branch])
        target = row
        for key in path[:-1]:
            target = target[key]
        target[path[-1]] = value
        return self.replace(index, row)


class ArithmeticParserTests(unittest.TestCase):
    def test_complete_catalogue(self):
        rows = module.expected_frames()
        self.assertEqual(module.compare_frames(wire(rows)), rows)

    def test_reject_changed_complete_fields(self):
        rows = module.expected_frames()
        fixture = FrameFixture(rows)
        for key in rows[0]["before"]:
            with self.subTest(key=key), self.assertRaises(module.FrameError):
                module.compare_frames(fixture.with_value(0, ("before", key), None))
        for path in [("case",), ("after", "pc"), ("after", "meter"),
                     ("error",), ("tag",), ("cost",), ("otherCost",), ("phiAfter",), ("worldAfter", "storageProviderSample")]:
            with self.subTest(path=path), self.assertRaises(module.FrameError):
                module.compare_frames(fixture.with_value(0, path, None))

    def test_reject_bool_as_integer_and_float(self):
        fixture = FrameFixture(module.expected_frames())
        for path in [("case",), ("before", "pc"), ("after", "pc"),
                     ("worldBefore", "blockAccountOrder")]:
            for value in [False, 0.0]:
                with self.subTest(path=path, value=value), self.assertRaises(module.FrameError):
                    module.compare_frames(fixture.with_value(0, path, value))
        with self.assertRaises(module.FrameError):
            module.compare_frames(fixture.with_value(0, ("after", "meter", 0), False))

    def test_reject_wrong_results_with_valid_shapes(self):
        rows = module.expected_frames()
        fixture = FrameFixture(rows)

        def reject(index, changed):
            with self.subTest(case=index), self.assertRaises(module.FrameError):
                module.compare_frames(fixture.replace(index, changed))

        for error in ["stackUnderflow", "outOfGas"]:
            i = next(i for i, r in enumerate(rows) if r["error"] == error and r["before"]["stack"])
            bad = copy.deepcopy(rows[i])
            bad["after"]["stack"] = bad["before"]["stack"]
            reject(i, bad)
        i = next(i for i, r in enumerate(rows) if r["op"] == "sub" and
                 r["tag"] == "continue" and r["before"]["stack"][:2] == [9, 2])
        bad = copy.deepcopy(rows[i])
        bad["after"]["stack"][0] = (2 - 9) % 2**256
        reject(i, bad)
        i = next(i for i, r in enumerate(rows) if r["cost"] == 0 and r["tag"] == "continue")
        bad = copy.deepcopy(rows[i])
        bad["phiAfter"] += 1
        reject(i, bad)
        i = next(i for i, r in enumerate(rows) if r["op"] == "mul" and
                 r["tag"] == "continue" and r["before"]["stack"][:2] == [2**255, 2])
        bad = copy.deepcopy(rows[i])
        bad["after"]["stack"][0] = 1
        reject(i, bad)
        i = next(i for i, r in enumerate(rows) if r["op"] == "div" and
                 r["tag"] == "continue" and r["before"]["stack"][:2] == [9, 2])
        bad = copy.deepcopy(rows[i])
        bad["after"]["stack"][0] = 2 // 9
        reject(i, bad)
        i = next(i for i, r in enumerate(rows) if r["op"] == "div" and
                 r["error"] == "outOfGas" and r["before"]["stack"][1] == 0)
        bad = copy.deepcopy(rows[i])
        bad["tag"], bad["error"] = "continue", None
        bad["after"]["stack"].insert(0, 0)
        bad["after"]["pc"] += 1
        reject(i, bad)
        for op in ["mul", "div"]:
            i = next(i for i, r in enumerate(rows) if r["op"] == op and
                     r["cost"] == 5 and r["tag"] == "continue")
            bad = copy.deepcopy(rows[i])
            bad["after"]["meter"][0] -= 1
            bad["phiAfter"] -= 1
            reject(i, bad)
            bad = copy.deepcopy(rows[i])
            bad["otherCost"] += 1
            reject(i, bad)

    def test_signed_and_unsigned_controls(self):
        rows = module.expected_frames()
        fixture = FrameFixture(rows)

        def reject(index, data):
            with self.subTest(case=index), self.assertRaises(module.FrameError):
                module.compare_frames(data)

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
                reject(i, fixture.with_value(i, ("after", "stack", 0), value % modulus))
        # Remainder follows the dividend sign, independently of the divisor sign.
        for words, alternatives in [([modulus - 7, 2], [1]),
                                    ([7, modulus - 2], [-1, 7]),
                                    ([modulus - 7, modulus - 2], [1]),
                                    ([2**255, 3], [1, 2])]:
            i = result("smod", words)
            for value in alternatives:
                reject(i, fixture.with_value(i, ("after", "stack", 0), value % modulus))
        for words, value in [([modulus - 1, 0], modulus - 1),
                             ([modulus - 1, 2**255], modulus - 1),
                             ([2, 7], 1), ([2**255, 3], 1)]:
            i = result("mod", words)
            reject(i, fixture.with_value(i, ("after", "stack", 0), value))
        for op in ["sdiv", "mod", "smod"]:
            i = result(op, [2**255, 0, 17], "halt")
            bad = copy.deepcopy(rows[i])
            bad["tag"], bad["error"] = "continue", None
            bad["after"]["stack"].insert(0, 0)
            bad["after"]["pc"] += 1
            reject(i, fixture.replace(i, bad))
            i = result(op, [7, 2])
            for amount in [1, rows[i]["veryLow"], rows[i]["otherCost"]]:
                bad = copy.deepcopy(rows[i])
                if amount > rows[i]["before"]["meter"][0]:
                    bad["after"] = copy.deepcopy(rows[i]["before"])
                    bad["after"]["stack"] = bad["after"]["stack"][2:]
                    bad["tag"], bad["error"] = "halt", "outOfGas"
                else:
                    bad["after"]["meter"][0] = rows[i]["before"]["meter"][0] - amount
                bad["phiAfter"] = bad["after"]["meter"][0] + 16
                reject(i, fixture.replace(i, bad))
            for key in rows[i]["after"]:
                reject(i, fixture.with_value(i, ("after", key), None))
            for key in rows[i]["worldAfter"]:
                reject(i, fixture.with_value(i, ("worldAfter", key), None))

    def test_signextend_controls(self):
        rows = module.expected_frames()
        fixture = FrameFixture(rows)
        modulus = 2**256
        def result(words, tag="continue"):
            return next(i for i, r in enumerate(rows) if r["op"] == "signextend" and
                        r["cost"] == 5 and r["tag"] == tag and
                        r["before"]["stack"][:len(words)] == words)
        def reject(i, path, value):
            with self.subTest(case=i, path=path, value=value), self.assertRaises(module.FrameError):
                module.compare_frames(fixture.with_value(i, path, value))
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
        # Python's value equality treats an integer 1 as equal to True.
        reject(404, ("worldAfter", "created199"), 1)
        for key in ["cost", "otherCost", "veryLow", "phiAfter"]:
            reject(i, (key,), rows[i][key] + 1)
        reject(i, ("after", "stack"), rows[i]["before"]["stack"][1:])
        # Wrong tier or sibling prices give different shortage or quantitative results.
        for amount in [rows[i]["veryLow"], rows[i]["otherCost"], 1]:
            bad = copy.deepcopy(rows[i])
            if amount > rows[i]["before"]["meter"][0]:
                bad["after"] = copy.deepcopy(rows[i]["before"])
                bad["after"]["stack"] = bad["after"]["stack"][2:]
                bad["tag"], bad["error"] = "halt", "outOfGas"
            else:
                bad["after"]["meter"][0] = rows[i]["before"]["meter"][0] - amount
            bad["phiAfter"] = bad["after"]["meter"][0] + 16
            with self.subTest(amount=amount), self.assertRaises(module.FrameError):
                module.compare_frames(fixture.replace(i, bad))
        valid = wire(rows)
        for bad in [wire(rows[:400] + rows[401:]), wire(rows + [rows[-1]]),
                    wire(rows[:400] + rows[400:][::-1]),
                    valid.replace('"case": 400', '"case": 400, "case": 400', 1),
                    valid.replace('"op": "signextend"', '"op": "signextend", "extra": 0', 1)]:
            with self.assertRaises(module.FrameError):
                module.compare_frames(bad)

    def test_ternary_controls(self):
        rows = module.expected_frames()
        fixture = FrameFixture(rows)
        modulus = 2**256
        def reject(i, path, value):
            with self.subTest(case=i, path=path), self.assertRaises(module.FrameError):
                module.compare_frames(fixture.with_value(i, path, value))
        for op in ["addmod", "mulmod"]:
            selected = [(i, r) for i, r in enumerate(rows) if r["op"] == op]
            # All three failed-pop residual stacks and charge precedence are observable.
            for depth in range(3):
                i, r = next((i, r) for i, r in selected if len(r["before"]["stack"]) == depth)
                reject(i, ("error",), "outOfGas")
                reject(i, ("after", "meter", 0), r["before"]["meter"][0] + 1)
                if depth:
                    reject(i, ("after", "stack"), r["before"]["stack"])
            i, r = next((i, r) for i, r in selected if r["error"] == "outOfGas" and
                        len(r["before"]["stack"]) >= 3 and r["before"]["stack"][2] == 0)
            reject(i, ("tag",), "continue")
            reject(i, ("after", "stack"), r["before"]["stack"][2:])
            # Unbounded intermediates distinguish wrapped ADD/MUL then MOD substitutes.
            distinguished = 0
            for i, r in selected:
                if r["tag"] != "continue":
                    continue
                x, y, z = r["before"]["stack"][:3]
                if z == 0:
                    reject(i, ("after", "stack", 0), 1)
                    reject(i, ("after", "meter", 0), r["before"]["meter"][0]) if r["cost"] else None
                    continue
                result = r["after"]["stack"][0]
                unbounded = x + y if op == "addmod" else x * y
                wrong = (unbounded % modulus) % z
                if result != wrong:
                    reject(i, ("after", "stack", 0), wrong)
                    distinguished += 1
                # Moving modulus into either operand position must change discriminators.
                for alternative in [(y + z) % x if x else 0,
                                    (x + z) % y if y else 0] if op == "addmod" else [
                                    (y * z) % x if x else 0, (x * z) % y if y else 0]:
                    if alternative != result:
                        reject(i, ("after", "stack", 0), alternative)
            self.assertGreater(distinguished, 0)
            i, r = next((i, r) for i, r in selected if r["tag"] == "continue" and r["cost"] == 8)
            for key in r["after"]:
                reject(i, ("after", key), None)
            for key in r["worldAfter"]:
                reject(i, ("worldAfter", key), None)
            for path in [("case",), ("after", "pc"), ("after", "meter", 0),
                         ("after", "stack", 0), ("worldAfter", "blockAccountOrder")]:
                for value in [False, 0.0]:
                    reject(i, path, value)
            for key in ["cost", "otherCost", "veryLow", "phiAfter"]:
                reject(i, (key,), r[key] + 1)
            # Independent tier and sibling prices must not replace the selected field.
            for amount in [1, r["veryLow"], r["otherCost"]]:
                bad = copy.deepcopy(r)
                if amount > r["before"]["meter"][0]:
                    bad["after"] = copy.deepcopy(r["before"])
                    bad["after"]["stack"] = bad["after"]["stack"][3:]
                    bad["tag"], bad["error"] = "halt", "outOfGas"
                else:
                    bad["after"]["meter"][0] = r["before"]["meter"][0] - amount
                bad["phiAfter"] = bad["after"]["meter"][0] + 16
                with self.subTest(op=op, amount=amount), self.assertRaises(module.FrameError):
                    module.compare_frames(fixture.replace(i, bad))
        valid = wire(rows)
        for bad in [wire(rows[:627] + rows[628:]), wire(rows + [rows[-1]]),
                    wire(rows[:627] + rows[627:][::-1]),
                    valid.replace('"case": 627', '"case": 627, "case": 627', 1),
                    valid.replace('"op": "addmod"', '"op": "addmod", "extra": 0', 1)]:
            with self.assertRaises(module.FrameError):
                module.compare_frames(bad)

    def test_exp_value_and_charge_controls(self):
        rows = module.expected_frames()
        fixture = FrameFixture(rows)
        selected = [(i, r) for i, r in enumerate(rows) if r["op"] == "exp"]
        def reject(i, changed):
            self.assertNotEqual(changed, rows[i])
            with self.subTest(case=i), self.assertRaises(module.FrameError):
                module.compare_frames(fixture.replace(i, changed))
        def charged(r, amount):
            wrong = copy.deepcopy(r)
            wrong["after"] = copy.deepcopy(r["before"])
            base, exponent = wrong["after"]["stack"][:2]
            wrong["after"]["stack"] = wrong["after"]["stack"][2:]
            if r["before"]["meter"][0] < amount:
                wrong["tag"], wrong["error"] = "halt", "outOfGas"
            else:
                wrong["tag"], wrong["error"] = "continue", None
                wrong["after"]["stack"].insert(0, pow(base, exponent, 2**256))
                wrong["after"]["meter"][0] -= amount
                wrong["after"]["pc"] += 1
            wrong["phiAfter"] = wrong["after"]["meter"][0] + 16
            return wrong
        # Each wrong charging rule must produce a proper-shaped different observation.
        rules = {
            "base byte count": lambda r, b, e: r["expBase"] + r["expPerByte"] * ((b.bit_length()+7)//8),
            "zero needs one byte": lambda r, b, e: r["expBase"] + r["expPerByte"] * max(1,(e.bit_length()+7)//8),
            "floor bytes": lambda r, b, e: r["expBase"] + r["expPerByte"] * (e.bit_length()//8),
            "truncated exponent": lambda r, b, e: r["expBase"] + r["expPerByte"] * (((e % 2**64).bit_length()+7)//8),
            "signed exponent": lambda r, b, e: r["expBase"] + r["expPerByte"] * ((abs(e if e < 2**255 else e-2**256).bit_length()+7)//8),
            "swapped prices": lambda r, b, e: r["expPerByte"] + r["expBase"] * ((e.bit_length()+7)//8),
            "sibling price": lambda r, b, e: r["otherCost"],
            "tier price": lambda r, b, e: r["veryLow"],
            "wrapped charge": lambda r, b, e: (r["expBase"] + r["expPerByte"]*((e.bit_length()+7)//8)) % 2**256,
            "zero exponent free": lambda r, b, e: 0 if e == 0 else r["expBase"] + r["expPerByte"]*((e.bit_length()+7)//8),
        }
        for name, rule in rules.items():
            found = False
            for i, r in selected:
                if len(r["before"]["stack"]) < 2:
                    continue
                b, e = r["before"]["stack"][:2]
                wrong = charged(r, rule(r,b,e))
                if wrong != r:
                    with self.subTest(rule=name): reject(i, wrong)
                    found = True
                    break
            self.assertTrue(found, name)
        i, r = next((i,r) for i,r in selected if r["tag"] == "continue" and
                    pow(r["before"]["stack"][1],r["before"]["stack"][0],2**256) != r["after"]["stack"][0])
        wrong = copy.deepcopy(r)
        wrong["after"]["stack"][0] = pow(r["before"]["stack"][1],r["before"]["stack"][0],2**256)
        reject(i, wrong)
        wrong = copy.deepcopy(r); wrong["after"]["stack"][0] ^= 1; reject(i, wrong)
        for depth in (0,1):
            i,r = next((i,r) for i,r in selected if len(r["before"]["stack"]) == depth)
            wrong=copy.deepcopy(r); wrong["error"]="outOfGas"; reject(i,wrong)
            wrong=copy.deepcopy(r); wrong["after"]["meter"][0]+=1; reject(i,wrong)
            if depth:
                wrong=copy.deepcopy(r); wrong["after"]["stack"]=r["before"]["stack"]; reject(i,wrong)
        i,r=next((i,r) for i,r in selected if r["error"] == "outOfGas")
        for key,value in [("stack",r["before"]["stack"][1:]),("pc",r["before"]["pc"]+1),
                          ("meter",[r["before"]["meter"][0]+1]+r["before"]["meter"][1:])]:
            wrong=copy.deepcopy(r); wrong["after"][key]=value; reject(i,wrong)

    def test_exp_complete_fields_types_and_framing(self):
        rows=module.expected_frames()
        fixture = FrameFixture(rows)
        i=next(i for i,r in enumerate(rows) if r["op"] == "exp" and r["tag"] == "continue")
        def reject(path,value):
            with self.subTest(path=path,value=value), self.assertRaises(module.FrameError):
                module.compare_frames(fixture.with_value(i, path, value))
        for section in ["before","after"]:
            for key in rows[i][section]: reject((section,key),None)
        for section in ["worldBefore","worldAfter"]:
            for key in rows[i][section]: reject((section,key),None)
        for path in [("after","pc"),("after","stack",0),("phiBefore",),("phiAfter",),
                     ("expBase",),("expPerByte",),("otherCost",),("veryLow",)]:
            target=rows[i]
            for key in path: target=target[key]
            for value in [False,float(target),target+1]: reject(path,value)
        for j in range(6): reject(("after","meter",j),rows[i]["after"]["meter"][j]+1)
        for path in [("after","memory",0),("after","returnData",0),
                     ("after","logs",0,1,0),("after","warmSlots",0,1),
                     ("worldAfter","storageProviderSample")]:
            target=rows[i]
            for key in path: target=target[key]
            reject(path,target+1)
        for key in ["expBase","expPerByte"]:
            bad = rows[i].copy()
            del bad[key]
            with self.assertRaises(module.FrameError):
                module.compare_frames(fixture.replace(i, bad))
        with self.assertRaises(module.FrameError):
            module.compare_frames(fixture.with_value(i, ("cost",), 10))
        valid=wire(rows)
        for bad in [wire(rows[:843]+rows[844:]),wire(rows+[rows[-1]]),
                    wire(rows[:843]+rows[843:][::-1]),
                    valid.replace('"case": 843','"case": 843, "case": 843',1),
                    valid.replace('"op": "exp"','"op": "exp", "extra": 0',1)]:
            with self.assertRaises(module.FrameError): module.compare_frames(bad)

    def test_exp_actual_decoder_rejections(self):
        # Both native and interpreted entry points reject the same malformed input rows.
        row=["843","exp","10","50","1000","71","60","9","0","2,1"]
        probes=[row[:-1],row+["extra"]]
        for j in [0,2,3,4,5,6,7,8]:
            bad=row.copy(); bad[j]="-1"; probes.append(bad)
        for j in [0,2,3,4,5,6,7,8]:
            bad=row.copy(); bad[j]="bad"; probes.append(bad)
        for j,value in [(1,"expp"),(8,"2"),(9,str(2**256)),(9,"1,"),(9,"-1"),
                        (9,",".join(["1"]*1025))]:
            bad=row.copy(); bad[j]=value; probes.append(bad)
        root=SCRIPT.parents[4]
        commands=[[str(root/".lake/build/bin/arithmetic-native-tests")],
                  ["lake","env","lean","--run","scripts/ArithmeticNativeTests.lean"]]
        with tempfile.TemporaryDirectory(prefix="exp-decoder-") as temporary:
            path=Path(temporary)/"input.tsv"
            for command in commands:
                path.write_text("\t".join(row)+"\n")
                result=subprocess.run(command+[str(path)],cwd=root,capture_output=True,text=True)
                self.assertEqual(result.returncode,0,result.stderr)
                self.assertEqual(json.loads(result.stdout)["expPerByte"],50)
                for probe in probes:
                    path.write_text("\t".join(probe)+"\n")
                    result=subprocess.run(command+[str(path)],cwd=root,capture_output=True,text=True)
                    with self.subTest(command=command,probe=probe[:9]):
                        self.assertNotEqual(result.returncode,0)
                        self.assertEqual(result.stdout,"")

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
