#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Mutation regressions for document guards; never modify the working repository."""
import pathlib
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent


class SpecChecks(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="stfspec-doc-check-")
        self.addCleanup(self.temp.cleanup)
        self.root = pathlib.Path(self.temp.name)
        for path in ("STFSpec",):
            shutil.copytree(ROOT / path, self.root / path)
        for path in ("scripts/check_spec.py", "scripts/check_boundaries.py", "scripts/gen_gaps.py",
                     "scripts/boundaries.toml", "STFSpecMathlib/lakefile.toml", "STFSpecSecurity/lakefile.toml", "reference.toml"):
            target = self.root / path
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / path, target)
        for pkg in ("STFSpecMathlib", "STFSpecSecurity"):
            for source in (ROOT / pkg).rglob("*.lean"):
                if ".lake" in source.parts:
                    continue
                target = self.root / source.relative_to(ROOT)
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source, target)

    def edit(self, path, old, new):
        target = self.root / path
        text = target.read_text()
        self.assertIn(old, text)
        target.write_text(text.replace(old, new, 1))

    def run_check(self, diagnostic=None, script="check_spec.py"):
        result = subprocess.run([sys.executable, str(self.root / "scripts" / script)],
                                capture_output=True, text=True, cwd=self.root)
        if diagnostic is None:
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        else:
            self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn(diagnostic, result.stdout + result.stderr)
        return result

    def test_baseline(self):
        self.run_check()

    def test_orphan_guidance(self):
        shutil.copyfile(self.root / "STFSpec/informal/modules/EthBase.md",
                        self.root / "STFSpec/informal/modules/EthUnregistered.md")
        self.run_check("unregistered spec guidance")

    def test_proof_source_import_drift(self):
        self.edit("STFSpecMathlib/STFSpecMathlib/Field.lean", "import STFSpec.Field", "import STFSpec.Curve")
        self.run_check("proof source imports")

    def test_proof_submodule_import_drift(self):
        self.edit("STFSpecMathlib/STFSpecMathlib/Field.lean", "import STFSpec.Field",
                  "import STFSpec.Field\nimport STFSpecMathlib.Field.Helper")
        target = self.root / "STFSpecMathlib/STFSpecMathlib/Field/Helper.lean"
        target.parent.mkdir(parents=True)
        target.write_text("import STFSpec.Curve\n")
        self.run_check("proof source imports")

    def test_missing_argument(self):
        self.edit("STFSpec/informal/modules/EthBase.md", "### Informal correctness argument", "### Pending argument")
        self.run_check("lacks its informal correctness argument")

    def test_missing_premises(self):
        self.edit("STFSpec/informal/modules/EthBase.md", "**Premises.**", "**Assumptions to infer.**")
        self.run_check("informal argument lacks Premises")

    def test_duplicate_section(self):
        self.edit("STFSpec/informal/modules/EthBase.md", "## 6. Data structures", "## 5. Interface")
        self.run_check("numbered sections must occur once each")

    def test_reordered_sections(self):
        self.edit("STFSpec/informal/modules/EthBase.md", "## 5. Interface", "## 6. Data structures")
        self.run_check("numbered sections must occur once each")

    def test_empty_section(self):
        path = self.root / "STFSpec/informal/modules/EthBase.md"
        text = path.read_text()
        start = text.index("## 4. Tests")
        end = text.index("## 5. Interface")
        path.write_text(text[:start] + "## 4. Tests\n\n" + text[end:])
        self.run_check("section 4 is empty")

    def test_module_pin(self):
        self.edit("STFSpec/informal/modules/EthBase.md", "@e1a316a0", "@aaaaaaaa")
        self.run_check("document pin does not match")

    def test_inventory_pin(self):
        self.edit("STFSpec/informal/eels-inventory.json", "e1a316a06fc3d3e0a5da36fdc78580811e9d8a36", "bad")
        self.run_check("inventory pin does not match")

    def test_duplicate_common_declaration(self):
        self.edit("STFSpec/informal/modules/EthStateless.md", "```lean", "```lean\nstructure Log where dummy : Nat")
        self.run_check("Log: expected one §5 declaration")

    def test_unreachable_provider(self):
        self.edit("STFSpec/informal/modules/EthBase.md", "```lean", "```lean\ndef invalidDependency : Log → Nat")
        self.run_check("cannot reach its owner EthVmCore")

    def test_proof_import_drift(self):
        self.edit("STFSpec/informal/modules/EthFieldMathlib.md", "**Depends on:** `EthField`", "**Depends on:** `EthCurve`")
        self.run_check("import registry says")

    def test_dependency_cycle(self):
        self.edit("scripts/boundaries.toml", "deps = []", 'deps = ["EthStateless"]')
        self.run_check("dependency cycle:")

    def test_missing_owner(self):
        self.edit("STFSpec/informal/contracts.toml", 'Log = "EthVmCore"', 'Log = "EthUnknown"')
        self.run_check("unknown declaration owner EthUnknown")

    def test_bad_decision(self):
        self.edit("STFSpec/informal/modules/EthBase.md", "## 9. Open decisions", "## 9. Open decisions\n\nD9999 is unknown.")
        self.run_check("mentions decision D9999")

    def test_unknown_question_id(self):
        self.edit("STFSpec/informal/modules/EthBase.md", "## 9. Open decisions", "## 9. Open decisions\n\nSee Q999 and B99.")
        self.run_check("cites Q999")

    def test_gap_generation_refuses_invalid_spec(self):
        target = self.root / "STFSpec/informal/GAPS.md"
        before = target.read_bytes()
        self.edit("STFSpec/informal/modules/EthBase.md", "**Premises.**", "**Infer these.**")
        self.run_check("cannot generate a validated gap register", "gen_gaps.py")
        self.assertEqual(target.read_bytes(), before)

    def test_gap_generation_rebases_module_links(self):
        self.run_check(script="gen_gaps.py")
        text = (self.root / "STFSpec/informal/GAPS.md").read_text()
        self.assertIn("](REVIEW.md)", text)
        self.assertNotIn("](../REVIEW.md)", text)


if __name__ == "__main__":
    unittest.main()
