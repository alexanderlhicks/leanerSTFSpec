#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Pin and archive regressions using small synthetic fixtures; no downloads."""
import hashlib
import io
import json
import pathlib
import shutil
import subprocess
import sys
import tarfile
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]


class ReferenceChecks(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="stfspec-reference-check-")
        self.addCleanup(self.temp.cleanup)
        self.root = pathlib.Path(self.temp.name)
        for name in ("reference.toml", "lean-toolchain", "STFSpecMathlib/lean-toolchain",
                     "STFSpecSecurity/lean-toolchain", "STFSpec/informal/CONTRACT.md",
                     "README.md", "scripts/gen_arch_diagram.py", "scripts/boundaries.toml",
                     "STFSpec/informal/contracts.toml"):
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / name, target)

    def check(self, diagnostic=None, fetch=False):
        args = [sys.executable, str(ROOT / "scripts/check_reference.py"), "--root", str(self.root)]
        if fetch:
            args += ["--fetch", str(self.root)]
        result = subprocess.run(args, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0 if diagnostic is None else 1, result.stdout + result.stderr)
        if diagnostic:
            self.assertIn(diagnostic, result.stdout + result.stderr)

    def archive(self, value, distinct=1):
        data = json.dumps(value).encode()
        path = self.root / "fixtures_zkevm.tar.gz"
        with tarfile.open(path, "w:gz") as archive:
            member = tarfile.TarInfo("fixtures/blockchain_tests/for_amsterdam/frontier/test/case.json")
            member.size = len(data)
            archive.addfile(member, io.BytesIO(data))
        pin = self.root / "reference.toml"
        text = pin.read_text().replace("size_bytes = 586431069", f"size_bytes = {path.stat().st_size}")
        text = text.replace("44cfcb54fe08b870c53c96879f8ebbc960434032eb3696139dbe2a1629eebe1a", hashlib.sha256(path.read_bytes()).hexdigest())
        text = text.replace("json_files = 6875", "json_files = 1").replace("guest_records = 29030", "guest_records = 1")
        pin.write_text(text.replace("distinct_guest_inputs = 24283", f"distinct_guest_inputs = {distinct}"))

    def test_baseline(self):
        self.check()

    def test_toolchain_drift(self):
        for name in ("lean-toolchain", "STFSpecMathlib/lean-toolchain", "STFSpecSecurity/lean-toolchain"):
            with self.subTest(name=name):
                path = self.root / name
                old = path.read_text()
                path.write_text("leanprover/lean4:v4.33.0\n")
                self.check("toolchain")
                path.write_text(old)

    def test_schema_version(self):
        path = self.root / "reference.toml"
        path.write_text(path.read_text().replace("schema = 1", "schema = 2", 1))
        self.check("schema")

    def test_archive_pair(self):
        self.archive({"case": {"statelessInputBytes": "0x1501", "statelessOutputBytes": "0x" + "00" * 43}})
        self.check(fetch=True)

    def test_separate_fields_are_not_a_pair(self):
        self.archive({"a": {"statelessInputBytes": "0x1501"}, "b": {"statelessOutputBytes": "0x" + "00" * 43}})
        self.check("unpaired", fetch=True)

    def test_output_width(self):
        self.archive({"statelessInputBytes": "0x1501", "statelessOutputBytes": "0x00"})
        self.check("43 bytes", fetch=True)

    def test_distinct_inputs(self):
        pair = {"statelessInputBytes": "0x1501", "statelessOutputBytes": "0x" + "00" * 43}
        self.archive({"first": pair, "duplicate": pair}, distinct=2)
        path = self.root / "reference.toml"
        path.write_text(path.read_text().replace("guest_records = 1", "guest_records = 2"))
        self.check("distinct", fetch=True)

    def diagram(self):
        subprocess.run([sys.executable, str(self.root / "scripts/gen_arch_diagram.py")], check=True, capture_output=True)
        return (self.root / "README.md").read_text()

    def test_diagram_pin(self):
        path = self.root / "reference.toml"
        path.write_text(path.read_text().replace("tests-zkevm@v21.0.0", "tests-zkevm@v22.0.0"))
        self.assertIn("EEST zkevm fixtures · tests-zkevm@v22.0.0", self.diagram())

    def test_diagram_proof_edges(self):
        text = self.diagram()
        self.assertIn("CurveM --> FieldM", text)
        self.assertIn("PairingM --> CurveM", text)

    def test_fixture_index_archive_prefix(self):
        self.archive({"statelessInputBytes": "0x1501", "statelessOutputBytes": "0x" + "00" * 43})
        result = subprocess.run([sys.executable, str(ROOT / "scripts/gen_fixture_index.py"),
                                 str(self.root / "fixtures_zkevm.tar.gz"), "--root", str(self.root)],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        text = (self.root / "STFSpec/informal/eest-fixture-index.txt").read_text()
        self.assertIn("blockchain_tests/for_amsterdam/frontier/test\t1\n", text)
        self.assertNotIn("fixtures/blockchain_tests", text)

    def test_corrupt_archive_is_not_parsed(self):
        self.archive({"statelessInputBytes": "0x1501", "statelessOutputBytes": "0x" + "00" * 43})
        (self.root / "fixtures_zkevm.tar.gz").write_bytes(b"not a tar archive")
        self.check("archive", fetch=True)


if __name__ == "__main__":
    unittest.main()
