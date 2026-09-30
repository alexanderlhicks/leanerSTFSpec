#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Regression cases for the independent authenticated fixture extraction tool."""
import copy
from contextlib import redirect_stdout, redirect_stderr
import hashlib
import io
import json
import pathlib
import subprocess
import tarfile
import tempfile
import unittest
from unittest.mock import patch

import verify_fixture_archive as fixtures


HASH = "0x" + "11" * 32
FILE = "blockchain_tests/for_amsterdam/area/test.json"
ENGINE = "blockchain_tests_engine/for_amsterdam/area/test.json"
OUTPUT = "0x" + "00" * 43


def case(blocks=None, engine=False):
    return {"test": {"network": "Amsterdam", "_info": {"hash": HASH,
            "fixture-format": "blockchain_test_engine" if engine else "blockchain_test"},
            "engineNewPayloads" if engine else "blocks": [] if blocks is None else blocks}}


def block(input="0x1501", output=OUTPUT):
    return {"statelessInputBytes": input, "statelessOutputBytes": output}


def index(path=FILE):
    return {"test_count": 1, "test_cases": [{"id": "test", "json_path": path,
            "fixture_hash": HASH, "fork": "Amsterdam", "format": "blockchain_test"}]}


def archive(path, entries, records=1, distinct=1):
    with tarfile.open(path, "w:gz") as stream:
        for name, value in entries:
            raw = value if isinstance(value, bytes) else json.dumps(value).encode()
            member = tarfile.TarInfo("fixtures/" + name)
            member.size = len(raw)
            stream.addfile(member, io.BytesIO(raw))
    return {"size_bytes": path.stat().st_size,
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "json_files": len(entries), "guest_records": records,
            "distinct_guest_inputs": distinct, "input_field": "statelessInputBytes",
            "output_field": "statelessOutputBytes"}


class ArchiveTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.path = pathlib.Path(self.temporary.name) / "fixtures.tar.gz"

    def verify(self, meta=None, value=None, extra=(), records=1, distinct=1):
        entries = [(".meta/index.json", index() if meta is None else meta),
                   (FILE, case([block()]) if value is None else value), *extra]
        pin = archive(self.path, entries, records, distinct)
        return fixtures.verify_archive(self.path, pin)

    def test_authenticated_snapshot_survives_in_place_write(self):
        pin = archive(self.path, [(".meta/index.json", index()), (FILE, case([block()]))])
        replacement = self.path.with_name("replacement.tar.gz")
        archive(replacement, [(".meta/index.json", index()), (FILE, case([block("0x9999")]))])
        original_open = fixtures.tarfile.open

        def mutate_then_parse(*args, **kwargs):
            self.path.write_bytes(replacement.read_bytes())
            return original_open(*args, **kwargs)

        with patch.object(fixtures.tarfile, "open", side_effect=mutate_then_parse):
            report, _, _ = fixtures.verify_archive(self.path, pin)
        self.assertEqual(report["archive_sha256"], pin["sha256"])
        # Inspect the authenticated source itself so equal-size/count replacement cannot hide.
        archive(self.path, [(FILE, case([block()]))])
        pin = {**pin, "size_bytes": self.path.stat().st_size,
               "sha256": hashlib.sha256(self.path.read_bytes()).hexdigest()}
        with fixtures.authenticated_source(self.path, pin) as (source, _):
            self.path.write_bytes(b"in-place changed")
            self.assertEqual(hashlib.sha256(source.read()).hexdigest(), pin["sha256"])

    def test_lean_snapshot_survives_in_place_write(self):
        pin = archive(self.path, [(FILE, case([block()]))])
        original_open = fixtures.tarfile.open

        def mutate_then_parse(*args, **kwargs):
            self.path.write_bytes(b"in-place changed")
            return original_open(*args, **kwargs)

        with patch.object(fixtures.tarfile, "open", side_effect=mutate_then_parse):
            result = fixtures.check_lean(self.path, pin, self.parser(), {FILE: 1}, None)
        self.assertEqual(result["lean_guest_records_extracted"], 1)

    def test_unsafe_members_rejected_end_to_end(self):
        for name in ("../test.json", "/test.json", "a/../test.json", "../readme.txt"):
            with self.subTest(name=name):
                pin = archive(self.path, [(name, {})], records=0, distinct=0)
                with self.assertRaisesRegex(fixtures.FixtureError, "unsafe"):
                    fixtures.verify_archive(self.path, pin)
        for kind in (tarfile.SYMTYPE, tarfile.LNKTYPE, tarfile.FIFOTYPE,
                     tarfile.CHRTYPE, tarfile.BLKTYPE, tarfile.DIRTYPE):
            with self.subTest(kind=kind):
                with tarfile.open(self.path, "w:gz") as stream:
                    member = tarfile.TarInfo("fixtures/special.json")
                    member.type = kind
                    member.linkname = "target"
                    stream.addfile(member)
                pin = {**fixtures.DEFAULT_FIELDS, "size_bytes": self.path.stat().st_size,
                       "sha256": hashlib.sha256(self.path.read_bytes()).hexdigest()}
                with self.assertRaisesRegex(fixtures.FixtureError, "forbidden"):
                    fixtures.verify_archive(self.path, pin)

    def test_pin_controls_guest_field_names(self):
        value = case([{"customIn": "0x1501", "customOut": OUTPUT}])
        pin = archive(self.path, [(".meta/index.json", index()), (FILE, value)])
        pin.update(input_field="customIn", output_field="customOut")
        report, _, _ = fixtures.verify_archive(self.path, pin)
        self.assertEqual(report["guest_records"], 1)

    def test_downstream_executable_can_define_main(self):
        root = pathlib.Path(__file__).resolve().parents[1]
        path = pathlib.Path(self.temporary.name) / "Client.lean"
        path.write_text("import STFSpec.Conformance\ndef main : IO Unit := pure ()\n")
        run = subprocess.run(["lake", "env", "lean", str(path)], cwd=root,
                             capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)

    def test_lone_surrogate_keys_rejected(self):
        for raw in (r'{"\ud800": {}, "\udc00": {}}', r'{"value":"\ud800"}'):
            with self.assertRaisesRegex(fixtures.FixtureError, "lone surrogate"):
                fixtures.strict_json(raw)

    def test_full_content_selection(self):
        root = self.report_root()
        executable = self.parser(json.dumps(self.content_reply()))
        report = self.cli_report(root, "--lean-parser", executable, "--lean-content-all")
        self.assertTrue(report["lean_selection"]["content_all"])
        self.assertEqual(report["lean_guest_records_content_compared"], 1)
        self.assertNotIn(str(root), json.dumps(report))

    def test_executable_declarations_are_pure(self):
        root = pathlib.Path(__file__).resolve().parents[1]
        run = subprocess.run(["lake", "exe", "check-decls", "FixtureRecordsMain"],
                             cwd=root, capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)

    def test_duplicate_normalized_archive_paths(self):
        for name in (FILE, "./fixtures/" + FILE):
            with self.subTest(name=name):
                with tarfile.open(self.path, "w:gz") as stream:
                    for member_name in ("fixtures/" + FILE, name):
                        raw = json.dumps(case([block()])).encode()
                        member = tarfile.TarInfo(member_name)
                        member.size = len(raw)
                        stream.addfile(member, io.BytesIO(raw))
                pin = {**fixtures.DEFAULT_FIELDS, "size_bytes": self.path.stat().st_size,
                       "sha256": hashlib.sha256(self.path.read_bytes()).hexdigest()}
                with self.assertRaisesRegex(fixtures.FixtureError, "duplicate archive JSON path"):
                    fixtures.verify_archive(self.path, pin)

    def test_complete_metadata_links_and_zero_executions(self):
        report, identities, counts = self.verify()
        self.assertEqual(report["metadata_links"], 1)
        self.assertEqual(report["semantic_guest_executions"], 0)
        self.assertEqual(identities[0], {"file": FILE, "testId": "test",
                                      "blockIndex": 0, "infoHash": HASH})
        self.assertEqual(counts, {FILE: 1})

    def test_authentication_precedes_tar_parsing(self):
        self.path.write_bytes(b"not even a tar archive")
        pin = {"size_bytes": self.path.stat().st_size, "sha256": "0" * 64}
        with patch.object(fixtures.tarfile, "open", side_effect=AssertionError("parsed")):
            with self.assertRaisesRegex(fixtures.FixtureError, "authentication"):
                fixtures.verify_archive(self.path, pin)

    def test_size_authentication(self):
        pin = archive(self.path, [])
        pin["size_bytes"] += 1
        with self.assertRaisesRegex(fixtures.FixtureError, "authentication"):
            fixtures.verify_archive(self.path, pin)

    def test_metadata_hash_mismatch(self):
        meta = index()
        meta["test_cases"][0]["fixture_hash"] = "0x" + "22" * 32
        with self.assertRaisesRegex(fixtures.FixtureError, "hash/format/fork mismatch"):
            self.verify(meta=meta)

    def test_metadata_format_and_fork_mismatch(self):
        for field, value in (("format", "blockchain_test_engine"), ("fork", "BPO2")):
            with self.subTest(field=field):
                meta = index()
                meta["test_cases"][0][field] = value
                with self.assertRaisesRegex(fixtures.FixtureError, "hash/format/fork mismatch"):
                    self.verify(meta=meta)

    def test_metadata_count_mismatch(self):
        meta = index()
        meta["test_count"] = 2
        with self.assertRaisesRegex(fixtures.FixtureError, "test_count"):
            self.verify(meta=meta)

    def test_missing_metadata_fork_cannot_match_null_network(self):
        meta, value = index(), case([block()])
        del meta["test_cases"][0]["fork"]
        value["test"]["network"] = None
        with self.assertRaisesRegex(fixtures.FixtureError, "missing fork"):
            self.verify(meta=meta, value=value)

    def test_metadata_fork_and_format_require_present_strings(self):
        for field in ("fork", "format"):
            for value in (None, False, 1, [], {}):
                with self.subTest(field=field, value=value):
                    meta = index()
                    meta["test_cases"][0][field] = value
                    with self.assertRaisesRegex(fixtures.FixtureError, field + " string required"):
                        self.verify(meta=meta)
            meta = index()
            del meta["test_cases"][0][field]
            with self.subTest(field=field, missing=True), \
                    self.assertRaisesRegex(fixtures.FixtureError, "missing " + field):
                self.verify(meta=meta)

    def test_fixture_network_requires_string(self):
        for engine in (False, True):
            for network in (None, False, 1, [], {}):
                with self.subTest(engine=engine, network=network):
                    value = case([], engine)
                    value["test"]["network"] = network
                    with self.assertRaisesRegex(fixtures.FixtureError, "network string required"):
                        fixtures.guest_records(ENGINE if engine else FILE, value)
            value = case([], engine)
            del value["test"]["network"]
            with self.subTest(engine=engine, missing=True), \
                    self.assertRaisesRegex(fixtures.FixtureError, "missing network"):
                fixtures.guest_records(ENGINE if engine else FILE, value)

    def test_metadata_boolean_count(self):
        meta = index()
        meta["test_count"] = True
        with self.assertRaisesRegex(fixtures.FixtureError, "test_count"):
            self.verify(meta=meta)

    def test_duplicate_metadata_identity(self):
        meta = index()
        meta["test_count"] = 2
        meta["test_cases"].append(copy.deepcopy(meta["test_cases"][0]))
        with self.assertRaisesRegex(fixtures.FixtureError, "duplicate metadata"):
            self.verify(meta=meta)

    def test_missing_metadata_test_and_extra_fixture(self):
        with self.assertRaisesRegex(fixtures.FixtureError, "identities differ"):
            self.verify(value={})
        with self.assertRaisesRegex(fixtures.FixtureError, "identities differ"):
            self.verify(meta={"test_count": 0, "test_cases": []})

    def test_missing_index(self):
        pin = archive(self.path, [(FILE, case([block()]))])
        with self.assertRaisesRegex(fixtures.FixtureError, "missing .meta"):
            fixtures.verify_archive(self.path, pin)

    def test_duplicate_archive_path(self):
        with self.assertRaisesRegex(fixtures.FixtureError, "duplicate archive"):
            self.verify(extra=[(FILE, case([block()]))])

    def test_archive_counts(self):
        with self.assertRaisesRegex(fixtures.FixtureError, "counts"):
            self.verify(records=2)
        with self.assertRaisesRegex(fixtures.FixtureError, "counts"):
            self.verify(distinct=2)

    def test_duplicate_json_key(self):
        for raw in (b'{"test":{},"test":{}}', b'{"outer":{"x":1,"x":2}}'):
            with self.assertRaisesRegex(fixtures.FixtureError, "duplicate JSON key"):
                fixtures.strict_json(raw)

    def test_non_json_constants(self):
        for value in ("NaN", "Infinity", "-Infinity"):
            with self.assertRaisesRegex(fixtures.FixtureError, "non-JSON"):
                fixtures.strict_json(value)

    def test_path_traversal(self):
        for path in ("../test.json", "/test.json", "a/../test.json", "a//test.json",
                     "a\\test.json", "fixtures/../test.json"):
            with self.subTest(path=path), self.assertRaisesRegex(fixtures.FixtureError, "unsafe"):
                fixtures.archive_name(path)

    def test_guest_hex_malformed(self):
        for value in ("0x0", "0xgg", "0x00 0", "00", None, 15):
            with self.subTest(value=value), self.assertRaisesRegex(fixtures.FixtureError, "hex"):
                self.verify(value=case([block(value)]))

    def test_unpaired_guest_fields(self):
        for field in ("statelessInputBytes", "statelessOutputBytes"):
            value = block()
            del value[field]
            with self.assertRaisesRegex(fixtures.FixtureError, "unpaired"):
                self.verify(value=case([value]))

    def test_output_length(self):
        for length in (0, 42, 44):
            with self.assertRaisesRegex(fixtures.FixtureError, "43 bytes"):
                self.verify(value=case([block(output="0x" + "00" * length)]))

    def test_label_independence(self):
        value = block()
        value.update(expectException="INVALID_BLOCK", executionWitness={"anything": True})
        _, identities, _ = self.verify(value=case([value]))
        self.assertEqual(identities, self.verify()[1])
        self.assertEqual(fixtures.guest_records(FILE, case([value]))[0],
                         fixtures.guest_records(FILE, case([block()]))[0])

    def test_no_guest_record(self):
        report, _, _ = self.verify(value=case([{}]), records=0, distinct=0)
        self.assertEqual(report["guest_records"], 0)

    def test_engine_has_no_guest_records(self):
        self.assertEqual(fixtures.guest_records(ENGINE, case([{"params": []}], True))[0], [])

    def test_dual_shape_rejected(self):
        for engine in (False, True):
            value = case([], engine)
            value["test"]["blocks" if engine else "engineNewPayloads"] = []
            with self.assertRaisesRegex(fixtures.FixtureError, "conflicting fixture"):
                fixtures.guest_records(ENGINE if engine else FILE, value)

    def test_shape_and_format_rejections(self):
        for value in ([], {"test": None}, case("not an array"), case([None])):
            with self.assertRaises(fixtures.FixtureError):
                fixtures.guest_records(FILE, value)
        with self.assertRaisesRegex(fixtures.FixtureError, "fixture-format"):
            fixtures.guest_records(FILE, case([], True))

    def test_sorted_identity_block_positions(self):
        value = {"z": case([block()])["test"], "a": case([{}, block(), block()])["test"]}
        records = fixtures.guest_records(FILE, value)[0]
        self.assertEqual([(item[0]["testId"], item[0]["blockIndex"]) for item in records],
                         [("a", 1), ("a", 2), ("z", 0)])

    def parser(self, reply="ok 1"):
        path = pathlib.Path(self.temporary.name) / "parser"
        path.write_text("#!/usr/bin/env python3\nimport sys\nfor line in sys.stdin:\n"
                        f"    print({reply!r}, flush=True)\n")
        path.chmod(0o700)
        return path

    def report_root(self):
        """A real dirty Git snapshot and a small authenticated CLI input."""
        root = pathlib.Path(self.temporary.name) / "source"
        root.mkdir()
        pin = archive(self.path, [(".meta/index.json", index()), (FILE, case([block()]))])
        fields = "\n".join(f"{key} = {json.dumps(value)}" for key, value in pin.items())
        (root / "reference.toml").write_text(
            '[release]\ntag = "test-pin"\ncommit = "test-commit"\n'
            '[release.fixtures]\n' + fields + "\n")
        (root / "lean-toolchain").write_text("leanprover/lean4:v4.34.0\n")
        (root / ".gitignore").write_text(".lake/\ninternal/\n")
        for command in (["init", "--quiet"], ["add", "."],
                        ["-c", "user.name=Fixture Test", "-c", "user.email=test@example.invalid",
                         "commit", "--quiet", "-m", "test baseline"]):
            subprocess.run(["git", *command], cwd=root, check=True, capture_output=True)
        return root

    def cli_report(self, root, *arguments):
        output = io.StringIO()
        with patch("sys.argv", ["verify_fixture_archive.py", str(self.path),
                                "--root", str(root), *map(str, arguments)]), redirect_stdout(output):
            self.assertEqual(fixtures.main(), 0, output.getvalue())
        return json.loads(output.getvalue())

    def test_report_qualifies_head_with_staged_source_and_dirty_content(self):
        root = self.report_root()
        clean = self.cli_report(root)
        self.assertFalse(clean["source_provenance"]["dirty"])
        source = root / "scripts/FixtureRecordsMain.lean"
        source.parent.mkdir(parents=True)
        source.write_text("-- newly staged source\n")
        subprocess.run(["git", "add", str(source.relative_to(root))], cwd=root, check=True)
        dirty = self.cli_report(root)
        self.assertEqual(clean["spec_commit"], dirty["spec_commit"])
        self.assertTrue(dirty["source_provenance"]["dirty"])
        self.assertIn(str(source.relative_to(root)), dirty["source_provenance"]["changed_paths"])
        self.assertNotEqual(clean["source_provenance"]["sha256"],
                            dirty["source_provenance"]["sha256"])
        entries = {entry["path"]: entry for entry in dirty["source_provenance"]["files"]}
        self.assertEqual(entries[str(source.relative_to(root))]["sha256"],
                         hashlib.sha256(source.read_bytes()).hexdigest())
        source.write_text("-- unstaged source change\n")
        edited = self.cli_report(root)
        self.assertNotEqual(dirty["source_provenance"]["sha256"],
                            edited["source_provenance"]["sha256"])
        source.unlink()
        deleted = self.cli_report(root)
        self.assertNotEqual(edited["source_provenance"]["sha256"],
                            deleted["source_provenance"]["sha256"])
        entries = {entry["path"]: entry for entry in deleted["source_provenance"]["files"]}
        self.assertEqual(entries[str(source.relative_to(root))]["kind"], "deleted")

    def test_report_source_digest_is_reproducible_and_excludes_private_artifacts(self):
        root = self.report_root()
        before = self.cli_report(root)["source_provenance"]
        for name in (".lake/build/bin/private", "internal/evidence/private", "untracked-secret"):
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("private content must not be published\n")
        after = self.cli_report(root)["source_provenance"]
        self.assertEqual(before, after)
        encoded = json.dumps(after["files"], sort_keys=True, separators=(",", ":")).encode()
        self.assertEqual(after["sha256"], hashlib.sha256(encoded).hexdigest())
        self.assertNotIn("private", json.dumps(after))
        self.assertIn("untracked", after["scope"])

    def hidden_source_edit(self, flag):
        root = self.report_root()
        before = self.cli_report(root)["source_provenance"]
        subprocess.run(["git", "update-index", flag, "lean-toolchain"], cwd=root, check=True)
        (root / "lean-toolchain").write_text("hidden modified source\n")
        after = self.cli_report(root)["source_provenance"]
        self.assertNotEqual(before["sha256"], after["sha256"])
        self.assertTrue(after["dirty"])
        self.assertEqual(after["changed_paths"], ["lean-toolchain"])

    def test_source_edit_despite_assume_unchanged(self):
        self.hidden_source_edit("--assume-unchanged")

    def test_source_edit_despite_skip_worktree(self):
        self.hidden_source_edit("--skip-worktree")

    def test_source_mode_despite_core_filemode_false(self):
        root = self.report_root()
        before = self.cli_report(root)["source_provenance"]
        subprocess.run(["git", "config", "core.filemode", "false"], cwd=root, check=True)
        source = root / "lean-toolchain"
        source.chmod(source.stat().st_mode | 0o100)
        after = self.cli_report(root)["source_provenance"]
        self.assertNotEqual(before["sha256"], after["sha256"])
        self.assertTrue(after["dirty"])
        self.assertEqual(after["changed_paths"], ["lean-toolchain"])

    def test_source_staged_and_unstaged_deletions(self):
        root = self.report_root()
        (root / "lean-toolchain").unlink()
        commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
        before = fixtures.source_provenance(root, commit)
        subprocess.run(["git", "add", "lean-toolchain"], cwd=root, check=True)
        after = fixtures.source_provenance(root, commit)
        self.assertEqual(before, after)
        self.assertTrue(after["dirty"])
        self.assertEqual(after["changed_paths"], ["lean-toolchain"])

    def test_source_symlink_target_and_kind_changes(self):
        root = self.report_root()
        source = root / "source-link"
        source.symlink_to("first-target")
        subprocess.run(["git", "add", "source-link"], cwd=root, check=True)
        subprocess.run(["git", "-c", "user.name=Fixture Test", "-c",
                        "user.email=test@example.invalid", "commit", "--quiet", "-m", "link"],
                       cwd=root, check=True)
        before = self.cli_report(root)["source_provenance"]
        self.assertFalse(before["dirty"])
        for target in ("second-target", None):
            source.unlink()
            if target is None:
                source.write_text("ordinary file\n")
            else:
                source.symlink_to(target)
            after = self.cli_report(root)["source_provenance"]
            self.assertTrue(after["dirty"])
            self.assertEqual(after["changed_paths"], ["source-link"])
            self.assertNotEqual(before["sha256"], after["sha256"])

    def test_source_tracks_all_committed_paths(self):
        root = self.report_root()
        source = root / "internal/committed"
        source.parent.mkdir()
        source.write_text("tracked source\n")
        subprocess.run(["git", "add", "--force", "internal/committed"], cwd=root, check=True)
        report = self.cli_report(root)["source_provenance"]
        self.assertIn("internal/committed", report["changed_paths"])
        self.assertTrue(report["dirty"])

    def test_report_identifies_resolved_parser_and_requested_selection(self):
        root = self.report_root()
        executable = self.parser()
        link = executable.with_name("parser-link")
        link.symlink_to(executable)
        report = self.cli_report(root, "--lean-parser", link, "--lean-files", "0")
        self.assertEqual(report["lean_parser"], {
            "path": executable.name,
            "sha256": hashlib.sha256(executable.read_bytes()).hexdigest()})
        self.assertEqual(report["lean_selection"], {
            "count_limit": 0, "count_files": [], "requested_content_files": [],
            "content_files": [], "selected_files": [], "content_all": False})
        executable.write_text(executable.read_text() + "# different artifact\n")
        changed = self.cli_report(root, "--lean-parser", link, "--lean-files", "0")
        self.assertEqual(changed["spec_commit"], report["spec_commit"])
        self.assertNotEqual(changed["lean_parser"]["sha256"], report["lean_parser"]["sha256"])
        unbounded = self.cli_report(root, "--lean-parser", link)
        self.assertIsNone(unbounded["lean_selection"]["count_limit"])
        self.assertEqual(unbounded["lean_selection"]["count_files"], [FILE])

    def test_report_records_content_paths_and_index_bound_in_report_and_index(self):
        root = self.report_root()
        identity = {"file": FILE, "testId": "test", "blockIndex": 0, "infoHash": HASH}
        executable = self.parser(json.dumps({"count": 1, "records": [
            {"id": identity, "input": "0x1501", "expected": OUTPUT}]}))
        saved_report = pathlib.Path(self.temporary.name) / "report.json"
        saved_index = pathlib.Path(self.temporary.name) / "index.json"
        report = self.cli_report(root, "--lean-parser", executable, "--lean-files", "0",
            "--lean-content-file", FILE, "--lean-content-file", FILE, "--bound", "0",
            "--report", saved_report, "--index", saved_index)
        self.assertEqual(report["lean_selection"], {
            "count_limit": 0, "count_files": [], "requested_content_files": [FILE, FILE],
            "content_files": [FILE], "selected_files": [FILE], "content_all": False})
        self.assertEqual(report["index_bound"], 0)
        self.assertEqual(report["lean_files_checked"], 1)
        self.assertEqual(report["lean_guest_records_content_compared"], 1)
        self.assertEqual(json.loads(saved_report.read_text()), report)
        self.assertEqual(json.loads(saved_index.read_text()), {"report": report, "records": []})

    def test_report_preserves_selection_failure_before_missing_parser(self):
        root = self.report_root()
        missing = pathlib.Path(self.temporary.name) / "missing-parser"
        output = io.StringIO()
        with patch("sys.argv", ["verify_fixture_archive.py", str(self.path), "--root", str(root),
                "--lean-parser", str(missing), "--lean-content-file", "absent.json"]), \
                redirect_stderr(output):
            self.assertEqual(fixtures.main(), 1)
        self.assertIn("content check file is absent from the authenticated archive", output.getvalue())

    def test_lean_batch_count(self):
        pin = archive(self.path, [(FILE, case([block()]))])
        self.assertEqual(fixtures.check_lean(self.path, pin, self.parser(), {FILE: 1}, None),
                         {"lean_files_checked": 1, "lean_guest_records_extracted": 1,
                          "lean_content_files_checked": 0, "lean_guest_records_content_compared": 0})

    def test_lean_batch_count_mismatch(self):
        pin = archive(self.path, [(FILE, case([block()]))])
        with self.assertRaisesRegex(fixtures.FixtureError, "Lean extraction"):
            fixtures.check_lean(self.path, pin, self.parser("ok 0"), {FILE: 1}, None)

    def test_lean_reauthenticates_archive_before_reading(self):
        pin = archive(self.path, [(FILE, case([block()]))])
        self.path.write_bytes(b"changed archive")
        with self.assertRaisesRegex(fixtures.FixtureError, "authentication"):
            fixtures.check_lean(self.path, pin, self.parser(), {FILE: 1}, None)

    def test_lean_batch_requires_every_selected_file(self):
        pin = archive(self.path, [])
        with self.assertRaisesRegex(fixtures.FixtureError, "missed authenticated files"):
            fixtures.check_lean(self.path, pin, self.parser(), {FILE: 1}, None)

    def test_actual_lean_driver_and_io_errors(self):
        executable = pathlib.Path(__file__).resolve().parents[1] / ".lake/build/bin/fixture-records"
        path = pathlib.Path(self.temporary.name) / "fixture.json"
        path.write_text(json.dumps(case([block()])))
        command = json.dumps([FILE, str(path)]) + "\n"
        command += json.dumps([FILE, str(path.with_name("missing.json"))]) + "\n"
        run = subprocess.run([str(executable)], input=command, capture_output=True, text=True)
        self.assertEqual(run.returncode, 1)
        self.assertEqual(run.stdout.splitlines()[0], "ok 1")
        self.assertTrue(run.stdout.splitlines()[1].startswith("error IO:"))
        self.assertEqual(run.stderr, "")

    def test_actual_lean_content_identity_and_bytes(self):
        executable = pathlib.Path(__file__).resolve().parents[1] / ".lake/build/bin/fixture-records"
        pin = archive(self.path, [(FILE, case([block("0x00AaFf")]))])
        result = fixtures.check_lean(self.path, pin, executable, {FILE: 1}, 0, [FILE])
        self.assertEqual(result["lean_content_files_checked"], 1)
        self.assertEqual(result["lean_guest_records_content_compared"], 1)

    def test_content_mismatch_even_when_count_matches(self):
        pin = archive(self.path, [(FILE, case([block()]))])
        fake = self.parser(json.dumps({"count": 1, "records": []}))
        with self.assertRaisesRegex(fixtures.FixtureError, "identity/byte-content mismatch"):
            fixtures.check_lean(self.path, pin, fake, {FILE: 1}, 0, [FILE])

    def content_reply(self):
        return {"count": 1, "records": [{"id": {"file": FILE, "testId": "test",
            "blockIndex": 0, "infoHash": HASH}, "input": "0x1501", "expected": OUTPUT}]}

    def test_content_count_rejects_boolean_and_float(self):
        pin = archive(self.path, [(FILE, case([block()]))])
        for count in (True, 1.0):
            with self.subTest(count=count):
                reply = self.content_reply()
                reply["count"] = count
                with self.assertRaisesRegex(fixtures.FixtureError, "identity/byte-content mismatch"):
                    fixtures.check_lean(self.path, pin, self.parser(json.dumps(reply)),
                                        {FILE: 1}, 0, [FILE])

    def test_content_block_index_rejects_boolean_and_float(self):
        pin = archive(self.path, [(FILE, case([block()]))])
        for block_index in (False, 0.0):
            with self.subTest(block_index=block_index):
                reply = self.content_reply()
                reply["records"][0]["id"]["blockIndex"] = block_index
                with self.assertRaisesRegex(fixtures.FixtureError, "identity/byte-content mismatch"):
                    fixtures.check_lean(self.path, pin, self.parser(json.dumps(reply)),
                                        {FILE: 1}, 0, [FILE])

    def test_content_reply_requires_exact_shape_and_integer_values(self):
        expected = self.content_reply()
        expected["records"][0]["id"]["blockIndex"] = 10 ** 100 + 1
        self.assertTrue(fixtures.same_json_value(fixtures.strict_json(json.dumps(expected)), expected))
        for actual in ([], None, {**expected, "extra": 0}, {"count": 1},
                       {**expected, "records": {}}):
            self.assertFalse(fixtures.same_json_value(actual, expected))
        changed = copy.deepcopy(expected)
        changed["records"][0]["id"]["blockIndex"] += 1
        self.assertFalse(fixtures.same_json_value(changed, expected))

    def test_actual_lean_driver_malformed_command(self):
        executable = pathlib.Path(__file__).resolve().parents[1] / ".lake/build/bin/fixture-records"
        run = subprocess.run([str(executable)], input="{}\n[]\n", capture_output=True, text=True)
        self.assertEqual(run.returncode, 1)
        self.assertTrue(all(line.startswith("error command") for line in run.stdout.splitlines()))

    def test_bound_sorted_and_guest_specific(self):
        identities = [dict(file=FILE, testId=name, blockIndex=0, infoHash=HASH)
                      for name in ("z", "a", "m")]
        special = dict(file="blockchain_tests/f/eip8025_optional_proofs/x/f.json",
                       testId="special", blockIndex=0, infoHash=HASH)
        self.assertEqual(fixtures.bounded_index(identities, 1), [identities[1]])
        self.assertEqual(fixtures.bounded_index([*identities, special], 0), [special])
        self.assertEqual(fixtures.bounded_index(identities, 1),
                         fixtures.bounded_index(list(reversed(identities)), 1))
        with self.assertRaisesRegex(fixtures.FixtureError, "duplicate guest"):
            fixtures.sorted_index([identities[0], identities[0]])
        with self.assertRaisesRegex(fixtures.FixtureError, "natural"):
            fixtures.bounded_index(identities, -1)


if __name__ == "__main__":
    unittest.main()
