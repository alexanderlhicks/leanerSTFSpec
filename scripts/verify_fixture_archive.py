#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Authenticate the pinned archive and verify all metadata links and guest byte records.

No semantic guest execution occurs. --lean-parser runs the Lean extraction
helper against authenticated original JSON files, after full metadata verification.
--lean-files bounds this extraction check by sorted file name; omission checks all files.
This bound is a parser check, not a conformance tier or a choice of R5's CI policy.
--lean-content-file additionally compares identities and decoded byte content for explicitly
selected files; --lean-content-all compares the full corpus. Ordinary counts establish
extraction counts only.

Source provenance hashes a sorted tracked-file manifest (including kinds, executable
modes, additions and deletions) as UTF-8 JSON with sort_keys=True and separators=(',', ':').
HEAD blob contents supply the baseline independently of assume-unchanged, skip-worktree
and core.filemode. The manifest is retained to make the aggregate digest independently
recomputable. Artifact identities are repository-relative paths or external basenames;
these identities do not establish binary/source correspondence.
"""
import argparse
from contextlib import contextmanager
from collections import Counter
import hashlib
import json
import os
import pathlib
import stat
import subprocess
import tarfile
import tempfile
import tomllib


from fixture_archive import (FixtureError, archive_json, archive_members, archive_name,
                             authenticated_source, hex_bytes, paired_bytes, strict_json)
from typing import Any
import sys

# Defaults support direct projection probes; CLI/archive verification always supplies the pin.
DEFAULT_FIELDS = {"input_field": "statelessInputBytes", "output_field": "statelessOutputBytes"}


def same_json_value(actual: Any, expected: Any) -> bool:
    """Compare JSON shape and values without equating booleans, floats and integers."""
    if type(actual) is not type(expected):
        return False
    if isinstance(expected, dict):
        return actual.keys() == expected.keys() and all(
            same_json_value(actual[key], value) for key, value in expected.items())
    if isinstance(expected, list):
        return len(actual) == len(expected) and all(
            same_json_value(a, b) for a, b in zip(actual, expected))
    return actual == expected


def object_value(value: Any, location: str) -> dict[str, Any]:
    """Require a JSON object at a named fixture location."""
    if not isinstance(value, dict):
        raise FixtureError(f"{location}: object required")
    return value


def required(value: dict[str, Any], field: str, location: str) -> Any:
    """Require field presence, preserving explicit null for later shape validation."""
    if field not in value:
        raise FixtureError(f"{location}: missing {field}")
    return value[field]


def metadata(value: Any) -> dict[tuple[str, str], dict[str, Any]]:
    """Validate metadata and index it by its unique file/test identity."""
    value = object_value(value, ".meta/index.json")
    cases = required(value, "test_cases", ".meta/index.json")
    count = required(value, "test_count", ".meta/index.json")
    if not isinstance(cases, list) or type(count) is not int or count != len(cases):
        raise FixtureError("metadata test_count differs from test_cases length")
    entries, ids = {}, set()
    for entry in cases:
        entry = object_value(entry, "metadata test case")
        test_id = required(entry, "id", "metadata test case")
        path = required(entry, "json_path", "metadata test case")
        fixture_hash = required(entry, "fixture_hash", "metadata test case")
        if not isinstance(test_id, str) or not isinstance(path, str):
            raise FixtureError("metadata identity strings required")
        if archive_name(path) != path:
            raise FixtureError("metadata path must be archive-relative")
        if len(hex_bytes(fixture_hash, "metadata fixture_hash")) != 32:
            raise FixtureError("metadata fixture_hash must be 32 bytes")
        for field in ("format", "fork"):
            if not isinstance(required(entry, field, "metadata test case"), str):
                raise FixtureError(f"metadata {field} string required")
        if test_id in ids or (path, test_id) in entries:
            raise FixtureError(f"duplicate metadata identity: {path}:{test_id}")
        ids.add(test_id)
        entries[path, test_id] = entry
    return entries


def guest_records(file: str, value: Any, pin=DEFAULT_FIELDS):
    """Project only blocks' paired fields, independently of all validity labels."""
    value = object_value(value, file)
    engine = file.startswith("blockchain_tests_engine/")
    if not engine and not file.startswith("blockchain_tests/"):
        raise FixtureError(f"unsupported fixture file: {file}")
    records, hashes = [], {}
    for test_id, test in sorted(value.items()):
        location = f"{file}:{test_id}"
        test = object_value(test, location)
        info = object_value(required(test, "_info", location), location + "._info")
        info_hash = required(info, "hash", location)
        if len(hex_bytes(info_hash, location + "._info.hash")) != 32:
            raise FixtureError(f"{location}: _info.hash must be 32 bytes")
        expected_format = "blockchain_test_engine" if engine else "blockchain_test"
        if required(info, "fixture-format", location) != expected_format:
            raise FixtureError(f"{location}: fixture-format mismatch")
        network = required(test, "network", location)
        if not isinstance(network, str):
            raise FixtureError(f"{location}: network string required")
        hashes[file, test_id] = (info_hash, expected_format, network)
        container, other = (("engineNewPayloads", "blocks") if engine
                            else ("blocks", "engineNewPayloads"))
        if other in test:
            raise FixtureError(f"{location}: conflicting fixture shapes")
        blocks = required(test, container, location)
        if not isinstance(blocks, list):
            raise FixtureError(f"{location}: {container} must be an array")
        if engine:
            # Engine payloads are a distinct stateful format. They are never a guest source.
            continue
        for index, block in enumerate(blocks):
            block = object_value(block, f"{location}:blocks[{index}]")
            pair = paired_bytes(block, pin, f"{location}:blocks[{index}]")
            if pair is None:
                continue
            input_bytes, _ = pair
            records.append(({"file": file, "testId": test_id, "blockIndex": index,
                             "infoHash": info_hash}, hashlib.sha256(input_bytes).digest()))
    return records, hashes


def sorted_index(index: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Order complete guest identities, rejecting duplicates."""
    def key(record):
        return record["file"], record["testId"], record["blockIndex"], record["infoHash"]
    result = sorted(index, key=key)
    if any(key(a) == key(b) for a, b in zip(result, result[1:])):
        raise FixtureError("duplicate guest identity")
    return result


def bounded_index(index: list[dict[str, Any]], bound: int) -> list[dict[str, Any]]:
    """Explicit tooling bound, pending the public core/ci tier policy."""
    if type(bound) is not int or bound < 0:
        raise FixtureError("bound must be a natural number")
    counts, selected = Counter(), []
    for record in sorted_index(index):
        file = pathlib.PurePosixPath(record["file"])
        directory = str(file.parent)
        if "eip8025_optional_proofs" in file.parts or counts[directory] < bound:
            selected.append(record)
        counts[directory] += 1
    return selected


def verify_archive(path: pathlib.Path, fixtures: dict[str, Any]):
    """Authenticate before tar/JSON parsing, then verify the entire corpus in one pass."""
    files, records, inputs, links, meta, counts = set(), [], set(), {}, None, {}
    with authenticated_source(path, fixtures) as (source, sha256):
        for name, value in archive_json(source):
            files.add(name)
            if name == ".meta/index.json":
                meta = metadata(value)
            else:
                extracted, hashes = guest_records(name, value, fixtures)
                counts[name] = len(extracted)
                records.extend(identity for identity, _ in extracted)
                inputs.update(fingerprint for _, fingerprint in extracted)
                links.update(hashes)
    if meta is None:
        raise FixtureError("missing .meta/index.json")
    if links.keys() != meta.keys():
        missing, extra = meta.keys() - links.keys(), links.keys() - meta.keys()
        raise FixtureError(f"metadata identities differ: missing {len(missing)}, "
                           f"extra {len(extra)}")
    for identity, (fixture_hash, fixture_format, network) in links.items():
        entry = meta[identity]
        if (fixture_hash != entry["fixture_hash"] or fixture_format != entry["format"] or
                network != entry["fork"]):
            raise FixtureError(f"metadata hash/format/fork mismatch: {identity}")
    actual = (len(files), len(records), len(inputs))
    expected = tuple(fixtures[field] for field in
                     ("json_files", "guest_records", "distinct_guest_inputs"))
    if actual != expected:
        raise FixtureError(f"archive JSON/guest/distinct counts {actual} != {expected}")
    report = {"authenticated": True, "archive_size_bytes": fixtures["size_bytes"],
              "archive_sha256": sha256, "json_files": len(files),
              "guest_records": len(records), "distinct_guest_input_fingerprints": len(inputs),
              "metadata_links": len(links), "semantic_guest_executions": 0}
    return report, sorted_index(records), counts


def lean_selection(counts: dict[str, int], limit: int | None, requested_content_files):
    """Identify exactly the count slice and additional content inputs requested."""
    count_files = sorted(counts) if limit is None else sorted(counts)[:limit]
    content_files = sorted(set(requested_content_files))
    if not set(content_files) <= counts.keys():
        raise FixtureError("content check file is absent from the authenticated archive")
    return {"count_limit": limit, "count_files": count_files,
            "requested_content_files": list(requested_content_files),
            "content_files": content_files,
            "selected_files": sorted(set(count_files + content_files))}


def expected_content(name: str, raw: bytes, pin: dict[str, Any]) -> list[dict[str, Any]]:
    """Reconstruct canonical byte/identity replies from authenticated original JSON."""
    original = strict_json(raw)
    identities, _ = guest_records(name, original, pin)
    result = []
    for identity, _ in identities:
        block = original[identity["testId"]]["blocks"][identity["blockIndex"]]
        input_bytes, output_bytes = paired_bytes(block, pin, name)
        result.append({"id": identity, "input": "0x" + input_bytes.hex(),
                       "expected": "0x" + output_bytes.hex()})
    return result


@contextmanager
def lean_session(executable: pathlib.Path):
    """Keep one parser alive, closing it on success and reaping it on every failure."""
    with subprocess.Popen([str(executable)], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                          text=True) as process:
        try:
            yield process
            process.stdin.close()
            if process.wait() != 0:
                raise FixtureError("Lean extraction process failed")
        finally:
            if process.poll() is None:
                process.kill()
                process.wait()


def check_lean(path: pathlib.Path, fixtures: dict[str, Any], executable: pathlib.Path,
               counts: dict[str, int], limit: int | None, content_files=(), *, selection=None):
    """Compare a selected authenticated file set with the actual Lean CLI replies."""
    if selection is None:
        selection = lean_selection(counts, limit, content_files)
    selected = set(selection["selected_files"])
    content_files = set(selection["content_files"])
    checked = extracted = content_checked = content_records = 0
    with authenticated_source(path, fixtures) as (source, _), \
            tempfile.TemporaryDirectory(prefix="stfspec-fixture-") as directory, \
            lean_session(executable) as process:
        temporary = pathlib.Path(directory) / "fixture.json"
        for name, raw in archive_members(source):
            if name not in selected:
                continue
            temporary.write_bytes(raw)
            content = name in content_files
            command = [name, str(temporary)] + (["content"] if content else [])
            process.stdin.write(json.dumps(command) + "\n")
            process.stdin.flush()
            reply = process.stdout.readline().strip()
            if content:
                expected = {"count": counts[name],
                            "records": expected_content(name, raw, fixtures)}
                if not same_json_value(strict_json(reply), expected):
                    raise FixtureError(f"Lean identity/byte-content mismatch: {name}")
                content_checked += 1
                content_records += counts[name]
            elif reply != f"ok {counts[name]}":
                raise FixtureError(f"Lean extraction {name}: {reply!r}, expected {counts[name]}")
            checked += 1
            extracted += counts[name]
    if checked != len(selected):
        raise FixtureError("Lean extraction missed authenticated files")
    return {"lean_files_checked": checked, "lean_guest_records_extracted": extracted,
            "lean_content_files_checked": content_checked,
            "lean_guest_records_content_compared": content_records}


def artifact_identity(path: pathlib.Path, root: pathlib.Path | None = None):
    """Identity of the selected artifact, without a source-correspondence claim."""
    path = path.resolve(strict=True)
    with path.open("rb") as stream:
        sha256 = hashlib.file_digest(stream, "sha256").hexdigest()
    display = path.name
    if root is not None and path.is_relative_to(root.resolve()):
        display = path.relative_to(root.resolve()).as_posix()
    return {"path": display, "sha256": sha256}


def source_provenance(root: pathlib.Path, commit: str) -> dict[str, Any]:
    """Hash a reproducible manifest of tracked working-tree inputs, including additions.

    Each file contributes its path, kind, executable mode and SHA-256; deletions are
    explicit. Symlink targets are hashed without following them. Untracked/ignored
    content is excluded. All tracked paths are included; Git index flags cannot hide edits.
    The manifest records identities only, never the source or private file content.
    """
    root = root.resolve()

    def git_paths(arguments):
        return set(subprocess.check_output(["git", *arguments], cwd=root).split(b"\0")) - {b""}

    tracked = git_paths(["ls-files", "--cached", "-z"])
    baseline = {}
    objects = []
    for record in subprocess.check_output(["git", "ls-tree", "-r", "-z", commit],
                                          cwd=root).split(b"\0"):
        if not record:
            continue
        details, name = record.split(b"\t", 1)
        mode, kind, oid = details.split()
        if kind != b"blob" or mode not in (b"100644", b"100755", b"120000"):
            raise FixtureError(f"unsupported baseline source kind: {name.decode('utf-8')}")
        objects.append((name, mode, oid))
    if objects:
        # Git objects supply the baseline independently of index flags and core.filemode.
        raw = subprocess.check_output(["git", "cat-file", "--batch"], cwd=root,
                                      input=b"".join(oid + b"\n" for _, _, oid in objects))
        offset = 0
        for name, mode, _ in objects:
            end = raw.index(b"\n", offset)
            _, kind, size = raw[offset:end].split()
            if kind != b"blob":
                raise FixtureError("baseline source object is not a blob")
            offset = end + 1
            size = int(size)
            baseline[name] = {"path": name.decode("utf-8"),
                "kind": "symlink" if mode == b"120000" else "file", "mode": mode.decode(),
                "sha256": hashlib.sha256(raw[offset:offset + size]).hexdigest()}
            offset += size + 1
    files = []
    changed = []
    for name in sorted(tracked | baseline.keys()):
        path = root / name.decode("utf-8")
        entry = {"path": name.decode("utf-8"), "kind": "deleted", "mode": None, "sha256": None}
        if name in tracked and (path.exists() or path.is_symlink()):
            mode = path.lstat().st_mode
            if stat.S_ISLNK(mode):
                raw = os.fsencode(os.readlink(path))
                entry.update(kind="symlink", mode="120000", sha256=hashlib.sha256(raw).hexdigest())
            elif stat.S_ISREG(mode):
                with path.open("rb") as stream:
                    sha256 = hashlib.file_digest(stream, "sha256").hexdigest()
                entry.update(kind="file", mode="100755" if mode & stat.S_IXUSR else "100644",
                             sha256=sha256)
            else:
                raise FixtureError(f"unsupported tracked source kind: {entry['path']}")
        files.append(entry)
        if entry != baseline.get(name):
            changed.append(entry["path"])
    encoded = json.dumps(files, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return {"dirty": bool(changed), "changed_paths": changed,
            "scope": "tracked worktree files, including staged additions; "
                     "untracked/ignored excluded",
            "digest_format": "sha256 of UTF-8 JSON files manifest, "
                             "sort_keys=True, separators=(',', ':')",
            "sha256": hashlib.sha256(encoded).hexdigest(), "files": files}


def main() -> int:
    """Verify the pinned corpus and emit qualified extraction evidence."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=pathlib.Path, help="pinned gzip tar archive")
    parser.add_argument("--root", type=pathlib.Path,
                        default=pathlib.Path(__file__).resolve().parents[1],
                        help="repository containing reference.toml and source provenance")
    parser.add_argument("--report", type=pathlib.Path, help="write JSON extraction evidence")
    parser.add_argument("--index", type=pathlib.Path,
                        help="write sorted record identities with report")
    parser.add_argument("--bound", type=int, help="explicit per-directory index bound (not a tier)")
    parser.add_argument("--lean-parser", type=pathlib.Path, help="fixture-records executable")
    parser.add_argument("--lean-files", type=int, help="check first N sorted files for counts")
    parser.add_argument("--lean-content-file", action="append", default=[], metavar="ARCHIVE_PATH",
                        help="also compare actual identities/bytes for this authenticated file")
    parser.add_argument("--lean-content-all", action="store_true",
                        help="compare every fixture identity and byte pair (requires parser)")
    args = parser.parse_args()
    try:
        if args.lean_files is not None and (args.lean_files < 0 or args.lean_parser is None):
            raise FixtureError("--lean-files requires --lean-parser and a nonnegative bound")
        if (args.lean_content_file or args.lean_content_all) and args.lean_parser is None:
            raise FixtureError("--lean-content-file requires --lean-parser")
        if args.bound is not None and args.bound < 0:
            raise FixtureError("--bound requires a nonnegative bound")
        release = tomllib.loads((args.root / "reference.toml").read_text())["release"]
        report, index, counts = verify_archive(args.archive, release["fixtures"])
        report.update(pin_tag=release["tag"], pin_commit=release["commit"],
                      lean_toolchain=(args.root / "lean-toolchain").read_text().strip(),
                      spec_commit=subprocess.check_output(
                          ["git", "rev-parse", "HEAD"], cwd=args.root, text=True).strip())
        report["source_provenance"] = source_provenance(args.root, report["spec_commit"])
        report["host_verifier"] = artifact_identity(pathlib.Path(__file__), args.root)
        if args.bound is not None:
            index = bounded_index(index, args.bound)
        report["index_bound"] = args.bound
        report["indexed_guest_records"] = len(index)
        if args.lean_parser:
            content_files = sorted(counts) if args.lean_content_all else args.lean_content_file
            report["lean_selection"] = lean_selection(counts, args.lean_files, content_files)
            report["lean_selection"]["content_all"] = args.lean_content_all
            report["lean_parser"] = artifact_identity(args.lean_parser, args.root)
            report.update(check_lean(args.archive, release["fixtures"],
                                     args.lean_parser.resolve(strict=True), counts, args.lean_files,
                                     selection=report["lean_selection"]))
        if args.index:
            args.index.write_text(json.dumps({"report": report, "records": index}, indent=2) + "\n")
        if args.report:
            args.report.write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps(report, sort_keys=True))
    except (OSError, ValueError, tarfile.TarError, subprocess.SubprocessError) as error:
        print(f"fixture archive: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
