#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Validate the pin and toolchains; --fetch DIR also verifies the archive and guest pairs.

Archive bytes are authenticated before parsing. Counts are over JSON objects containing
both fields, never text occurrences. Downloads are installed atomically.
"""
import argparse
from collections import Counter
import hashlib
import json
import pathlib
import re
from fixture_archive import archive_json, authenticated_source, paired_bytes
import sys
import tarfile
import tempfile
import tomllib
import urllib.parse
import urllib.request


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def fixture_stats(path, fx):
    """Return file/record/distinct counts and area index; reject malformed guest records."""
    files = records = 0
    inputs, areas = set(), Counter()
    with authenticated_source(path, fx) as (source, _):
        for name, value in archive_json(source):
            files += 1
            areas["/".join(name.split("/")[:4])] += 1
            todo = [value]
            while todo:
                node = todo.pop()
                if isinstance(node, list):
                    todo.extend(node)
                elif isinstance(node, dict):
                    pair = paired_bytes(node, fx, name)
                    if pair is not None:
                        inputs.add(hashlib.sha256(pair[0]).digest())
                        records += 1
                    todo.extend(node.values())
    return files, records, len(inputs), areas


def check_pin(root, m):
    rel, spec, fx = m["release"], m["release"]["spec"], m["release"]["fixtures"]
    errors = []
    if m.get("schema") != 1:
        errors.append("unsupported reference schema (expected 1)")
    for label, value, pattern in (("release.commit", rel["commit"], r"[0-9a-f]{40}"),
                                  ("release.tag", rel["tag"], r"tests-zkevm@v\d+\.\d+\.\d+"),
                                  ("fixtures.sha256", fx["sha256"], r"[0-9a-f]{64}")):
        if not isinstance(value, str) or not re.fullmatch(pattern, value):
            errors.append(f"{label} has an invalid shape")
    for key in ("protocol_fork_index", "schema_revision"):
        if type(spec[key]) is not int or not 0 <= spec[key] <= 255:
            errors.append(f"{key} must fit one byte")
    if spec["schema_id"] != (spec["protocol_fork_index"] << 8) | spec["schema_revision"]:
        errors.append("schema_id != protocol_fork_index << 8 | schema_revision")
    for key in ("size_bytes", "json_files", "guest_records", "distinct_guest_inputs"):
        if type(fx[key]) is not int or fx[key] <= 0:
            errors.append(f"fixtures.{key} must be positive")
    if fx["distinct_guest_inputs"] > fx["guest_records"]:
        errors.append("distinct guest input count exceeds guest records")
    if pathlib.PurePosixPath(fx["asset"]).name != fx["asset"] or fx["asset"] in ("", ".", ".."):
        errors.append("fixtures.asset must be a filename")
    expected = rel["repository"].rstrip("/") + "/releases/download/" + urllib.parse.quote(rel["tag"], safe="") + "/" + fx["asset"]
    if fx["url"] != expected:
        errors.append("fixtures.url must name the repository, release tag and asset")
    contract = (root / "STFSpec/informal/CONTRACT.md").read_text()
    if rel["tag"] not in contract or rel["commit"][:8] not in contract:
        errors.append("CONTRACT.md does not cite the pinned tag and commit")
    for name in ("lean-toolchain", "STFSpecMathlib/lean-toolchain", "STFSpecSecurity/lean-toolchain"):
        if (root / name).read_text().strip() != m["lean"]["toolchain"]:
            errors.append(f"{name}: toolchain differs from reference.toml")
    return errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=pathlib.Path, default=pathlib.Path("."))
    parser.add_argument("--fetch", type=pathlib.Path, metavar="DIR")
    args = parser.parse_args()
    try:
        m = tomllib.loads((args.root / "reference.toml").read_text())
        errors = check_pin(args.root, m)
        rel, fx = m["release"], m["release"]["fixtures"]
        if args.fetch and not errors:
            args.fetch.mkdir(parents=True, exist_ok=True)
            path = args.fetch / fx["asset"]
            if not path.exists():
                with tempfile.NamedTemporaryFile(dir=args.fetch, delete=False) as temporary:
                    tmp = pathlib.Path(temporary.name)
                try:
                    print(f"downloading {fx['url']}", flush=True)
                    urllib.request.urlretrieve(fx["url"], tmp)
                    if tmp.stat().st_size != fx["size_bytes"] or digest(tmp) != fx["sha256"]:
                        raise ValueError("downloaded archive fails size/sha256 authentication")
                    tmp.replace(path)
                finally:
                    tmp.unlink(missing_ok=True)
            if path.stat().st_size != fx["size_bytes"]:
                errors.append("archive size differs from reference.toml")
            if digest(path) != fx["sha256"]:
                errors.append("archive sha256 differs from reference.toml")
            if not errors:
                files, records, distinct, _ = fixture_stats(path, fx)
                for label, actual, expected in (("JSON files", files, fx["json_files"]),
                                                ("guest records", records, fx["guest_records"]),
                                                ("distinct inputs (SHA-256 fingerprints)", distinct, fx["distinct_guest_inputs"])):
                    if actual != expected:
                        errors.append(f"{label}: {actual} != {expected}")
                print(f"fixtures: authenticated archive; {files} JSON files, {records} paired records, {distinct} distinct input fingerprints")
    except (OSError, ValueError, KeyError, TypeError, tarfile.TarError) as error:
        print(f"reference: {error}")
        return 1
    for error in errors:
        print("reference:", error)
    print(f"check_reference: {rel['tag']} @ {rel['commit'][:8]}; {len(errors)} problems")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
