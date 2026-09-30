# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Shared R9 archive authentication, strict JSON and paired guest-byte validation.

Authentication hashes a private 0600 temporary snapshot and parses that same snapshot.
Changes to the original file during copying either yield the pinned bytes or fail its
size/digest check; later in-place writes cannot affect parsing. Archive paths are never
extracted. Normal directory entries may be skipped; links and special files are rejected.
"""
from collections.abc import Iterator, Mapping
from contextlib import contextmanager
import hashlib
import json
import pathlib
import re
import tarfile
import tempfile
from typing import Any, BinaryIO


class FixtureError(ValueError):
    """An archive, metadata or byte-record verification failure."""


def strict_json(raw: bytes | str) -> Any:
    """Parse JSON, rejecting duplicate keys, constants and lone surrogate escapes."""
    def pairs(entries: list[tuple[str, Any]]) -> dict[str, Any]:
        result = {}
        for key, value in entries:
            if key in result:
                raise FixtureError(f"duplicate JSON key: {key}")
            result[key] = value
        return result

    def constant(value: str) -> None:
        raise FixtureError(f"non-JSON numeric constant: {value}")

    value = json.loads(raw, object_pairs_hook=pairs, parse_constant=constant)
    todo = [value]
    while todo:
        node = todo.pop()
        if isinstance(node, str):
            if re.search("[\ud800-\udfff]", node):
                raise FixtureError("lone surrogate in JSON string")
        elif isinstance(node, dict):
            todo.extend(node.keys())
            todo.extend(node.values())
        elif isinstance(node, list):
            todo.extend(node)
    return value


def archive_name(name: str) -> str:
    """Normalize permitted archive prefixes and reject ambiguous/traversal paths."""
    name = name.removeprefix("./").removeprefix("fixtures/")
    path = pathlib.PurePosixPath(name)
    if (not name or path.is_absolute() or "\\" in name or
            any(part in ("", ".", "..") for part in name.split("/"))):
        raise FixtureError(f"unsafe archive path: {name}")
    return name


def hex_bytes(value: Any, location: str) -> bytes:
    """Decode an even-length ASCII hex byte string with the exact 0x prefix."""
    if not isinstance(value, str) or not re.fullmatch(r"0x(?:[0-9a-fA-F]{2})*", value):
        raise FixtureError(f"{location}: hex bytes required")
    return bytes.fromhex(value[2:])


def paired_bytes(node: Mapping[str, Any], pin: Mapping[str, Any],
                 location: str) -> tuple[bytes, bytes] | None:
    """Validate a pair using the pin's field names, without interpreting validity labels."""
    input_field, output_field = pin["input_field"], pin["output_field"]
    has_in, has_out = input_field in node, output_field in node
    if has_in != has_out:
        raise FixtureError(f"{location}: unpaired guest fields")
    if not has_in:
        return None
    input_bytes = hex_bytes(node[input_field], location + "." + input_field)
    output_bytes = hex_bytes(node[output_field], location + "." + output_field)
    if len(output_bytes) != 43:
        raise FixtureError(f"{location}: guest output must be 43 bytes")
    return input_bytes, output_bytes


@contextmanager
def authenticated_source(path: pathlib.Path, fixtures: Mapping[str, Any]
                         ) -> Iterator[tuple[BinaryIO, str]]:
    """Authenticate a private snapshot before any tar or JSON parsing."""
    with tempfile.TemporaryFile(mode="w+b") as snapshot:
        digest = hashlib.sha256()
        size = 0
        with path.open("rb") as source:
            while chunk := source.read(1024 * 1024):
                snapshot.write(chunk)
                digest.update(chunk)
                size += len(chunk)
        sha256 = digest.hexdigest()
        if size != fixtures["size_bytes"] or sha256 != fixtures["sha256"]:
            raise FixtureError("archive fails reference.toml size/sha256 authentication")
        snapshot.seek(0)
        yield snapshot, sha256


def archive_members(source: BinaryIO) -> Iterator[tuple[str, bytes]]:
    """Stream unique JSON members; validate every member's path and allowed kind."""
    names = set()
    with tarfile.open(fileobj=source, mode="r|gz") as archive:
        for member in archive:
            # Tar directory names conventionally end in /; the top-level root is allowed.
            raw_name = member.name.rstrip("/") if member.isdir() else member.name
            if raw_name in ("fixtures", "./fixtures") and member.isdir():
                continue
            name = archive_name(raw_name)
            if member.isdir() and not name.endswith(".json"):
                continue
            if not member.isfile():
                raise FixtureError(f"archive member kind is forbidden: {member.name}")
            if not name.endswith(".json"):
                continue
            if name in names:
                raise FixtureError(f"duplicate archive JSON path: {name}")
            names.add(name)
            with archive.extractfile(member) as stream:
                yield name, stream.read()


def archive_json(source: BinaryIO) -> Iterator[tuple[str, Any]]:
    """Parse each original JSON member under the shared strict JSON policy."""
    for name, raw in archive_members(source):
        yield name, strict_json(raw)
