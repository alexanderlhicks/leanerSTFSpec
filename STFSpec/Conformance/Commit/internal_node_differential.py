#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Compare complete internal-node outputs with current authenticated pinned EELS.

From the repository root, run:
EELS/.venv/bin/python -I -B STFSpec/Conformance/Commit/internal_node_differential.py \
    --eels EELS --output SCRATCH.lean
Use an output outside both checkouts. The driver does not manually change resource
limits; reference imports may change them (`src/ethereum/__init__.py:30` at the pin).
Authentication uses pinned source/lock blobs and installed types/RLP RECORD; the frozen
installation, interpreter/startup and RECORD are trusted environment inputs. Byte/list
models are constructed only after exact source classes are checked. Richer Extended
fields use this private caller-owned interpretation, without raw class equality.
Unsupported/cyclic arbitrary Python objects and guest/resource behavior are outside this
finite evidence. Oracle instrumentation is restored in finally.
"""

import base64
import dataclasses
import hashlib
import importlib.metadata
import importlib.util
import json
from pathlib import Path
import platform
import sys
import subprocess
import tomllib

ROOT = Path(__file__).resolve().parents[3]


def main():
    if not sys.flags.isolated or not sys.flags.dont_write_bytecode:
        print("run with the frozen EELS venv launcher -I -B", file=sys.stderr)
        raise SystemExit(2)
    SPEC = importlib.util.spec_from_file_location(
        "commit_node_differential_shared", ROOT / "scripts/differential.py"
    )
    shared = importlib.util.module_from_spec(SPEC)
    SPEC.loader.exec_module(shared)
    driver = shared.Driver(__doc__, __file__, 0)

    def require(ok, why):
        if not ok:
            raise AssertionError(why)

    def digest(data):
        return hashlib.sha256(data).hexdigest()

    def package_inventory(name, package):
        distribution = importlib.metadata.distribution(name)
        pin = tomllib.loads((ROOT / "reference.toml").read_text())["release"][
            "python_dependencies"
        ][name]
        require(distribution.version == pin, "version differs from pin: " + name)
        hashes, records = {}, []
        for file in distribution.files or []:
            relative = Path(file)
            source = Path(distribution.locate_file(file)).absolute()
            if relative.name == "RECORD" and relative.parent.name.endswith(".dist-info"):
                records.append(source)
            if not relative.parts or relative.parts[0] != package or relative.suffix != ".py":
                continue
            require(
                source.resolve() == source and source.is_relative_to(driver.eels / ".venv"),
                "package path outside frozen venv",
            )
            require(
                file.hash is not None and file.hash.mode == "sha256" and file.size is not None,
                "package file lacks SHA256 RECORD",
            )
            hashes[source] = (file.hash.value, file.size)
        require(len(records) == 1 and bool(hashes), "missing package sources/RECORD")
        record = records[0]
        require(
            record.resolve() == record and record.is_relative_to(driver.eels / ".venv"),
            "RECORD outside venv",
        )
        return {
            "version": distribution.version,
            "package": Path(distribution.locate_file(package)).absolute(),
            "record": record,
            "record_bytes": record.read_bytes(),
            "hashes": hashes,
        }

    rlp_auth = package_inventory("ethereum-rlp", "ethereum_rlp")

    def check_rlp_bytes(source, data):
        expected = rlp_auth["hashes"].get(source)
        observed = base64.urlsafe_b64encode(hashlib.sha256(data).digest()).decode().rstrip("=")
        return source.resolve() == source and expected == (observed, len(data))

    def check_rlp():
        require(
            rlp_auth["record"].read_bytes() == rlp_auth["record_bytes"], "rlp RECORD changed"
        )
        require(
            set(rlp_auth["package"].rglob("*.py")) == set(rlp_auth["hashes"]),
            "rlp source inventory changed",
        )
        for source in rlp_auth["hashes"]:
            require(
                check_rlp_bytes(source, source.read_bytes()),
                "rlp bytes differ from RECORD: " + str(source),
            )

    class AuthenticatedRlpLoader(shared.FreshSourceLoader):
        def get_code(self, fullname):
            source = Path(self.get_filename(fullname))
            require(
                check_rlp_bytes(source, self.get_data(str(source))),
                "rlp import bytes differ from installed RECORD",
            )
            return super().get_code(fullname)

    class AuthenticatedRlpFinder(shared.FreshSourceFinder):
        def find_spec(self, fullname, path=None, target=None):
            if fullname.split(".", 1)[0] != "ethereum_rlp":
                return None
            spec = super().find_spec(fullname, path, target)
            require(
                spec is not None and isinstance(spec.loader, shared.FreshSourceLoader),
                "rlp not fresh Python source",
            )
            source = Path(spec.origin).absolute()
            require(
                source.resolve() == source and source in rlp_auth["hashes"],
                "rlp outside authenticated source inventory",
            )
            spec.loader = AuthenticatedRlpLoader(fullname, str(source), driver)
            return spec

    check_rlp()
    require(
        not any(name.split(".", 1)[0] == "ethereum_rlp" for name in sys.modules),
        "rlp imported before authentication",
    )
    sys.meta_path.insert(0, AuthenticatedRlpFinder(driver))
    from ethereum import merkle_patricia_trie as mpt
    from ethereum.crypto import hash as hash_module
    from ethereum_rlp import rlp
    from ethereum_rlp.exceptions import EncodingError
    from ethereum_types.bytes import Bytes, Bytes32
    from ethereum_types.numeric import Uint, U256

    for module, path in [
        (mpt, "ethereum/merkle_patricia_trie.py"),
        (hash_module, "ethereum/crypto/hash.py"),
    ]:
        driver.check_source(module, path)
    driver.check_source(rlp, "ethereum_rlp/rlp.py", dependency=True)
    require(
        Bytes is bytes and hash_module.Hash32 is Bytes32, "unexpected byte/hash class aliases"
    )
    require(
        type(mpt.InternalNode) is type(mpt.LeafNode | mpt.ExtensionNode | mpt.BranchNode),
        "unexpected node union",
    )

    @dataclasses.dataclass(frozen=True)
    class LocalRecord:
        first: bytes
        second: Uint

    def typename(value):
        return type(value).__module__ + "." + type(value).__qualname__

    def exact_tree(value):
        """Require exact admitted Python classes before any bytes/int/list conversion."""
        cls = type(value)
        if cls is bytes or cls is bytearray or cls is Bytes32:
            return {"class": typename(value), "hex": value.hex()}
        if cls is bool:
            return {"class": typename(value), "value": value}
        if cls is Uint or cls is U256:
            return {"class": typename(value), "decimal": str(int(value))}
        if cls is str:
            return {"class": typename(value), "value": value}
        if cls is tuple or cls is list:
            return {"class": typename(value), "items": [exact_tree(v) for v in value]}
        if cls is LocalRecord:
            require(
                type(value.first) is bytes and type(value.second) is Uint,
                "local record fields wrong exact class",
            )
            return {
                "class": typename(value),
                "fields": [exact_tree(value.first), exact_tree(value.second)],
            }
        raise TypeError("exact admitted Extended class required: " + typename(value))

    def model_field(field):
        # Interpret the recorded exact-class field using the same checked dispatch.
        name = field["class"]
        if "hex" in field:
            return {"bytes": field["hex"]}
        if name == "builtins.bool":
            return {"bytes": "01" if field["value"] else ""}
        if name in ("ethereum_types.numeric.Uint", "ethereum_types.numeric.U256"):
            number = int(field["decimal"])
            return {"bytes": number.to_bytes((number.bit_length() + 7) // 8, "big").hex()}
        if name == "builtins.str":
            return {"bytes": field["value"].encode().hex()}
        return {"list": [model_field(v) for v in field.get("items", field.get("fields", []))]}

    def to_item(value):
        """Interpret a field only after exact-class checks, retaining provider checks."""
        tree = exact_tree(value)
        item = model_field(tree)
        if type(value) in (Uint, U256):
            encoded = value.to_be_bytes()
            require(type(encoded) is bytes, "numeric provider did not return exact bytes")
            require(encoded.hex() == item["bytes"], "numeric provider/model mismatch")
        elif type(value) in (tuple, list):
            require(
                item == {"list": [to_item(v) for v in value]}, "nested provider/model mismatch"
            )
        elif type(value) is LocalRecord:
            require(
                item == {"list": [to_item(value.first), to_item(value.second)]},
                "record provider/model mismatch",
            )
        return item

    def exact_node(node):
        if node is None:
            return {"class": "builtins.NoneType"}
        require(
            type(node) in (mpt.LeafNode, mpt.ExtensionNode, mpt.BranchNode),
            "exact pinned node class required",
        )
        if type(node) is mpt.LeafNode:
            require(
                type(node.rest_of_key) is bytes and all(v < 16 for v in node.rest_of_key),
                "invalid leaf nibble path",
            )
            return {
                "class": typename(node),
                "path": exact_tree(node.rest_of_key),
                "value": exact_tree(node.value),
            }
        if type(node) is mpt.ExtensionNode:
            require(
                type(node.key_segment) is bytes and all(v < 16 for v in node.key_segment),
                "invalid extension nibble path",
            )
            return {
                "class": typename(node),
                "path": exact_tree(node.key_segment),
                "subnode": exact_tree(node.subnode),
            }
        require(
            type(node.subnodes) is tuple and len(node.subnodes) == 16,
            "branch must have exact tuple of 16 children",
        )
        return {
            "class": typename(node),
            "children": exact_tree(node.subnodes),
            "value": exact_tree(node.value),
        }

    def assembled(node):
        exact_node(node)
        if node is None:
            return b""
        if type(node) is mpt.LeafNode:
            hp = mpt.nibble_list_to_compact(node.rest_of_key, True)
            require(type(hp) is bytes, "HP must be exact bytes")
            return (hp, node.value)
        if type(node) is mpt.ExtensionNode:
            hp = mpt.nibble_list_to_compact(node.key_segment, False)
            require(type(hp) is bytes, "HP must be exact bytes")
            return (hp, node.subnode)
        return list(node.subnodes) + [node.value]

    def identity_snapshot():
        driver.check_clean()
        driver.check_dependency()
        check_rlp()
        return {
            "commit": driver.head,
            "source_git_blobs": driver.oracle_blobs,
            "source_sha256": {
                name: digest((driver.eels / name).read_bytes()) for name in driver.oracle_blobs
            },
            "types_record": {
                "path": str(driver.dependency_record),
                "sha256": digest(driver.dependency_record.read_bytes()),
            },
            "types_sources": driver.dependency_sources(),
            "rlp_record": {
                "path": str(rlp_auth["record"]),
                "sha256": digest(rlp_auth["record"].read_bytes()),
            },
            "rlp_sources": {
                str(path): {"sha256_urlsafe": value, "size": size}
                for path, (value, size) in rlp_auth["hashes"].items()
            },
        }

    before = identity_snapshot()
    original_hash = mpt.keccak256
    observations, negatives = [], []

    def validate_result(result, structure, encoded):
        """Require the precise inline structure class or pinned digest class."""
        if len(encoded) < 32:
            require(type(result) is type(structure), "wrong exact inline result class")
            require(exact_tree(result) == exact_tree(structure), "inline structure mismatch")
        else:
            require(type(result) is Bytes32, "wrong exact digest result class")
            require(result == original_hash(encoded), "wrong concrete digest")
        return exact_tree(result)

    def probe(name, node, expected_size=None):
        input_tree = exact_node(node)
        structure = assembled(node)
        structure_tree = exact_tree(structure)
        encoded = rlp.encode(structure)
        require(type(encoded) is bytes, "RLP whole output must be exact bytes")
        if expected_size is not None:
            require(len(encoded) == expected_size, "wrong constructed threshold size")
        queries = []

        def recording(preimage):
            require(type(preimage) is bytes, "query preimage must be exact bytes")
            answer = original_hash(preimage)
            require(type(answer) is Bytes32, "query result must be exact pinned Bytes32")
            queries.append({"preimage": exact_tree(preimage), "answer": exact_tree(answer)})
            return answer

        try:
            mpt.keccak256 = recording
            result = mpt.encode_internal_node(node)
            result_tree = validate_result(result, structure, encoded)
        finally:
            mpt.keccak256 = original_hash
        require(exact_node(node) == input_tree, "node changed")
        require(exact_tree(structure) == structure_tree, "structure changed")
        require(len(queries) == (0 if len(encoded) < 32 else 1), "wrong query count")
        if len(encoded) < 32:
            require(result_tree == structure_tree, "inline structure mismatch")
        else:
            require(queries[0]["preimage"] == exact_tree(encoded), "wrong whole query preimage")
            require(result == original_hash(encoded), "wrong concrete digest")
        # Confirm the lossless byte/list adapter preserves complete source wire encoding.
        model = to_item(structure)

        def model_value(item):
            if "bytes" in item:
                return bytes.fromhex(item["bytes"])
            return [model_value(v) for v in item["list"]]

        require(
            rlp.encode(model_value(model)) == encoded, "Extended adapter changed source bytes"
        )
        observations.append(
            {
                "name": name,
                "input": input_tree,
                "assembled": structure_tree,
                "assembled_item": model,
                "encoded": exact_tree(encoded),
                "encoded_size": len(encoded),
                "result": result_tree,
                "result_item": to_item(result),
                "queries": queries,
                "node_unchanged": True,
                "oracle_restored": mpt.keccak256 is original_hash,
            }
        )

    probe("long-leaf-value", mpt.LeafNode(b"", bytes(range(256)) * 17))
    probe("long-extension-path", mpt.ExtensionNode(bytes(range(16)) * 257, b""))
    probe(
        "long-branch-middle-child",
        mpt.BranchNode(
            (b"",) * 7 + ([bytes(range(256)) * 17, [b"\x00", b"\xff"]],) + (b"",) * 8, b"end"
        ),
    )
    probe("none", None, 1)
    for path in (b"", b"\x00", b"\x0f", b"\x01\x02", b"\x01\x02\x03", bytes(range(16))):
        probe("leaf-path-" + path.hex(), mpt.LeafNode(path, b"v"))
        probe("extension-path-" + path.hex(), mpt.ExtensionNode(path, b"\x01"))
    probe(
        "leaf-nested-value", mpt.LeafNode(b"\x01\x02\x03", [b"", (b"\x80", [b"\x00", b"\x7f"])])
    )
    probe("extension-inline-child", mpt.ExtensionNode(b"\x0f", (b"\x20", b"v")))
    probe(
        "branch-distinct-ordered-children-value",
        mpt.BranchNode(tuple(bytes([v]) for v in range(16)), b"V"),
        18,
    )
    probe(
        "branch-sixteen-hash-children",
        mpt.BranchNode(tuple(Bytes32(bytes([v]) * 32) for v in range(16)), b""),
        532,
    )
    probe("branch-all-empty", mpt.BranchNode((b"",) * 16, b""), 18)
    probe(
        "branch-heterogeneous-inline",
        mpt.BranchNode(
            (b"", (b"\x20", b"v"), [b"\x31", [b"", b"\xff"]])
            + tuple(bytes([v]) for v in range(3, 16)),
            [b"end", b"value"],
        ),
    )
    probe("extension-hash-child", mpt.ExtensionNode(b"\x0f\x00", Bytes32(bytes(range(32)))))
    for length in (31, 32, 33):
        probe(
            "leaf-whole-rlp-" + str(length), mpt.LeafNode(b"", b"\xab" * (length - 3)), length
        )
        probe(
            "extension-whole-rlp-" + str(length),
            mpt.ExtensionNode(b"", b"\xab" * (length - 3)),
            length,
        )
        probe(
            "branch-whole-rlp-" + str(length),
            mpt.BranchNode((b"",) * 16, b"\xab" * (length - 18)),
            length,
        )
        probe(
            "branch-child7-whole-rlp-" + str(length),
            mpt.BranchNode((b"",) * 7 + (b"\xab" * (length - 18),) + (b"",) * 8, b""),
            length,
        )
        probe(
            "leaf-nested-list-whole-rlp-" + str(length),
            mpt.LeafNode(b"", [b"\x01"] * (length - 3)),
            length,
        )
        for parity in (0, 1):
            path = b"\x0f" * (2 * (length - 4) + parity)
            probe(
                "leaf-path-only-parity" + str(parity) + "-whole-rlp-" + str(length),
                mpt.LeafNode(path, b""),
                length,
            )
            probe(
                "extension-path-only-parity" + str(parity) + "-whole-rlp-" + str(length),
                mpt.ExtensionNode(path, b""),
                length,
            )
    for name, value in [
        ("bytearray", bytearray(b"\x00\x80")),
        ("Uint-zero", Uint(0)),
        ("Uint-128", Uint(128)),
        ("U256", U256(256)),
        ("str-utf8", "λ"),
        ("true", True),
        ("false", False),
        ("dataclass", LocalRecord(b"x", Uint(7))),
        ("list-empty", []),
        ("tuple-empty", ()),
    ]:
        probe("Extended-field-" + name, mpt.LeafNode(b"", value))

    # `encode_node` (EthCommit C10) is observed to establish the caller boundary.
    encode_node_observations = []
    for name, value, expected_class in [
        ("raw-bytes", b"x", bytes),
        ("empty-bytes", b"", bytes),
        ("hash32-bytes", Bytes32(bytes(range(32))), Bytes32),
        ("Uint-zero", Uint(0), bytes),
        ("nested-list", [b"x"], bytes),
        ("false", False, bytes),
        ("singleton-bytearray", bytearray(b"\x01"), bytearray),
    ]:
        input_tree = exact_tree(value)
        result = mpt.encode_node(value)
        require(type(result) is expected_class, "wrong exact encode_node result class")
        encode_node_observations.append(
            {
                "name": name,
                "input": input_tree,
                "result": exact_tree(result),
                "result_is_input": result is value,
            }
        )

    def expect_failure(name, action, expected):
        try:
            action()
        except BaseException as failure:
            require(type(failure) is expected, "wrong exact failure class for " + name)
            negatives.append(
                {
                    "name": name,
                    "class": typename(failure),
                    "message": str(failure),
                    "exit_code": failure.code if type(failure) is SystemExit else None,
                }
            )
        else:
            raise AssertionError("negative control accepted: " + name)

    class BytesSubclass(bytes):
        pass

    class FakeLeaf:
        rest_of_key = b""
        value = b"v"

    expect_failure(
        "exact-bytes-before-normalization", lambda: exact_tree(BytesSubclass(b"x")), TypeError
    )
    expect_failure("int-is-not-Uint", lambda: exact_tree(0), TypeError)
    expect_failure(
        "duck-leaf-is-not-pinned-class", lambda: exact_node(FakeLeaf()), AssertionError
    )
    expect_failure(
        "15-child-model-rejected",
        lambda: exact_node(mpt.BranchNode((b"",) * 15, b"")),
        AssertionError,
    )
    inline_node = mpt.LeafNode(b"", b"v")
    inline_structure = assembled(inline_node)
    inline_encoding = rlp.encode(inline_structure)
    inline_result = mpt.encode_internal_node(inline_node)
    validate_result(inline_result, inline_structure, inline_encoding)
    expect_failure(
        "result-tuple-required-not-list",
        lambda: validate_result(list(inline_result), inline_structure, inline_encoding),
        AssertionError,
    )
    wrong_inline = (inline_result[0], b"changed")
    expect_failure(
        "changed-inline-field-rejected",
        lambda: validate_result(wrong_inline, inline_structure, inline_encoding),
        AssertionError,
    )
    hash_node = mpt.LeafNode(b"", b"\xab" * 29)
    hash_structure = assembled(hash_node)
    hash_encoding = rlp.encode(hash_structure)
    hash_result = mpt.encode_internal_node(hash_node)
    validate_result(hash_result, hash_structure, hash_encoding)
    expect_failure(
        "digest-bytes-required-to-be-Bytes32",
        lambda: validate_result(bytes(hash_result), hash_structure, hash_encoding),
        AssertionError,
    )
    wrong_digest = Bytes32(bytes([hash_result[0] ^ 1]) + hash_result[1:])
    expect_failure(
        "changed-digest-byte-rejected",
        lambda: validate_result(wrong_digest, hash_structure, hash_encoding),
        AssertionError,
    )
    expect_failure(
        "encode_node-None-fails-in-RLP", lambda: mpt.encode_node(None), EncodingError
    )
    account = mpt.Account(Uint(0), U256(0), Bytes32(b"\x00" * 32))
    require(
        type(account) is mpt.Account
        and type(account.nonce) is Uint
        and type(account.balance) is U256
        and type(account.code_hash) is Bytes32,
        "wrong exact account class/fields",
    )
    expect_failure(
        "encode_node-account-needs-storage-root",
        lambda: mpt.encode_node(account),
        AssertionError,
    )

    for name, node in [
        ("actual-unsupported-leaf-int", mpt.LeafNode(b"", 0)),
        ("actual-unsupported-leaf-None", mpt.LeafNode(b"", None)),
        ("actual-unsupported-extension-child", mpt.ExtensionNode(b"\x01", object())),
        ("actual-unsupported-branch-value", mpt.BranchNode((b"",) * 16, 0)),
        ("actual-unknown-node", object()),
    ]:
        query_preimages = []

        def failure_recording(preimage):
            require(type(preimage) is bytes, "wrong failure query preimage class")
            query_preimages.append(preimage.hex())
            return original_hash(preimage)

        try:
            mpt.keccak256 = failure_recording
            expect_failure(
                name,
                lambda: mpt.encode_internal_node(node),
                AssertionError if name == "actual-unknown-node" else EncodingError,
            )
            require(query_preimages == [], "failing RLP performed a query")
            negatives[-1]["query_preimages"] = query_preimages
        finally:
            mpt.keccak256 = original_hash

    # This is a runtime-annotation observation, excluded from the exact 16-child API probes.
    bad_branch = mpt.BranchNode((b"",) * 15, b"V")
    bad_branch_result = mpt.encode_internal_node(bad_branch)
    require(
        type(bad_branch_result) is list and len(bad_branch_result) == 16,
        "unexpected source branch arity guard",
    )
    negatives.append(
        {
            "name": "actual-source-does-not-check-branch-arity",
            "result": exact_tree(bad_branch_result),
            "encoded_hex": rlp.encode(bad_branch_result).hex(),
            "query_count": 0,
        }
    )

    # Injected query errors are instrumentation effects, not native EELS protocol faults.
    class QueryFailure(Exception):
        pass

    failure_calls = []

    def failing_hash(preimage):
        require(type(preimage) is bytes, "query-failure preimage wrong class")
        failure_calls.append(preimage.hex())
        raise QueryFailure("deliberate query instrumentation failure")

    try:
        mpt.keccak256 = failing_hash
        expect_failure(
            "instrumented-query-failure-propagates",
            lambda: mpt.encode_internal_node(mpt.LeafNode(b"", b"\xab" * 29)),
            QueryFailure,
        )
        require(len(failure_calls) == 1, "query failure must happen once")
        negatives[-1]["query_preimages"] = failure_calls
    finally:
        mpt.keccak256 = original_hash

    arbitrary_answer = Bytes32(b"\xa5" * 32)
    arbitrary_calls = []

    def arbitrary_hash(preimage):
        require(type(preimage) is bytes, "arbitrary-answer preimage wrong class")
        arbitrary_calls.append(preimage.hex())
        return arbitrary_answer

    try:
        mpt.keccak256 = arbitrary_hash
        arbitrary_result = mpt.encode_internal_node(mpt.LeafNode(b"", b"\xab" * 29))
        require(
            type(arbitrary_result) is Bytes32
            and arbitrary_result is arbitrary_answer
            and len(arbitrary_calls) == 1,
            "query answer not retained",
        )
        negatives.append(
            {
                "name": "instrumented-arbitrary-answer-retained",
                "result": exact_tree(arbitrary_result),
                "query_preimages": arbitrary_calls,
                "answer_identity_retained": True,
            }
        )
        mpt.keccak256 = failing_hash
        require(
            type(mpt.encode_internal_node(None)) is bytes
            and mpt.encode_internal_node(None) == b"",
            "None queried failing oracle",
        )
        require(len(failure_calls) == 1, "None unexpectedly queried oracle")
        negatives.append(
            {
                "name": "None-bypasses-instrumented-failing-oracle",
                "result": exact_tree(b""),
                "query_count": 0,
            }
        )
    finally:
        mpt.keccak256 = original_hash

    for name, fullname, path, loader_class in [
        (
            "changed-pin-source-import-rejected",
            "ethereum.merkle_patricia_trie",
            Path(mpt.__file__),
            shared.FreshSourceLoader,
        ),
        (
            "changed-types-import-rejected",
            "ethereum_types.bytes",
            driver.dependency_package / "bytes.py",
            shared.FreshSourceLoader,
        ),
        (
            "changed-rlp-import-rejected",
            "ethereum_rlp.rlp",
            Path(rlp.__file__),
            AuthenticatedRlpLoader,
        ),
    ]:
        loader = loader_class(fullname, str(path), driver)
        original_bytes = path.read_bytes()
        loader.get_data = (
            lambda source, data=original_bytes: data
            + b"\n# deliberate private in-memory negative control\n"
        )
        expect_failure(
            name,
            lambda: loader.get_code(fullname),
            AssertionError if loader_class is AuthenticatedRlpLoader else ImportError,
        )

    original_lock = (driver.eels / "uv.lock").read_bytes()
    modified_lock_blob = (
        driver.git(
            "hash-object",
            "--stdin",
            "--no-filters",
            input=original_lock + b"\n# deliberate in-memory negative control\n",
        )
        .decode()
        .strip()
    )
    require(
        modified_lock_blob != driver.oracle_blobs["uv.lock"],
        "changed lock bytes had unchanged git identity",
    )
    original_git = driver.git

    def changed_lock_observation(*args, **kwargs):
        observed = original_git(*args, **kwargs)
        if args[:3] == ("hash-object", "--no-filters", "--"):
            paths = args[3:]
            hashes = observed.splitlines()
            hashes[paths.index("uv.lock")] = modified_lock_blob
            return "\n".join(hashes) + "\n"
        return observed

    try:
        # Inject changed observed bytes into the real checker, without editing EELS.
        driver.git = changed_lock_observation
        expect_failure(
            "changed-lock-bytes-fail-pin-hash-comparison", driver.check_clean, SystemExit
        )
        require(negatives[-1]["exit_code"] == 2, "wrong authentication failure exit")
        negatives[-1].update(
            expected=driver.oracle_blobs["uv.lock"], modified=modified_lock_blob, accepted=False
        )
    finally:
        driver.git = original_git

    rlp_source = Path(rlp.__file__)
    record_entry = rlp_auth["hashes"][rlp_source]
    try:
        rlp_auth["hashes"][rlp_source] = ("A" * 43, record_entry[1])
        expect_failure("wrong-rlp-RECORD-hash-rejected", check_rlp, AssertionError)
    finally:
        rlp_auth["hashes"][rlp_source] = record_entry

    require(mpt.keccak256 is original_hash, "oracle not restored")
    after = identity_snapshot()
    require(before == after, "authenticated source/lock/dependency identities changed")
    result = {
        "status": "bounded observations; no universal theorem",
        "probe_count": len(observations),
        "negative_control_count": len(negatives),
        "python": sys.version,
        "python_executable": sys.executable,
        "sys_prefix": sys.prefix,
        "isolated": bool(sys.flags.isolated),
        "dont_write_bytecode": sys.dont_write_bytecode,
        "recursion_limit_observed_without_modification": sys.getrecursionlimit(),
        "platform": platform.platform(),
        "seed": driver.seed,
        "case_generation": "fixed deterministic inputs; seed is unused",
        "rlp_version": rlp_auth["version"],
        "types_version": driver.version,
        "pycryptodome_version": importlib.metadata.version("pycryptodome"),
        "keccak_backend": "hashlib" if hash_module._USE_HASHLIB else "pycryptodome",
        "driver_sha256": digest((ROOT / "scripts/differential.py").read_bytes()),
        "probe_sha256": digest(Path(__file__).read_bytes()),
        "reference_toml_sha256": digest((ROOT / "reference.toml").read_bytes()),
        "before": before,
        "after": after,
        "identities_equal": before == after,
        "observations": observations,
        "encode_node_observations": encode_node_observations,
        "negative_controls": negatives,
    }
    result["argv"] = sys.argv
    result["cwd"] = str(Path.cwd())
    result["recursion_limit_manual_changes"] = False
    result["script_sha256"] = digest(Path(__file__).read_bytes())

    def lean_item(item):
        if "bytes" in item:
            return '.bytes (raw "0x' + item["bytes"] + '")'
        return ".list [" + ", ".join(lean_item(v) for v in item["list"]) + "]"

    def lean_node(node):
        name = node["class"]
        if name == "builtins.NoneType":
            return "none"
        if name == "ethereum.merkle_patricia_trie.BranchNode":
            children = ", ".join(lean_item(model_field(v)) for v in node["children"]["items"])
            return (
                "some (.branch ⟨#["
                + children
                + "], by decide⟩ ("
                + lean_item(model_field(node["value"]))
                + "))"
            )
        field = node["value"] if name.endswith("LeafNode") else node["subnode"]
        tag = "leaf" if name.endswith("LeafNode") else "extension"
        return (
            "some (."
            + tag
            + ' (pathHex "0x'
            + node["path"]["hex"]
            + '") ('
            + lean_item(model_field(field))
            + "))"
        )

    lines = [
        "-- Generated actual authenticated source comparisons; do not commit.",
        "import STFSpec.Conformance.Commit.InternalNodeGuards",
        "import STFSpec.Conformance.Commit.InternalNodeCallerProofs",
        "import STFSpec.Conformance.Fixtures.Hex",
        "open STFSpec.Base STFSpec.Codec STFSpec.Commit STFSpec.Hash",
        "open STFSpec.Conformance.Commit.InternalNodeGuards",
        "private def raw (text : String) : ByteArray :=",
        '  (STFSpec.Conformance.Internal.decodeHex "node differential" text).toOption.getD',
        "    ByteArray.empty",
        "private def pathHex (text : String) : Nibbles :=",
        "  Nibbles.ofList ((raw text).data.toList.map (fun b ↦ ⟨b.toNat % 16, by omega⟩))",
    ]
    for i, case in enumerate(observations):
        wire = 'raw "0x' + case["encoded"]["hex"] + '"'
        expected = lean_item(case["result_item"])
        assembly = lean_item(case["assembled_item"])
        hashed = case["encoded_size"] >= 32
        recorded = ".bytes testAnswer.toBytes.toByteArray" if hashed else assembly
        trace = "[" + wire + "]" if hashed else "[]"
        failure = (
            '(match error with | .error e => e == "original oracle failure" | .ok _ => false)'
            if hashed
            else "(match error with | .ok item => sameItem item ("
            + assembly
            + ") | .error _ => false)"
        )
        lines += [
            f"def case{i} (_ : Unit) : Bool :=",
            "  let node : Option InternalNode := " + lean_node(case["input"]),
            "  let (actual, queries) := observe node",
            "  let (error, errorQueries) := observeFailure node",
            "  sameItem (assembleInternalNode node) (" + assembly + ") &&",
            "  decide (Rlp.encode (assembleInternalNode node) = " + wire + ") &&",
            "  sameItem (encodeInternalNode (m := Id) node) (" + expected + ") &&",
            "  sameItem actual (" + recorded + ") && queries == " + trace + " &&",
            "  " + failure + " && errorQueries == " + trace,
            f"#guard case{i} ()",
        ]
    driver.output.write_text("\n".join(lines) + "\n")
    command = [
        "lake",
        "env",
        "lean",
        "--root=" + str(driver.output.parent),
        "-DwarningAsError=true",
        "-o",
        str(driver.output.with_suffix(".olean")),
        str(driver.output),
    ]
    compiled = subprocess.run(command, cwd=driver.root)
    result["lean_command"] = command
    result["lean_exit"] = compiled.returncode
    result["emitted_comparisons"] = len(observations)
    result["emitted_sha256"] = digest(driver.output.read_bytes())
    # Recheck provenance after Lean compilation as well as after source instrumentation.
    require(identity_snapshot() == before, "source identity changed during Lean execution")
    driver.output.with_suffix(".json").write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n"
    )
    print(
        json.dumps(
            {
                key: result[key]
                for key in (
                    "probe_count",
                    "negative_control_count",
                    "identities_equal",
                    "keccak_backend",
                    "rlp_version",
                    "types_version",
                    "isolated",
                )
            },
            sort_keys=True,
        )
    )

    return compiled.returncode


if __name__ == "__main__":
    raise SystemExit(main())
