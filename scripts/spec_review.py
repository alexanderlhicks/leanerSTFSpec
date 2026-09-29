#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Small, reproducible counterexamples for the informal-spec review.

Run with the Python interpreter from an EELS `uv sync --frozen --no-dev`
environment, passing that checkout. This is review evidence, not conformance.
"""
import argparse
import importlib.metadata
import json
import pathlib
import platform
import ssl
import subprocess
import sys
import tomllib


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("eels", type=pathlib.Path)
    args = parser.parse_args()
    root = pathlib.Path(__file__).resolve().parents[1]  # scripts/ -> repository root
    release = tomllib.loads((root / "reference.toml").read_text())["release"]
    commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=args.eels, text=True).strip()
    if commit != release["commit"]:
        parser.error("checkout does not match the pinned reference (reference.toml)")
    if subprocess.check_output(["git", "status", "--porcelain", "--", "src", "uv.lock"], cwd=args.eels):
        parser.error("pinned source or lock has local changes")
    versions = {name: importlib.metadata.version(name) for name in release["python_dependencies"]}
    if versions != release["python_dependencies"]:
        parser.error("installed dependencies do not match the pinned reference (reference.toml)")
    sys.path.insert(0, str(args.eels / "src"))

    from ethereum_rlp import rlp
    from ethereum_types.bytes import Bytes, Bytes32
    from ethereum_types.numeric import U256, Uint
    from ethereum.crypto.hash import keccak256
    from ethereum.forks.amsterdam.execution_engine.requests import (
        decode_execution_requests, encode_execution_requests,
    )
    from ethereum.forks.amsterdam.incremental_mpt import (
        HashedNode, IncrementalMPT, MutableBranchNode, MutableLeafNode,
        decode_witness_to_mpt, mpt_root, mpt_set,
    )
    from ethereum.forks.amsterdam.witness_state import WitnessState, _decode_account_from_leaf
    from ethereum.merkle_patricia_trie import (
        EMPTY_TRIE_ROOT, bytes_to_nibble_list, encode_account, nibble_list_to_compact,
    )
    from ethereum.state import Account, Address, BlockDiff, EMPTY_CODE_HASH
    from py_ecc.bls.hash_to_curve import clear_cofactor_G1, map_to_curve_G1
    from py_ecc.optimized_bls12_381 import FQ, normalize

    once = clear_cofactor_G1(map_to_curve_G1(FQ(0)))
    twice = clear_cofactor_G1(once)
    assert normalize(once) != normalize(twice)

    requests = decode_execution_requests((Bytes(b"\x00"),))
    assert encode_execution_requests(requests) == ()

    def partial():
        branch = MutableBranchNode(children=[None] * 16, value=Bytes(b""))
        branch.children[0] = MutableLeafNode(rest_of_key=Bytes(b"\x01"), value=Bytes(b"old"))
        branch.children[1] = HashedNode(_hash=keccak256(b"unavailable sibling"))
        return IncrementalMPT(secured=False, default=Bytes(b""), root_node=branch,
                              _data={Bytes(b"\x01"): Bytes(b"old")})

    failed = False
    try:
        mpt_set(partial(), Bytes(b"\x01"), Bytes(b""))
    except AssertionError:
        failed = True
    assert failed
    inserted = partial()
    mpt_set(inserted, Bytes(b"\x02"), Bytes(b"new"))
    mpt_set(inserted, Bytes(b"\x01"), Bytes(b""))
    mpt_root(inserted)

    raw = Bytes(rlp.encode((Bytes(b"\xf1\x23"), Bytes(b"a" * 40))))
    root_hash = keccak256(raw)
    trie = decode_witness_to_mpt({root_hash: raw}, root_hash, secured=False, default=Bytes(b""))
    assert mpt_root(trie) == root_hash
    mpt_set(trie, Bytes(b"\xff"), Bytes(b""))
    assert mpt_root(trie) != root_hash

    address = Address(b"\x11" * 20)
    account = Account(nonce=Uint(1), balance=U256(2), code_hash=EMPTY_CODE_HASH)
    storage_root = keccak256(b"nonempty storage commitment")
    account_leaf = encode_account(account, storage_root)
    path = nibble_list_to_compact(bytes_to_nibble_list(keccak256(address)), True)
    raw_account = Bytes(rlp.encode((path, account_leaf)))
    parent_root = keccak256(raw_account)
    def backend():
        return WitnessState(_node_db={parent_root: raw_account}, _code_db={}, _state_root=parent_root)
    diff = BlockDiff(account_changes={address: account})
    without_read = backend().compute_state_root(diff)
    with_read = backend()
    assert with_read.get_account_optional(address) == account
    assert with_read.compute_state_root(diff) != without_read

    # SC5/SC6 preserve the source decoder's broader leaf domain (O4(e)).
    empty_account = Account(nonce=Uint(0), balance=U256(0), code_hash=EMPTY_CODE_HASH)
    for fields in ((b"", b"", b"", b""), ([], [], [], [])):
        assert _decode_account_from_leaf(Bytes(rlp.encode(fields))) == (empty_account, EMPTY_TRIE_ROOT)
    leading_zero = (b"\x00\x01", b"\x00" * 33 + b"\x02", b"", b"")
    assert _decode_account_from_leaf(Bytes(rlp.encode(leading_zero))) == (account, EMPTY_TRIE_ROOT)
    for fields in ((b"", b"", b""), (b"", b"\x01" + b"\x00" * 32, b"", b""),
                   (b"", b"", b"x", b""), ([b"x"], b"", b"", b"")):
        try:
            _decode_account_from_leaf(Bytes(rlp.encode(fields)))
        except (AssertionError, ValueError, TypeError, OverflowError):
            pass
        else:
            raise AssertionError("malformed account leaf unexpectedly accepted")
    slot = Bytes32(b"\x22" * 32)
    slot_path = nibble_list_to_compact(bytes_to_nibble_list(keccak256(slot)), True)
    storage_node = Bytes(rlp.encode((slot_path, Bytes(rlp.encode([b"x"])))))
    storage_root = keccak256(storage_node)
    raw_account = Bytes(rlp.encode((path, encode_account(account, storage_root))))
    parent_root = keccak256(raw_account)
    state = WitnessState(_node_db={parent_root: raw_account, storage_root: storage_node},
                         _code_db={}, _state_root=parent_root)
    assert state.get_storage(address, slot) == U256(0)

    # Lookup-path availability cannot imply progress when decoding is eager.
    valid_leaf = Bytes(rlp.encode((nibble_list_to_compact(Bytes(b"\x01"), True), b"a" * 40)))
    malformed_sibling = Bytes(rlp.encode([b"x"]))
    children = [b""] * 17
    children[0], children[1] = keccak256(valid_leaf), keccak256(malformed_sibling)
    branch = Bytes(rlp.encode(children))
    branch_hash = keccak256(branch)
    nodes = {branch_hash: branch, keccak256(valid_leaf): valid_leaf,
             keccak256(malformed_sibling): malformed_sibling}
    try:
        decode_witness_to_mpt(nodes, branch_hash, secured=False, default=Bytes(b""))
    except AssertionError:
        pass
    else:
        raise AssertionError("malformed available off-path node was not eagerly rejected")

    print(json.dumps({
        "commit": commit, "python": platform.python_version(), "openssl": ssl.OPENSSL_VERSION,
        "dependencies": versions,
        "checks": {
            "double_cofactor_changes_output": True,
            "request_type_only_blob_is_normalized_away": True,
            "insert_before_delete_avoids_stub_collapse": True,
            "noncanonical_noop_delete_changes_root": True,
            "account_root_update_depends_on_prior_lookup": True,
            "account_leaf_defaults_leading_zeros_and_rejections": True,
            "storage_leaf_rlp_list_defaults_to_zero": True,
            "eager_decode_rejects_malformed_available_off_path_node": True,
        },
    }, indent=2))


if __name__ == "__main__":
    main()
