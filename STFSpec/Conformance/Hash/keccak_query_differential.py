#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Compare concrete query acquisition with the four actual authenticated EELS globals.

Run with EELS/.venv/bin/python -I -B, --eels EELS --output EXTERNAL.lean.
Reads state.py:36, merkle_patricia_trie.py:71, amsterdam/fork.py:116 and
amsterdam/vm/__init__.py:40 at reference.toml's pin; checks crypto/hash.py and
frozen dependency versions. This finite observation does not establish generic
oracle coupling, F20 entry points, EEST guest behavior or cryptographic security.
Spec guidance: STFSpec/informal/modules/EthHash.md §§3–4, 7.
"""

import hashlib
import importlib.metadata
from pathlib import Path
import sys
import tomllib

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "scripts"))
from differential import setup_driver


def array(value):
    return "⟨#[" + ", ".join(f"0x{x:02x}" for x in value) + "]⟩"


def main():
    context = setup_driver(__doc__, __file__, 19004)
    pin = tomllib.loads((context.root / "reference.toml").read_text())["release"]
    versions = {}
    for name in ("ethereum-types", "ethereum-rlp", "pycryptodome"):
        versions[name] = importlib.metadata.version(name)
        if versions[name] != pin["python_dependencies"][name]:
            context.parser.error(f"dependency version differs from reference.toml: {name}")
    from ethereum import merkle_patricia_trie, state
    from ethereum.crypto import hash as hash_module
    from ethereum.forks.amsterdam import fork, vm

    sources = {}
    for module in (merkle_patricia_trie, state, hash_module, fork, vm):
        relative = Path(module.__file__).resolve().relative_to(context.eels / "src").as_posix()
        path = context.check_source(module, relative)
        sources[path.relative_to(context.eels).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    constants = [
        ("emptyCodeHash", bytes(state.EMPTY_CODE_HASH), b""),
        ("emptyTrieRoot", bytes(merkle_patricia_trie.EMPTY_TRIE_ROOT), b"\x80"),
        ("emptyOmmerHash", bytes(fork.EMPTY_OMMER_HASH), b"\xc0"),
        ("transferTopic", bytes(vm.TRANSFER_TOPIC), b"Transfer(address,address,uint256)"),
    ]
    guards = ["import STFSpec.Hash", "open STFSpec.Hash STFSpec.Base"]
    vectors = {}
    for field, value, preimage in constants:
        if len(value) != 32 or bytes(hash_module.keccak256(preimage)) != value:
            context.parser.error(f"pinned constant/preimage differs: {field}")
        vectors[field] = {"preimage": preimage.hex(), "digest": value.hex()}
        guards.append(f"#guard (HashConsts.query (m := Id)).{field}.toBytes.toByteArray = {array(value)}")
        guards.append(f"#guard HashConsts.literals.{field}.toBytes.toByteArray = {array(value)}")
        guards.append(f"#guard (KeccakQuery.keccak (m := Id) {array(preimage)}).toBytes.toByteArray = {array(value)}")
    return context.run(guards, versions=versions, sources=sources, vectors=vectors,
        backend="hashlib" if hash_module._USE_HASHLIB else "pycryptodome",
        oracle_sources=context.oracle_blobs, dependency_sources=context.dependency_sources(),
        dependency_record=str(context.dependency_record), constants=len(constants),
        limitations="finite concrete values; no generic coupling, F20 entries, EEST or security claim")


if __name__ == "__main__":
    raise SystemExit(main())
