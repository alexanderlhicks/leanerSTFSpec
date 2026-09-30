#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Compare primitive records and four concrete constants with the pinned EELS.

Run with the pinned EELS checkout at /tmp/eels:
  /tmp/eels/.venv/bin/python -I STFSpec/Conformance/Base/value_records_differential.py \
    --eels /tmp/eels --output /tmp/value-records-differential.lean
Sources: ethereum/state.py:36, merkle_patricia_trie.py:71, amsterdam/fork.py:116,
amsterdam/vm/__init__.py:40, and amsterdam/fork_types.py:45,58,62,87.
Generated observations are uncommitted evidence, not normative fixtures.
Spec guidance: STFSpec/informal/modules/EthBase.md §§3–4.
"""

import ast
import dataclasses
import hashlib
import importlib.metadata
from pathlib import Path
import random
import sys
import tomllib

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "scripts"))
from differential import setup_driver


def main():
    context = setup_driver(__doc__, __file__, 5004)
    pin = tomllib.loads((context.root / "reference.toml").read_text())["release"]
    versions = {}
    for name in ("ethereum-types", "ethereum-rlp", "pycryptodome"):
        versions[name] = importlib.metadata.version(name)
        if versions[name] != pin["python_dependencies"][name]:
            context.parser.error(f"dependency version differs from reference.toml: {name}")
    from ethereum import merkle_patricia_trie, state
    from ethereum.crypto import hash as hash_module
    from ethereum.forks.amsterdam import fork, fork_types, vm
    from ethereum_types import bytes as bytes_module, numeric

    sources = {}
    for module in (merkle_patricia_trie, state, hash_module, fork, fork_types, vm):
        relative = Path(module.__file__).resolve().relative_to(context.eels / "src").as_posix()
        path = context.check_source(module, relative)
        relative = path.relative_to(context.eels).as_posix()
        sources[relative] = hashlib.sha256(path.read_bytes()).hexdigest()
    dependencies = {}
    for module in (bytes_module, numeric):
        relative = f"ethereum_types/{module.__name__.rsplit('.', 1)[1]}.py"
        path = context.check_source(module, relative, dependency=True)
        dependencies[str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()
    tree = ast.parse(Path(fork_types.__file__).read_bytes())
    classes = {node.name: node for node in tree.body if isinstance(node, ast.ClassDef)}
    expected_fields = {
        "Authorization": [("chain_id", "U256"), ("address", "Address"), ("nonce", "U64"),
                          ("y_parity", "U8"), ("r", "U256"), ("s", "U256")],
        "StateGasPerByte": [("rate", "Uint")],
    }
    for name, expected in expected_fields.items():
        fields = [(node.target.id, ast.unparse(node.annotation))
                  for node in classes[name].body if isinstance(node, ast.AnnAssign)]
        actual = [field.name for field in dataclasses.fields(getattr(fork_types, name))]
        if fields != expected or actual != [field for field, _ in expected]:
            context.parser.error(f"pinned field names/order/types changed: {name}")

    guards = ["import STFSpec.Base", "open STFSpec.Base"]
    vectors = {}
    for name, value in (("emptyCodeHash", state.EMPTY_CODE_HASH),
                        ("emptyTrieRoot", merkle_patricia_trie.EMPTY_TRIE_ROOT),
                        ("emptyOmmerHash", fork.EMPTY_OMMER_HASH),
                        ("transferTopic", vm.TRANSFER_TOPIC)):
        if len(value) != 32:
            context.parser.error(f"wrong source constant width: {name}")
        vectors[name] = value.hex()
        data = ", ".join(str(byte) for byte in value)
        guards.append(f"#guard HashConsts.literals.{name}.toBytes = "
                      f"(Bytes.ofList ([{data}] : List UInt8))")
        guards.append(f"#guard HashConsts.literals.{name}.toNat = {int.from_bytes(value, 'big')}")

    rng = random.Random(context.seed)
    bounds = [0, 1, 2, 2**64 - 1, 2**64, 2**256 - 1, 2**256, 2**4096 + 17]
    pairs = [(rate, count) for rate in bounds for count in bounds]
    pairs += [(rng.getrandbits(rng.choice([8, 64, 256, 512])),
               rng.getrandbits(rng.choice([8, 64, 256, 512]))) for _ in range(64)]
    for rate, count in pairs:
        g, n = fork_types.StateGasPerByte(numeric.Uint(rate)), numeric.Uint(count)
        forward, reverse = int(g * n), int(n * g)
        guards.append(f"#guard (StateGasPerByte.mk {int(g.rate)}).charge {int(n)} = {forward}")
        guards.append(f"#guard (StateGasPerByte.mk {int(g.rate)}).charge {int(n)} = {reverse}")
    # Source objects are constructed and observed directly. Boundary tuples vary all six fields.
    cases = [(0, bytes(20), 0, 0, 0, 1),
             (2**256 - 1, bytes([255]) * 20, 2**64 - 1, 255, 1, 2**256 - 1),
             (1, bytes(range(20)), 2**63, 1, 2**255, 2**255 - 1)]
    cases += [(rng.getrandbits(256), bytes(rng.getrandbits(8) for _ in range(20)),
               rng.getrandbits(64), rng.getrandbits(8), rng.getrandbits(256),
               rng.getrandbits(256)) for _ in range(32)]
    for chain, address, nonce, parity, r, s in cases:
        a = fork_types.Authorization(numeric.U256(chain), state.Address(address),
                                    numeric.U64(nonce), numeric.U8(parity),
                                    numeric.U256(r), numeric.U256(s))
        data = ", ".join(str(byte) for byte in a.address)
        byte_expr = f"(Bytes.ofList ([{data}] : List UInt8))"
        # Every emitted observation is one guard; local bindings add no declaration rows.
        record = (f"let address : Address := (Address.ofBytes? {byte_expr}).get (by decide); "
                  f"let auth : Authorization := "
                  f"⟨U256.ofNat {int(a.chain_id)}, address, U64.ofNat {int(a.nonce)}, "
                  f"U8.ofNat {int(a.y_parity)}, U256.ofNat {int(a.r)}, U256.ofNat {int(a.s)}⟩; ")
        for lean_name, source_name in (("chainId", "chain_id"), ("nonce", "nonce"),
                                      ("yParity", "y_parity"), ("r", "r"), ("s", "s")):
            value = int(getattr(a, source_name))
            guards.append(f"#guard {record}auth.{lean_name}.toNat = {value}")
        guards.append(f"#guard {record}auth.address.toBytes = {byte_expr}")
    return context.run(guards, versions=versions, sources=sources, dependencies=dependencies,
                       fields=expected_fields, vectors=vectors, charge_pairs=len(pairs),
                       authorization_cases=len(cases), oracle_sources=context.oracle_blobs,
                       dependency_sources=context.dependency_sources(),
                       dependency_record=str(context.dependency_record))


if __name__ == "__main__":
    raise SystemExit(main())
