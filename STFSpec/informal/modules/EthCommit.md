# `EthCommit`: Merkle Patricia tries over bytes — mathematical root, witness decoding, partial trie, incremental root

*Status: informal specification, draft. Date: 2026-10-01. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F4, F5, F16, F19, F20 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D4, D5, D16, D18, D19, D20, D25 · questions: B3 (Q32/Q34), B15 (Q33/Q35), Q48, Q49, Q50, Q51; DISC-001, DISC-003, DISC-004.*

Abbreviations: `mpt:` = `merkle_patricia_trie.py`, `inc:` = `forks/amsterdam/incremental_mpt.py`, `ws:` = `forks/amsterdam/witness_state.py`. "[verified]" = read in the pinned source; "[executed]" = additionally run against the pinned EELS with `ethereum_rlp`/`ethereum_types` from the pinned environment; "[inference]" = argued, not tested.

## 1. Purpose

`EthCommit` is the commitment layer (ARCHITECTURE §2, L1). It defines the hexary Merkle Patricia trie **generic over encoded keys and values** (`ByteArray → ByteArray` maps): nibbles and hex-prefix encoding, node types and their encoding, the mathematical root (`patricialize`), a typed trie-with-default used by `EthBlock` for transaction/receipt/withdrawal roots, the read-only node database, **eager** witness decoding (D19), the partial trie with hashed stubs, lookup/update/delete, and the incremental root. It knows nothing about accounts (D16, D20): account and storage encodings and the state root are in `EthStateCommit`.

## 2. Requirements

### 2.1 Nibbles and hex-prefix

- C1. `bytesToNibbleList` splits each byte into high then low nibble (`mpt:395–404`).
- C2. `nibbleListToCompact x isLeaf` (`mpt:360–392`): flag nibble `2·isLeaf + parity`; even length → `[16·flag]` followed by nibble pairs; odd → first byte `16·(flag) + x[0]`, then pairs. Precondition: every element `< 16` (EELS does not check; the Lean type carries it).
- C3. `compactToNibbles` (`inc:859–889`) is the decoder used on witness data, and is **lenient** [executed]: it reads `isLeaf` from bit 1 and parity from bit 0 of the first nibble and **ignores bits 2–3**; for even parity it **ignores the low nibble** of the first byte; it raises `IndexError` on an empty input. So `0xf1 0x23` decodes to leaf path `[1,2,3]`, and `0x0f` to an empty extension path (which C14 then rejects). The Lean decoder must return exactly these results and fail exactly with `.malformed .compactEmpty` only on raw empty input (Q48). The later empty decoded extension path still belongs to `.malformed .pathEmpty` at `inc:959` (C14).
- C4. `commonPrefixLength` (`mpt:350–357`).

### 2.2 The mathematical root

- C5. `EMPTY_TRIE_ROOT = keccak256(rlp(b""))` = `0x56e8…b421` (`mpt:71–75`). In Lean it is `HashConsts.emptyTrieRoot` (`EthBase`; D5), acquired through the oracle at the caller-owned F20 boundary and passed to the operations that need it (`decodeRoot`, `rootHash`, `mathRoot`). The literal is its value at `m := Id` only (`HashConsts.literals`, `EthBase`), and `EthHash` checks that `HashConsts.query` at `Id` yields it (`EthHash` §7).
- C6. `encode_internal_node` (`mpt:213–249`): `none ↦ b""`; leaf `↦ (HP(rest, true), value)`; extension `↦ (HP(seg, false), subnode)`; branch `↦ 16 subnodes ++ [value]`; if `len(rlp(·)) < 32` the **unencoded structure** is returned (inlined in the parent), else `keccak256(rlp(·))`.
- C7. `patricialize obj level` (`mpt:507–581`): empty → `none`; one key → leaf with `key[level:]` (possibly **empty**: valid, e.g. below a branch at level 63 of a 64-nibble key); if all keys share a non-empty prefix from `level` → extension over the longest common prefix; else a branch whose value is the key ending at `level` (if any) and whose children are the recursive results at `level + 1`. EELS picks an arbitrary first key (`next(iter(obj))`); the result is independent of the choice (§7.3). The Lean definition takes an `ExtTreeMap Nibbles ByteArray` and an explicit
  `PatricializeDomain obj level` proof (Q50): every full key reaches `level` and
  every consumed prefix agrees. Every finite map starts at zero. Keys/values may
  be empty, lengths odd/arbitrarily finite and keys prefix-related. No behavior
  for a direct outside-domain helper call is selected.
- C8. `root` (`mpt:478–504`): `r = encode_internal_node (patricialize (prepare t) 0)`; if `len(rlp r) < 32` return `keccak256(rlp r)` else `r` (already the hash). The empty trie gives C5. Q50 separates the caller's F20 acquisition from
  local execution: `mathRoot emptyRoot ∅ = pure emptyRoot`, with no new local
  query or local oracle failure. Concrete Id/pinned-root equality requires
  coherent supplied constants plus complete assembled-node `Encodable` and
  host premises; it is not equality of the entire Python/local generic trace.
- C9. `_prepare_data` (`mpt:407–448`): encode each value (`encode_node`, C10); `None` values and empty encodings are rejected by `assert`; keys are `keccak256`-hashed if `secured`; keys become nibble lists. Consumers must never pass a value whose encoding is empty; in Lean this is a precondition carried by the value class (`encode v ≠ empty` for non-default `v`).
- C10. `encode_node` (`mpt:252–269`) dispatches: `Account` → `encode_account` (owned by `EthStateCommit`, needs the storage root); `Bytes` → identity; otherwise `rlp.encode`. In Lean this is the `TrieValue` class; the `Account` instance is supplied by `EthStateCommit`.
- C11. The typed trie (`mpt:274–347`): a map with `secured` and `default`; `trie_set` with the default **erases** the key; `trie_get` returns the default when absent; `copy_trie` is a shallow copy (identity on a persistent Lean map). `EthBlock` uses it (unsecured) for the transaction, receipt and withdrawal roots (`fork.py:351–354`), so its root must equal C8 on those value types.

### 2.3 Node database and eager decoding (D19; CONTRACT O4)

- C12. `build_node_db` (`ws:37–42`) keys every witness entry by `keccak256(entry)`, folding in input order with **last entry wins**. In Lean `NodeDB.build` hashes through the oracle (monadic, D5/F4), so authenticity is the separate predicate `NodeDB.Authentic H db` (every entry `b` under `h` has `H b = h`), which `NodeDB.build` establishes at `m := Id` with `H := keccak256`. Repeated identical entries are harmless; different entries with the same digest must preserve last-write behaviour and yield a collision in the security proof. Extra entries are allowed (fixture `test_validation_state_extra_unused_trie_node`), subject to C16(f).
- C13. `decode_witness_to_mpt db r` (`inc:994–1040`): if `r = EMPTY_TRIE_ROOT`, the empty trie **without consulting the DB** (`inc:1024–1030`); else `db[r]` (missing → `KeyError`, O4(a)) and decode it. Decoding is pure in Lean (F4), so the empty root is an explicit parameter: `decodeRoot emptyRoot db r`, called with `HashConsts.emptyTrieRoot`.
- C14. `_decode_witness_node bytes` (`inc:917–991`), in this order: compute `keccak256(bytes)` iff `len ≥ 32` (cached, C18; Lean decoding is pure (F4), so a DB entry takes its reference `h` as the cached hash, and the inline case is open, §10); RLP-decode (failure → O4(b)); a byte string must be empty (→ empty node) else malformed; a list of length 2: first item must be a string, `compactToNibbles` (C3); **leaf**: the second item must be a string (any value, including empty [executed]); **extension**: path must be non-empty, child resolved by C15 must be a branch **or an unresolved stub**; a list of length 17: resolve the 16 children, value = item 16 if it is a string, **otherwise the empty value** [executed]; require `occupied ≥ 2` where stubs count as occupied and the value counts iff non-empty; any other length is malformed.
- C15. `_resolve_child_ref` (`inc:892–914`): an empty string → no child; a string of length ≠ 32 → malformed; a 32-byte string present in the DB → decode that entry (recursively, eager); absent → an **unresolved stub** `HashedNode h` (not an error); an inline list → decode `rlp.encode(list)`.
- C16. **Accepted non-canonical encodings** [executed; each reachable only with a trie that no canonical state produces]: (a) hex-prefix flag bits 2–3 set or a non-zero padding nibble (C3); (b) an inline child whose RLP is ≥ 32 bytes (it is then given a cached hash, C18); (c) a hash reference to a DB entry shorter than 32 bytes; (d) a branch value that is a list (read as empty); (e) a leaf with an empty value or a path whose length does not match its depth; (f) a child reference equal to `EMPTY_TRIE_ROOT`: if the DB contains the entry `0x80`, it decodes to **no child**, otherwise it is a stub — so adding the "unused" entry `0x80` can turn an accepted witness into a rejected one (occupancy drops below 2) [executed]. The Lean decoder must reproduce these outcomes exactly (P2), and the agreement theorem (§7.4) covers them through its collision disjunct.
- C17. **Cycles and sharing.** EELS recurses without a visited set: a reference cycle ends in `RecursionError`, caught as `false` (O12, classified O4 by CONTRACT); the Lean decoder tracks the hashes on the current path and returns `malformed` on a repeat. A DB built by C12 can contain a cycle only through a Keccak fixpoint chain, which cannot be ruled out in Lean without an assumption, so totality needs the check (ARCHITECTURE §5.4). A **shared** hash reached along two paths is decoded twice by EELS; on a DAG-shaped witness this is exponential in depth (16 identical children per level) [inference from `inc:892–914`]. Memoising completed, validated decodings must preserve mathematical decoding and raw encodings (§7.6). This is the DAG memo of DISC-004/B15, internal to one `decodeRoot`; it is not the per-root storage-trie memo of `EthStateWitness` (F6, open). Its effect on host-resource acceptance requires D14/O12 treatment. Deep acyclic chains can exceed Python's recursion limit in EELS: the guest-process limit is 100,000 (py_ecc raises it; 12,288 applies only after `import ethereum`), and the witness-chain depth at which the reference fails has not been re-measured under it (DISC-001, O12 unresolved).
- C18. **Cached encodings.** A decoded node keeps its original bytes and, iff they are ≥ 32 bytes, their hash (`inc:932–934`, `:955–956`, `:967–968`, `:986–988`). When a parent is re-encoded, a child's reference is (`_encode_mutable_node_to_extended`, `inc:287–313`): empty → `b""`; stub → its hash; an unmodified node with a cached hash → that hash (**not** recomputed, even if non-canonical); otherwise the node is re-encoded from its fields (C6 rules: `< 32` bytes inline, else hash).
- C19. **Visited nodes lose their cache.** Every node on the path of an update or delete is invalidated (`_invalidate_hash`, `inc:231–237`, called at `:490` and `:694`) — including nodes that end up unchanged, such as a mismatching leaf in a no-op delete — and is then re-encoded from its fields. Off-path nodes keep their cached encoding. For a non-canonical witness this makes the root after a **no-op delete differ** from the pre-root [executed]. A functional implementation achieves this by rebuilding every visited node through the smart constructor and must **not** short-circuit "unchanged" subtrees to the original node.

### 2.4 Lookup (guest path)

- C20. `_trie_lookup root keyHash` (`ws:53–100`) walks the decoded trie with the 64 nibbles of a 32-byte key hash: a stub → error (O4(c): the `AssertionError` at `ws:73`, witnessed on corpus inputs by running the pinned EELS over the full fixture corpus); leaf → its value iff `nibbles[pos:] = rest` else absent (an empty value is returned as present, and later fails leaf decoding in `EthStateCommit`); extension → absent if the next `|seg|` nibbles differ (a shorter remainder differs), else continue; branch at `pos = 64` → its value, empty ↦ absent; else descend into child `nibbles[pos]`. The walk is a loop that terminates because `pos` strictly increases on every extension/branch step and leaves are terminal.
- C21. `mpt_get` (`inc:349–378`) answers from the flat `_data` map and only *records* the traversal; `_data` is empty for decoded tries. It is host-side witness construction (`stateless_host_exec_witness.py:82`, `:120`), not the guest lookup.

### 2.5 Update, delete, root (guest path)

- C22. `mpt_set m key value` (`inc:417–470`): the default value deletes; otherwise the value is encoded (C10) and inserted; a key is hashed iff `secured`. The Lean generic API takes the already-encoded value (`Option ByteArray`, `none` = delete).
- C23. **Insert** (`inc:473–677`): empty → new leaf; a stub on the path → failure (`assert` in `_invalidate_hash`, O4(c)); leaf with equal remaining key → replace value; otherwise split into (extension over the common prefix, if non-empty, of) a branch built from the two remainders, a remainder of length 0 becoming the branch value (`_create_branch_from_two_leaves`); extension: full prefix match → recurse into the child, partial → `_split_extension` (the old child is reused unchanged when one nibble of the segment remains, else wrapped in a shorter extension; the "unexpected collision" `assert` at `inc:644` is unreachable [inference: the remainders differ at `prefix_len`]); branch → set value at an empty remainder, else recurse into child `remaining[0]`.
- C24. **Delete** (`inc:680–784`): empty → empty; a stub on the path → failure; leaf → removed iff its path equals the remainder, else unchanged; extension with a mismatching segment → unchanged; extension → recurse and **merge** a resulting extension or leaf child into it (segment concatenation), drop it if the child vanishes; branch → clear the value or recurse into the child; if nothing changed return the branch, otherwise collapse (C25).
- C25. **Collapse** (`_collapse_branch`, `inc:787–828`): with exactly one child and no value, the sole child is first passed to `_record_witness`, which **fails on a stub** (`inc:245`): deleting a key whose only remaining sibling is unresolved is a witness failure (EELS unit test `test_partial_witness_delete_collapses_to_hashed_node`; fixture `test_validation_state_missing_delete_auxiliary_node`). Otherwise leaf child → leaf with the nibble prepended; extension child → extension with the nibble prepended; branch child → one-nibble extension. With no children and a value → leaf with **empty path**. The `assert` at `inc:793` (a branch with nothing left) is unreachable from a branch with ≥ 2 occupied entries [inference].
- C26. **Order sensitivity.** Because C25 fails only when the sibling set has shrunk to a single stub, the success of a mixed sequence of inserts and deletes depends on order [executed: delete-then-insert fails, insert-then-delete succeeds on the same trie]. Whoever sequences updates (`EthStateWitness`) must reproduce EELS's order.
- C27. `mpt_root` (`inc:831–856`): empty → `EMPTY_TRIE_ROOT`; if the root's reference (C18) is bytes it is the root, else `keccak256(rlp ·)` of the inline structure — the same rule as C8.

### 2.6 Host-side items

- C28. `build_mpt`/`_build_mutable_tree` (`inc:126–228`) build a mutable tree from a full map exactly as `patricialize`; `Witness`, `_record_witness`, `_compute_node_hash_and_rlp`, `_mpt_traverse_for_witness` (`inc:101–106`, `:240–346`, `:381–414`) record accessed node preimages for witness generation (`stateless_host_exec_witness.py`). They do not affect guest outputs **except** the stub `assert` of `_record_witness` inside collapse (C25). They are specified here as reference definitions for host tooling and tests: `buildMpt m` must satisfy `represents (buildMpt m) m` with no stubs, and the recorded witness of a lookup is the set of path-node preimages.

### 2.7 Failure behaviour

- C29. Every decoding, lookup and update failure is a `TrieError` (mapped to `WitnessError`, then to O4 → `false`). Preconditions of the mathematical root (C9) are type-level, not runtime failures. No function may depend on host recursion limits (O12, DISC-001; C17); all recursion is structural or on an explicit measure (§7.1).

## 3. EELS source map

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `merkle_patricia_trie.py::EMPTY_TRIE_ROOT` | 71 | `HashConsts.emptyTrieRoot` (`EthBase`) | literal is the `Id` value (`HashConsts.literals`); `Id` check in `EthHash` (C5) |
| `merkle_patricia_trie.py::LeafNode` | 91 | `InternalNode.leaf` | |
| `merkle_patricia_trie.py::ExtensionNode` | 110 | `InternalNode.extension` | |
| `merkle_patricia_trie.py::BranchNode` | 165 | `InternalNode.branch` | |
| `merkle_patricia_trie.py::K` | 189 | type parameter of `Trie` | |
| `merkle_patricia_trie.py::V` | 190 | type parameter of `Trie` | |
| `merkle_patricia_trie.py::encode_internal_node` | 213 | `encodeInternalNode` | |
| `merkle_patricia_trie.py::encode_node` | 252 | `TrieValue.encode` | `Account` instance in `EthStateCommit` |
| `merkle_patricia_trie.py::Trie` | 274 | `Trie` | |
| `merkle_patricia_trie.py::copy_trie` | 315 | `copyTrie` | identity |
| `merkle_patricia_trie.py::trie_set` | 325 | `trieSet` | |
| `merkle_patricia_trie.py::trie_get` | 341 | `trieGet` | |
| `merkle_patricia_trie.py::common_prefix_length` | 350 | `commonPrefixLength` | |
| `merkle_patricia_trie.py::nibble_list_to_compact` | 360 | `nibbleListToCompact` | |
| `merkle_patricia_trie.py::bytes_to_nibble_list` | 395 | `bytesToNibbleList` | |
| `merkle_patricia_trie.py::_prepare_data` | 407 | `prepareData` | internal |
| `merkle_patricia_trie.py::_prepare_trie` | 451 | `prepareTrie` | internal |
| `merkle_patricia_trie.py::root` | 478 | `root`, `mathRoot` | |
| `merkle_patricia_trie.py::patricialize` | 507 | `patricialize` | |
| `forks/amsterdam/incremental_mpt.py::*` | 50–1040 | `Node`, `Ref`, `IncrementalMPT`, `decodeWitnessToMpt`, `update`/`delete`/`mptSet`, `mptRoot`, `compactToNibbles`, host-side `buildMpt`/`mptGet`/`Witness` | whole file; per-item mapping in §5 |
| `forks/amsterdam/witness_state.py::_trie_lookup` | 53 | `lookup` | generic walk |
| `forks/amsterdam/witness_state.py::build_node_db` | 37 | `NodeDB.build` | |

### Implemented pure path operations

The following operations and their public model laws are implemented on the stated typed domains
in `STFSpec/Commit/Nibbles.lean`; compact decoding, internal-node encoding and raw
NodeDB construction and mathematical-root support are documented below. The remaining
source-map items are open. `Nibbles` has private packed storage and a byte-range
invariant, with public `size`, `get`, `toList` and `ofList` (§5/§6; F19). Ordinary model
equations specify their observations (D25).

| Exact pinned EELS source | Lean declaration/public type and domain | Success/effects | Ordered failures/handler | Model law | Deterministic/differential evidence |
|---|---|---|---|---|---|
| `src/ethereum/merkle_patricia_trie.py:395–404` | `STFSpec.Commit.bytesToNibbleList : ByteArray → Nibbles`; every finite byte array | High then low nibble; length `2*n`; pure | None on this domain; no O-row | `toList_bytesToNibbleList`; `size_bytesToNibbleList`; `get_bytesToNibbleList_high/low`; `highNibble_mul_add_lowNibble` | `NibblesGuards.allByteSplits` (all 256); empty/zero/ff/long buffers; authenticated driver |
| `src/ethereum/merkle_patricia_trie.py:360–392` | `STFSpec.Commit.nibbleListToCompact : Nibbles → Bool → ByteArray`; every finite bounded path and leaf flag; `Nibbles` supplies the range premise | Four flag combinations, even zero padding/odd first digit, ordered pairs; pure, nonempty `n/2+1` bytes | None on this domain; invalid Python nibble values are outside it, not a new runtime error API | `nibbleListToCompact_eq_model`; `size_nibbleListToCompact`; `nibbleListToCompact_nonempty/pair/header/flag/first/empty` | `NibblesGuards.allCompactFlags` (all ordered pairs/both flags and singleton flags); empty/odd/even/long paths; authenticated driver |
| `src/ethereum/merkle_patricia_trie.py:350–357` | `STFSpec.Commit.commonPrefixLength : Nibbles → Nibbles → Nat`; every pair of finite bounded paths | Stops at first mismatch or either end; pure | None on this domain; no O-row | `commonPrefixLength_eq_model`; `_le_left/right`, `_symm`, `_self`, `_take_iff`, `_equal_prefixes`, `_maximal` | Empty/proper prefixes in both orders, first/end mismatch and 4096-digit common prefix; authenticated driver |

`STFSpec/Conformance/Commit/NibblesGuards.lean` owns deterministic value guards; `STFSpec/Conformance/Commit/NibblesCallerProofs.lean` composes public laws and observers. `STFSpec/Conformance/Commit/nibbles_differential.py` invokes the three actual pinned Python functions. It authenticates current source/lock and installed dependency RECORD bytes, checks exact Python input/result classes before normalization, preserves source/environment identity before/after and retains class/domain/authentication negative controls. Emitted guards compare full outputs, including long paths. This finite reference evidence supplies no EEST guest execution or whole-trie theorem.

Run from the repository root with the pinned EELS environment and an evidence destination outside both repositories:

```sh
EELS/.venv/bin/python -I -B STFSpec/Conformance/Commit/nibbles_differential.py \
  --eels EELS --output EXTERNAL.lean
```

The interpreter, installation/startup and installed dependency RECORD remain trust inputs. The reference import setup may change its recursion limit; the driver records the limit before and after imports and does not change it manually.

### Implemented internal-node encoding

`STFSpec/Commit/InternalNode.lean` implements the existing nonrecursive §5 type:
children are already encoded `RlpItem` structures/references. Its total assembly
and operational model equalities and local effect laws are proved on all typed
inputs. The finite source comparison supplies bounded Python evidence.
Raw database construction is documented separately below. Partial-witness
node/cache and patricialization/root construction remain open.

| Exact pinned source | Lean declaration/public type and domain | Success/effects | Ordered failures/handler | Public laws | Regression evidence |
|---|---|---|---|---|---|
| `src/ethereum/merkle_patricia_trie.py:88–183,228–241` | `InternalNode`; `assembleInternalNode : Option InternalNode → RlpItem`; every finite bounded path, arbitrary byte/list field, sixteen ordered branch children | None is empty bytes; leaf/extension HP followed by the unchanged field; branch children then value at position 16; pure | None in the typed domain; unsupported Python classes/fields are outside the caller interpretation | `assembleInternalNode_eq_model`, `_none/leaf/extension/branch`; `branch_items_get/value/length` | Empty/odd/even HP, empty extension, nested values, distinct ordered children/value-last |
| `src/ethereum/merkle_patricia_trie.py:213–249`; locked `ethereum_rlp/rlp.py:66–88,91–140` (0.1.6) | `encodeInternalNode : {m} → [Monad m] → [KeccakQuery m] → Option InternalNode → m RlpItem`; operationally all typed inputs; standard correspondence requires complete `Rlp.Encodable (assembleInternalNode node)` | One assembly and one packed RLP encoding; complete width < 32 returns the structure; otherwise exactly one whole-preimage query and all 32 answer bytes | No local error/guard/handler; original monadic query failures propagate; no guest outcome selected here | `encodeInternalNode_eq_model`, `_eq/inline/hash/none/id/of_pure_answer/recording`; `run_encodeInternalNode_exceptT/stateT/error`; `toList_encode_assembleInternalNode`, `size_encode_assembleInternalNode` | 31/32/33 bytes from HP parity, fields, nested payload, branch value and child 7; arbitrary/failing oracles and transformer client |

`InternalNodeGuards.lean` compares complete byte/list trees, preimages and answers;
`InternalNodeCallerProofs.lean` composes public laws, complete domain premises,
child ordering and transformer contexts.
`STFSpec/Conformance/Commit/internal_node_differential.py` authenticates the current
pinned source/lock and installed ethereum-types/ethereum-rlp RECORD bytes and exact
classes/origins before and after running with the isolated pinned venv launcher
`-I -B`. It covers absence, leaf/extension paths and fields, ordered branch items,
thresholds, nested structures and long values/paths. Adjacent `encode_node` (C10)
observations, expected-exception checks and source/effect observations are recorded
separately. Altered actual inline/digest results exercise the production result
validator, and changed observed lock bytes exercise the Driver rejection path.
The catalog is fixed; the seed does not vary it. Missing `-I`/`-B` startup rejection
checks are separate from the in-run controls. Output metadata owns case/control
counts and source/environment identities.

The driver compiles generated Lean guards with warnings fatal. Each guard compares
full assembly, RLP bytes, concrete `Id` output, arbitrary recording-oracle answer,
query preimages and error propagation. Instrumentation is restored in `finally`.
The driver does not manually change resource limits; pinned reference imports may
change them (`src/ethereum/__init__.py:30`). Interpreter/startup, the pinned
installation and RECORD remain trusted inputs. This is finite source
evidence; EEST execution, throughput and host-resource acceptance remain unverified.

From the repository root, reproduce with an output outside both repositories:

```sh
EELS/.venv/bin/python -I -B STFSpec/Conformance/Commit/internal_node_differential.py \
  --eels EELS --output SCRATCH.lean
```

Python tuple/list and byte/fixed-byte classes are normalized only after exact
class checks. Richer Extended fields require a caller-owned byte/list
interpretation; the existing `RlpItem` API asserts no raw Python class equality
or totality for arbitrary unsupported/custom/cyclic Python objects. Q47's total
completion governs unconditional operational laws. For standard/pinned
correspondence, `encodable_assembleInternalNode_leaf_iff/extension_iff/branch_iff`
retain HP width, every field and the complete joined encoded payload bound,
rather than assuming only child encodability. Actual trie/schema callers must
establish these premises and reference host compatibility.

`encode_account` (in `merkle_patricia_trie.py`) is claimed by `EthStateCommit`.

**External semantics.** `ethereum_rlp.rlp` encode/decode and `Extended` (owned by `EthCodec`): this module relies on decode being **strict** (non-canonical length prefixes and single bytes `< 0x80` wrapped as strings are rejected, truncated input rejected [executed]) and on `Rlp.encode_eq_of_decode_eq_ok` and `decode_success_encodable` ([EthCodec §7](EthCodec.md#7-contract-and-laws)) for successfully decoded bytes. These proved raw-codec laws supply exact reencoding and the Q47 domain; applying them to inline child references and their accepted witness interpretation in C15 remains an EthCommit obligation. Leading zero bytes inside strings are just bytes. `ethereum_types` `Bytes`, `Uint`, `ulen`, `slotted_freezable` (value semantics only); `copy.copy` in `copy_trie` (shallow; identity in Lean); `utils.hexadecimal.hex_to_bytes` (G1) for the constant.

### Implemented bounded provider operations (Q49)

These **discharged** sequence support operations in `STFSpec/Commit/Nibbles.lean`
are not additional EELS functions. They supply the typed `Bytes` slice semantics
used at `merkle_patricia_trie.py:538/543/547/556` and ordinary Python byte
lexicographic ordering. All operations are pure: no hashing, state effects,
error constructors, O-row or arbitrary key-size cap. `Fin 16` supplies digit
bounds; all natural counts/offsets are accepted, including enormous ones.

| Source/support semantics | Lean declaration/public type and domain | Success/effects and failures | Public laws | Deterministic/differential evidence |
|---|---|---|---|---|
| Lean bounded generator support (Q49), not an EELS function | `Nibbles.generate : Nat → (Nat → Fin 16) → Nibbles`; all natural lengths and bounded callbacks | Exactly `n` digits; callback visits ascending `0..n-1`, none at zero or outside the interval; pure, no error result | `size_generate`, `get_generate`, `toList_generate`, `generate_congr`, `generate_zero` | `NibblesOperationsGuards.allGenerators`: zero/15/affine/mixed callbacks, empty/singleton/64/4096/4097 full outputs; bounded callback congruence and zero tests; Python sequence support differential |
| Typed `Bytes` copying windows, `merkle_patricia_trie.py:538/543/547/556`; ethereum-types 0.4.1 | `Nibbles.extract : Nibbles → Nat → Nat → Nibbles`; all bounded paths and natural start/stop offsets | Start inclusive, stop exclusive, clipped at size, reversed/equal/unavailable windows empty; no effects or failure | `size_extract`, `get_extract`, `toList_extract`, `extract_of_stop_le_start`, `extract_of_size_le_start` | `allWindows`: every small window plus 128/1024-bit offsets; long clipped/reversed windows; actual typed-index Python `Bytes` slice observations |
| Prefix/suffix copies of the same sequence model | `Nibbles.take`, `Nibbles.drop : Nibbles → Nat → Nibbles`; every natural count | Oversized take retains the path; oversized drop returns empty; no effects or failure | `toList_take/drop`, `size_take/drop`, `get_take/drop`, `take_zero`, `drop_zero`, `take_size`, `drop_size`, `take_of_size_le`, `drop_of_size_le`, `take_take`, `drop_drop`, `take_drop`, `drop_take`, `size_take_le`, `size_drop_le` | All small and huge offsets, full long prefix/suffix outputs; public symbolic clipped/composed windows |
| Python byte lexicographic order, a support helper rather than new EELS function | `Ord Nibbles`, `Std.TransOrd Nibbles`, `Std.LawfulEqOrd Nibbles`, `DecidableEq Nibbles`; all finite bounded path pairs | First differing digit determines order, proper prefix first; leading zeros significant; comparator equality is actual path equality; pure, no failure | `compare_toList`, `compare_eq_eq_iff`, `compare_of_toList_eq` | All 16×16 digit pairs; empty/proper prefix, unequal lengths with first/last mismatch, significant zero, long equal/prefix/mismatch paths; actual Python byte order; real map distinct-key/overwrite tests and symbolic insert/lookup/extensionality |
| Remaining-length and maximal-prefix provider support | All paths; strict suffix laws require `level < x.size` and `0 < n`; bounded prefix equivalence requires `k ≤ a.size` and `k ≤ b.size` | No consumer recursion, key filtering or root selection is implemented | `size_drop_add_lt`, `size_drop_succ_lt`, `take_commonPrefixLength`, `take_eq_iff_le_commonPrefixLength` | `NibblesOperationsCallerProofs.remaining_length`, `prefix_paths`; every new public law has a symbolic public-only client |

`STFSpec/Conformance/Commit/NibblesOperationsGuards.lean` owns complete-value
regressions; `NibblesOperationsCallerProofs.lean` uses only public seams for map
insert/lookup/extensionality, clipped windows and prefix/measure support.
`STFSpec/Conformance/Commit/nibble_operations_differential.py` executes bounded
sequence support observations with the frozen venv launcher `-I -B`,
authenticating all pinned source/lock blobs and installed ethereum-types Python
RECORD rows before fresh source imports. It checks exact classes before
normalization, preserves source identities, retains
invalid-class/domain/authentication controls and emits full Lean output
comparisons through generated `#guard`s. This is finite sequence-support
evidence, not EEST guest execution, new source-operation coverage or measured
C1–C4 completion. Run from the repository root with an evidence destination
outside both repositories:

```sh
EELS/.venv/bin/python -I -B STFSpec/Conformance/Commit/nibble_operations_differential.py \
  --eels EELS --output EXTERNAL.lean
```

### Implemented compact decoding

The pure decoder is **discharged** in `STFSpec/Commit/Compact.lean`. Its narrowly
owned diagnostics live in `STFSpec/Commit/TrieError.lean`; the other constructors
implement the existing §5 type only, without implementing their node/trie consumers.

| Exact pinned EELS source | Lean declaration/public type and domain | Success/effects | Ordered failures/handler | Model law | Deterministic/differential evidence |
|---|---|---|---|---|---|
| `src/ethereum/forks/amsterdam/incremental_mpt.py:859–889` | `STFSpec.Commit.compactToNibbles : ByteArray → Except TrieError (Nibbles × Bool)`; every finite byte array | Pure; first high nibble bit1 supplies leaf, bit0 parity; ignores high bits2–3 and even low padding; retains odd low digit, then each suffix high before low | Only raw empty input: `.malformed .compactEmpty` (Q48), corresponding to `IndexError` at `:878`; guest inner handler `stateless.py:303` projects existing O4; `:959` extension-path rejection is a later consumer | `compactToNibbles_eq_model`, `_error_iff`, `_ok_iff`, `_success_iff`, `_size`, `_leaf`, `_index_lt`, `_get`; `compactToNibbles_nibbleListToCompact`; `nibbleListToCompact_inj`; normalization/image laws | `CompactGuards.allLeadingBytes` (all 256 with empty/multiple-byte suffixes), exact empty/00/0f/20/2f/f123, canonical odd/even/zero/15/mixed long paths and normalization counterexamples; authenticated `STFSpec/Conformance/Commit/compact_differential.py` |

`CompactCallerProofs.lean` uses the public model/observer laws. The decoder
builds an indexed digit List and crosses `Nibbles.ofList`, which maps it to a
byte List before the packed copy. This local allocation exception is owned by
[DEBT-COMPACT-DECODE](../DEBT.md#debt-compact-decode--temporary-digit-lists).
Run the compact driver from the repository root with the pinned EELS environment
and an evidence destination outside both repositories:

```sh
EELS/.venv/bin/python -I -B STFSpec/Conformance/Commit/compact_differential.py \
  --eels EELS --output EXTERNAL.lean
```

Finite actual-source and native complete-result observations validate this slice;
no node, root, witness or guest acceptance/refinement is discharged.

### Implemented mathematical-root domain support

Q50 ([issue #26](https://github.com/alexanderlhicks/leanerSTFSpec/issues/26))
clarifies the reachable helper domain. `STFSpec/Commit/Root.lean` implements
the **pure domain/descent support** in this subsection, not a new EELS
operation or root. Private callback-based branch support is described below.
Its private partition retains full keys and values, uses an explicit packed-digit
bounds guard. `RootDomainGuards.partition` tests the filter expression in the
public `PatricializeDomain.child` statement. `RootDomainGuards.remaining` tests a
local copy of the measure expression `(obj.keys.map (fun k ↦ k.size - level)).sum`;
this is a termination sum, not a runtime/aggregate-cost bound. No repeated-prefix
search is adopted.

| Exact pinned EELS context | Lean support/public domain | Success/effects and failures | Proved law | Deterministic evidence |
|---|---|---|---|---|
| `merkle_patricia_trie.py:507–543` | `PatricializeDomain : ExtTreeMap Nibbles ByteArray → Nat → Prop`; arbitrary finite full keys/byte values | Proof seam only; no queries/errors/rejection or outside-domain completion | `PatricializeDomain.zero`, public `depth`/`consumedPrefix` | `RootDomainGuards.domainCheck_iff`; empty/singleton/multikey, short-key and inconsistent-prefix counterexamples |
| `merkle_patricia_trie.py:567–571` | Ending keys and branch lookup on this domain | Unique ending key; optional empty value stays present; no new effects | `ending_unique`, `ending_prefix_key`, `branch_value_representative_eq` | `RootDomainCallerProofs.ending_value/absent_branch_value`; actual insertion permutations and empty/prefix key values |
| `merkle_patricia_trie.py:564–576` | Public `PatricializeDomain.child` over the explicit guarded `obj.filter`, each `Fin 16` | Keys remain full; ending keys excluded before digit access; empty children allowed; strict sum requires the domain and `obj.size > 1` | public `ending_not_mem_child`/`child`; private `child_keys`, `mem_child`, `child_lookup`, `multikey_measure_pos`, `child_measure_lt` | All sixteen complete child key/value outputs, sums/domain/strictness including empty groups; symbolic `root_child` |
| `merkle_patricia_trie.py:555–562` | Public `PatricializeDomain.extension`; all keys reach and agree at `level+amount` | Pure domain preservation; private strict descent requires `obj.size > 0` and `amount > 0` | `extension`; private `remainingSum_extension_lt`/`extension_measure_lt` | Odd 257/259-digit prefix keys, complete retained paths/sums; zero advancement/empty-map/singleton-zero counter-premise guards |

`RootDomainGuards.cases` compares complete structured outputs through committed
`#guard`s. Uncommitted local native checks are separate finite support evidence;
no native support runner is supplied here. Pinned `mpt:478–581` was read directly,
without a replacement oracle.
The universal support proofs consume only public Nibbles and Std laws. Actual
C7–C8, composition with the existing C6 laws,
whole-constructor choice independence,
canonicality, source-root agreement, assembled-node `Encodable`/host premises,
F20 consumer coherence, D5 coupling and C1–C4 remain open.

### Implemented mathematical-root longest shared-prefix support

`Root.lean` adds private pure selection for the future C7 constructor. The actual
finite map retains full keys and every byte value. `selectSharedPrefix` traverses
its ordered key list once, handles an empty map as `none`, and otherwise returns
a selected member and additional length. `sharedPrefixFold` initializes the cap
from that member's remaining length, compares pairs at the current `level`, shrinks
the cap and stops at zero. `sharedPrefixScan` structurally consumes a remaining
counter; explicit `size` bounds guard both `get` indices. It neither copies suffixes
nor scans the consumed prefix. The ordinary List/drop reference is proof support.

| Exact pinned EELS context | Lean private support and domain | Success/effects and failures | Ordinary proof | Deterministic/source evidence |
|---|---|---|---|---|
| `merkle_patricia_trie.py:534,543–552` | `sharedPrefixScan`, `pairSharedPrefix`, `sharedPrefixFold`; all finite paths, natural levels/caps | Pure capped longest suffix-prefix length; guarded exhaustion; no query/error or new input restriction | `sharedPrefixScan_model` at all valid bounds; all-input `pairSharedPrefix_model`; `sharedPrefixFold_model` | Owner-private pair/fold examples; capped/unequal/empty/4097-digit complete observations |
| `merkle_patricia_trie.py:534,543–552` | `selectSharedPrefix : ExtTreeMap Nibbles ByteArray → Nat → Option (Nibbles × Nat)`; private support only | `none` exactly for empty keys; otherwise an actual member and selected length; values unaffected | `selectSharedPrefix_none_iff`, `selectSharedPrefix_member`, `selectSharedPrefix_domain` | Empty/singleton/ending keys, empty values, insertion permutations; genuine source leaf/extension/branch prefix observations |
| `merkle_patricia_trie.py:555–562` | `sharedPrefixFrom` on `PatricializeDomain obj level` and a real member | Every full key reaches and agrees at `level+amount`; positive length supplies existing extension and strict sum descent | `sharedPrefixFrom_le_iff/domain/bound/maximal/positive_descent` | Universal domain/extension/child clients; arbitrary consumed depth, odd unequal keys, complete long paths and sums |
| `merkle_patricia_trie.py:534,543–552` | Same domain and explicit selected-member premises | Length and complete additional prefix independent of member; identical full-key sets give identical length regardless of values/history; zero excludes a common positive next domain | `sharedPrefixFrom_representative_eq/prefix_representative_eq/keys_eq/zero_iff` | Alternative members, all16 next digits, prefix relationships; wrong-depth/consumed-prefix negatives where premises fail |

`RootPrefixGuards` observes the legible List/drop reference through public path
and map contracts. Root's all-input `pairSharedPrefix_model`, `sharedPrefixFold_model`,
`sharedPrefixFrom_model` and `selectSharedPrefix_model` equalities connect those
reference expressions to the private packed implementation. Private law clients
and finite scanner checks live in Root; no private declaration names are constructed
by consumers. `RootPrefixCallerProofs` consumes public domain fields and the existing
`child` law. No provider storage or generated provider equations are unfolded.
The selector allocates one list of full-key references through public `obj.keys`; scan work is bounded by each current cap and matching remaining digits,
with no packed key copy. These are source-structure bounds, not allocation/throughput
measurements or completed C1–C4. There is no new D18 performance exception.

The finite authenticated source driver executes genuine pinned `patricialize` both
with and without a restored trace hook. It reads complete selected prefix values
from the top frame and checks exact node/path classes before normalization; no
callable, class, recursion, encoding or hash is replaced. Current source/lock and
installed types/RLP/crypto identities are checked before and after. Full prefix
observations are emitted as Lean reference guards and elaborated with
`lake env lean -DwarningAsError=true`. The committed driver does not compile or run
a native Root executable; the all-input owner equalities provide the implementation
bridge for these reference observations:

```sh
EELS/.venv/bin/python -I -B STFSpec/Conformance/Commit/root_prefix_differential.py \
  --eels EELS --output EXTERNAL.lean
```

Only pure selection support is supplied. Actual C7–C8, whole-constructor choice
independence, canonicality, C6/root composition, source-root agreement, complete
assembled-node `Encodable`, oracle coherence/coupling, host/resources and guest
acceptance remain open. No outside-domain `patricialize` behavior is selected.


### Mathematical-root private branch support

`Root.lean` reuses its existing guarded full-key `childPartition`, with ordinary
List/filter reference equality, exact optional lookup, disjointness and coverage.
`branchParts` is a private pure decomposition model with sixteen numeric maps
and an optional ending lookup. On the explicit domain and a real member, that
lookup is present exactly for the unique ending key, with its original bytes;
`some empty` remains distinct from `none`. The decomposition and ending bytes
are representative independent.

The private `branchStage` supplies each full child map, an erased equality
identifying that actual partition, and its next-depth domain proof to a callback.
`Vector.ofFnM` sequences the callback then actual C6 `encodeInternalNode` for
ascending digits 0..15. The returned branch defaults the ending lookup only at
its final `.bytes` field and does not encode or hash the parent. Ending lookup
is direct; it does not build another vector of sixteen maps just to project a
field. No recursive `patricialize`, root wrapper or public constructor seam is
added. The equality witness enables later Root-local use of the existing private
strict-descent fact without repeated filtering; it is not recursion in this item.

| Exact pinned EELS context | Lean private support and domain | Success/effects and failures | Ordinary proof | Deterministic/source evidence |
|---|---|---|---|---|
| `merkle_patricia_trie.py:564–572` | Existing `childPartition`; `branchParts : ExtTreeMap Nibbles ByteArray → Nat → Nibbles → BranchParts`; full finite maps | Whole keys/values retained; guarded digit reads; optional ending bytes including empty; pure | `inChild_reference`, `childPartition_model`, `mem_child`, `child_lookup_model`, `child_disjoint`, `child_coverage`, `ending_excluded`, `childPartition_domain`, `branchParts_get/ending_present/ending_none_iff/ending_representative` | Owner-local universal partition/lookup/index/ending examples; all16 groups, empty map/depth999, ending and continuing keys, long odd full paths, member/insertion alternatives, wrong-domain negatives |
| `merkle_patricia_trie.py:574–577` | `childAction`, `childReferences`; supplied child callback with actual-partition equality and next-depth proof | Construct then actual C6 encode for each digit; the first-callback error theorem assumes its run is pure error; finite guards cover later failure positions | `childReferences_first/list/pure`, `childAction_construct_error`, `branchStage_first_error`; reassociation/list equations explicitly require `LawfulMonad`; query instance on `ExceptT ε m` needs no underlying query instance | Complete State/ExceptT traces, all16 constructor-failure positions and all10 queried encoding failures, actual31/32/33 preimages and full32-byte answers; genuine pinned ascending construct/encode observations |
| `merkle_patricia_trie.py:578–581` | `branchStage : ... → m InternalNode`; private callback support only | Sixteen references then defaulted ending bytes; no parent query; retains empty values | `branchStage_assembled`, `branchStage_representative`, `branch_reference_position`, `branch_value_position`; representative rewriting needs no `LawfulMonad` assumption | Whole assembled wire/state, empty and nonempty ending fields, all members and insertion permutations; one-child/empty-value example preserves Q50 and supplies no canonical occupancy theorem |

`RootBranchGuards` uses explicitly labeled test instrumentation of verified actual
private Root names; it copies no recursive executable algorithm. Private branch
law examples live in Root; reusable `RootBranchCallerProofs` clients use existing public
`PatricializeDomain`, Nibbles, Std, Vector and InternalNode laws. Provider storage
and generated provider equations are not unfolded. A branch performs at most
sixteen guarded filters, one per executed callback, retaining full keys. This
source-structure bound and final emitted-code inspection supply no allocation,
throughput or C1–C4 result and require no new D18 exception.

The fresh driver below authenticates pinned source/lock, installed types/RLP/crypto
and exact classes before normalization and after execution. A restored trace hook
observes genuine top-level branch groups, optional ending selection, and all sixteen
alternating child construction/encoding calls. Complete source results match
untraced replays; no source callable, class, recursion, encoder or hash is replaced.
It emits complete grouping/ending observations for source-selected and minimum
members, including reversed insertion and complete31/32/33 child encodings.
The driver compares grouping and optional ending lookup; it does not compare the
complete callback stage. Committed stage guards independently compare full
assembled wire/state, including a nonempty ending value at position sixteen.
Those support fields, not recursive Lean construction/root agreement, are compared
by generated guards. Separate uncommitted local O3 native runs exercise complete
stage outputs and traces; no native runner is committed here:

```sh
EELS/.venv/bin/python -I -B STFSpec/Conformance/Commit/root_branch_differential.py \
  --eels EELS --output EXTERNAL.lean
```

The interpreter, frozen installation/RECORD, startup and host crypto remain trust
inputs. No Python-host or generic-oracle coupling interpretation is adopted.
Q50 allows empty byte values: `{[] ↦ empty, [0] ↦ empty}` forms a branch with one
occupied numeric reference and an empty byte field under the supplied finite
callback. A later canonical occupancy/lookup theorem needs appropriate value
premises; no rejection or domain restriction is introduced. Actual C7–C8,
whole-constructor choice independence, canonical witnesses, complete assembled-node
`Encodable`, source-root correspondence, F20 coherence/D5 coupling and resources
remain open.

### Implemented raw node database (C12)

`STFSpec/Commit/NodeDB.lean` implements the C12 seam in `STFSpec.Commit`.
The following rows are implemented for their stated domains, alongside the path,
compact and internal-node operations above. The database is shared read-only by
consumer convention; its authenticity predicate is separate from its representation (F4).
Their shared-contract owner is registered in [contracts.toml](../contracts.toml)
and [COMPOSITION §2](../COMPOSITION.md#2-type-ownership-and-adapters).

| Source at the pin / operation | Public declaration / domain | Success, effects and ordered failure | Ordinary law / deterministic evidence |
|---|---|---|---|
| `forks/amsterdam/witness_state.py:37–42` (`build_node_db`) | `NodeDB.build {m} [Monad m] [KeccakQuery m] : Array ByteArray → m NodeDB`; every raw array, including empty/invalid RLP, duplicates and unused entries | Exactly one query per entry in input order, then insert the raw entry under the returned Hash32; equal answers overwrite. Empty input has no query. An oracle-monad failure stops before insertion and every later query; construction introduces no error or handler/O-row. Caller owns oracle failures; concrete Id has none | `build_eq_reference`, `build_empty`, `build_singleton`, `build_append`, `build_push`; `NodeDBGuards.lean` observes all raw values, traces, arbitrary collisions and all four failure positions; authenticated actual-source differential |
| C12/F4 representation and authenticity | `NodeDB` with `map : Std.HashMap Hash32 ByteArray`; `Authentic (H : ByteArray → Hash32) (db : NodeDB) : Prop` | Every stored entry satisfies `H b = h`; predicate only, with no generic-oracle coherence promise | `authentic_insert`, `authentic_model`, `authentic_build_id` establish concrete authenticity without hash injectivity; `NodeDBCallerProofs.recovered_preimage` supplies the future decoder premise |
| C12/D25 ordered reference and pure model | `buildReference {m} [Monad m] [KeccakQuery m] : List ByteArray → NodeDB → m NodeDB`; `model : (ByteArray → Hash32) → List ByteArray → NodeDB → NodeDB`; all lists/tables | List fold has the same query/insertion order; model extends an arbitrary table with a chosen pure interpretation. Reference is proof support, not a runtime conversion or scan | `buildReference_cons` (LawfulMonad), `build_id_model`, `lookup_model`, `lookup_build_id` expose the full last-matching-entry fold; public-only split/last-write/different-key/reconstruction clients |
| D5/F15 transformer composition | Same ordered reference over StateT/ExceptT; all lists and initial tables, explicit `LawfulMonad` for ordinary reassociation laws | Added state unchanged; added exceptions wrap success; underlying query effects and failures forward exactly | `run_buildReference_stateT`, `run_buildReference_exceptT`, `run_buildReference_error`; both transformer orders and retained/lost state guards |

Run `EELS/.venv/bin/python -I -B STFSpec/Conformance/Commit/node_db_differential.py
--eels EELS --output OUTSIDE/NodeDBSource.lean`. The driver calls actual pinned
`build_node_db`, authenticates all pinned source/lock bytes and installed
Python-source RECORD entries before imports and afterward, and compiles fresh
source without cached bytecode. Exact classes are recorded before byte
normalization. Instrumentation restores callables in `finally`, records their
before/after identities and demonstrates query order, last-write collisions and
failure prefixes. Instrumented answers are controls, not concrete Keccak collisions.
The isolated interpreter, startup, frozen installation/RECORD, loader and host
hash backend remain trust premises.

Run `python3 scripts/test_node_db.py --observations OUTSIDE/NodeDBSource.observations.json
--output OUTSIDE/native`. Current actual-module setup/import artifacts and fresh
C/olean equality precede owned O3/Werror object compilation. Complete source and
native observations agree with the pinned concrete tables and independent
arbitrary-answer controls, including reconstructed full-256-bit keys, empty raw
values, extra entries, larger tables, sibling extensions and retained-parent checks.
The native link map and exact archive-member/object comparisons identify the
selected owned providers. No checksum substitutes for table or trace observations.
These finite functional runs establish no table distribution, throughput,
allocation, C1–C4, R4, generic oracle coupling, decoder/root or guest/EEST claim.

## 4. Tests

`InternalNodeGuards.lean` checks absent, leaf and extension structures, nested
fields, and complete encodings at the 31/32/33-byte threshold under arbitrary and
failing oracles. Its concrete `Id` guard checks a branch of sixteen distinct
32-byte child references against the full digest obtained from the authenticated
pinned C6 operation. The driver in §3 additionally compares full ordered branches,
HP parities, nested values and long structures with pinned EELS. Symbolic clients
in `InternalNodeCallerProofs.lean` compose domain, model, ordering and lift laws.
These node tests cover C6; root construction and witness operations remain open.

The implemented pure operations evaluate all byte splits, all ordered nibble pairs under both
leaf flags, all singleton flags, empty/odd/even encodings, zero/15 extremes and long paths.
Prefix guards cover asymmetric proper prefixes and first/end mismatches.
`NibblesGuards.longChecks` compares whole outputs, and the differential driver emits
full actual-source observations. The compact decoder guards in §3 additionally
cover exact raw-empty failure, every leading byte, ordered suffix digits, canonical
inverses and accepted-wire normalization.
Witness decoding and trie cases below remain open; resource gates are owned by REVIEW §7.

`NibblesOperationsGuards.lean` checks bounded generators, clipped windows,
huge offsets, significant zeros and lawful map keys through complete outputs.
Public caller proofs cover symbolic copies, map lookup and conditional measures.
Uncommitted local finite native checks provide complete-value and persistence evidence.
They do not demonstrate physical release or reclamation of sibling allocations,
dynamic allocation, lifetime costs, throughput or completed C1–C4 gates. To
reproduce the committed deterministic cases natively, compile a temporary Lean
executable importing `STFSpec.Conformance.Commit.NibblesOperationsGuards` and
check its `allDigitPairs`, `allWindows`, `allGenerators`, `longChecks` and
`mapChecks`; retain parent and sibling values and compare their full public
observations before and after map updates. The committed Python driver evaluates
generated `#guard`s. Witness-node and trie cases remain open.


- **EEST fixture areas:** every `blockchain_tests`/`blockchain_tests_engine` area checks the state, transaction, receipt and withdrawal roots, so the mathematical root is exercised by the whole corpus (corpus pin: `reference.toml`). Witness decoding and the partial trie specifically: `amsterdam/eip8025_optional_proofs`, especially `test_witness_state_deletes.py` (collapse adds an auxiliary sibling node), `test_witness_state_replay_order.py` (insert-before-delete), `test_witness_validation_state.py` (missing storage proof node, missing absent-slot proof leaf, missing delete auxiliary node, missing sender/absent/failed-call-target account nodes, extra unused node, unsorted but complete).
- **EELS unit tests** (`tests/json_loader/test_incremental_mpt.py` at e1a316a0): `TestCompactToNibbles` (even/odd leaf/extension, empty even leaf, round trip), `TestHashedNode` (stub in root computation; insert/delete/traverse into a stub raise), `TestDecodeWitnessToMpt(More)`, `TestMalformedWitnessNodes` (malformed RLP, non-empty string node, list length 3, extension with empty child ref, extension to leaf, extension to extension, non-hash child bytes, branch with 0 and 1 occupied entries, extension with empty path), `TestPartialWitness` (root preserved; modify known path; insert into stub fails; delete collapsing onto a stub fails), `TestBuildVsDecode` (roots match after mutation), `TestDecodeEdgeCases`. From `test_witness_state.py`: `TestCanonicalSecureTrieValidation` (zero-length extension paths and unresolved stubs in account and storage tries). Port each as a `#guard`.
- **`core` `#guard` cases** (all dependencies must be implemented before evaluation, F16; core proof holes are banned): `mathRoot` of the empty map equals `HashConsts.literals.emptyTrieRoot`; hex-prefix vectors for all four flag combinations and the empty path; `compactToNibbles` on `0xf1 0x23`, `0x0f`, `0x2f` and empty input (C3); `patricialize` on 0, 1, 2 keys, keys sharing a prefix, a 64-nibble pair differing only in the last nibble (empty-path leaves), and a key ending at a branch (unsecured); transaction-trie roots of small blocks from fixtures.
- **Adversarial witnesses** (hand-built DBs; cycles only through the internal `decodeRoot` API with a DB that is not keccak-keyed): missing root (O4(a)); missing child never accessed (accepted); malformed node off every accessed path (rejected, eager); on-path cycle of length 1 and 3 (malformed); diamond sharing (accepted, and memoised decode equal to unmemoised); a DAG of depth 8 with 16 identical children (cost test); empty-path leaf below a depth-63 branch (accepted); branch collapse whose sole sibling is a stub (rejected) and the same after an insertion (accepted, C26); each non-canonical case of C16 including the `0x80` entry flip; no-op delete through a non-canonical node changing the root (C19).
- **Property tests:** `rootHash (buildMpt m) = mathRoot m`; random update/delete sequences on fully resolved tries against `mathRoot` of the updated map; random pruning of a canonical trie to a witness, then sequences whose success matches the data-availability characterisation (§7.5); differential checks against EELS through a Python harness (bug-finding only).

`RootDomainGuards` additionally compares empty/singleton/multikey
maps, empty and prefix-related full keys/values, all sixteen numeric children,
ending exclusion, representative branch lookups, reversed insertion and odd/long
paths. It checks actual complete key/value lists, remaining-length sums and the
finite domain predicate (proved equivalent by `domainCheck_iff`), including short
keys/inconsistent consumed prefixes and missing positive-extension/multikey
premises. `RootDomainCallerProofs` supplies universal domain, lookup and distinct
insert-permutation clients through public contracts. Root owns private strict-descent
proofs and scanner law clients; conformance guards test the public domain/filter
contracts and the stated reference expressions. Uncommitted local finite native
checks remain separate evidence. No constructor differential or root correspondence
is claimed by these support tests.

`RootBranchGuards` compares complete values, including every numeric
constructor and queried encoding failure position. `printComplete` retains full
wire bytes, full-key/value groups, preimages, answers, original errors and states.
Root holds private universal branch law clients; `RootBranchCallerProofs` consumes
public provider contracts. To reproduce separate uncommitted native support cases,
compile a temporary executable
importing those modules and invoke `RootBranchGuards.printComplete`; additionally
compare every complete generated `sourceBranches` row from the driver above.
Retain default limits, warnings as errors, fresh current-module imports and sidecar
identities. These are bounded branch-support tests, not completed C7/C8 or EEST
root tests. No checksum or sampled field substitutes for complete values.

## 5. Interface

```lean
-- public: nibbles and hex-prefix
structure Nibbles                              -- constructor and packed storage private
-- invariant: every stored byte < 16; range evidence is internal (F19)
def Nibbles.size : Nibbles → Nat
def Nibbles.get (x : Nibbles) : Fin x.size → Fin 16
def Nibbles.toList : Nibbles → List (Fin 16)
def Nibbles.ofList : List (Fin 16) → Nibbles
def Nibbles.generate (n : Nat) (f : Nat → Fin 16) : Nibbles  -- Q49
def Nibbles.extract (x : Nibbles) (start stop : Nat) : Nibbles
def Nibbles.take (x : Nibbles) (n : Nat) : Nibbles
def Nibbles.drop (x : Nibbles) (n : Nat) : Nibbles
instance : Ord Nibbles
instance : Std.TransOrd Nibbles
instance : Std.LawfulEqOrd Nibbles
instance : DecidableEq Nibbles
def bytesToNibbleList : ByteArray → Nibbles
def nibbleListToCompact : Nibbles → (isLeaf : Bool) → ByteArray
def compactToNibbles : ByteArray → Except TrieError (Nibbles × Bool)     -- lenient, C3
def commonPrefixLength : Nibbles → Nibbles → Nat

-- D5: hashing kernels retain generic m; executable entry points specialise to Id.
-- The empty-trie root is HashConsts.emptyTrieRoot (EthBase), projected by callers
-- from their existing constants context and passed in where needed (C5, F20).
variable {m : Type → Type} [Monad m] [KeccakQuery m]

-- public: mathematical root
inductive InternalNode
  | leaf (restOfKey : Nibbles) (value : RlpItem)
  | extension (keySegment : Nibbles) (subnode : RlpItem)
  | branch (subnodes : Vector RlpItem 16) (value : RlpItem)   -- no nested occurrence, so Vector is accepted (contrast F5)
def assembleInternalNode : Option InternalNode → RlpItem
def assembleInternalNodeModel : Option InternalNode → RlpItem   -- public byte-list HP model
def internalNodeWireModel : Option InternalNode → List UInt8   -- full total RLP model
def encodeInternalNode : Option InternalNode → m RlpItem        -- C6, full width ≥ 32 hashes
def encodeInternalNodeModel : Option InternalNode → m RlpItem   -- same effects, model bytes
structure PatricializeDomain (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat) : Prop where
  depth : ∀ k, k ∈ obj → level ≤ k.size
  consumedPrefix : ∀ k, k ∈ obj → ∀ j, j ∈ obj → k.take level = j.take level
def patricialize (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (domain : PatricializeDomain obj level) : m (Option InternalNode)
def mathRoot (emptyRoot : Hash32) (t : Std.ExtTreeMap Nibbles ByteArray) : m Hash32
def secureKeys (secured : Bool) (t : Std.ExtTreeMap ByteArray ByteArray) : m (Std.ExtTreeMap Nibbles ByteArray)

-- public: typed trie with default (EthBlock's tries)
class TrieValue (V : Type) where
  encode : V → ByteArray
  isDefault : V → Bool
  encode_ne_empty : ∀ v, isDefault v = false → encode v ≠ ByteArray.empty
structure Trie (K V : Type) [Ord K] where
  secured : Bool
  default : V
  data : Std.ExtTreeMap K V                 -- invariant: no default values stored
def trieSet [TrieValue V] (t : Trie K V) (k : K) (v : V) : Trie K V
def trieGet (t : Trie K V) (k : K) : V
def copyTrie (t : Trie K V) : Trie K V := t
def prepareTrie [TrieValue V] [KeyBytes K] (t : Trie K V) : m (Std.ExtTreeMap Nibbles ByteArray)  -- internal
def root [TrieValue V] [KeyBytes K] (t : Trie K V) : m Hash32

-- public: node DB and partial trie
structure NodeDB where
  map : Std.HashMap Hash32 ByteArray        -- read-only after build
def NodeDB.Authentic (H : ByteArray → Hash32) (db : NodeDB) : Prop :=   -- F4: a predicate, not a field
  ∀ h b, db.map[h]? = some b → H b = h
def NodeDB.build (entries : Array ByteArray) : m NodeDB       -- keys through the oracle; Authentic keccak256 at Id

structure Enc where                         -- immutable cached encoding (C18)
  rlp : ByteArray
  hash? : Option Hash32                     -- some iff rlp.size ≥ 32
inductive Node
  | leaf (path : Nibbles) (value : ByteArray) (enc : Enc)
  | ext (path : Nibbles) (child : Node) (enc : Enc)
  | branch (children : Array (Option Node)) (value : ByteArray) (enc : Enc)   -- size 16, stated separately (F5)
  | hashed (h : Hash32)                     -- unresolved stub (EELS HashedNode)
abbrev Ref := Option Node                   -- none = empty; inline vs hashed is a property of Enc (B3; provenance, DISC-003)
def Node.WF : Node → Prop                   -- every branch has exactly 16 children, plus the §6 invariants
def childRef : Ref → RlpItem                -- C18: "" · stub hash · cached hash · inline RLP item
inductive Malformed | rlp | nonEmptyString | compactEmpty | pathEmpty | badListLength (n : Nat) | refLength (n : Nat)
  | extChild | occupancy (n : Nat) | cycle
inductive TrieError | missingRoot (h : Hash32) | malformed (why : Malformed) | unresolved (h : Hash32)

-- smart constructors (the only way ops build nodes; internal but with public laws).
-- They compute Enc, which may hash, so they are monadic (F4).
def mkLeaf (path : Nibbles) (value : ByteArray) : m Node
def mkExt (path : Nibbles) (child : Node) : m Node          -- merges ext/leaf children (C24)
def mkBranch (children : Array (Option Node)) (value : ByteArray) : m (Except TrieError Ref)  -- size 16; collapse, C25

-- decoding and lookup are pure (F4); builds, updates, deletes and root hashing are monadic
def decodeRoot (emptyRoot : Hash32) (db : NodeDB) (r : Hash32) : Except TrieError Ref   -- eager, C13–C17
def lookup (t : Ref) (key : Nibbles) : Except TrieError (Option ByteArray)             -- C20
def update (t : Ref) (key : Nibbles) (value : ByteArray) : m (Except TrieError Ref)    -- C23, value ≠ empty
def delete (t : Ref) (key : Nibbles) : m (Except TrieError Ref)                        -- C24–C25
def rootHash (emptyRoot : Hash32) (t : Ref) : m Hash32                                 -- C27

structure IncrementalMPT where secured : Bool; root : Ref
def decodeWitnessToMpt (emptyRoot : Hash32) (db : NodeDB) (r : Hash32) (secured : Bool) : Except TrieError IncrementalMPT
def mptSet (t : IncrementalMPT) (key : ByteArray) (encoded : Option ByteArray) : m (Except TrieError IncrementalMPT)  -- hashes the key iff secured
def mptRoot (emptyRoot : Hash32) (t : IncrementalMPT) : m Hash32

-- host-side (public, not on the guest path; C28)
def buildMpt (t : Std.ExtTreeMap Nibbles ByteArray) : m Ref
structure Witness where accessedNodes : Std.HashMap Hash32 ByteArray
def mptGetRecording (t : Ref) (key : Nibbles) (w : Witness) : Except TrieError Witness

-- proof-level (public definitions, may be unfolded); stated at m := Id, concrete keccak256
def Canonical : Ref → Prop
def canonTrie (m : Std.ExtTreeMap Nibbles ByteArray) : Ref       -- patricialize as Nodes
def represents (t : Ref) (m : Std.ExtTreeMap Nibbles ByteArray) : Prop   -- t is a pruning of canonTrie m
def collisionWitness (db : NodeDB) (m) : Option (ByteArray × ByteArray)  -- computable
```

Mapping of `incremental_mpt.py` items: `MutableLeafNode`/`MutableExtensionNode`/`MutableBranchNode`/`HashedNode`/`MutableNode` → `Node`/`Ref`; `IncrementalMPT` → `IncrementalMPT` (the flat `_data` is dropped: it is unused on the guest path, C21); `_encode_mutable_node`, `_encode_mutable_node_to_extended`, `_compute_node_hash_and_rlp`, `_invalidate_hash` → `Enc` construction and `childRef`; `mpt_set`, `_mpt_insert_node`, `_insert_into_leaf`, `_create_branch_from_two_leaves`, `_insert_into_extension`, `_split_extension`, `_insert_into_branch` → `update`/`mptSet`; `_mpt_delete_node`, `_delete_from_extension`, `_delete_from_branch`, `_collapse_branch` → `delete`/`mkBranch`/`mkExt`; `mpt_root` → `mptRoot`; `compact_to_nibbles` → `compactToNibbles`; `_resolve_child_ref`, `_decode_witness_node`, `decode_witness_to_mpt` → `decodeRoot`/`decodeWitnessToMpt`; `_build_mutable_tree`, `build_mpt` → `buildMpt`; `Witness`, `_record_witness`, `_mpt_traverse_for_witness`, `mpt_get` → `Witness`/`mptGetRecording`.

## 6. Data structures

| Type | Representation | Model | Abstraction | Invariant | Persistence | Complexity |
|---|---|---|---|---|---|---|
| `Nibbles` | `ByteArray` with bound proof | `List (Fin 16)` | `toList` | every byte `< 16` | value | generate O(n) plus callback; slice O(k) copying; compare O(1+common prefix); source bounds only (Q49) |
| `Trie K V` | `ExtTreeMap K V` | finite map with default | `trieGet` | no default values stored | value | O(log n) |
| `NodeDB` | `Std.HashMap Hash32 ByteArray` | finite map | `get?` | `NodeDB.Authentic keccak256` (established by `NodeDB.build` at `Id`; a predicate, not a field, F4) | built linearly, then **read-only shared** | build expected O(n) plus one keccak per entry; lookup expected O(1) (not worst-case; ARCHITECTURE §5.0) |
| `Node`/`Ref` | inductive with immutable `Enc` per resolved node | a set of maps (`represents` is a relation, D25) | `represents` | `Enc` agrees with C18/C19; ext child is a branch or stub; every branch has exactly 16 children (F5) and occupancy ≥ 2 | functional; tries are not snapshot-reachable (built once per root computation), so path copying suffices | lookup O(d) node steps (d ≤ 64 branch levels for secured keys) plus path comparisons; update/delete O(d) nodes rebuilt, each with one RLP encoding and ≤ one keccak; `rootHash` O(1) (cached at the root) |
| DAG decode memo (DISC-004, B15; not the per-root storage-trie memo of `EthStateWitness`, F6) | `Std.HashMap Hash32 (Except TrieError Node)` threaded linearly during one `decodeRoot` | partial function on hashes | memo consistency (Nipkow Ch. 18) | an entry equals the unmemoised decode of that hash | linear-only | total decode O(Σ distinct reachable entry sizes + keccak) instead of EELS's path-expanded cost |

NodeDB reuses EthBase's Q51 Hashable Hash32 support and existing actual-equality
laws (EthBase §3). Public Std map laws supply insertion/lookup, distinct-key
preservation and equal-key overwrite without a distinct-support-hash premise.
C12 construction and concrete authenticity are supplied by the implementation
rows in §3; Keccak keys come from KeccakQuery (D5/F4). Expected table bounds remain
conditional on a suitable distribution; adversarial-distribution, allocation and
composed cost measurements remain open (ARCHITECTURE §5.0, C1–C4).

Computing `Enc` strictly in the smart constructor re-hashes the whole path on every update (O(u·d) keccaks for `u` updates), whereas EELS hashes each dirty node once at root time. Either is correct; the choice is internal to this module (DECISIONS B15, Q33) and still open.

## 7. Contract and laws

### 7.0 Pure path laws

`Nibbles.length_toList`, `getElem_toList` and `get_lt` supply abstraction
length/index/range; `toList_inj`/`ext` supply extensionality. `toList_ofList`,
`size_ofList` and `ofList_toList` supply the model construction boundary.
The operation models (`bytesToNibbleListModel`,
`nibbleListToCompactModel`, `commonPrefixLengthModel`) are legible finite-list
references beside packed implementations with ordinary all-input equations.
The per-operation laws are named in §3. `nibbleListToCompact_pair` exposes
indexed pair observations through the encoder model without exposing its storage.
Prefix `_take_iff` has explicit
`k ≤ a.size` and `k ≤ b.size` hypotheses; `_maximal` requires the result strictly
below both sizes and states that the next bounded digits differ. Compact
`_flag` is `2*leaf + parity`; `_first` distinguishes even zero padding from the
odd first digit.

`compactToNibbles_eq_model` preserves the entire result, including Q48's exact
empty diagnostic. `_error_iff` states that raw empty input is the sole failure;
`_success_iff` states every nonempty input succeeds. `_ok_iff`, `_size`, `_leaf`
and `_get` characterize exact values, length, flag and ordered digit observations.
`compactToNibbles_index_lt` supplies the decoded byte-index bound to callers.
`compactToNibbles_nibbleListToCompact` recovers every bounded path and both leaf
flags; `nibbleListToCompact_inj` derives canonical path/flag injectivity through
this inverse. `compactToNibbles_normalization` preserves the accepted decoded
value upon canonical reencoding. `nibbleListToCompact_decode_eq_iff` states byte
identity exactly on the canonical encoder image. Arbitrary accepted wires do
not have a byte-identity inverse: `0f → 00`, `2f → 20` and `f123 → 3123`.

The splitter and encoder each generate a single packed output in linear byte
steps; prefix comparison performs at most the shorter path length in packed
steps and stops early on mismatch. `toList` allocates its mathematical list;
`ofList` copies digits once. `Nibbles.generate` models `(List.range n).map f`; callback
congruence requires agreement only at indices below `n`. `extract` models
`(x.toList.drop start).take (stop-start)` and has size `min stop x.size-start`. `take`
and `drop` model List prefix/suffix copies, with all-input size/get and composition laws
in §3. Guarded natural bounds precede `ByteArray.extract`; these operations copy
surviving digits rather than retaining a view. Comparison scans packed digits directly,
then compares sizes only after the shared prefix; `compare_toList` establishes
lexicographic order, and lawful Std instances plus `compare_eq_eq_iff` prevent distinct
model keys from aliasing in maps. List references occur only in models/proofs, not
executable generation/slicing/order. Strict remaining-length support has explicit
starting-level and positive-advance hypotheses; bounded path-prefix equivalence retains
both size bounds. These are source-structure bounds, not allocation/throughput
measurements or completed resource gates. The decoder's temporary digit and byte Lists
plus packed copy are linear in decoded length; no fusion or single-allocation claim is
made (DEBT-COMPACT-DECODE). Q50's actual finite-map domain, ending-key/branch
lookup laws and private extension/child strict sum support are discharged in
`Root.lean` (§3). Root adds private longest shared-prefix selection and its
ordinary domain/maximality/member-independence support there, alongside bounded
private full-key partition/decomposition and ordered supplied-callback/C6 branch
support with explicit lawful sequencing and original first-callback-error laws (§3).
The constructor
still owes actual C7–C8, canonicality, whole-constructor choice independence and aggregate
copying/comparison costs.
Repeated full suffix copies can be quadratic; key cursors and node-path-only copies are
a possible consumer design, not an implemented performance claim. A consuming change
must assess aggregate copying/comparison costs and record any justified performance
exception in [DEBT](../DEBT.md) under D18.

### 7.0.1 Internal-node operational laws

C6's assembly and full RLP model equations are unconditional on typed inputs.
`encodeInternalNode_eq/inline/hash/recording` expose zero/one exact whole query;
`_of_pure_answer` retains the complete arbitrary answer and `_id` supplies concrete
execution. `run_encodeInternalNode_exceptT/stateT/error` preserve underlying
computations, added state and original errors, with `LawfulMonad` where bind laws
are needed. These local equations discharge no global oracle coupling (D5).
The standard-domain iff laws require the complete assembled structure, including
HP width and joined payload. The branch positions and value-last law preserve
arbitrary nested items. No child reference validation or recursive child hash is added.

### 7.0.2 Raw database laws

C12's implemented public laws are listed in §3. `build_eq_reference` holds for
arbitrary Monad/KeccakQuery instances; ordered reassociation, singleton/push and
transformer laws state LawfulMonad explicitly. `build_id_model`, full lookup and
`authentic_build_id` use the concrete Id interpretation. No injectivity premise is
needed: an overwrite retains a preimage whose own digest is the shared key.
Arbitrary generic answers carry no concrete authentication guarantee.

### 7.1 Totality [T]

- C12 construction is a total finite Array fold, with a total structural List reference/model.

- `compactToNibbles`, `patricialize` (Q50 reachable domain; private Σ remaining full-key lengths support strictly decreases through each child and positive shared extension; actual recursion unimplemented), `encodeInternalNode` (nonrecursive assembly plus total RLP and one monadic query), `lookup`/`update`/`delete` (remaining key length; leaves terminal), `decodeRoot` (lexicographic: DB entries not on the current path, then inline subterm size; ARCHITECTURE §5.4). All are total on arbitrary DBs without collision assumptions.

### 7.2 Per-operation commuting obligations (D25) [C]

The remaining whole-trie laws are stated at `m := Id` (concrete `keccak256`),
where the monadic operations are pure functions; `mathRoot t` abbreviates
`Id.run (mathRoot emptyTrieRoot t)` with the reference constant, and likewise for
`rootHash`, `update`, `delete` and `buildMpt`. Coupling at a generic oracle monad
belongs to `EthSecurity` and remains open (D5).

- `trieGet (trieSet t k v) k' = if k' = k then v else trieGet t k'`; `root t = mathRoot (prepareTrie t)`.
- Invariant preservation: `update`/`delete`/`mkBranch`/`mkExt` preserve `Canonical` and the `Enc` rule.
- Simulation for the **root-compatible** abstraction relation (which includes canonical encoding/commitment compatibility, not just matching lookups): `represents t m → update t k v = .ok t' → represents t' (m.insert k v)`; `represents t m → delete t k = .ok t' → represents t' (m.erase k)`; `represents t m → lookup t k = .ok r → r = m[k]?`; `represents t m → rootHash t = mathRoot m`. No collision assumption is needed for these: they are structural, because the smart constructors mirror `patricialize` (Nipkow et al. Ch. 12 `nodeP` pattern).
- `rootHash (canonTrie m) = mathRoot m`; `represents (buildMpt m) m`.

### 7.3 Canonical form and order independence [C]

- `Canonical (canonTrie m)`; `Canonical t ∧ Canonical t' ∧ (∀ k, lookup t k = lookup t' k) ∧ no stubs → canonicalSerialization t = canonicalSerialization t'` (representation/cache identity is not required) (Exercise 12.1).
- `patricialize` does not depend on the choice of "arbitrary key": the Lean definition uses the minimum key and a lemma shows every choice gives the same node.
- **Order independence of successful roots:** under the canonical representation/encoding hypotheses, if two update sequences from `t` both succeed and produce the same final map `m'`, both roots equal `mathRoot m'`. This does not cover arbitrary accepted noncanonical witnesses: C19 gives a no-op deletion that changes the root. There is no general licence to reorder witness updates.

### 7.4 Trie agreement theorem (collision-reporting form) [C], feeds [S]

After Kestrel ACL2 `mmp-trees.lisp` and Miller et al. (ARCHITECTURE §5.4):

```lean
theorem decode_agreement (db : NodeDB) (r : Hash32) (t : Ref) (m)
    (hauth : db.Authentic keccak256)
    (hdec : decodeRoot emptyTrieRoot db r = .ok t) (hroot : mathRoot m = r) :
    represents t m ∨ ∃ x y, collisionWitness db m = some (x, y) ∧ x ≠ y ∧ keccak256 x = keccak256 y
```

The collision pair consists of a DB entry (or an inline subterm) and a node encoding of `canonTrie m` at the same position. It also covers every non-canonical acceptance of C16: a non-canonical node under a root equal to a canonical root is a collision. The composed statement for a root computation is: `decodeRoot` then a successful `mptSet` sequence yields `mathRoot (m.applyAll ops)` for **every** `m` with `mathRoot m = r`, or a computable collision.

### 7.5 Data availability (progress) [C]

- `lookup t k` fails iff the walk for `k` reaches a stub; `update` fails iff the insertion path reaches a stub; `delete` fails iff its path reaches a stub or a collapse leaves exactly one child that is a stub. For a pruning `t` of `canonTrie m`, "all nodes on the path of `k` resolved" implies success of `lookup`/`update`; for `delete` additionally "the sibling of every collapsing branch resolved". Authenticated absence (a mismatching leaf or empty child on a resolved path) is success.
- Conjectures to settle: success of an insert-only (resp. delete-only) sequence is independent of its order.

### 7.6 Caches [C]

- Memoised `decodeRoot` equals a mathematical, cycle-detecting traversal on every finite DB, including off-path malformed nodes. On cycles both reject; diamond sharing is not a cycle. Agreement with Python additionally requires host-resource compatibility: its unmemoised recursion is not a total mathematical definition.
- `Enc` cache: for resolved nodes built by smart constructors, `enc` is the encoding of the fields; for decoded nodes, `enc.rlp` is the DB bytes and, given `NodeDB.Authentic keccak256`, `keccak256 enc.rlp = h` when referenced by `h` (ARCHITECTURE §5.4 "[C] a decoded node's hash equals its reference").
- [R] Exact reproduction of C18/C19 on non-canonical witnesses is a conformance obligation (checked by the adversarial `#guard`s against EELS), not a theorem about the model.

### Informal correctness argument

**Claim.** Canonical full tries implement the mathematical finite-map root, while witness operations reproduce the reference's lenient decoding, cached raw encodings and ordered incremental updates on every successful path.

**Premises.** Codec/hash equations; explicit distinction between canonical representations and accepted raw witness representations; finite graph traversal with cycle detection; available sibling nodes when collapse requires them.

**Argument.** Induct on remaining key length for canonical construction and lookup. Extension/branch/leaf cases partition keys; smart constructors compress precisely the empty and single-child cases. For incremental updates, the same cases prove lookup preservation and the new value at the updated key. A collapse onto a stub must resolve that stub or fail, which explains order-dependent success. Witness decoding uses visiting/finished states: a visiting edge rejects a cycle; a finished edge reuses its decoded node without changing its raw encoding. Preserve the source encoding of unchanged nodes and re-encode only dirtied paths. Consequently canonical root uniqueness and successful update order independence apply only under canonical-representation hypotheses. They are false for general accepted witnesses: even a no-op delete can canonicalise an accepted noncanonical leaf and change its root.

**Open obligations.** Define canonicality separately from lookup agreement, prove cached-encoding and memoization refinement, and resolve host RecursionError differences. Hash-relative full-root folding also needs an explicit secure-key collision/order convention. Totality must not assume hash injectivity.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthCodec`
- **Used by:** `EthStateCommit` (state and storage tries), `EthBlock` (transaction, receipt and withdrawal roots through `Trie`/`root`), and transitively `EthStateFull`, `EthStateWitness`, `EthSecurity`.
- **Pure path seam:** the public bounded List abstraction and the path equations/laws of §7.0 supply digit order, canonical compact output, lenient decoding and maximal prefix comparison; future node/trie consumers still own their contracts.
- **Seams provided:** C12 `NodeDB.build`/`Authentic` and ordinary query/model/Id laws (§3); the following trie seams remain unimplemented: `mathRoot` (the definition roots are compared with), `decodeRoot`/`lookup`/`mptSet`/`mptRoot` (the partial trie behind the witness backend; replacement exercise 2 replaces exactly this), `represents` and the agreement theorem (for `EthStateCommit` and `EthSecurity`).
- **Relies on:** `EthCodec`'s strict RLP decode, its round-trip `encode (decode b) = b`, and RLP injectivity/prefix-freeness (for the collision theorem's reduction); every keccak through `EthHash`'s `KeccakQuery` (reached through `EthCodec`; D5), with its `ExceptT`/`StateT` lift instances (F15) and concrete `keccak256` at `Id`; `HashConsts.emptyTrieRoot` supplied by the caller (C5).
- **Guarantees:** totality; the laws of §7; key sequencing is the caller's responsibility (C26).

## 9. Open decisions

- D4: keccak dominates decode/root cost; the reference or a proved fast path.
- D5 (broad scope, monad-parametric): `NodeDB.build`, the smart constructors, `update`/`delete`, root hashing and `mathRoot` go through `KeccakQuery`; decoding and lookup stay pure; `NodeDB.Authentic` is a separate predicate; the empty-trie root is `HashConsts.emptyTrieRoot` (F4, C5, C12, C13). Open: coupling at generic `m`.
- D16, D20 (accepted): generic over bytes; `encode_account` stays outside.
- D18: HashMap expected bounds for `NodeDB` and the memo.
- D19 (accepted): eager decoding; the memo is the permitted internal laziness only in the sense of sharing, with the proof of §7.6.
- D25 (accepted): `represents` as the abstraction relation.
- Q50: the explicit reachable-domain proof and supplied-empty-root interpretation follow C7/C8/§5; domain/descent support is in §3, while actual constructors and source agreement remain open.
- Q49: bounded construction, clipped copies and lawful ordering use the exact provider equations in §3/§5/§7.0; root domains and decoder allocation replacement are separate.
- Q48: raw empty compact diagnostic ownership is distinct from the later empty decoded extension-path failure; C3/§5/§7 specify the seam.
- NEW-COMMIT-1: DECISIONS B3 (Q32): `Ref` hidden behind the trie API; `Option Node` only if it keeps the provenance DISC-003 needs (open: not yet tested).
- NEW-COMMIT-2: DECISIONS B15 (Q33): internal and interface-neutral; strict versus lazy `Enc` still open (§6).
- NEW-COMMIT-3: DECISIONS B3 (Q34) and DISC-003: reproduce the reference's non-canonical acceptances (C16, C19); a deviation needs an accepted decision record.
- NEW-COMMIT-4: DECISIONS B15 (Q35) and DISC-004: memoised decoding needs a proof that it preserves accept/reject, error precedence and observations (§7.6); host-resource interaction is DISC-001 (O12 unresolved).

## 10. Gaps

- **Implemented slice:** C12 raw construction, ordered reference/model laws, full last-write lookup and concrete Id authenticity (§3). Decoder/root/cache/security composition and generic oracle coupling remain open; the finite complete-map and sibling tests do not discharge C1–C4 or R4.

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **Non-canonical acceptance** (C16, C19) is verified only on hand-made examples; no fixture exercises it, and upstream has not been asked whether it is intended. The `0x80` flip (C16(f)) means "extra unused entries are harmless" is false in general.
- **Pure decoding and the inline-node hash** (F4 vs C14/C18): decoding is pure, so a decoded node cannot compute a hash. A DB entry takes its reference as its cached hash (sound under `NodeDB.Authentic`), but an inline subterm of 32 bytes or more (C16(b)) has no reference, and the reference hashes it during decoding. Where that hash is computed (through the oracle when the node is first re-encoded or rooted, as a lazy `Enc` would, or in a monadic decoding step) is open (B15).
- **Exponential decode on DAG witnesses** (C17) is recorded in DISC-004; the reviewed memoized decoder still needs a refinement proof and resource-acceptance policy. It interacts with DISC-001 and with any guest cycle budget.
- **Inline witness interpretation:** compose the proved `Rlp.encode_eq_of_decode_eq_ok` and `decode_success_encodable` contracts (EthCodec §7) at C15. Raw-codec reencoding is supplied; proving which decoded subterms represent accepted witness children, and preserving their provenance/caches, remains open.
- **Order-sensitivity conjectures** (§7.5) are unproved; the mixed-order counterexample is verified.
- **No proof strategy yet** for `decode_agreement` in detail: the definition of `collisionWitness` (which pairs are compared, how inline subterms are included) and its computability need a design; Kestrel's `mmp-trees.lisp` is a shape, not a proof to port. Cassez (FM 2021) is precedent for incremental-equals-scratch only.
- **`patricialize` choice-independence** and the Canonical-uniqueness lemma for a hexary trie with branch values and variable-length keys (unsecured tries) have no existing Lean proof; the Nipkow chapter is binary.
- **Internal-node scope:** C6 operational/model/lift laws are proved as in §3/§7.0.1. Complete standard-domain and Python Extended interpretation/host premises remain caller obligations. Root/patricialization/witness/cache/database laws, canonical trie-shape conditions and resource gates remain open. Empty extension paths and arbitrary nested fields are valid C6 inputs; witness validity is a separate contract.
- **Pure path scope:** the `Nibbles` representation/invariant, implemented pure path operations and Q49 bounded generation/clipped copies/lawful order are discharged as in §3/§7.0. Q50 domain/strict sum-descent support is discharged in §3. Private longest shared-prefix selection and its domain/maximality/representative laws, and bounded private branch partition/ending/callback-C6 sequencing support, are supplied in §3. Actual C7–C8, trie mutation/integration, aggregate copy/allocation costs and C1–C4 measurements remain open; slices copy O(k).
- **Compact decoding scope:** Q48's empty diagnostic, lenient value model, canonical inverse/injectivity and accepted-wire normalization are discharged in §3/§7.0. The later extension-path rejection, diagnostic adapters to witness/guest channels and whole-node/trie/W1 proof remain unimplemented. Allocation replacement belongs to DEBT-COMPACT-DECODE; no arbitrary accepted-wire byte identity is claimed.
- **Additional Nibbles interfaces:** future consumers use the supplied equality and lawful ordering in §3/§7.0. Any additional default-value or container-specific interface remains a scoped consumer obligation behind the private storage boundary.
- **Unsecured-trie key properties:** the transaction/receipt/withdrawal tries use RLP-encoded indices as keys; whether they are prefix-free matters only for the branch-value case of `patricialize` and is not checked here.
- **`TrieValue` for `EthBlock`'s value types** (transactions, receipts, withdrawals; `encode_node`'s `Bytes` identity versus RLP) must be instantiated by `EthBlock`; this spec only fixes the class.
- **Host-side items** (C28) are specified at reduced depth; whether they belong in `STFSpec/informal/EXCLUDED.md` (G6) instead is undecided.
- **EEST coverage** of witness malformations is thin: `eip8025_optional_proofs` covers missing nodes and extra nodes, not malformed RLP, bad node shapes, cycles or non-canonical encodings; the EELS unit tests cover node shapes only.
- **`Std` caveats:** `ExtTreeMap` has no proved cost bounds; `HashMap` bounds are expected only, and adversarial key distributions for `NodeDB` are unmeasured (keys are keccak outputs, so this is mostly moot, but the memo is keyed the same way).
