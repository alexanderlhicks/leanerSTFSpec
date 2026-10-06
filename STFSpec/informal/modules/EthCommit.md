# `EthCommit`: Merkle Patricia tries over bytes — mathematical root, witness decoding, partial trie, incremental root

*Status: informal specification, draft. Date: 2026-10-06. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F4, F5, F16, F19, F20 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D4, D5, D16, D18, D19, D20, D25 · questions: B3 (Q32/Q34), B15 (Q33/Q35), Q48, Q49, Q50, Q51, Q52, Q53, Q54, Q55, Q59; DISC-001, DISC-003, DISC-004.*

Abbreviations: `mpt:` = `merkle_patricia_trie.py`, `inc:` = `forks/amsterdam/incremental_mpt.py`, `ws:` = `forks/amsterdam/witness_state.py`. "[verified]" = read in the pinned source; "[executed]" = additionally run against the pinned EELS with `ethereum_rlp`/`ethereum_types` from the pinned environment; "[inference]" = argued, not tested.

## 1. Purpose

`EthCommit` is the commitment layer (ARCHITECTURE §2, L1). It defines the hexary Merkle Patricia trie **generic over encoded keys and values** (`ByteArray → ByteArray` maps): nibbles and hex-prefix encoding, node types and their encoding, the mathematical root (`mathRoot` with `patricialize`), a typed trie-with-default used by `EthBlock` for transaction/receipt/withdrawal roots, the read-only node database, **eager** witness decoding (D19), the partial trie with hashed stubs, lookup/update/delete, and the incremental root. It knows nothing about accounts (D16, D20): account and storage encodings and the state root are in `EthStateCommit`.

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
- C9. `_prepare_data` (`mpt:407–448`): encode each stored value once (`encode_node`, C10); stored `None` fails before encoding (`:435`), and exact empty encodings fail next (`:439`); only then hash a key if `secured` and convert it to nibbles. No stored default or invalid value is filtered. Q53 supplies the separate `Trie.PrepareSafe` proof from `TrieValue.Valid`; `NoDefault` does not supply it. The initial typed preparation/root domain is explicitly `secured = false`; secure traversal, collisions and source-history coupling remain open (§7).
- C10. `encode_node` (`mpt:252–269`) dispatches: `Account` → `encode_account` (owned by `EthStateCommit`, needs the per-address storage root/callback); `Bytes` → identity; otherwise `rlp.encode`. `TrieValue.encode` is total on Lean values, with source agreement only on concretely interpreted valid supported non-`None` values (§7.0.3). EthBlock owns its actual transaction/receipt/withdrawal encodings. A bare `Account` has no context-free instance supplied by this contract.
- C11. The typed trie (`mpt:274–347`): a map with `secured` and an arbitrary supplied `default`; `trie_set` compares by lawful value equality with that default and **erases** on equality, otherwise inserts without encoding, validity checks or hashing (`:334–338`). `trie_get` returns the default when absent; `copy_trie` is a shallow copy (identity on a persistent Lean map). Setters preserve `NoDefault` when it holds, but may retain invalid nondefault values; preservation of `PrepareSafe` has the exact iff in §7.0.3. EthBlock's three tries are unsecured with default `None` (`forks/amsterdam/vm/__init__.py:107–117`); their root calls (`fork.py:351–354`) must compose preparation with C8 using the supplied F20 empty root.

### 2.3 Node database and eager decoding (D19; CONTRACT O4)

- C12. `build_node_db` (`ws:37–42`) keys every witness entry by `keccak256(entry)`, folding in input order with **last entry wins**. In Lean `NodeDB.build` hashes through the oracle (monadic, D5/F4), so authenticity is the separate predicate `NodeDB.Authentic H db` (every entry `b` under `h` has `H b = h`), which `NodeDB.build` establishes at `m := Id` with `H := keccak256`. Repeated identical entries are harmless; different entries with the same digest must preserve last-write behaviour and yield a collision in the security proof. Extra entries are allowed (fixture `test_validation_state_extra_unused_trie_node`), subject to C16(f).
- C13. `decode_witness_to_mpt db r` (`inc:994–1040`): if `r = EMPTY_TRIE_ROOT`, the empty trie **without consulting the DB** (`inc:1024–1030`); else `db[r]` (missing → `KeyError`, O4(a)) and decode it. Q55 makes complete decoding a generic `KeccakQuery` action: `decodeRoot emptyRoot db r`, with the caller's existing `HashConsts.emptyTrieRoot` (F20). Empty-root bypass returns `pure (.ok none)` without DB lookup or local query; missing root returns the existing typed error without a local query. The wrapper only packages a successful root with `secured`, preserving decoder effects and failures.
- C14. `_decode_witness_node bytes` (`inc:917–991`), in this order: compute `keccak256(bytes)` iff `len ≥ 32` (cached, C18; Q55 requires exactly one `KeccakQuery` on the complete newly entered raw preimage before whole RLP parsing, retaining its actual answer verbatim; an incoming DB key never supplies that answer); RLP-decode (failure → O4(b)); a byte string must be empty (→ empty node) else malformed; a list of length 2: first item must be a string (list → `.malformed .compactPathList` at `inc:946`, Q52), then `compactToNibbles` (C3); **leaf**, only after successful compact decoding with the leaf flag: the second item must be a string (list → `.malformed .leafValueList` at `inc:951`, Q52) (any value, including empty [executed]); **extension**: path must be non-empty, child resolved by C15 must be a branch **or an unresolved stub**; a list of length 17: resolve the 16 children, value = item 16 if it is a string, **otherwise the empty value** [executed]; require `occupied ≥ 2` where stubs count as occupied and the value counts iff non-empty; any other length is malformed.
  Whole RLP decoding at `inc:936` must succeed before either field-shape check; malformed second fields or trailing bytes therefore win over Q52. Raw empty compact bytes fail with `compactEmpty` before interpreting item 1, while an empty decoded extension path fails with `pathEmpty` before child resolution. A descendant failure propagates unchanged through `inc:960` before the parent child-kind check at `:961`. Branch item 16 remains lenient; `leafValueList` belongs only to a two-item leaf. The complete C14 dispatcher is implemented in §3; WitnessError/guest adapters remain unimplemented.
- C15. `_resolve_child_ref` (`inc:892–914`): an empty string → no child; a string of length ≠ 32 → malformed; a 32-byte string present in the DB → decode that entry (recursively, eager); absent → an **unresolved stub** `HashedNode h` (not an error); an inline list → decode `rlp.encode(list)`.
- C16. **Accepted non-canonical encodings** [executed; each reachable only with a trie that no canonical state produces]: (a) hex-prefix flag bits 2–3 set or a non-zero padding nibble (C3); (b) an inline child whose RLP is ≥ 32 bytes (it is then given a cached hash, C18); (c) a hash reference to a DB entry shorter than 32 bytes; (d) a branch value that is a list (read as empty); (e) a leaf with an empty value or a path whose length does not match its depth; (f) a child reference equal to `EMPTY_TRIE_ROOT`: if the DB contains the entry `0x80`, it decodes to **no child**, otherwise it is a stub — so adding the "unused" entry `0x80` can turn an accepted witness into a rejected one (occupancy drops below 2) [executed]. The Lean decoder must reproduce these outcomes exactly (P2), and the agreement theorem (§7.4) covers them through its collision disjunct.
- C17. **Cycles and sharing.** EELS recurses without a visited set: a reference cycle ends in `RecursionError`, caught as `false` (O12, classified O4 by CONTRACT); the Lean decoder tracks the hashes on the current path and returns `malformed` on a repeat. A DB built by C12 can contain a cycle only through a Keccak fixpoint chain, which cannot be ruled out in Lean without an assumption, so totality needs the check (ARCHITECTURE §5.4). A **shared** hash reached along two paths is decoded twice by EELS; on a DAG-shaped witness this is exponential in depth (16 identical children per level) [inference from `inc:892–914`]. Memoising completed, validated decodings must preserve mathematical decoding and raw encodings (§7.6). This is the DAG memo of DISC-004/B15, internal to one `decodeRoot`; it is not the per-root storage-trie memo of `EthStateWitness` (F6, open). Q55's mathematical traversal baseline has no completed-node memo: repeated sibling references are distinct occurrences. B15 does not select a memo here; effect suppression, shared stateful answers and path-dependent cached failures require explicit refinement premises. Its effect on host-resource acceptance requires D14/O12 treatment. Deep acyclic chains can exceed Python's recursion limit in EELS: the guest-process limit is 100,000 (py_ecc raises it; 12,288 applies only after `import ethereum`), and the witness-chain depth at which the reference fails has not been re-measured under it (DISC-001, O12 unresolved).
- C18. **Cached encodings.** A decoded node keeps its original bytes and, iff they are ≥ 32 bytes, their hash (`inc:932–934`, `:955–956`, `:967–968`, `:986–988`). When a parent is re-encoded, a child's reference is (`_encode_mutable_node_to_extended`, `inc:287–313`): empty → `b""`; stub → its hash; an unmodified node with a cached hash → that hash (**not** recomputed, even if non-canonical); otherwise the node is re-encoded from its fields (C6 rules: `< 32` bytes inline, else hash).
- C19. **Visited nodes lose their cache.** Every node on the path of an update or delete is invalidated (`_invalidate_hash`, `inc:231–237`, called at `:490` and `:694`) — including nodes that end up unchanged, such as a mismatching leaf in a no-op delete — and is then re-encoded from its fields. Off-path nodes keep their cached encoding. For a non-canonical witness this makes the root after a **no-op delete differ** from the pre-root [executed]. A functional implementation achieves this by rebuilding every visited node through the smart constructor and must **not** short-circuit "unchanged" subtrees to the original node.

### 2.4 Lookup (guest path)

- C20. `_trie_lookup root keyHash` (`ws:53–100`) is pure tree lookup; guest callers (`ws:148–205`) supply a Hash32 split into 64 nibbles and own hashing, root decoding/caching and later leaf decoding/defaults. Q59 preserves a total `lookup` on every finite bare Ref/Nibbles input: none → absence; stub → `.unresolved h` before key exhaustion; leaf → its complete value, including empty as present, iff its complete path equals the remaining key; extension → compare its complete path to the clipped remaining prefix and descend/drop path length only on match, including empty paths and ext-to-leaf/ext; terminal branch → nonempty value or absence before child bounds; nonterminal in-bounds branch → exactly the selected child/drop1. Only a reached out-of-range selected slot returns `.malformed (.branchIndex i children.size)`, where `i < 16` and `children.size ≤ i`. No size16/occupancy/cache/WF check, out-of-range-slot absence, off-path scan or normalization enters lookup. Raw/cache fields are ignored and unconstrained. The source invalid list access has a defined IndexError; the typed adaptation is Q59's disposition, not a demonstrated guest outcome. Source value/stub correspondence uses valid selected accesses and explicit actual Hash32-to-64-nibble/source-class/host premises; odd generalized Nibbles are governed by Lean equations, not direct byte-entry observations. Structural proper-child Node-size descent handles matched empty extensions without requiring key consumption; the local operation/proofs are supplied in §3.
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

- C29. Typed decoding, lookup and update diagnostics use `TrieError`. A witness/guest adapter projects only its established reachable failures through `WitnessError` under CONTRACT O4/O13; a bare helper diagnostic alone establishes neither block reachability, first handler nor output. In particular Q59's selected-slot diagnostic is separate from unresolved-stub O4(c) and downstream-leaf O4(e); output bytes are unchanged. Q55 forwards underlying query-monad failures unchanged, without converting them to a decoder diagnostic or adding an outcome projection; the caller owns any later adapter. Preconditions of the mathematical root (C9) are type-level, not runtime failures. No function may depend on host recursion limits (O12, DISC-001; C17); all recursion is structural or on an explicit measure (§7.1).

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
| `merkle_patricia_trie.py::encode_node` | 252 | `TrieValue.encode` | unimplemented Q53 bridge; contextual Account encoding in `EthStateCommit` |
| `merkle_patricia_trie.py::Trie` | 274 | `Trie` | C11 storage discharged below |
| `merkle_patricia_trie.py::copy_trie` | 315 | `copyTrie` | C11 discharged; persistent identity |
| `merkle_patricia_trie.py::trie_set` | 325 | `trieSet` | C11 storage/safety discharged below |
| `merkle_patricia_trie.py::trie_get` | 341 | `trieGet` | C11 discharged |
| `merkle_patricia_trie.py::common_prefix_length` | 350 | `commonPrefixLength` | |
| `merkle_patricia_trie.py::nibble_list_to_compact` | 360 | `nibbleListToCompact` | |
| `merkle_patricia_trie.py::bytes_to_nibble_list` | 395 | `bytesToNibbleList` | |
| `merkle_patricia_trie.py::_prepare_data` | 407 | `prepareTrieModel` | pure unsecured fold discharged below; concrete value bridge remains conditional |
| `merkle_patricia_trie.py::_prepare_trie` | 451 | `prepareTrie` | pure safe/unsecured seam discharged below |
| `merkle_patricia_trie.py::root` | 478 | `root`, `mathRoot` | |
| `merkle_patricia_trie.py::patricialize` | 507 | `patricialize` | |
| `forks/amsterdam/incremental_mpt.py::*` | 50–1040 | `Node`, `Ref`, `IncrementalMPT`, `decodeWitnessToMpt`, `update`/`delete`/`mptSet`, `mptRoot`, `compactToNibbles`, host-side `buildMpt`/`mptGet`/`Witness` | whole file; per-item mapping in §5 |
| `forks/amsterdam/witness_state.py::_trie_lookup` | 53–100 | `lookup` | supplied pure Q59 bare walk/seven equations; source value/stub bridge restricted to valid selected accesses and actual Hash32 keys; typed out-of-range-slot adaptation separate |
| `forks/amsterdam/witness_state.py::build_node_db` | 37 | `NodeDB.build` | |

### Supplied nominal partial-node carriers

`STFSpec/Commit/Node.lean` supplies exactly `Enc`, recursive `Node` with four
constructors, and `Ref := Option Node`, reexported by `STFSpec.Commit`. This is
**type-only support**, separate from nonrecursive encoded `InternalNode` and generic
`Trie`. Existing Nibbles/Hash32 and core ByteArray/Array/Option providers supply the
fields. No deriving, instance, default, hand-written public law or operation is added.
B3/NEW-COMMIT-1 keeps semantic adoption conditional on demonstrating DISC-003
provenance, failure and observation sufficiency; bare carrier clients discharge
none of that gate. Outstanding operation and admission obligations are owned by §10.

| Exact pinned EELS source | Declaration/domain and status | Fields/effects | Errors/admission boundary | Law/client evidence |
|---|---|---|---|---|
| `src/ethereum/forks/amsterdam/incremental_mpt.py:48–81,287–346,932–968,985–988` | `Enc`, `Enc.mk`, `Enc.rlp`, `Enc.hash?`; **supplied carrier** for every finite ByteArray and optional Hash32 | Retain complete raw/cached values; no query/effect | No error or admission API; completed caches do not model every intermediate mutable Python cache state | Private arbitrary full-field projections and both cache-presence choices at widths 31/32/33; no threshold/provenance/hash theorem |
| `src/ethereum/forks/amsterdam/incremental_mpt.py:48–98` | `Node.leaf/ext/branch/hashed`; **supplied recursive carrier** | Exact §5 fields, recursive Node child and Array (Option Node) children; no effect | Arbitrary arity/cache/path/child shape is expressible; constructors supply no decoder acceptance or Node.WF | Private variant discrimination, arbitrary complete-field matches, arities 0/15/16/17 and two-level recursive-array consumers |
| `src/ethereum/forks/amsterdam/incremental_mpt.py:92–98,892–914`; `src/ethereum/forks/amsterdam/witness_state.py:53–100` | `Ref := Option Node`; **supplied alias** | Absence, unresolved stub and present resolved node are distinct; ext child excludes absence | No lookup/child realization/admission/error behavior is implemented | Private Ref consumers distinguish absence/stub/present empty-value leaf; ext-to-leaf/ext controls establish bare expressibility only |

`STFSpec/Conformance/Commit/NodeCallerProofs.lean` imports the public owning module;
all its hand-written support is private. Ordinary kernel proofs check full retention
and structural consumption without a new nested equality/printing instance or
independent executable trie traversal. The compiled declaration audit covers generated
nested-inductive support as well. Field correspondence is not whole source-runtime
refinement. No Python oracle is required for this item, which adds no executable trie
operation. Remaining provenance/admission/operation gates are owned by §10.

### Supplied nominal incremental-trie carrier

`STFSpec/Commit/IncrementalMPT.lean` supplies exactly the §5 guest record
`IncrementalMPT { secured : Bool, root : Ref }`, reexported by `STFSpec.Commit`.
The root uses the existing nominal Ref; every supplied Bool/Ref is retained without
validation, hashing, normalization or a default constructor. This is the existing
§5 guest projection. Semantic representation adoption remains conditional on
B3/NEW-COMMIT-1/DISC-003 provenance, failure and observation sufficiency; field
retention establishes none of that obligation.

The source's omitted flat `_data` follows C21. Omitted `default` follows C22's
caller-owned default comparison and already-encoded Option policy
(`inc:441/452`). Omitted `witness` follows C28/C25: recorded contents are host
support, but collapse calls `_record_witness` (`inc:797`) and its stub assertion
(`inc:245`) remains a required future guest failure. This carrier implements no
such update, recording or collapse operation.

| Exact pinned EELS source | Declaration/domain and status | Fields/effects | Errors/admission boundary | Law/client evidence |
|---|---|---|---|---|
| `src/ethereum/forks/amsterdam/incremental_mpt.py:111–123,1024–1040`; `_data` C21, default C22 (`:441/452`), witness C28/C25 (`:797/:245`) | `IncrementalMPT`, `IncrementalMPT.mk`, `.secured`, `.root`; **supplied nominal carrier** | Exact supplied Bool and Ref; no query/effect | No operation/error/admission API; source default/witness/flat-data fields are outside this guest projection | Private public-import signature and exact-field retention clients: constructor/projections/reconstruction, both flags, absence/stubs and all Node variants; arbitrary arity/raw/cache/ext-child and nested fields |

`STFSpec/Conformance/Commit/IncrementalMPTCallerProofs.lean` supplies ordinary
private full-field clients through the public owner. Only the structure's generated
constructor, projections, eliminators and equations accompany its declaration;
no deriving, instance, public helper or hand-written public law is added. Field
correspondence needs no Python oracle because this item implements no executable
trie operation. Remaining representation/admission/operation gates are owned by §10
and REVIEW §3.

### Implemented pure path operations

The following operations and their public model laws are implemented on the stated typed domains
in `STFSpec/Commit/Nibbles.lean`; compact decoding, internal-node encoding, raw
NodeDB construction and recursive C7/C8 construction are documented below. The remaining
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
Raw database construction is documented separately below. This C6 slice implements
no partial-witness node/cache. Recursive C7 construction and the C8 local root are
supplied below.

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

**External semantics.** `ethereum_rlp.rlp` encode/decode and `Extended` (owned by `EthCodec`): this module relies on decode being **strict** (non-canonical length prefixes and single bytes `< 0x80` wrapped as strings are rejected, truncated input rejected [executed]) and on `Rlp.encode_eq_of_decode_eq_ok` and `decode_success_encodable` ([EthCodec §7](EthCodec.md#7-contract-and-laws)) for successfully decoded bytes. These proved raw-codec laws supply exact reencoding and the Q47 domain; the complete decoder in §3 privately inherits Encodable through actual parsed child membership and reparses the exact inline encoding. Whole accepted-witness representation/source agreement remains an EthCommit obligation. Leading zero bytes inside strings are just bytes. `ethereum_types` `Bytes`, `Uint`, `ulen`, `slotted_freezable` (value semantics only); `copy.copy` in `copy_trie` (shallow; identity in Lean); `utils.hexadecimal.hex_to_bytes` (G1) for the constant.

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
implement the existing §5 type. Complete decoding and pure bare lookup are supplied
in the subsections below; mutation and witness consumers remain unimplemented.

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

### Implemented complete generic decoding (Q55)

`STFSpec/Commit/Decoder.lean` supplies the complete operation pair and its three
public equations. Totality and local operational laws are **discharged**; whole
source refinement, consumer adapters and W1 remain separate obligations. The
committed driver and guards supply scoped decode-side B3/DISC-003 evidence for
non-canonical raw/inline inputs. Root/mutation provenance and failure/observation
refinement remain conditional under B3/NEW-COMMIT-1; this is no full gate closure.

| Exact pinned EELS source | Lean declaration/public type and domain | Success/effects | Ordered failures | Laws and conformance |
|---|---|---|---|---|
| `src/ethereum/forks/amsterdam/incremental_mpt.py:892–991,1024–1033` | `decodeRoot` with `Monad m`, `KeccakQuery m`, supplied `emptyRoot`, arbitrary `NodeDB` and root key; returns `m (Except TrieError Ref)` | Empty-root bypass; complete eager recursive fields and actual occurrence caches; inline lists encode and actually reparse; repeated siblings/DAG occurrences query independently | Missing root before query; actual-key current-path cycle before entry query; eligible raw query before strict RLP, then original C14/C15 depth-first first error; underlying query failures forward unchanged | Public `decodeRoot_empty`, `decodeRoot_missing` require plain Monad; private threshold, raw-entry/path, inline Encodable/subterm, leaf fields, cycle, ordered-children and underlying-failure laws; complete `DecoderGuards` and authenticated acyclic source comparisons |
| `src/ethereum/forks/amsterdam/incremental_mpt.py:994–1040` | `decodeWitnessToMpt`, same generic classes/arguments plus supplied `secured`; returns `m (Except TrieError IncrementalMPT)` | Packages the successful complete root with the exact flag; retains decoder effects and failures | Typed errors map unchanged; underlying monad failures retain their transformer behavior | Public `decodeWitnessToMpt_eq` exposes the literal bind tree with plain Monad; private public-import clients use explicit LawfulMonad for simplification and test full fields, states and both flags |

The private outer recursion decreases the finite list of database keys outside
the current path after inserting an actual present key. The private inner
recursion decreases the actual parsed RLP subterm size, using inherited Encodable
and `Rlp.decode_encode` to prove exact inline reparse identity. These measures and
key enumeration are erased proof support; there is no executed budget, fallback,
completed-node memo, authentication premise or added admission invariant.

`STFSpec/Conformance/Commit/DecoderCallerProofs.lean` uses only the five public
declarations. `DecoderGuards.lean` observes complete recursive fields, all raw/cache
bytes, preimages/answers and retained effects with arbitrary stateful/failing
oracles. Controls include all sixteen earliest branch positions, root-seeded
cycles, diamond/repeated siblings, raw lengths 31/32/33, all C16 cases and the
supplied-empty-root child flip. The complete differential driver authenticates
the original pin/lock, supplied RLP/types raw wheel SHA-256 and size against that
lock, corresponding installed Python bytes and trusted crypto RECORD bytes,
traces unchanged original functions and compares full acyclic source outcomes to
Id and concrete recording-state runs, including each actual returned secured flag.
The interpreter/host and installed crypto RECORD remain trusted inputs. Strict
output framing rejects bool/int confusion, invalid tags/widths and
missing/duplicate/trailing records.

Obtain `ethereum_rlp-0.1.6`, `ethereum_types-0.4.1`, `mypy_extensions-1.1.0`,
`typing_extensions-4.15.0` and the platform-compatible `pycryptodome-3.23.0` wheels
from the corresponding wheel URLs in pinned EELS `uv.lock`; check each raw file's
SHA-256 and size against its lock row. Use a fresh source checkout at the reference
pin and an isolated `.venv` containing those five packages only. Pass the exact
RLP/types wheel paths below; the driver independently rechecks their lock hashes
and sizes and complete installed Python inventories. Create a new external output
directory for each run. Full dependency acquisition via frozen `uv sync --no-dev`
is also supported, with its host/install inputs retaining the shared driver contract.

```sh
EELS/.venv/bin/python -I -B STFSpec/Conformance/Commit/decoder_differential.py \
  --eels EELS --output EXTERNAL.lean --rlp-wheel RLP.whl --types-wheel TYPES.whl
python3 -B STFSpec/Conformance/Commit/decoder_differential.py --self-test
python3 -B -O STFSpec/Conformance/Commit/decoder_differential.py --self-test
```

Finite comparisons supply conformance evidence. They do not prove full witness
agreement, Node.WF/cache bundles, generic action/result-cache lifetime, consumer
Id/error bridges, mutation/root agreement, security, host O12, production costs
or guest readiness. WitnessError/O4 adapters remain unimplemented.

### Implemented decoder field diagnostic declarations (Q52)

`TrieError.lean` implements the two diagnostic declarations. The complete C14
dispatch is supplied in the complete generic decoding subsection above. These
declarations add no acceptance rule or adapter.

| Exact pinned source | Lean declaration/public type and domain | Success/effects | Ordered failure/handler | Support laws | Evidence |
|---|---|---|---|---|---|
| `src/ethereum/forks/amsterdam/incremental_mpt.py:936,944–947` | `Malformed.compactPathList : Malformed`; declaration support only; whole-RLP-decoded two-item node with a list first field | Nominal diagnostic value, no traversal/effect | After whole RLP and arity; before compact decoding; future `TrieError.malformed` → WitnessError → O4, inner `stateless.py:303–304`; adapter unimplemented | Ordinary inductive distinctness and wrapper injectivity; `DecoderDiagnosticCallerProofs.malformed_inj` | `c2c0c0`, `c2c078`; competing `c4c0810180` rejects in the actual codec first |
| `src/ethereum/forks/amsterdam/incremental_mpt.py:947–951` | `Malformed.leafValueList : Malformed`; declaration support only; successful compact decoding with leaf flag and list second field | Nominal diagnostic value, no traversal/effect | After compact success/leaf flag; raw-empty failure wins; descendant failures propagate unchanged; same unimplemented adapter/O4 as above | `compact_error_distinct`, `nonempty_compact`, `node_wire_bound`, `failed_rlp_no_item` compose public existing contracts | `c220c0`; competing `c220c080` codec failure; `c280c0` raw-empty compact failure; `c22080`, `c22078` source acceptance controls |

`DecoderDiagnosticGuards.lean` distinguishes every diagnostic and TrieError
wrapper (including distinct payloads), compares complete actual RLP parses of
minimal/competing/descendant controls, and actual compact results for all sixteen
flags and noncanonical padding/high bits. `DecoderDiagnosticCallerProofs.lean`
uses only public codec/compact/diagnostic contracts. The finite source driver
runs genuine pinned `_decode_witness_node` and asserts ordered exception lines
for ten named cases. It records all 85 complete outcomes, checks aggregate counts
and the allowed exception classes, restores tracing and repeats every call untraced. Full raw
values, complete source/lock and installed types/RLP/crypto identities are
retained before/after. Emitted guards compare actual successful RLP and compact
values against Lean seams; there is no Lean whole-node diagnostic comparison.

```sh
EELS/.venv/bin/python -I -B STFSpec/Conformance/Commit/decoder_diagnostic_differential.py \
  --eels EELS --output EXTERNAL.lean
```

Interpreter/startup, frozen installation/RECORD and host remain trust inputs.
Uncommitted local finite native checks are separate support evidence. The command
above is the committed source-only reproducer, emitting interpreter `#guard`s;
no native diagnostic runner is committed here.
These earlier diagnostic-seam observations discharge no whole decoder,
WitnessError adapter, W1, guest or resource gate. The complete operation and its
current evidence are owned above.

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
`#guard`s. Uncommitted local finite native checks execute those same expressions
as separate support evidence. To reproduce them, compile a temporary executable
importing `STFSpec.Conformance.Commit.RootDomainGuards` and check every named
`RootDomainGuards.cases` result. No native support runner is committed here.
Pinned `mpt:478–581` was read directly, without a replacement oracle.
The universal support proofs consume only public Nibbles and Std laws. Recursive
C7/C6 construction and every-node representative independence are supplied below.
The total local C8 wrapper is supplied below. Canonicality, whole-source refinement,
assembled-node `Encodable`/host premises,
F20 consumer coherence, D5 coupling and C1–C4 remain open.

### Implemented mathematical-root longest shared-prefix support

`Root.lean` adds private pure selection used by the C7 constructor. The actual
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

This subsection supplies pure selection support; recursive C7 and every-node
choice independence are supplied below. C8/root composition, canonicality,
source-root agreement, complete assembled-node `Encodable`, oracle coherence/coupling,
host/resources and guest acceptance remain open. No outside-domain behavior is selected.


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
field. This support subsection adds no recursive constructor or root wrapper.
The recursive C7 below uses the equality witness for strict descent on the supplied
child without repeated filtering.

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
by generated guards. Uncommitted local finite native checks exercise complete
stage outputs and traces; §4 describes their reproduction. No native runner is
committed here. Reproduce the committed source driver with:

```sh
EELS/.venv/bin/python -I -B STFSpec/Conformance/Commit/root_branch_differential.py \
  --eels EELS --output EXTERNAL.lean
```

The interpreter, frozen installation/RECORD, startup and host crypto remain trust
inputs. No Python-host or generic-oracle coupling interpretation is adopted.
Q50 allows empty byte values: `{[] ↦ empty, [0] ↦ empty}` forms a branch with one
occupied numeric reference and an empty byte field under the supplied finite
callback. A later canonical occupancy/lookup theorem needs appropriate value
premises; no rejection or domain restriction is introduced. Recursive C7 and
every-node choice independence are supplied below. C8, canonical witnesses,
complete assembled-node `Encodable`, source-root correspondence, F20 coherence/D5
coupling and resources remain open.

### Implemented recursive mathematical construction (C7)

`patricialize` in `Root.lean` implements C7 on Q50's actual finite full-map domain,
under the existing `Monad`/`KeccakQuery` parameters. This is the already specified
operation ([issue #34](https://github.com/alexanderlhicks/leanerSTFSpec/issues/34)).
It visibly dispatches empty, singleton, positive longest shared prefix, then branch.
Empty returns `pure none` before selecting a member or querying. Singleton uses
that full key's actual `drop level` and original complete value. Extension copies
only its new segment, recurses on the same full map at the advanced depth and
C6-encodes the child once. Branch uses the accepted private ordered support,
recursing on the supplied child map rather than filtering it a second time. Each
of sixteen ascending construction/encoding pairs precedes the final defaulted
ending field. The C7 return performs no parent encoding or parent query.

| Exact pinned EELS | Lean public operation/domain | Success/effects and failures | Ordinary equation/proof | Deterministic/source evidence |
|---|---|---|---|---|
| `merkle_patricia_trie.py:507–581` | `patricialize : (obj : ExtTreeMap Nibbles ByteArray) → (level : Nat) → PatricializeDomain obj level → m (Option InternalNode)`; no key/value/length cap | Empty/singleton terminal; recursive extension and sixteen ordered full-key children use actual C6; original oracle errors retained; no new local error or outside-domain completion | `patricialize_empty/singleton/extension/branch`; generic equations retain bind association; `patricialize_branch_lawful` explicitly requests `LawfulMonad` | `RootConstructionGuards`: full node variants/paths/nested fields/values, arbitrary State answers and all first errors at actual leaf31/32/33 boundaries and an extension over a hashed branch; authenticated complete source comparisons |
| `merkle_patricia_trie.py:531–581` | Private `patricializeWith` with valid map/depth-dependent member selectors; public operation supplies `minimumKeySelector` | Alternative selectors are used afresh at every recursive descendant; no query commutation, collision or constant-coherence premise | Private well-founded `patricializeWith_independent`; singleton-member equality, existing prefix/ending independence and strict child/extension descent; public arbitrary-member dispatch equations | Actual alternative selectors for every input member and changing descendant depth; genuine source first-member/insertion variants of the same final map |
| `merkle_patricia_trie.py:507–581` | Same public operation, any two domain proofs or maps with equal optional full-key lookups | Equal complete monadic action, including query effects; different-value insertion permutations need equal final maps | `patricialize_domain_irrel`, `patricialize_ext`; caller proofs use public equations and provider contracts | Repeated different-value writes retain last-write values; empty values and prefix relationships stay permitted |

`patricializeWith_independent` compares two complete recursive constructors, not
just equal final digests or one-step equations. It quantifies arbitrary valid
selectors of each current map and depth, so choices may differ at every node.
The private constructor/selector stay private; public clients consume the ordinary
arbitrary-representative equations, proof irrelevance and optional-lookup extensionality.
`RootConstructionCallerProofs` uses only those public equations and provider laws,
including original ExceptT errors suppressing all later construction/encoding.
`RootConstructionGuards` accesses the actual private selector constructor only as
narrowly scoped test instrumentation and supplies no new production selector API.

Total recursion uses the existing remaining-length sum. Under the multikey premise,
positive advancement and every child (including empty groups) strictly descend.
The actual-partition equality and domain proofs are erased; emitted recursive C
bodies do not call the separately emitted `remainingMeasure`/`remainingSum` definitions.
Prefix selection enumerates one full-key reference list per multikey node and scans
packed remaining digits under the current cap; extensions copy only their label,
singletons their terminal suffix, and branches perform sixteen guarded filters.
These source/C observations supply no aggregate allocation, throughput or C1–C4
result and justify no new D18 exception.

The fresh source driver authenticates source/lock, exact callable/classes and installed
types/RLP/crypto before and after. A restored trace hook records genuine recursive
calls, actual child maps, complete structures and query inputs/answers; untraced
replays match. No callable, class, recursion, encoder or hash is replaced. The
emitted guards compare entire returned structures and full ordered queries,
including ending/continuing keys, empty values, all sixteen groups, odd/long shared
prefixes, unequal lengths, all member/insertion variants and complete 31/32/33-byte
child encodings.

The committed source driver elaborates and guards each complete observation in its
own named definition, then collects them in `sourceConstructions` and exposes
`allSourceConstructions`. This avoids one monolithic
compiler/evaluator workload while preserving every input, structure and query trace;
it raises no resource limits.
Generated map keys and returned paths validate every source digit below sixteen and
use explicit bounded literal lists, so ordinary nonzero-depth domain proofs reduce
without a hex parser or modulo conversion. Complete byte values and queries remain
unchanged.

```sh
EELS/.venv/bin/python -I -B STFSpec/Conformance/Commit/root_construction_differential.py \
  --eels EELS --output EXTERNAL.lean
```

Uncommitted local finite native checks compare complete constructor results and
ordered query/error traces. To reproduce the committed deterministic cases natively,
compile a temporary executable importing
`STFSpec.Conformance.Commit.RootConstructionGuards` and invoke
`RootConstructionGuards.printComplete`. For source cases, compile the generated
`EXTERNAL.lean` as a temporary module and compare every complete `sourceConstructions`
row and `allSourceConstructions`. Retain default limits, warnings as errors and fresh
current-module imports and sidecar identities. No native constructor runner is
committed here.

The evidence is finite C7 source correspondence. C8/root equality, witnesses/caches,
canonical occupancy or decoded lookup simulation, complete assembled `Encodable`,
host/resource equivalence, F20 coherence, D5 generic oracle coupling and guest/security
closure remain separate. Q50's two-key empty-value case still permits one occupied
numeric child; canonicality theorems require their actual representation/value premises.

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

Run `python3 STFSpec/Conformance/Commit/node_db_native.py --observations OUTSIDE/NodeDBSource.observations.json
--output OUTSIDE/native`. Current actual-module setup/import artifacts and fresh
C/olean equality precede owned O3/Werror object compilation. Complete source and
native observations agree with the pinned concrete tables and independent
arbitrary-answer controls, including reconstructed full-256-bit keys, empty raw
values, extra entries, larger tables, sibling extensions and retained-parent checks.
The native link map and exact archive-member/object comparisons identify the
selected owned providers. The parser enforces exact observation schemas, canonical
natural fields and byte-list types/widths before comparing values; validated counts
come from observed tables and traces. Parser regressions run in CI with normal
Python and `-O`; the full native driver requires default Python mode for its
provenance checks. No checksum substitutes for table or trace observations.
These finite functional runs establish no table distribution, throughput,
allocation, C1–C4, R4, generic oracle coupling, decoder/root or guest/EEST claim.


### Implemented mathematical full-map root

C8 is **implemented** as the total local mathematical operation in `Root.lean`.
The public `mathRoot` takes the already prepared full-nibble map and the supplied
empty root; Typed preparation is a separate consumer. Executable dispatch
requires only `Monad` and `KeccakQuery`. Empty maps return the supplied constant
without constructing a node or making a local query. Nonempty maps run actual C7
at zero, then query the complete top assembly once, regardless of its wire width.
Descendant queries precede that final query; an earlier failure suppresses it.

| Exact pinned EELS source | Lean declaration/public domain | Success/effects | Ordered failures/handler | Ordinary model law | Deterministic/source evidence |
|---|---|---|---|---|---|
| `src/ethereum/merkle_patricia_trie.py:478–504` with C6 `:213–249` | `mathRoot : Hash32 → ExtTreeMap Nibbles ByteArray → m Hash32`; every finite full map; supplied C5/F20 empty constant | Empty returns supplied constant, zero local queries; nonempty actual C7 then exactly one query of full top RLP; returns all 32 answer bytes | Original descendant or final oracle failure; no added error/handler or query after earlier failure | `mathRoot_eq/empty/nonempty/ext/id`; private `mathRootReference`, ordinary whole-action `mathRoot_eq_reference` with explicit `LawfulMonad` | `MathRootGuards`, public-only `MathRootCallerProofs`; authenticated genuine original-Trie root driver |
| Same operation in transformer contexts (D5/F15) | `run_mathRoot_exceptT/stateT`; `run_mathRoot_construction_error/query_error`; explicit `LawfulMonad` | Transformer equations retain actual C7 computation and underlying query effects; state at the final query is C7's returned state | Original construction/final-query errors preserved; error law premises state the actual failing action | Authored public run equations, public-only clients | Complete initial state prefixes and every descendant/top first error in finite controls |

The private reference first C6-encodes the constructed top node, then applies
C8's second RLP-width threshold. It observes Python's returned Extended byte/list
result as an `RlpItem`: a returned digest is the raw 32 bytes, while its RLP is
33 bytes. It performs no unchecked conversion from an arbitrary reference item
into `Hash32`. Public `Hash32`/`Bytes`/RLP width laws prove the 33-byte fact for
every answer, including leading zeros. C6's public inline/hash equations then
prove ordinary equality of the full reference and fused actions, with explicit
`LawfulMonad` for eliminated/reassociated binds. This equality uses total RLP
(Q47) and is unconditional on `Encodable`; no collision or concrete-oracle
hypothesis is involved.

Concrete pinned-root correspondence additionally requires compatible prepared
maps and value interpretations, the complete assembly's `Encodable`, coherent
caller-acquired F20 constants and successful source-host behavior. The total local
reference is not an unconditional equality to arbitrary Python objects or host
executions. In particular Python's empty root makes a query on `80`, while the
Q50 local empty branch makes zero queries. No generic equality of those
whole traces is claimed. Raw odd full paths and empty byte values are Q50/C7/C6
composition controls; original typed `Trie` observations retain their real packed
key conversion, default elimination and preparation behavior.

`MathRootGuards` checks full top wires of 31/32/33 bytes, arbitrary full-width
answers (zero, significant leading zeros and high/full-bit patterns), ordered
branch/extension descendant-then-top queries, every first error and nonempty initial
state prefixes with zero/nonzero query counters. It also compares actual private
reference/fused actions, including original errors, without exporting the reference
as a consumer seam. `MathRootCallerProofs` uses authored public laws only.

`STFSpec/Conformance/Commit/math_root_differential.py` authenticates pinned
source/lock and installed types/RLP/crypto RECORD bytes before and after fresh
source imports. Original `Trie`, `trie_set`, preparation, packing, value encoding,
C7, C6, RLP and hashing execute unchanged. A restored trace hook records actual
prepared mappings, complete root bytes and every complete query preimage/answer;
each full call is replayed without tracing. Source-only preparation failures
are distinguished from successful local C8 comparisons. Secured-key preparation
queries and the empty source query on `80` are recorded separately from the local
C8 trace. Insertion variants compare the same final maps; default erasure and
last-write controls retain genuine source behavior. Interpreter/startup, frozen
installation/RECORD and host crypto remain trust inputs. The committed driver
elaborates generated Lean guards comparing complete values, without changing
resource limits. Uncommitted local finite native checks compare the same complete
values; the repository does not supply a native runner for these cases.

Run from the repository root with the pinned environment and an evidence destination
outside both repositories. This command reproduces the source observations and
generated Lean guards:

```sh
EELS/.venv/bin/python -I -B STFSpec/Conformance/Commit/math_root_differential.py \
  --eels EELS --output EXTERNAL.lean
```

This is finite genuine-source evidence. Typed preparation, concrete value bridges, canonicality,
witnesses/caches, whole-source refinement, assembled `Encodable` and host proofs,
F20 acquisition/coherence, D5 generic coupling, aggregate costs, fuel and
guest/security readiness remain open.

### Generic typed-trie storage (C11/Q53)

`STFSpec/Commit/Trie.lean` implements the generic storage and proves its safety laws.
`TrieValue` has exactly total `encode`, separate `Valid` and `encode_ne_empty`
under validity; this class alone supplies no concrete source encoding bridge.
`NoDefault` and `PrepareSafe` are proof predicates, never intrinsic fields.

| Exact pinned EELS source | Public declaration/domain and status | Success/effects | Ordered failures/domain boundary | Model law | Validation |
|---|---|---|---|---|---|
| `src/ethereum/merkle_patricia_trie.py:274–312` | `Trie K V` under `Ord K`; constructor `Trie.mk`; **discharged storage** | All supplied secured/default/map fields retained; any finite map admitted | No runtime guard; directly stored defaults and invalid values admitted | `Trie.ext`, `Trie.ext_lookup`; `Trie.noDefault_empty`, `Trie.prepareSafe_empty`; `Trie.prepareSafe_default_update/secured_update` | Arbitrary defaults/both flags; direct valid stored default is safe but fails `NoDefault` |
| `src/ethereum/merkle_patricia_trie.py:315–322` | `copyTrie : Trie K V → Trie K V`; **discharged storage** | Persistent identity; derived writes leave old observations available | None; source has independent shallow dictionary with frozen values | `copyTrie_eq/data/default/secured/get/noDefault/prepareSafe`, `copyTrie_old_observation` | Copies before insert/overwrite/delete retain complete old maps and results |
| `src/ethereum/merkle_patricia_trie.py:325–338` | `trieSet : [Ord K] → [Std.TransOrd K] → [BEq V] → [LawfulBEq V] → Trie K V → K → V → Trie K V`; **discharged storage/safety** | Actual supplied-default equality erases, every other value inserts; fields retained; no encoding/query/validity branch | No error or `Valid` premise; Python default-equality agreement remains a concrete bridge premise | `trieSet_data/lookup/default/secured/erases_iff/noDefault/prepareSafe_iff/delete_prepareSafe_iff/overwrite` | Arbitrary nonempty defaults; unsafe insert/safe deletion; deletion at another key cannot repair an invalid retained binding |
| `src/ethereum/merkle_patricia_trie.py:341–347` | `trieGet : [Ord K] → [Std.TransOrd K] → Trie K V → K → V`; **discharged storage** | Present value or precisely supplied default, with no effects | None | `trieGet_eq/of_present/of_absent/empty/set_same/set_of_ne` | Same/distinct/missing keys and both setter branches; complete optional and numeric observations |

`STFSpec/Conformance/Commit/TrieGuards.lean` supplies deterministic cases and
separate-predicate counterexamples with a test-local `Option Bytes` validity
interpretation. `TrieCallerProofs.lean` imports the normal owner and uses public
laws only; existing Nibbles, U256, Address and Hash32 key providers and lawful
Nat/U256/Bytes equality demonstrate storage use without production value/key
instances or a `KeyBytes` requirement.

`trie_storage_differential.py` runs through the frozen EELS `.venv/bin/python -I -B`,
with source/pin/lock and installed RECORD/classes authenticated before and after.
It calls original `Trie`, `trie_set`, `trie_get` and `copy_trie`, compares complete
secured/default/maps/getter results and copied old observations, and emits Lean
cases for 216 authenticated source observations. Uncommitted local finite native checks
replayed those cases and local controls through fresh current C/olean and O3 native
objects, comparing 224 complete observations; no native storage runner is committed.
The committed source-only reproducer is
`EELS/.venv/bin/python -I -B STFSpec/Conformance/Commit/trie_storage_differential.py
--eels EELS --output OUTSIDE/TrieStorageSource.lean`, followed by
`lake env lean OUTSIDE/TrieStorageSource.lean`. Numeric Uint values/Bytes32 keys
(observed as existing Lean U256 values) and optional Bytes values/finite Bytes keys
are separate concrete interpretations; no key
adapter instance is supplied. Python equality agreement on supplied-default comparisons
is checked as a concrete premise; lawful Lean equality alone proves no arbitrary
heterogeneous Python bridge. Finite comparisons are distinct from the symbolic laws.
This C11 storage slice supplies no preparation API, source bridge theorem, root,
guest/EEST or cost claim; generic preparation is supplied separately below.

### Pure unsecured typed preparation (Q53)

`STFSpec/Commit/Preparation.lean` supplies the generic byte-key contract and pure
preparation seam. `KeyBytes K` has exactly injective `toBytes` and agreement of
`Ord.compare` with byte-list lexicographic comparison. Q54 supplies production
`Bytes` order ([EthBase §3](EthBase.md#3-eels-source-map)). The named production
`instKeyBytesBytes : KeyBytes STFSpec.Base.Bytes` is supplied in the same Preparation
owner, using the direct `STFSpec.Base.BytesOrder` import and exactly
`Bytes.toByteArray`. Its fields cover every finite existing Bytes, including empty
keys, significant zeros, unequal lengths and prefixes. The public `toBytes_bytes`
equation names the exact packed export for consumers, beyond injection/order alone.
Injection applies public
`Bytes.ofByteArray` to export equality and uses `ofByteArray_toByteArray`; order
uses only `compare_toList` and `toByteArray_toList`. Production value-encoding
bridges and concrete Python key/alias/equality interpretations remain open.
Test-local List UInt8 coverage is retained alongside production Bytes-key controls.
Key interpretation is injective; value encoding need not be.

| Exact pinned EELS source | Public declaration/domain and status | Success/effects | Ordered failures/domain boundary | Ordinary law | Validation |
|---|---|---|---|---|---|
| Q53/Q54 provider adapter; `Bytes.toByteArray`, `ofByteArray_toByteArray`, `compare_toList`, `toByteArray_toList` from EthBase; source key context `src/ethereum/merkle_patricia_trie.py:407–448`, inherited content order `ethereum_types/bytes.py:165` (0.4.1) | `instKeyBytesBytes : KeyBytes STFSpec.Base.Bytes`; **discharged functional instance**, every finite existing Bytes with its existing lawful order/equality | Exact complete packed export; injective byte keys and unsigned lexical order, proper prefix first; pure, no query/filter/failure | Conditional on a consumer choosing existing Bytes; supplies no concrete Python alias/equality bridge, encoder, secured policy or cost bound | `toBytes_bytes (k : Bytes) : KeyBytes.toBytes k = k.toByteArray`; ordinary instance fields `toBytes_injective` via public inverse and `compare_toBytes` via public order/export laws; no provider representation unfolding | Private `PreparationCallerProofs` instance synthesis, exact export/injection/order/actual-equality and complete generic map/root clients; private `PreparationGuards` whole Bytes-key maps, reconstruction/overwrite/distinct keys/aliased values, significant zeros, first/last mismatch and raw ordinal bytes `[128]` after `[1]`; List clients retained |
| `src/ethereum/merkle_patricia_trie.py:407–448` | `prepareTrieModel : Trie K V → ExtTreeMap Nibbles ByteArray`; `Ord`/`TransOrd`, `KeyBytes`, `TrieValue`; **discharged pure model** | One stored-map fold, one encoding/path insertion per stored binding; retain valid stored defaults; do not encode an absent default or filter values | Total model also computes on invalid values; no source-success claim there. Pinned preparation asserts stored None before encode and exact empty encoding next; safety excludes both at the frontend | `prepareTrieModel_eq_reference` equates executable fold with mapped-list `prepareTrieReference`; `keyBytes_path_injective`, `prepareTrieModel_lookup/lookup_some_iff/image_nonempty/size/empty_iff/congr/insert` | `PreparationGuards` complete empty/prefix/zero/noninjective-value/default maps; `PreparationCallerProofs` public-only clients; actual pinned complete-map comparisons |
| `src/ethereum/merkle_patricia_trie.py:451–475` | `prepareTrie {m} [Monad m]` under lawful key order, `secured = false` and `PrepareSafe`; **discharged local seam** | `pure` complete prepared map, zero local query/failure; proof arguments erased; no `NoDefault` premise | No runtime error or handler/O-row added; concrete supported non-None equality/dispatch and host premises remain caller obligations | `prepareTrie_eq/empty/proof_irrel`; State/Except callers need no query instance or `LawfulMonad` | Direct valid stored default executes despite failed `NoDefault`; carried State unchanged and Except succeeds; unsafe None/empty interpretations cannot satisfy safety |

Private Bytes clients import the existing public Commit aggregate without a local
Bytes instance. They specialize exact exported bytes, injectivity, byte-order and
actual-equality implications; full optional prepared lookup/image, cardinality,
empty-map equivalence, insertion/overwrite and the complete pure preparation action
retain caller-supplied `TrieValue V`. Symbolic `Trie Bytes V` root clients retain
`PrepareSafe`, `secured = false`, caller `emptyRoot`, `Monad` and `KeccakQuery`;
only the separate sequential-reference client adds `LawfulMonad`. The adapter
adds no production value instance, equality/order/default provider, coercion,
source alias or runtime traversal API. These functional clients establish no
consumer encoding/source/root bridge, resource/cost or readiness result.

Executable preparation calls the existing map fold and packed splitter directly;
List enumeration occurs only in the legible reference and proofs/observations.
Public image and cardinality laws use lawful key equality plus interpreted-key
injection, without value injection, default-equality or hash premises. Equal raw
stored maps give equal complete preparation irrespective of default/secured fields.
The raw insertion law does not change the default-deleting setter semantics (C11).
The callback contains one encoding application per visited binding; its visit
cardinality is the public map size. This source-structure observation is not a
compiler evaluation-count, allocation, throughput or C1–C4 claim. Interpretation,
encoding and key-prefix costs are unconstrained by the generic classes; there is
no new D18 performance exception.

The authenticated driver invokes genuine pinned `_prepare_trie` with a restored
trace hook and untraced replay. It retains full post-dictionary stored maps and
all complete prepared paths/values, normalized by path for map comparison. No
source dictionary insertion-order or arbitrary heterogeneous Python-equality theorem
is claimed. The trace checks source encoding order/count,
zero unsecured Keccak calls, and failure before encoding None or after encoding
empty bytes, suppressing later bindings. Original source/lock, installed
types 0.4.1/RLP 0.1.6/Crypto, classes and callables are checked before and after;
no source callback, class, encoder, hash or limit is replaced. Generated whole-map
guards elaborate under default limits and warnings fatal. Local fresh O3 runs
compare every complete generated map plus fixed frontend regressions; those
uncommitted artifacts and their provenance are separate from the committed driver.

```sh
EELS/.venv/bin/python -I -B STFSpec/Conformance/Commit/preparation_differential.py \
  --eels EELS --output EXTERNAL.lean
```

Finite sample values include raw identity bytes, Uint zero/nonzero, empty/nested
tuples, typed-like raw envelopes and already-RLP bytes. The synthetic encoded
tuple is not an actual Withdrawal instance. None and empty raw bytes are original
source failures outside `PrepareSafe`. Supplied Git, interpreter/startup, frozen
installation/RECORD and host remain trust inputs. There is no all-input Python
bridge, production consumer instance, secure traversal/collision/source-history,
C8/root, EEST/guest, oracle-coupling or resource result.

### Implemented generic typed-root composition

Q53's safe unsecured `root` is supplied in `STFSpec/Commit/Root.lean` beside C8.
It directly calls `mathRoot emptyRoot (prepareTrieModel t)`, without an executable
preparation bind. The erased premises are `t.secured = false` and `t.PrepareSafe`;
there is no `NoDefault` requirement, default filter, new query, error or root policy.
The generic `KeyBytes`/`TrieValue` interpretation and caller-owned F20 constant are
retained from the existing seams. Concrete consumer adapters remain open.

| Exact pinned EELS source | Lean declaration/public domain | Success/effects | Ordered failures/handler | Ordinary public law | Deterministic/source evidence |
|---|---|---|---|---|---|
| `src/ethereum/merkle_patricia_trie.py:478–504`, preparation `:407–475` | `root : {m} → [Monad m] → [KeccakQuery m] → Hash32 → (t : Trie K V) → t.secured = false → t.PrepareSafe → m Hash32`; generic lawful ordered injective byte keys and total value encoding | Exact complete C8 action on pure complete preparation; empty data returns any supplied constant with zero local queries; nonempty queries retain all original preimages/answers and state | Original C8 descendant/final-query failure, without a new handler or runtime frontend failure | `root_eq_mathRoot`, `root_empty` under `Monad`; `root_eq_reference` identifies separately sequenced preparation only under `LawfulMonad` | Named public-only `TypedRootCallerProofs`; complete `TypedRootGuards`; authenticated genuine typed source driver |

Named clients consume only public preparation/root laws. They verify literal
composition, arbitrary caller empty roots, equal complete storage observations,
state and error forwarding, and the explicit lawful sequential-reference domain.
The deterministic suite observes every full digest, preimage, answer, diagnostic
and state field at seeded counters, including every descendant/top first error.
A directly stored valid default contributes a real query despite failing
`NoDefault`; distinct sample values with equal encodings retain identical root
effects. Empty input bypasses even a failing oracle.

`STFSpec/Conformance/Commit/typed_root_differential.py` runs genuine original
`Trie`, setters, `root`, `_prepare_trie`, `_prepare_data`, encoding, `patricialize`,
RLP and hashing. It authenticates source/lock and installed types/RLP/Crypto RECORD
bytes, class/callable identities and retained input/state before and after calls.
Tracing is restored in `finally`; each full root is also run without tracing.
Generated Lean fixtures start from original raw-byte/integer writes and defaults,
use actual `trieSet`, pure preparation and typed `root`, compare complete prepared
maps and concrete roots/query streams, and replay all source answer bytes.
Those local value/key instances are finite instrumentation, not production adapters.
Source preparation failures and secure fixtures stay source-only observations:
no runtime error or secure composition is invented for the safe frontend.
Python empty-root acquisition on `80` is recorded separately from the zero-query
local call using the coherent caller constant.

```sh
EELS/.venv/bin/python -I -B STFSpec/Conformance/Commit/typed_root_differential.py \
  --eels EELS --output EXTERNAL.lean
```

Generic source correspondence remains conditional on exact concrete supported-value
encoding/equality, lawful byte keys, schema and complete assembled `Encodable`,
coherent F20 constants and pinned host compatibility (§7.0.3). Finite source/native
observations supply no unconditional Python theorem, concrete production adapter,
secure traversal/collision/history policy, D5 coupling, canonicality, W1/S2,
C1–C4, fuel or guest/security readiness result.

### Implemented pure bare lookup

`STFSpec/Commit/Lookup.lean` supplies total pure `lookup` and exactly the seven constructor
equations in §7.0.5. All scanner, copying reference, offset traversal, proper-child decreases and
refinement theorems stay private. The ordinary private all-bare-input equality relates the offset
worker at every natural offset to the copying reference on the clipped suffix; no Node.WF, cache
or arity premise is used. Structural Node/Option/Array descent permits empty extensions. Execution
retains the original key, compares bounded digits and accesses only the selected child; it copies
no whole remaining suffix at a branch and never scans off-path children.

| Pinned source | Lean declaration/type and domain | Complete value/effects | Ordered failures and consumer boundary | Laws and controls |
|---|---|---|---|---|
| `src/ethereum/forks/amsterdam/witness_state.py:53–100`; nominal classes `incremental_mpt.py:48–98` | `lookup : Ref → Nibbles → Except TrieError (Option ByteArray)` on every finite bare tree/key with arbitrary Enc/arity | Pure; exact complete optional bytes, including present empty leaf values; no query, codec, DB/default or mutation | Reached stub before exhaustion; mismatched extension stops before child; terminal branch value before bounds; only a reached out-of-range selected slot gives exact Q59 `(index, actual arity)`. Guest reachability/adapters remain open under CONTRACT O4/O13 | **Discharged local constructor equations:** `lookup_none`, `lookup_hashed`, `lookup_leaf`, `lookup_ext`, `lookup_branch_emptyKey`, `lookup_branch_index`, `lookup_branch_oob`; private public-import `LookupCallerProofs.lean`, complete-result `LookupGuards.lean`, fresh original `lookup_differential.py` |

The source driver authenticates original pin/physical source and existing types/RLP
wheel/installed-source inputs before and after execution, retaining original function identities,
complete dataclass fields and actual Hash32 keys, full optional values, exception
class/message/args/throw site, and absence of local hash/codec/state calls. Value/stub comparisons
use valid selected accesses and explicit source-class/host premises. Missing-slot Python
IndexError is recorded separately; its exact selected index/arity tests the approved typed
adaptation, never source exception-payload or guest-output equivalence. Odd generalized paths
remain ordinary Lean controls. No whole Python theorem, authentication, WF/cache admission,
mutation/root, security/witness agreement, generic coupling/lifetime, resource or readiness result
follows. Interpreter/startup/frozen installation and host remain trusted inputs.

```sh
EELS/.venv/bin/python -I -B STFSpec/Conformance/Commit/lookup_differential.py \
  --eels EELS --output EXTERNAL.lean --rlp-wheel RLP_WHEEL --types-wheel TYPES_WHEEL
python3 -B STFSpec/Conformance/Commit/lookup_differential.py --self-test
python3 -B -O STFSpec/Conformance/Commit/lookup_differential.py --self-test
```

The exhaustive decoder diagnostic encoder preserves tags 0–10 and appends tag 11 with both
unrestricted Nat fields. `DecoderDiagnosticGuards.lean` varies both fields independently and
preserves wrappers/old distinctness; the complete decoder parser accepts nominal large fields and
rejects invalid/truncated/extra records in ordinary and optimized Python. Its decoder-output
sixteen-child grammar is retained; the separate bare lookup input grammar permits every finite
arity. Decoding itself never manufactures `branchIndex`.

## 4. Tests

**Pure lookup cases (Q59; supplied locally).** `LookupCallerProofs.lean` consumes
the seven equations in §7 through ordinary public imports; `LookupGuards.lean` and
`lookup_differential.py` compare complete optional bytes/diagnostics.
Cover none/stub with empty and nonempty keys; present empty leaf versus terminal empty
branch; full suffix equality/mismatch; clipped/overlong/mismatched extensions stopping
before a stub; matched empty-extension chains and ext-to-ext/leaf; every nibble index;
arities 0/1/15/16/17 with valid selected slots and extra ignored children; terminal short
branches before bounds; exact index/actual-arity fields only for out-of-range selected slots; selected
versus off-path stubs and arbitrary complete Enc/cache fields. Fresh original source
comparisons cover valid selected accesses with actual Hash32/source-class/host premises;
assert the adopted bounds diagnostic separately. Empty/odd generalized Nibbles are Lean
law cases, not direct original Hash32 byte-entry observations. The scoped controls
are supplied in §3; no whole source agreement theorem or benchmark is claimed.

C11 storage/safety and generic unsecured preparation validation are supplied in §3.
Concrete consumer/root seams still require cases distinguishing
default `none` from stored `some empty`, default nonempty bytes from invalid stored empty
bytes, and a valid value directly injected even when equal to the default. RLP `Uint(0)`
encodes as `80` and an empty tuple as `c0`; neither is an empty encoding. Cover arbitrary
defaults, field/get/copy laws, both sides of the setter safety iff, injective byte-key
interpretation and rejection of a tagged-key alias contract, whole prepared maps and
exactly-once encoding. Preparation has zero queries. Root tests must pass a nonliteral
empty root, retain whole C8 queries/answers, original failures and prior state, and use
only public contracts in proof clients. Authenticated pinned comparisons must cover
the concrete supported/schema/assembled-node `Encodable`, equality, F20 and host premises;
the generic preparation cases are supplied in §3, while concrete consumer validation remains open; generic typed-root validation is supplied below.

`InternalNodeGuards.lean` checks absent, leaf and extension structures, nested
fields, and complete encodings at the 31/32/33-byte threshold under arbitrary and
failing oracles. Its concrete `Id` guard checks a branch of sixteen distinct
32-byte child references against the full digest obtained from the authenticated
pinned C6 operation. The driver in §3 additionally compares full ordered branches,
HP parities, nested values and long structures with pinned EELS. Symbolic clients
in `InternalNodeCallerProofs.lean` compose domain, model, ordering and lift laws.
These node tests cover C6; recursive C7 construction is supplied in §3. C8/root tests are described below;
witness operations remain open.

The implemented pure operations evaluate all byte splits, all ordered nibble pairs under both
leaf flags, all singleton flags, empty/odd/even encodings, zero/15 extremes and long paths.
Prefix guards cover asymmetric proper prefixes and first/end mismatches.
`NibblesGuards.longChecks` compares whole outputs, and the differential driver emits
full actual-source observations. The compact decoder guards in §3 additionally
cover exact raw-empty failure, every leading byte, ordered suffix digits, canonical
inverses and accepted-wire normalization.
Q52 seam guards cover exact wires `c2c0c0`, `c220c0`, `c4c0810180`,
`c220c080`, `c280c0`, `c2c078`, `c22080`, `c22078`, `c200c0`, `c20078`,
`c210c0`, `c410c2c0c0`, `c410c220c0`. Source observations additionally record
all sixteen flags with byte/list second fields, accepted noncanonical padding/high
bits and a branch-list ending with two occupied hashed children, with aggregate
counts and allowed exception classes checked as described in §3. The latter is a
source acceptance control, not a branch decoder. Remaining dispatcher regressions
must assign Q52 in C14 order, distinguish compactEmpty/pathEmpty, preserve original
descendant errors and accept branch-list endings. Witness decoding and trie cases
below remain open; resource gates are owned by REVIEW §7.

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
- **Adversarial witnesses** (hand-built DBs; cycles only through the internal `decodeRoot` API with a DB that is not keccak-keyed): missing root (O4(a)); missing child never accessed (accepted); malformed node off every accessed path (rejected, eager); on-path cycle of length 1 and 3 (malformed); diamond sharing (accepted; baseline repeats occurrence queries, future memo refinement conditional); a DAG of depth 8 with 16 identical children (cost test); empty-path leaf below a depth-63 branch (accepted); branch collapse whose sole sibling is a stub (rejected) and the same after an insertion (accepted, C26); each non-canonical case of C16 including the `0x80` entry flip; no-op delete through a non-canonical node changing the root (C19).
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
-- Q53: generic storage/safety/key interpretation/preparation/root implemented; concrete consumers open.
variable [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]
class TrieValue (V : Type) where
  encode : V → ByteArray
  Valid : V → Prop
  encode_ne_empty : ∀ v, Valid v → encode v ≠ ByteArray.empty
class KeyBytes (K : Type) [Ord K] where
  toBytes : K → ByteArray
  toBytes_injective : Function.Injective toBytes
  compare_toBytes : ∀ a b,
    compare a b = compare (toBytes a).toList (toBytes b).toList
-- Implemented conditional existing-Bytes adapter; exact export/inverse/order fields (§3).
instance instKeyBytesBytes : KeyBytes STFSpec.Base.Bytes
theorem toBytes_bytes (k : STFSpec.Base.Bytes) : KeyBytes.toBytes k = k.toByteArray
structure Trie (K V : Type) [Ord K] where
  secured : Bool
  default : V
  data : Std.ExtTreeMap K V                 -- predicates are separate proof obligations
def Trie.NoDefault (t : Trie K V) : Prop :=
  ∀ k v, t.data[k]? = some v → v ≠ t.default
def Trie.PrepareSafe [TrieValue V] (t : Trie K V) : Prop :=
  ∀ k v, t.data[k]? = some v → TrieValue.Valid v
def trieSet [BEq V] [LawfulBEq V] (t : Trie K V) (k : K) (v : V) : Trie K V
-- v == t.default: erase; otherwise insert, with no preparation obligation.
def trieGet (t : Trie K V) (k : K) : V
def copyTrie (t : Trie K V) : Trie K V := t
-- Pure model; encode once per stored value, injective unsecured byte-key interpretation.
def prepareTrieModel [TrieValue V] [KeyBytes K] (t : Trie K V) :
    Std.ExtTreeMap Nibbles ByteArray :=
  t.data.foldl (fun out k v ↦
    out.insert (bytesToNibbleList (KeyBytes.toBytes k)) (TrieValue.encode v)) ∅
def prepareTrie [TrieValue V] [KeyBytes K] (t : Trie K V)
    (unsecured : t.secured = false) (safe : t.PrepareSafe) :
    m (Std.ExtTreeMap Nibbles ByteArray) := pure (prepareTrieModel t)
def root [TrieValue V] [KeyBytes K] (emptyRoot : Hash32) (t : Trie K V)
    (unsecured : t.secured = false) (safe : t.PrepareSafe) : m Hash32 :=
  mathRoot emptyRoot (prepareTrieModel t)

-- public: node DB and partial trie
structure NodeDB where
  map : Std.HashMap Hash32 ByteArray        -- read-only after build
def NodeDB.Authentic (H : ByteArray → Hash32) (db : NodeDB) : Prop :=   -- F4: a predicate, not a field
  ∀ h b, db.map[h]? = some b → H b = h
def NodeDB.build (entries : Array ByteArray) : m NodeDB       -- keys through the oracle; Authentic keccak256 at Id

-- Supplied bare Enc/Node/Ref carriers; the admission/cache obligations below remain future.
structure Enc where                         -- completed raw/cached values; C18 coherence separate
  rlp : ByteArray
  hash? : Option Hash32                     -- some iff rlp.size ≥ 32 is a future admission law
inductive Node where
  | leaf (path : Nibbles) (value : ByteArray) (enc : Enc)
  | ext (path : Nibbles) (child : Node) (enc : Enc)
  | branch (children : Array (Option Node)) (value : ByteArray) (enc : Enc)   -- size 16, stated separately (F5)
  | hashed (h : Hash32)                     -- unresolved stub (EELS HashedNode)
abbrev Ref := Option Node                   -- none = empty; inline vs hashed is a property of Enc (B3; provenance, DISC-003)
def Node.WF : Node → Prop                   -- every branch has 16 children, plus §6 invariants
                                          -- unimplemented; exact cache/provenance interpretation open (Q55)
def childRef : Ref → RlpItem                -- C18: "" · stub hash · cached hash · inline RLP item
inductive Malformed | rlp | nonEmptyString | compactPathList | compactEmpty | leafValueList
  | pathEmpty | badListLength (n : Nat) | refLength (n : Nat)
  | extChild | occupancy (n : Nat) | cycle
  | branchIndex (index : Nat) (arity : Nat)    -- Q59 selected-slot diagnostic supplied
inductive TrieError | missingRoot (h : Hash32) | malformed (why : Malformed) | unresolved (h : Hash32)

-- smart constructors (the only way ops build nodes; internal but with public laws).
-- They compute Enc, which may hash, so they are monadic (F4).
def mkLeaf (path : Nibbles) (value : ByteArray) : m Node
def mkExt (path : Nibbles) (child : Node) : m Node          -- merges ext/leaf children (C24)
def mkBranch (children : Array (Option Node)) (value : ByteArray) : m (Except TrieError Ref)  -- size 16; collapse, C25

-- Q55: complete generic decoders are supplied in §3; pure lookup is supplied separately in §3.
def decodeRoot (emptyRoot : Hash32) (db : NodeDB) (r : Hash32) :
    m (Except TrieError Ref)   -- eager, C13–C17; pre-RLP query on each eligible raw occurrence
def lookup (t : Ref) (key : Nibbles) : Except TrieError (Option ByteArray)             -- C20/Q59, supplied
def update (t : Ref) (key : Nibbles) (value : ByteArray) : m (Except TrieError Ref)    -- C23, value ≠ empty
def delete (t : Ref) (key : Nibbles) : m (Except TrieError Ref)                        -- C24–C25
def rootHash (emptyRoot : Hash32) (t : Ref) : m Hash32                                 -- C27

structure IncrementalMPT where secured : Bool; root : Ref  -- supplied nominal carrier only
def decodeWitnessToMpt (emptyRoot : Hash32) (db : NodeDB)
    (r : Hash32) (secured : Bool) : m (Except TrieError IncrementalMPT)
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

Mapping of `incremental_mpt.py` items:
`MutableLeafNode`/`MutableExtensionNode`/`MutableBranchNode`/`HashedNode`/`MutableNode` →
`Node`/`Ref`; `IncrementalMPT` → `IncrementalMPT` (guest projection omits flat `_data` under C21,
caller `default` under C22 (`inc:441/452`), and recorded `witness` under C28/C25; the future
collapse stub failure at `inc:797/:245` is retained); `_encode_mutable_node`,
`_encode_mutable_node_to_extended`, `_compute_node_hash_and_rlp`, `_invalidate_hash` → `Enc`
construction and `childRef`; `mpt_set`, `_mpt_insert_node`, `_insert_into_leaf`,
`_create_branch_from_two_leaves`, `_insert_into_extension`, `_split_extension`,
`_insert_into_branch` → `update`/`mptSet`; `_mpt_delete_node`, `_delete_from_extension`,
`_delete_from_branch`, `_collapse_branch` → `delete`/`mkBranch`/`mkExt`; `mpt_root` → `mptRoot`;
`compact_to_nibbles` → `compactToNibbles`; `_resolve_child_ref`, `_decode_witness_node`,
`decode_witness_to_mpt` → `decodeRoot`/`decodeWitnessToMpt`; `_build_mutable_tree`, `build_mpt` →
`buildMpt`; `Witness`, `_record_witness`, `_mpt_traverse_for_witness`, `mpt_get` →
`Witness`/`mptGetRecording`.

For a consumer choosing existing Base `Bytes`, §3/§5 owns the supplied adapter
and named exact-export equation. Generic preparation/storage contracts do not
require choosing this concrete provider.

**Decoder acquisition contract (Q55; implemented locally in §3).** Every newly entered root,
present DB child or inline child uses its complete raw bytes: below 32 bytes there
is no query and the cache hash is `none`; at or above 32 bytes exactly one query
precedes whole RLP parsing and its answer is kept as `some`. An empty-root bypass,
missing root, absent child/stub or already on-path repeated hash does not enter a
new raw occurrence and has no local query. Underlying `m` failure is forwarded
unchanged, with no parsing or later query. A successful query followed by the
existing typed RLP/shape error retains the query's effects; earlier typed failures
stop subsequent children/queries. The traversal is eager, depth first, with branch
children 0 through 15 before occupancy, in the unchanged C14 order.

An inline list is reencoded from the exact successfully parsed `RlpItem` subterm,
not reconstructed from nibble/path fields. Prove subterm `Encodable` inheritance
and canonical-wire reencoding via EthCodec's public laws. Preserve accepted raw
HP flag/padding bytes in `Enc.rlp`; no normalization, authenticity guard or inline
width restriction is introduced. Empty decoded nodes remain `none`, without an
`Enc`, even if their entered raw input queried before dispatch/rejection. A private
pure admission kernel may consume raw bytes and the already acquired optional
answer, with length/cache and recursive-domain proofs; it is not another public
pure cache-bearing decoder and cannot skip malformed-preimage queries.

**Pure lookup contract (Q59; supplied locally).** C20 and the seven supplied equations
in §7 determine every finite bare input, with no Enc/WF/path/child-kind/arity premise.
Bounds are checked only for the actual selected slot of a nonterminal branch. Stub
failure precedes exhaustion; terminal branch value precedes bounds. Lookup never hashes,
encodes, decodes, consults a DB/default or mutates its inputs. Source correspondence is
restricted as stated in C20; the original decoder's sixteen-child construction
(`inc:972–974`) does not certify every bare nominal constructor or establish a completed
reachable output invariant/guest adapter.

## 6. Data structures

| Type | Representation | Model | Abstraction | Invariant | Persistence | Complexity |
|---|---|---|---|---|---|---|
| `Nibbles` | `ByteArray` with bound proof | `List (Fin 16)` | `toList` | every byte `< 16` | value | generate O(n) plus callback; slice O(k) copying; compare O(1+common prefix); source bounds only (Q49) |
| `Trie K V` | `ExtTreeMap K V` | finite map with arbitrary default | `trieGet` | `NoDefault` is a separate setter-reachable predicate; preparation/root require distinct `PrepareSafe`, not `NoDefault` (Q53) | value | O(log n) |
| `NodeDB` | `Std.HashMap Hash32 ByteArray` | finite map | `get?` | `NodeDB.Authentic keccak256` (established by `NodeDB.build` at `Id`; a predicate, not a field, F4) | built linearly, then **read-only shared** | build expected O(n) plus one keccak per entry; lookup expected O(1) (not worst-case; ARCHITECTURE §5.0) |
| `Node`/`Ref` | inductive with immutable `Enc` per resolved node | a set of maps (`represents` is a relation, D25) | `represents` | `Enc` agrees with C18/C19; ext child is a branch or stub; every branch has exactly 16 children (F5) and occupancy ≥ 2 | functional; tries are not snapshot-reachable (built once per root computation), so path copying suffices | lookup O(d) node steps (d ≤ 64 branch levels for secured keys) plus path comparisons; update/delete O(d) nodes rebuilt, each with one RLP encoding and ≤ one keccak; `rootHash` O(1) (cached at the root) |

The §3 carriers supply none of this row's semantic or cost guarantees; its
outstanding admission/provenance gates are owned by §10. `Enc` stores completed
raw/cache values. No update/root cache schedule is implemented. Mutable dirty or
missing-cache intermediates require a separate representation/refinement design
under B15/Q33/D25; they have no representation in these mandatory `Enc.rlp` fields.
Q59's supplied bare lookup ignores every raw/cache field and imposes no admission invariant.
Its selected-access source domain is key-dependent; F5's future admitted size16 invariant
is sufficient but stronger. Proper-child traversal, not remaining-key-only descent,
terminates finite empty-extension chains. The supplied offset traversal avoids copying
the complete remaining suffix at every branch or scanning off-path children (D18);
its private copying reference has ordinary all-bare-input equality (D25). Aggregate
allocation, speed and composed resource bounds remain unmeasured.

**DAG decode memo (DISC-004, B15; distinct from F6).** Not selected; Q55 baseline has no completed-node memo. Any future sharing must preserve raw/cache values, path-dependent errors and observations under explicit oracle premises. Lifetime and effect refinement remain open. No adopted bound or D18 exception; measure any candidate.

NodeDB reuses EthBase's Q51 Hashable Hash32 support and existing actual-equality
laws (EthBase §3). Public Std map laws supply insertion/lookup, distinct-key
preservation and equal-key overwrite without a distinct-support-hash premise.
C12 construction and concrete authenticity are supplied by the implementation
rows in §3; Keccak keys come from KeccakQuery (D5/F4). Expected table bounds remain
conditional on a suitable distribution; adversarial-distribution, allocation and
composed cost measurements remain open (ARCHITECTURE §5.0, C1–C4).

Computing `Enc` strictly in the smart constructor re-hashes the whole path on every update (O(u·d) keccaks for `u` updates), whereas EELS hashes each dirty node once at root time. A concrete-value comparison may justify either under its representation/cache premises; whole generic update/root query-trace equivalence is a separate obligation. The choice is internal to this module (DECISIONS B15, Q33) and remains unselected by Q55.

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
Recursive C7 supplies public dispatch/extensionality and private every-node
representative independence. C8 supplies the total local root and ordinary
reference/fused equality (§3). Canonicality and aggregate copying/comparison
costs remain open.
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

### 7.0.3 Typed defaults, preparation validity and root composition (Q53)

The storage/safety and generic unsecured preparation laws are implemented as listed
in §3, including typed-root composition; concrete consumer bridges remain unimplemented. `Valid` is preparation validity for the chosen
typed interpretation, independently of a particular trie default; no `Decidable Valid`
instance is required. The class supplies only encoding nonemptiness under `Valid`.
Empty construction establishes `NoDefault` and `PrepareSafe` for **every** supplied
default. Neither predicate implies the other: a stored default can have a valid nonempty
encoding, and a stored nondefault can encode to empty or interpret Python `None`.

Under `[Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]`, and additionally
`[BEq V] [LawfulBEq V]` for setters, require these informal statements:

```lean
theorem trieGet_set_same : trieGet (trieSet t k v) k = v
theorem trieGet_set_of_ne (hne : k' ≠ k) :
  trieGet (trieSet t k v) k' = trieGet t k'
theorem trieSet_noDefault (h : t.NoDefault) : (trieSet t k v).NoDefault
theorem trieSet_prepareSafe_iff [TrieValue V] (h : t.PrepareSafe) :
  (trieSet t k v).PrepareSafe ↔ v = t.default ∨ TrieValue.Valid v
```

Setters preserve `secured` and `default`; copies preserve both predicates and all
observations. No `Valid` premise restricts the all-value setter. A retained
`[TrieValue V]` setter binder for compatibility would add no equality/validity premise.
An `Option ByteArray` interpretation can use total `encode none := empty`,
`encode (some b) := b` and `Valid v := ∃ b, v = some b ∧ b ≠ empty`.
With default `none`, `some empty` is stored but cannot satisfy preparation safety.
This total extension does not say Python `encode_node(None)` succeeds: it raises
locked `EncodingError`, while preparation raises its earlier explicit `AssertionError`.
No guest outcome or runtime error channel changes.

`KeyBytes` supplies an injective interpretation and comparison equality with ordinary
byte-list lexicographic order. The List comparator is a proof model, not a required
executable conversion. Source Bytes/fixed-byte keys compare by content: a tagged key
union with two distinct keys for the same bytes cannot meet this contract. A concrete
consumer must supply lawful key order/equality agreeing with that interpretation.
For the conditional existing-Bytes choice, EthBase §3/§5/§7 supplies Q54's
`Ord Bytes`, `Std.TransOrd`, `Std.LawfulEqOrd`, actual-equality and
packed-export List laws. The adapter, its named `toBytes_bytes` exact-export
contract and public-only complete preparation/root clients are owned by §3/§5.
Concrete source alias/equality bridges and consumer cost integration remain open;
generic Q53 preparation/storage contracts do not depend on choosing Bytes.

For `[TrieValue V] [KeyBytes K]`, `unsecured : t.secured = false` and
`safe : t.PrepareSafe`, require the following equations; preparation uses `Monad` only,
and root additionally uses `KeccakQuery`. Neither requires `NoDefault`:

```lean
theorem prepareTrie_eq {m} [Monad m] :
  prepareTrie (m := m) t unsecured safe = pure (prepareTrieModel t)
theorem root_eq_mathRoot {m} [Monad m] [KeccakQuery m] :
  root emptyRoot t unsecured safe = mathRoot emptyRoot (prepareTrieModel t)
theorem root_empty {m} [Monad m] [KeccakQuery m] (h : t.data = ∅) :
  root emptyRoot t unsecured safe = pure emptyRoot
theorem root_eq_reference {m} [Monad m] [KeccakQuery m] [LawfulMonad m] :
  root emptyRoot t unsecured safe = (do
    let prepared ← prepareTrie (m := m) t unsecured safe
    mathRoot emptyRoot prepared)
```

The executable root calls C8 directly on the pure prepared map; its composition and
empty equations use `Monad` alone. The separate sequential reference equality needs
`LawfulMonad` for `pure_bind`. Empty input reaches C8's explicit empty case without
a preparation bind, new local query or failure (Q50). Nonempty roots preserve C8's
complete preimages/answers, prior state and original underlying failures. Callers
project `emptyRoot` from their existing coherent `HashConsts` context (F20 and
CONTRIBUTING §7.2); typed root never reacquires constants. Any supplied value defines
the local operation; pinned `Id` root agreement additionally requires the coherent
pinned empty root.

Source correspondence applies only to concretely interpreted valid supported non-`None`
values, exact encoding dispatch/equations, value equality agreement with Python on
supplied-default comparisons, lawful byte keys, complete source-schema and assembled-node
`Encodable` premises (Q47), coherent F20 constants and pinned host compatibility.
Lawful Lean equality alone does not prove Python equality agreement. `encode` remains
total on all Lean `V`; invalid encodings have no source-success claim. Injective
unsecured keys make the pure prepared map independent of insertion history; this does
not license generic secure query reordering. Secure preparation/root, traversal order,
collisions, source history and generic oracle coupling remain open. No hash-injectivity
assumption enters totality, and no sorted collision policy is selected.

### 7.0.4 Decoder diagnostic declaration support

Q52's constructors are distinct by ordinary inductive equality. The public
clients in §3 prove wrapper injectivity and use `compactToNibbles_error_iff` to
exclude either field diagnostic and `pathEmpty` from compact primitive failures.
Public codec success binds the whole wire and supplies `Encodable`;
`failed_rlp_no_item` states generic `Except` success/error exclusivity. The declaration
clients support ordering arguments; complete C14 dispatch is separately owned by
§3, while the WitnessError/O4 adapter remains unimplemented.

### 7.0.5 Pure lookup equations (Q59; discharged locally)

Exactly these seven public laws are supplied in `Lookup.lean`. They expose complete
inputs/results and unconstrained Enc; no public offset/reference/prefix/domain/measure
helper is added. All operational and structural support stays private.

```lean
theorem lookup_none (key : Nibbles) : lookup none key = .ok none
theorem lookup_hashed (h : Hash32) (key : Nibbles) :
  lookup (some (.hashed h)) key = .error (.unresolved h)
theorem lookup_leaf (path : Nibbles) (value : ByteArray) (enc : Enc) (key : Nibbles) :
  lookup (some (.leaf path value enc)) key =
    .ok (if path = key then some value else none)
theorem lookup_ext (path : Nibbles) (child : Node) (enc : Enc) (key : Nibbles) :
  lookup (some (.ext path child enc)) key =
    if path = key.take path.size then lookup (some child) (key.drop path.size)
    else .ok none
theorem lookup_branch_emptyKey (children : Array Ref) (value : ByteArray)
    (enc : Enc) (key : Nibbles) (hkey : key.size = 0) :
  lookup (some (.branch children value enc)) key =
    .ok (if value.size = 0 then none else some value)
theorem lookup_branch_index (children : Array Ref) (value : ByteArray)
    (enc : Enc) (key : Nibbles) (hkey : 0 < key.size)
    (hindex : (key.get ⟨0, hkey⟩).val < children.size) :
  lookup (some (.branch children value enc)) key =
    lookup (children[(key.get ⟨0, hkey⟩).val]'hindex) (key.drop 1)
theorem lookup_branch_oob (children : Array Ref) (value : ByteArray)
    (enc : Enc) (key : Nibbles) (hkey : 0 < key.size)
    (hindex : children.size ≤ (key.get ⟨0, hkey⟩).val) :
  lookup (some (.branch children value enc)) key =
    .error (.malformed (.branchIndex (key.get ⟨0, hkey⟩).val children.size))
```

The selected index is derived from the actual key, never an independent caller-selected
slot. The in-bounds Array access uses the stated hindex proof. Public Nibbles/Array laws
supply bounded digits, clipped prefix/suffix and private proper-child size support.
Source value/stub correspondence additionally requires valid selected accesses, complete
nominal/source field correspondence, the actual Hash32-to-64-nibble bridge and host
premises. Python IndexError on an out-of-range selected slot is documented separately from the selected
typed adaptation; neither supplies a reachable guest fault/output (CONTRACT O4/O13).

### 7.1 Totality [T]

- C12 construction is a total finite Array fold, with a total structural List reference/model.
- Q53 preparation is a total stored-map fold; its mapped-list reference has ordinary equality.
  The safe/unsecured preparation frontend wraps that complete map in `pure`; typed root
  directly calls total C8 on the pure map without another bind.

- `compactToNibbles`, `mathRoot` (empty dispatch or actual C7 then one query), `patricialize` (Q50 reachable domain; private Σ remaining full-key lengths support strictly decreases through each child and positive shared extension), `encodeInternalNode` (nonrecursive assembly plus total RLP and one monadic query), `lookup` (Q59 finite proper-child Node-size descent, including zero-key-consumption empty extensions; private Array/Option child decrease), `update`/`delete` (their separate mutation domains/descent proofs; leaves terminal), `decodeRoot` (lexicographic: DB entries not on the current path, then inline subterm size; ARCHITECTURE §5.4). All are total on arbitrary DBs without collision assumptions. Q55 adds a finite acquisition/parse/admission stage before recursive continuation; prove its decreases and full path invariant, rather than assuming hash injectivity. This cycle totalization makes no claim about Python's finite host-limit query trace.

### 7.2 Per-operation commuting obligations (D25) [C]

The remaining whole-trie laws are stated at `m := Id` (concrete `keccak256`),
with its concrete interpretation; complete decoder premises explicitly use
`Id.run (decodeRoot emptyRoot db r)`. `mathRoot t` abbreviates
`Id.run (mathRoot emptyTrieRoot t)` with the reference constant, and likewise for
`rootHash`, `update`, `delete` and `buildMpt`. Coupling at a generic oracle monad
belongs to `EthSecurity` and remains open (D5).

- Typed get/set and storage/safety equations are discharged in §3. Generic preparation equations are discharged in §3; typed-root equations are discharged with the exact domains and monad-law premises in §7.0.3.
- Invariant preservation: `update`/`delete`/`mkBranch`/`mkExt` preserve `Canonical` and the `Enc` rule.
- Simulation for the **root-compatible** abstraction relation (which includes canonical encoding/commitment compatibility, not just matching lookups): `represents t m → update t k v = .ok t' → represents t' (m.insert k v)`; `represents t m → delete t k = .ok t' → represents t' (m.erase k)`; `represents t m → lookup t k = .ok r → r = m[k]?`; `represents t m → rootHash t = mathRoot m`. No collision assumption is needed for these: they are structural, because the smart constructors mirror `patricialize` (Nipkow et al. Ch. 12 `nodeP` pattern).
- `rootHash (canonTrie m) = mathRoot m`; `represents (buildMpt m) m`.

### 7.3 Canonical form and order independence [C]

These still-open sketches require a faithful encoded-value/representation domain: every stored encoded value is nonempty, resolved trees have no stubs/caches, and actual child-reference realization and complete assembled `Encodable` premises are supplied. Total C7 retains empty values; a terminal-empty binding and its absence can have identical complete preimages. The security-local [ToVCVio](ToVCVio.md) shell/shape and safe prepared-image laws establish only their bounded local facts, not this canonicalizer or map agreement.

- `Canonical (canonTrie m)`; `Canonical t ∧ Canonical t' ∧ (∀ k, lookup t k = lookup t' k) ∧ no stubs → canonicalSerialization t = canonicalSerialization t'` (representation/cache identity is not required) (Exercise 12.1).
- `patricialize` selects the minimum key. Private `patricializeWith_independent` proves equality of complete recursive constructions for arbitrary valid map/depth-dependent member selectors at every node. Public dispatch equations permit any actual representative without exporting the selector seam.
- **Order independence of successful roots:** under the canonical representation/encoding hypotheses, if two update sequences from `t` both succeed and produce the same final map `m'`, both roots equal `mathRoot m'`. This does not cover arbitrary accepted noncanonical witnesses: C19 gives a no-op deletion that changes the root. There is no general licence to reorder witness updates.

### 7.4 Trie agreement theorem (collision-reporting form) [C], feeds [S]

After Kestrel ACL2 `mmp-trees.lisp` and Miller et al. (ARCHITECTURE §5.4):

```lean
theorem decode_agreement (consts : HashConsts) (db : NodeDB) (r : Hash32) (t : Ref) (m)
    (hconsts : consts = Id.run HashConsts.query)
    (hauth : db.Authentic keccak256)
    (hdec : Id.run (decodeRoot consts.emptyTrieRoot db r) = .ok t) (hroot : mathRoot m = r) :
    represents t m ∨ ∃ x y, collisionWitness db m = some (x, y) ∧ x ≠ y ∧ keccak256 x = keccak256 y
```

This still-open outline additionally requires the faithful encoded-value and representation premises of §7.3, exact child realization and one shared deterministic hash interpretation. A comparison of empty and nonempty roots needs actual empty-root coherence; an arbitrary supplied empty constant supplies no second colliding preimage.

The collision pair consists of a DB entry (or an inline subterm) and a node encoding of `canonTrie m` at the same position. It also covers every non-canonical acceptance of C16: a non-canonical node under a root equal to a canonical root is a collision. The composed statement for a root computation is: `decodeRoot` then a successful `mptSet` sequence yields `mathRoot (m.applyAll ops)` for every `m` in that faithful encoded-value/representation domain with `mathRoot m = r`, or a computable collision. Arbitrary accepted lenient witnesses still need their own provenance/representation analysis; these sketches change no total core or witness behavior and close no source/security gate.

### 7.5 Data availability (progress) [C]

- Q59: on finite bare inputs, `lookup t k` fails iff the walk reaches a stub or a nonterminal branch with a out-of-range selected slot. On the explicit valid-selected-access domain it fails iff a stub is reached; this premise is not a runtime key/WF restriction. Source correspondence retains C20’s Hash32/source-class/host premises. The seven defining lookup equations and all-bare reference equality are supplied in §3;
  whole map/source agreement remains open. `update` fails iff the insertion path reaches a stub; `delete` fails iff its path reaches a stub or a collapse leaves exactly one child that is a stub. For a pruning `t` of `canonTrie m`, "all nodes on the path of `k` resolved" implies success of `lookup`/`update`; for `delete` additionally "the sibling of every collapsing branch resolved". Authenticated absence (a mismatching leaf or empty child on a resolved path) is success.
- Conjectures to settle: success of an insert-only (resp. delete-only) sequence is independent of its order.

### 7.6 Caches [C]

- Q55's successful resolved node keeps the complete admitted raw bytes in `Enc.rlp`; `Enc.hash?` is `some` iff raw length is at least 32, and that value is the actual occurrence's query answer. This includes exact reencoded parsed inline lists and arbitrary alias-keyed DB entries. Short authentic DB entries still have no cached hash. Smart-constructor field encodings and C18/C19 observers remain distinct obligations.
- At concrete `Id`, `db.map[h]? = some raw` and `NodeDB.Authentic keccak256 db` imply `keccak256 raw = h`; only with `32 ≤ raw.size` does this identify a decoded cache hash with the reference. Authenticity is needed for root binding/security, not arbitrary-DB admission or totality. Finite acyclic pinned source cache agreement additionally needs RLP/`Encodable` and host compatibility.
- Prove local empty/missing/stub equations, threshold/query-before-whole-RLP, verbatim answers, unchanged first typed error/descendant propagation and underlying failing-query forwarding/no later query. Exercise arbitrary, recording, stateful and failing oracles, including long malformed raw inputs, nonliteral empty roots, repeated siblings, short authentic entries and long inline/alias-keyed nodes. Generic sequencing transformations state `LawfulMonad` explicitly.
- A pure hash-relative value model under `H` can compare with the generic action only under explicit relevant-occurrence equations `KeccakQuery.keccak b = pure (H b)` and `LawfulMonad` for sequencing. This conditional value theorem supplies no failing/stateful trace equality or whole-trie coupling.
- B15 DAG memoization is unselected. Successful-node sharing may suppress repeated queries or reuse a stateful first answer; it needs mathematical/cache, path, effect and first-error refinement. Hash-only cached cycle failures are not justified by accept/reject agreement. F6 has a different per-root backend lifetime. Python's unmemoised host behavior remains DISC-001/DISC-004; no production cost/resource gate follows from this baseline.
- [R] Exact reproduction of C18/C19 on non-canonical witnesses is a conformance obligation (checked by the adversarial `#guard`s against EELS), not a theorem about the model.

### Informal correctness argument

**Claim.** Canonical full tries implement the mathematical finite-map root, while witness operations reproduce the reference's lenient decoding, cached raw encodings and ordered incremental updates on every successful path.

**Premises.** Codec/hash equations; explicit distinction between canonical representations and accepted raw witness representations; finite graph traversal with cycle detection; available sibling nodes when collapse requires them.

**Argument.** Induct on the existing construction domains for canonical construction and on finite proper-child Node size for Q59 bare lookup; an empty extension still moves into a proper child. Terminal branch dispatch precedes selected-slot bounds, and only the selected child is visited. The valid-selected-access source bridge is separate from the typed out-of-range selected-slot adaptation. Extension/branch/leaf cases partition keys; smart constructors compress precisely the empty and single-child cases. For incremental updates, the same cases prove lookup preservation and the new value at the updated key. A collapse onto a stub must resolve that stub or fail, which explains order-dependent success. Witness decoding tracks the current path: an on-path repeat rejects a cycle. Q55's baseline enters each shared sibling occurrence separately and obtains its eligible raw digest before parsing; completed-node reuse is a separate B15 refinement. Preserve the source encoding of unchanged nodes and re-encode only dirtied paths. Consequently canonical root uniqueness and successful update order independence apply only under canonical-representation hypotheses. They are false for general accepted witnesses: even a no-op delete can canonicalise an accepted noncanonical leaf and change its root.

**Open obligations.** Define canonicality separately from lookup agreement, prove cached-encoding and memoization refinement, and resolve host RecursionError differences. Hash-relative full-root folding also needs an explicit secure-key collision/order convention. Totality must not assume hash injectivity.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthCodec`
- **Used by:** `EthStateCommit` (state and storage tries), `EthBlock` (transaction, receipt and withdrawal roots through `Trie`/`root`), and transitively `EthStateFull`, `EthStateWitness`, `EthSecurity`.
- **Pure path seam:** the public bounded List abstraction and the path equations/laws of §7.0 supply digit order, canonical compact output, lenient decoding and maximal prefix comparison; future node/trie consumers still own their contracts.
- **Typed seam (Q53):** EthCommit supplies generic `Trie`/`TrieValue` storage/safety, `KeyBytes` and pure unsecured preparation laws (§3); typed root composition is supplied; concrete encoding bridges remain unimplemented. Consumers prove stored-value `PrepareSafe`, lawful byte-key interpretation and concrete Python equality/encoding agreement, and pass their coherent F20 empty root. `NoDefault` alone is insufficient. Initial root/preparation calls additionally prove `secured = false`; EthBlock owns its concrete value instances, and EthStateCommit owns contextual Account/storage integration.
- **Seams provided:** C12 `NodeDB.build`/`Authentic` and ordinary query/model/Id laws (§3); C7 `patricialize`, C8 `mathRoot` on prepared full-nibble maps and Q53 typed `root` (§3); complete generic `decodeRoot`/`decodeWitnessToMpt` and their three equations (§3); pure bare `lookup` and seven constructor equations (§3); the following trie seams remain unimplemented: `mptSet`/`mptRoot` (the partial trie behind the witness backend; replacement exercise 2 replaces exactly this), `represents` and the agreement theorem (for `EthStateCommit` and `EthSecurity`).
- **Relies on:** `EthCodec`'s strict RLP decode, its round-trip `encode (decode b) = b`, and RLP injectivity/prefix-freeness (for the collision theorem's reduction); every keccak through `EthHash`'s `KeccakQuery` (reached through `EthCodec`; D5), with its `ExceptT`/`StateT` lift instances (F15) and concrete `keccak256` at `Id`; `HashConsts.emptyTrieRoot` supplied by the caller (C5).
- **Guarantees:** totality; the laws of §7; key sequencing is the caller's responsibility (C26).

## 9. Open decisions

- D4: keccak dominates decode/root cost; the reference or a proved fast path.
- D5 (broad scope, monad-parametric): `NodeDB.build`, the smart constructors, `update`/`delete`, root hashing and `mathRoot` go through `KeccakQuery`; complete decoders follow Q55's generic pre-RLP acquisition; lookup stays pure; `NodeDB.Authentic` is a separate predicate; the empty-trie root is `HashConsts.emptyTrieRoot` (F4, C5, C12, C13). Open: coupling at generic `m`.
- D16, D20 (accepted): generic over bytes; `encode_account` stays outside.
- D18: HashMap expected bounds for `NodeDB`; any future memo requires measured/refined costs. Q55 adopts no production exception.
- D19 (accepted): eager decoding at B4 triggers; B15 sharing remains unselected, with the additional Q55 effect/path obligations in §7.6.
- D25 (accepted): `represents` as the abstraction relation.
- Q59: the approved disposition is owned by DECISIONS; C20/§§5/7 specify the supplied pure bare lookup, exact selected-slot diagnostic and seven equations. Private structural/reference proofs and complete-value/source controls are supplied locally; guest adapters remain unimplemented; no WF/cache/mutation/root/security/resource/readiness claim follows.
- Q55: complete generic operations, three public equations and private totality/acquisition/inline/ordered-error laws are supplied in §3. Whole agreement, generic interpretation/action lifetime, consumer bridges and cache bundles remain open.
- Q50: the explicit reachable-domain proof and supplied-empty-root interpretation follow C7/C8/§5; domain/descent and recursive C7 construction with finite authenticated source agreement are in §3; the total local C8 wrapper is supplied in §3; whole-source refinement remains open.
- Q53: arbitrary supplied defaults, separate preparation validity, lawful injective byte keys and
  the initial unsecured proof domain follow §2/§5/§7.0.3. Generic storage/safety/key
  interpretation/preparation are supplied in §3; typed root composition is supplied; the
  conditional existing-Bytes key instance is supplied in §3, while concrete consumer
  value/source bridges remain unimplemented; secure ordering/collision/source-history and generic
  coupling remain open.
- Q49: bounded construction, clipped copies and lawful ordering use the exact provider equations in §3/§5/§7.0; root domains and decoder allocation replacement are separate.
- Q52: two-item path-list and leaf-value-list diagnostics follow C14/§5; complete dispatcher ordering and source acceptance controls are supplied in §3/§4, while WitnessError/guest adapters remain open.
- Q48: raw empty compact diagnostic ownership is distinct from the later empty decoded extension-path failure; C3/§5/§7 specify the seam.
- NEW-COMMIT-1: DECISIONS B3 (Q32): `Ref` hidden behind the trie API; `Option Node` only if it keeps the provenance DISC-003 needs (decode-side committed conformance in §3; full representation/root/mutation gate remains open).
- NEW-COMMIT-2: DECISIONS B15 (Q33): internal and interface-neutral; strict versus lazy `Enc` still open (§6).
- NEW-COMMIT-3: DECISIONS B3 (Q34) and DISC-003: reproduce the reference's non-canonical acceptances (C16, C19); a deviation needs an accepted decision record.
- NEW-COMMIT-4: DECISIONS B15 (Q35) and DISC-004: memoised decoding needs a proof that it preserves accept/reject, error precedence and observations (§7.6); host-resource interaction is DISC-001 (O12 unresolved).

## 10. Gaps

- **Pure lookup (Q59; supplied local operation):** the selected-slot diagnostic, total operation
  and exactly seven constructor equations are supplied in §3, with private structural proper-child
  Node/Array/Option support, all-bare offset/reference equality, public-only clients and §4
  complete optional-value/first-error/cache-independent cases. Source value/stub agreement
  requires valid selected accesses and actual Hash32-to-64-nibble/source-class/host premises; odd
  generalized Nibbles and the typed out-of-range-slot adaptation are separate law/test domains. No
  reachable decoder/mutation invariant or guest outcome adapter follows. D18/D25
  executable/reference equality is supplied; aggregate copy/scan/resource costs remain unmeasured;
  decoder/WF/cache/update/root/security/generic coupling/lifetime/whole W1/S2/C1–C4/O12 and guest
  readiness obligations remain open.

- **Nominal partial-trie carrier scope:** exactly Enc/Node/Ref and secured/root IncrementalMPT are
  supplied in §3, with private public-import full-field/variant/recursive-array clients and
  declaration-audited generated support. Node.WF and its exact generic cache/provenance/timing
  meaning, childRef, smart constructors and update/delete/root operations remain
  unimplemented. Complete generic decoding and pure bare lookup are supplied separately in §3. Bare arbitrary
  arity/malformed cache/path/child expressibility is not admission. B3/NEW-COMMIT-1/DISC-003
  provenance sufficiency and eventual representation hiding remain unproved. The carriers alone
  discharge no C18/C19/canonicality/map/security/W1/S2/R2/G/C1–C4/O12/guest/EEST gate; no cache
  or host policy is selected.

- **Implemented slice:** C12 raw construction, ordered reference/model laws, full last-write lookup and concrete Id authenticity (§3). Decoder/root/cache/security composition and generic oracle coupling remain open; the finite complete-map and sibling tests do not discharge C1–C4 or R4.

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **Non-canonical acceptance** (C16, C19) is verified only on hand-made examples; no fixture exercises it, and upstream has not been asked whether it is intended. The `0x80` flip (C16(f)) means "extra unused entries are harmless" is false in general.
- **Decoder composition (Q55; partial W1):** complete generic operations and local totality/threshold/raw/inline/ordered-error laws are supplied in §3, with full finite state/failure/source conformance. Concrete Id/root binding still needs coherent F20 constants and authenticity plus eligible length; generic interpretation, consumer Id/error bridges and lifetime, whole cache/update/root/source simulation and W1 remain open.
- **Exponential decode on DAG witnesses** (C17) remains DISC-004. Q55's no-completed-memo baseline supplies sequencing, not a production cost bound; a B15 memo needs value/cache/path/effect/first-error refinement and host compatibility, distinct from F6 and DISC-001. No guest cycle budget or resource policy is adopted.
- **Inline witness representation:** the complete decoder privately composes inherited Encodable, exact reencoding/reparsing and strict actual-subterm descent at C15 (§3). Whole accepted-witness representation/source simulation and cache/update bundles remain open.
- **Order-sensitivity conjectures** (§7.5) are unproved; the mixed-order counterexample is verified.
- **No proof strategy yet** for `decode_agreement` in detail: the definition of `collisionWitness` (which pairs are compared, how inline subterms are included) and its computability need a design; Kestrel's `mmp-trees.lisp` is a shape, not a proof to port. Cassez (FM 2021) is precedent for incremental-equals-scratch only.
- **Canonical uniqueness** for a hexary witness trie with branch values and variable-length keys remains open and needs its actual value/representation premises. Recursive C7 representative independence is proved in §3; the Nipkow chapter is binary.
- **Internal-node scope:** C6 operational/model/lift laws are proved as in §3/§7.0.1. Complete standard-domain and Python Extended interpretation/host premises remain caller obligations. C8 supplies the total local wrapper and ordinary reference/fused equality (§3). Witness/cache/database laws, canonical trie-shape conditions and resource gates remain open; recursive C7 is supplied in §3. Empty extension paths and arbitrary nested fields are valid C6 inputs; witness validity is a separate contract.
- **Pure path scope:** the `Nibbles` representation/invariant, implemented pure path operations and Q49 bounded generation/clipped copies/lawful order are discharged as in §3/§7.0. Q50 domain/strict sum-descent support is discharged in §3. Private longest shared-prefix selection and its domain/maximality/representative laws, and bounded private branch partition/ending/callback-C6 sequencing support, are supplied in §3. Recursive C7 and every-node representative independence are discharged in §3. C8 is supplied in §3. Trie mutation/integration, aggregate copy/allocation costs and C1–C4 measurements remain open; slices copy O(k).
- **Field diagnostic composition:** complete C14 assignment/order, descendant propagation, ending-list leniency and eager decoding are implemented in §3. WitnessError/O4 adapters and whole W1 remain unimplemented; finite source observations are conformance evidence.
- **Compact decoding scope:** Q48's empty diagnostic, lenient value model, canonical inverse/injectivity and accepted-wire normalization are discharged in §3/§7.0. The later extension-path rejection is supplied by the complete decoder (§3); witness/guest adapters and whole-trie/W1 proof remain unimplemented. Allocation replacement belongs to DEBT-COMPACT-DECODE; no arbitrary accepted-wire byte identity is claimed.
- **Additional Nibbles interfaces:** future consumers use the supplied equality and lawful ordering in §3/§7.0. Any additional default-value or container-specific interface remains a scoped consumer obligation behind the private storage boundary.
- **Unsecured-trie key properties:** the transaction/receipt/withdrawal tries use RLP-encoded indices as keys; whether they are prefix-free matters only for the branch-value case of `patricialize` and is not checked here.
- **Typed-trie contracts (Q53):** generic storage, the `TrieValue` class, separate `NoDefault`/`PrepareSafe` laws, injective byte-lex `KeyBytes` and pure unsecured preparation with public clients are discharged in §3. Generic typed root and caller-empty-root equations of §5/§7.0.3 are supplied with public proof-only clients and §4 validation. Concrete encoding bridges remain open. Initial preparation/root proofs cover unsecured safe tries only; secure traversal/collisions/source history and generic coupling remain open.
- **Existing-Bytes key adapter (Q54):** `instKeyBytesBytes`, its named exact-export `toBytes_bytes` equation and ordinary all-finite injection/order fields are discharged in §3, with private public-import complete generic map and root clients. Choosing a concrete Python key/equality/alias interpretation, consumer encoding/root agreement, actual map/preparation/root/retention/replacement and C1–C4 costs remains open; no raw ByteArray order, additional production value/default/equality instance or secured policy is supplied.
- **`TrieValue` consumer instances (Q53):** EthBlock must supply valid legacy RLP and nonempty typed Bytes/withdrawal-already-RLP interpretations without double encoding. EthStateCommit owns contextual Account integration; this class does not furnish a bare Account instance. Concrete equality, schema/assembled `Encodable`, F20 and host premises remain required for source/root agreement.
- **Host-side items** (C28) are specified at reduced depth; whether they belong in `STFSpec/informal/EXCLUDED.md` (G6) instead is undecided.
- **EEST coverage** of witness malformations is thin: `eip8025_optional_proofs` covers missing nodes and extra nodes, not malformed RLP, bad node shapes, cycles or non-canonical encodings; the EELS unit tests cover node shapes only.
- **`Std` caveats:** `ExtTreeMap` has no proved cost bounds; `HashMap` bounds are expected only, and adversarial key distributions for `NodeDB` are unmeasured (keys are keccak outputs, so this is mostly moot, but the memo is keyed the same way).
