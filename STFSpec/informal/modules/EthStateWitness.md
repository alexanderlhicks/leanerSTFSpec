# `EthStateWitness`: the witness-state backend

*Status: informal specification, draft. Date: 2026-09-29. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F1, F4, F6, F7 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D5, D8, D18, D19 · questions: B1 (Q29/Q36), B4 (Q37), B15 (Q35), F6, F7; DISC-001, DISC-004.*

`ws:` = `forks/amsterdam/witness_state.py`. "[executed]" = run against the pinned EELS; "[inference]" = argued only.

## 1. Purpose

`EthStateWitness` implements `PreState` from an execution witness (ARCHITECTURE §5.4), mirroring EELS `WitnessState`: a node DB and a code DB built from the witness, the parent header's state root, eager decoding (D19) at the reference's trigger points, trie lookups and the post-state root over the partial trie. It proves `Models` up to a computable collision and a separate data-availability progress theorem. It is the backend of the stateless guest (`EthStateless`).

## 2. Requirements

- W1. **Construction** (`stateless.py:290–294`): node DB = `EthCommit.NodeDB.build witness.state`, code DB = `CodeDB.build witness.codes` (keyed by keccak, `ws:45–50`), state root = the last witness header's `state_root`. Both builds hash through the oracle (monadic, D5/F4); their authenticity is the separate predicates `NodeDB.Authentic`/`CodeDB.Authentic`, established at `m := Id`. The backend also carries the block's `HashConsts` (`emptyTrieRoot`, `emptyCodeHash`). Construction decodes nothing (W11).
- W2. **Decode trigger points** (O4; `ws:148–160`): the account trie at the first account access; a storage trie at the first `get_storage` of an account whose storage root is not `EMPTY_TRIE_ROOT`; in root computation, a **fresh** decode of every changed, uncleared storage trie (`ws:254–259`) and of the account trie (`ws:270–277`). Decoded read-only roots are cached by root hash (`ws:152–160`), so two accounts with equal storage roots share one decoding; that cache is not semantic (W10), and how the Lean backend shares storage-trie decodings is open (F6). Every decode is eager over everything reachable (`EthCommit` C13–C17). Decoding itself is pure (F4); lookups hash their keys through the oracle.
- W3. `get_account_optional a` (`ws:162–177`): look up `keccak256 a` in the decoded account trie (`EthCommit.lookup`; a stub on the path is O4(c): the `AssertionError` at `ws:73`, witnessed on 234 corpus inputs by running the pinned EELS over the full fixture corpus); absent → `none`; present → `EthStateCommit.decodeAccountLeaf`. Side effect: `storageRootCache[a] :=` the leaf's storage root, or `EMPTY_TRIE_ROOT` when absent.
- W4. `get_storage a k` (`ws:179–203`): if `a` is not in the cache, call `get_account_optional a` first (so an account-trie failure can surface here); an `EMPTY_TRIE_ROOT` storage root gives `0` **without decoding**; otherwise decode (cached) and look up `keccak256 k`; absent → `0`; present → `EthStateCommit.decodeStorageLeaf`.
- W5. `get_code h` (`ws:205–213`): `b""` for `EMPTY_CODE_HASH` (`HashConsts.emptyCodeHash`); else the code DB entry; missing → O4(d), an error, never an absent value (B2).
- W6. `compute_state_root d` (`ws:215–227`) delegates to `compute_state_root_and_trie_changes` (`ws:229–311`), which must be reproduced step by step:
  1. for each address with storage changes: if it is neither cleared nor cached, `get_account_optional` it; its old root is `EMPTY_TRIE_ROOT` if cleared, else the cached root; decode; apply **all non-zero writes first, then all zero writes** (deletions), each group in the diff's slot order (`ws:260–267`); record the new storage root;
  2. decode the account trie afresh;
  3. for each address in `storageChanges ∪ storageClears` (a Python `set`; iteration order hash-dependent) that is **not** in `accountChanges`: look the account up; if it exists, rewrite its leaf with the new storage root (`EMPTY_TRIE_ROOT` for a pure clear) (`ws:279–294`). `BlockDiff.storageClears` has no clear order, so this step's order is **open (F7)**: prove the W8 commutation or add a clear order;
  4. for each `accountChanges` entry **in first-write order** (`EthState` R6): `none` deletes; otherwise insert the encoded account with storage root: the new root if computed in step 1, else `EMPTY_TRIE_ROOT` if cleared, else the **cached** root, defaulting to `EMPTY_TRIE_ROOT` when the address was never looked up (`ws:296–309`);
  5. return `mpt_root` and an empty node list (`ws:311`).
- W7. **History condition.** Step 4's default means EELS's root depends on which addresses were looked up earlier. `EthState` guarantees every address in `accountChanges` was looked up (`AccountWritesLookedUp`, `EthState` R32). Under that condition, looking the account up again (pure, deterministic, and certain to succeed because it succeeded before) gives the same storage root; the Lean backend does so and needs no mutable cache.
- W8. **Order.** Preserve account first-write order and both storage-address and storage-slot first-write orders in BlockDiff. Step 1 partitions each ordered slot list into nonzero writes followed by zero writes, preserving order within each group. No map iteration substitutes for those lists. Step 3's storage-root-only rewrites of present accounts are conjectured to commute, but this needs proof for every accepted encoding, **including failures and observations**, before choosing a deterministic set order. Cross-address independence does not alone establish identical failure priority. This is F7 (open): `storageClears` has no clear order, so either prove the commutation or add a clear order to `BlockDiff` (`EthState` §7.5). A prototype's traversal (storage-address order, then the remaining clears in key order) is not adopted, and a first-clear order alone does not reproduce Python set iteration. The account, storage-address and slot orders are settled by B1.
- W9. **All failures are O4** and become `false` (`stateless.py:303`): missing root preimage, malformed reachable node, stub on a lookup/update path or collapsing onto a stub, missing code, and leaf-decoding failures (`EthStateCommit` SC5–SC6).
- W10. **Caches are not semantic** (ARCHITECTURE §7) except through W7: removing `_decoded_secure_roots` changes only cost; `_storage_root_cache` is replaced by re-lookup under W7.
- W11. **Decode timing** (B4, D19). Decode a root when the reference triggers it (W2), then eagerly decode everything reachable from it. Construction-time decoding of every storage trie is **not** required: pure functions decode on demand. Precomputation is permitted only after proving that its errors surface at the reference's triggers with the reference's precedence and observations (B15), and after measuring the extra work. "On demand" never means lazy, path-only validation. A malformed storage trie that execution never touches must remain accepted, and a malformed account-trie node anywhere must be rejected (the account trie is always decoded by root computation, `fork.py:350` → W6 step 2, unless the root is `EMPTY_TRIE_ROOT`). The following form compiles in a prototype of the interfaces: the account trie as a `Thunk (Except …)` decoded once, with any error surfacing at first access (`ws:148–160`), and storage tries decoded per query with no memo. The storage-trie memo is **open (F6)**: its ownership, lifetime and decode triggers are unspecified, and cache mechanics must stay outside semantic state. Until it is specified, per-query decoding is a DEBT candidate (D18).

## 3. EELS source map

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `forks/amsterdam/witness_state.py::build_code_db` | 45 | `CodeDB.build` | |
| `forks/amsterdam/witness_state.py::WitnessState` | 132 | `WitnessBackend` | caches replaced (W10, W11) |
| `forks/amsterdam/witness_state.py::WitnessState._get_decoded_secure_root` | 148 | `WitnessBackend.accountTrie`; per-query storage decoding | trigger W2; storage memo open (F6) |
| `forks/amsterdam/witness_state.py::WitnessState.get_account_optional` | 162 | `….getAccount?` | |
| `forks/amsterdam/witness_state.py::WitnessState.get_storage` | 179 | `….getStorage` | |
| `forks/amsterdam/witness_state.py::WitnessState.get_code` | 205 | `….getCode` | |
| `forks/amsterdam/witness_state.py::WitnessState.compute_state_root` | 215 | `….stateRoot` | |
| `forks/amsterdam/witness_state.py::WitnessState.compute_state_root_and_trie_changes` | 229 | `computeStateRootAndTrieChanges` | node list always empty |

`build_node_db` and `_trie_lookup` are claimed by `EthCommit`; `_decode_account_from_leaf` by `EthStateCommit`.

**External semantics.** `ethereum_rlp.rlp` (leaf decoding, `EthStateCommit`); Python `set`/`dict` iteration order (W8: dict order is insertion order and is observable in step 4; set order is hash-seeded and must be shown unobservable).

## 4. Tests

- **EEST fixture area:** `amsterdam/eip8025_optional_proofs` (100 files): `test_witness_validation_state.py` (missing storage proof node, missing absent-slot proof leaf, missing delete auxiliary node, missing sender, absent-account and failed-call-target account nodes, extra unused node, unsorted but complete), `test_witness_validation_codes.py` (missing codes incl. 7702 markers and system contracts; extra and unsorted codes), `test_witness_state_{reads,writes,deletes,replay_order}.py`, `test_witness_headers.py`. Every other `blockchain_tests` area runs through this backend when executed as zkevm stateless fixtures.
- **EELS unit tests:** `tests/json_loader/test_witness_state.py` (`TestBuildNodeDb`, `TestBuildCodeDb`, `TestGetAccountOptional`, `TestGetStorage`, `TestGetCode`, `TestComputeStateRoot`, `TestCanonicalSecureTrieValidation`).
- **`core` `#guard` cases:** a malformed storage trie never accessed (accepted); a malformed account-trie node off every path (rejected, even for a block that reads no account before root computation); a storage read of an account without storage (no decode); account-trie delete whose collapse needs a stub sibling, with the insertion ordered before and after it (W8 step 4); a pure storage clear of an untouched-account address (step 3); `getAccount?` failure surfacing first in `getStorage`; missing code; history condition: a root computation whose `accountChanges` address was never looked up (EELS uses `EMPTY_TRIE_ROOT`; documents why W7's precondition matters).
- **Differential:** against `EthStateFull` on complete witnesses (identical roots); against EELS `WitnessState` on random pruned witnesses (bug-finding).

## 5. Interface

```lean
-- public
variable {m : Type → Type} [Monad m] [KeccakQuery m]      -- D5; the guest uses m := Id
structure CodeDB where
  map : Std.HashMap Hash32 ByteArray
def CodeDB.Authentic (H : ByteArray → Hash32) (db : CodeDB) : Prop :=   -- F4: a predicate, not a field
  ∀ h c, db.map[h]? = some c → H c = h
def CodeDB.build (codes : Array ByteArray) : m CodeDB       -- keys through the oracle; Authentic keccak256 at Id

structure WitnessBackend where
  nodes : NodeDB
  codes : CodeDB
  stateRoot : Hash32
  consts : HashConsts
  accountTrie : Thunk (Except WitnessError Ref)   -- prototype form: pure decodeRoot, decoded once on first access (W11)
  -- storage tries: decoded per query (pure decodeRoot); a per-root memo is open (F6)
def WitnessBackend.build (nodes : NodeDB) (codes : CodeDB) (root : Hash32) (k : HashConsts) : WitnessBackend
def WitnessBackend.WF (w : WitnessBackend) : Prop :=       -- at Id
  NodeDB.Authentic keccak256 w.nodes ∧ CodeDB.Authentic keccak256 w.codes ∧
  w.consts = Id.run HashConsts.query ∧
  w.accountTrie.get = decodeRoot w.consts.emptyTrieRoot w.nodes w.stateRoot
-- build establishes WF when its DBs are authentic and k = Id.run HashConsts.query.
def WitnessBackend.toPreState (w : WitnessBackend) : PreState m
def computeStateRootAndTrieChanges (w : WitnessBackend) (d : BlockDiff) : m (Except WitnessError (Hash32 × List InternalNode))

-- the theorems are stated at m := Id (Models is at PreState Id, D5)
theorem WitnessBackend.models (w) (σ) (hwb : WitnessBackend.WF w) (hwf : MathState.WF σ) (hc : CodeAuthentic σ)
    (hr : mathStateRoot σ = w.stateRoot) :
    Models w.toPreState σ ∨ (StateCollision w.nodes w.codes.map.toList σ).isSome
theorem WitnessBackend.progress_lookup (w) (a) (hwb : WitnessBackend.WF w) : LookupAvailable w a → ∃ r, w.toPreState.getAccount? a = .ok r
theorem WitnessBackend.progress_root (w) (d) (hwb : WitnessBackend.WF w) : UpdatesAvailable w d → ∃ r, w.toPreState.stateRoot d = .ok r
theorem WitnessBackend.refines_eels : ...   -- under AccountWritesLookedUp, same results as WitnessState on the same call sequence
```

## 6. Data structures

| Type | Representation | Invariant | Persistence | Complexity |
|---|---|---|---|---|
| `NodeDB`, `CodeDB` | `Std.HashMap`, built linearly | `NodeDB.Authentic`/`CodeDB.Authentic` (keys are hashes of values; separate predicates, F4) | read-only shared | build expected O(n) + one keccak per entry |
| account trie | `Thunk (Except WitnessError Ref)` (prototype form) | its value equals `decodeRoot emptyTrieRoot nodes stateRoot` | forced once, then shared | one eager decode (with the DAG memo of `EthCommit`); lookup O(64) node steps |
| storage tries | none yet: decoded per query | each decode equals `decodeRoot emptyTrieRoot nodes h` | — | O(reachable storage-trie size) **per query**: a cost debt until the F6 memo is specified |
| root computation | `EthCommit.IncrementalMPT` per changed trie | as `EthCommit` | functional, linear use | O(u · d) node rebuilds for `u` updates |

Per-query storage decoding repeats work that EELS caches by root (`ws:152–160`). The per-root memo that would remove it is F6 (open; a DEBT candidate, D18): it must preserve the B4 triggers and B15 precedence and keep cache mechanics outside semantic state.

## 7. Contract and laws

- [C] **Agreement up to collision:** `WitnessBackend.models` — from `EthCommit.decode_agreement` on the account trie and on each storage trie, plus `EthStateCommit`'s leaf round trips; `WitnessBackend.WF` supplies node/code authentication and coherent constants/thunk; `ModelsCode` follows from its code-DB clause. These premises apply to arbitrary backend records, not only to records returned by `build`.
- [C] **Progress / data availability:** `LookupAvailable w a` requires successful eager account-root decoding (including off-path nodes), a resolved lookup path and successful account-leaf decoding. Storage lookup additionally requires successful eager decoding of its triggered storage root, a resolved slot path and successful storage-leaf decoding. `UpdatesAvailable w d` requires `BlockDiff.WF`, read-before-write, successful eager decoding at each W2 root trigger, every insertion/deletion path and every collapsing branch's remaining sibling resolved, and successful leaf decoding for every value inspected, **in the W6 replay order**. A resolved path alone is insufficient when malformed off-path nodes are eagerly decoded. Authenticated absence is success (ARCHITECTURE §5.3).
- [R] **Refinement to EELS:** for any sequence of provider calls made by `EthBlock` execution satisfying `AccountWritesLookedUp`, each call's result (value, or failure) equals EELS's; hence the guest's boolean is the same (W9, W11).
- [C] **Cache laws:** the account-trie thunk's value equals on-demand decoding; re-lookup equals the cached storage root under W7. Any storage-trie memo (F6, open) must equal per-query decoding, including error precedence (B15).
- [C] **Order laws:** step-3 commutation (W8; F7, open) and step-1 independence still need proofs. Slot iteration uses the diff's stored order, filtered into the nonzero and zero groups, so no insert/delete group commutation premise is required by the working interface.

### Informal correctness argument

**Claim.** On the reachable execution trace, successful witness answers and ordered root updates agree with the full-state model or yield an explicit collision, while unavailable data produces the reference failure.

**Premises.** WitnessBackend.WF (authenticated node/code dictionaries, coherent HashConsts and account thunk), initial root agreement, code authenticity of σ, the full code/node preimage set, EthCommit lenient decoding laws, immutable pre-state queries, and read-before-write for changed accounts.

**Argument.** Build node and code dictionaries in input order with the reference's duplicate-key policy. Lookup authenticates the relevant path and updates the account storage-root cache; repeating the lookup has the same answer. Reachable read-before-write ensures every changed account has its original storage root recorded, instead of the empty default. The pure provider redoes that immutable successful lookup (W7); its refinement is over reachable traces, not arbitrary history-dependent calls to the Python helper. Root computation processes storage-address and slot orders retained in BlockDiff, splitting slot writes into nonzero then zero groups while preserving order within each group. It then processes account changes in first-write order. Induct over these operations, applying the path/update agreement or extracting a collision. Preserve original raw encodings of unchanged nodes. Final storage-root-only account rewrites require a separate commutation argument before their iteration order can be changed.

**Open obligations.** Prove that last commutation law for all accepted witness encodings, complete cache-history reachability, and implement the collision extractor including σ's code bytes. Canonical full-state agreement is conditional; witness availability and host-resource compatibility cannot be deduced from the root alone.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthStateCommit`
- **Used by:** `EthStateless` (and `EthSecurity` in the security package).
- **Relies on:** `EthState`'s `AccountWritesLookedUp`, `BlockDiff.WF` and first-write `accountOrder`; `EthCommit`'s decoding, update semantics and agreement theorem; `EthStateCommit`'s leaf decodings.
- **Guarantees:** a `PreState` with `Models` up to collision, progress under availability, and EELS-equal accept/reject.

## 9. Open decisions

- D5 (broad scope, monad-parametric): node and code DB builds, key hashing in lookups, and root updates go through `KeccakQuery`; decoding is pure (F4); `toPreState` returns `PreState m`; the theorems are stated at `m := Id`.
- D8 (accepted): authenticated absence versus missing data.
- D19 (accepted): eager decoding from the reference's trigger (W11).
- NEW-STATE-1 (from `EthState`): resolved: DECISIONS B1 (Q29).
- NEW-WIT-1: resolved: DECISIONS B1 (Q36); only the clear order remains (F7).
- NEW-WIT-2: resolved: DECISIONS B4 (Q37): no construction-time decoding (W11).
- F6 (open): storage-trie memo ownership, lifetime and triggers (W11, §6).
- F7 (open): clear iteration order in W6 step 3 (W8).

## 10. Gaps

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **Order equivalences** (W8 step 3, which is F7, open; insert/delete groups) are unproved; step-4 order dependence is verified by executing a minimal example, but no fixture tests it on the account trie.
- **History condition** (W7) depends on an `EthState` invariant whose formal statement for a pure provider is not settled.
- **Storage-trie memo** (F6, open): ownership, lifetime and decode triggers are unspecified; until then storage tries are decoded per query (a DEBT candidate). Any precomputation must be shown not to reject anything EELS accepts, in particular storage tries reachable only from account leaves that EELS never reads (B4).
- **Leaf-failure fidelity:** CONTRACT O4(e) records the SC5/SC6 failures. Exact error adapters and precedence at each eager decode/lookup trigger remain implementation obligations; the failure ledger (X1) must close the individual sites.
- **Exponential decode on DAG witnesses and deep acyclic chains** (`EthCommit` C17) make EELS's behaviour host-dependent (DISC-001, O12 unresolved): the guest-process recursion limit is 100,000 (py_ecc raises it), and the witness-chain depth at which the reference fails has not been re-measured under it. The Lean backend's memoised, total decode is not yet reconciled with that.
- **`compute_state_root_and_trie_changes`' node list** is always empty at the pin; its intended content (trie changes for witness generation) is unspecified.
- **No fixtures** for malformed nodes, cycles, non-canonical encodings, malformed account or storage leaves, or balance overflow from witness data.
