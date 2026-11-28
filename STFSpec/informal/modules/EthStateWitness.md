# `EthStateWitness`: the witness-state backend

*Status: draft. The code database is implemented. Date: 2026-11-27. Pin: `tests-zkevm@v21.0.6` @59c1473d. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F1, F4, F6, F7, F20 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D5, D8, D18, D19 · questions: B1 (Q29/Q36), B4 (Q37), B15 (Q35), F6, F7, Q55, Q57, Q90; DISC-001, DISC-004.*

`ws:` = `forks/amsterdam/witness_state.py`. "[executed]" = run against the pinned EELS; "[inference]" = argued only. EELS `file:line` citations are at `59c1473d` except where marked and those listed in `STFSpec/informal/citation-remap-manual.txt`, which are still at `e1a316a0` (`tests-zkevm@v21.0.0`); verified observations are at `e1a316a0` unless marked as at `59c1473d` (GAPS-CROSSCUTTING X16).

## 1. Purpose

`EthStateWitness` implements `PreState` from an execution witness (ARCHITECTURE §5.4), mirroring EELS `WitnessState`: a node DB and a code DB built from the witness, the parent header's state root, eager decoding (D19) at the reference's trigger points, trie lookups and the post-state root over the partial trie. It proves `Models` up to a computable collision and a separate data-availability progress theorem. It is the backend of the stateless guest (`EthStateless`).

## 2. Requirements

- W1. **Construction** (`stateless.py:272–286`). The guest takes the last validated witness header as the parent. It builds the node DB from `witness.state` (`ws:28–30`), reads `parent_header.state_root`, and builds the code DB from `witness.codes` (`ws:33–35`), in that order. Both builders hash through `KeccakQuery` (D5/F4). `NodeDB.Authentic` and `CodeDB.Authentic` are separate predicates established for the builders at `m := Id`. EELS initializes an empty address-to-storage-root cache and an empty decoded-trie cache (`ws:75–81`). Construction decodes no trie (W11). The Lean backend carries the caller's `HashConsts` (`emptyTrieRoot`, `emptyCodeHash`) under EthStateless R5 (F20).
- W2. **Decode trigger points** (O4 and `ws:83–94`). Account reads and storage reads with a nonempty storage root use one read cache, keyed by root hash. On a miss, EELS runs `decode_witness_to_mpt` with `secured=True` and `default=b""` and stores the trie after successful decoding. Thus account and storage reads reuse the same decoded trie if their roots coincide, as do storage reads for two accounts with equal storage roots. An empty account root still goes through this wrapper and cache. The decoder returns an empty trie without reading the node DB (`incremental_mpt.py:1046–1053`). Root computation uses fresh decodes for the changed storage tries and the account trie (W6 steps 1–2). Each reached decode eagerly processes all reachable nodes (EthCommit C13–C17, including Q90 for secured tries). Q55 runs the complete decoder query action at the decode trigger. The read key hashes go through `KeccakQuery` (D5). F6 and W10 govern the open Lean cache contract.
- W3. **Account read** (`get_account_optional a`, `ws:96–110`). Obtain the account trie through W2 before hashing `a`. A decode failure ends the read before the key hash. `mpt_get` hashes `a` even for an empty account trie and then walks the path (`incremental_mpt.py:366–402`, `EthCommit.lookup`). A reached unresolved stub raises `AssertionError` with assertions enabled (`incremental_mpt.py:375`, O4(c)). If the path is absent, record `EMPTY_TRIE_ROOT` for `a` in the address cache and return `none`. If a leaf is present, run `EthStateCommit.decodeAccountLeaf` (SC5). Record its storage root for `a` and return the account only after the leaf decodes successfully.
- W4. **Storage read** (`get_storage a k`, `ws:112–127`). If the address cache has no entry for `a`, finish W3 first. Its decode, lookup and leaf failures precede any storage-trie work. If the cached storage root is `EMPTY_TRIE_ROOT`, return `0` before invoking the decoder wrapper or hashing `k`. Otherwise obtain the storage trie through W2 before `mpt_get` hashes `k` and walks its path. A decode failure skips key hashing, and a reached stub fails before leaf decoding (O4(c)). An absent slot returns `0`. Decode a present value with `rlp.decode_to(U256, leaf)` (EthStateCommit SC6).
- W5. **Code read** (`get_code h`, `ws:129–137`). If `h` equals `EMPTY_CODE_HASH` (`HashConsts.emptyCodeHash`), return `b""` before consulting the code DB. Otherwise index the code DB by `h`. A missing entry raises `KeyError` (O4(d), B2). This read hashes nothing and uses no trie or address-cache entry.
- W6. **Root replay at the current pin** (`compute_state_root d`, `ws:139–202`). EELS replays the complete block diff in this order. The historical tuple-return signatures in §5 leave the backend helper contract open (§10).
  1. Traverse `storage_changes.items()`. A cleared address uses `EMPTY_TRIE_ROOT`. For an uncleared address, run `get_account_optional` if the address cache lacks an entry, then take the cached root with `EMPTY_TRIE_ROOT` as the fallback. For every entry, including an empty slot map, freshly decode a secured storage trie with default `U256(0)`. Use `mpt_set_storage_slots` to apply nonzero writes before zero deletions, preserving slot order within each group. Record the resulting storage root (`ws:151–169`, `incremental_mpt.py:445–463`).
  2. Freshly decode the secured account trie with default `None` (`ws:171–178`).
  3. Traverse the Python set union `set(storage_changes) | set(storage_clears)` in its iteration order. For each address without an explicit account change, read its original account through `get_account_optional`. If the account is present, rewrite its leaf with the root from step 1 or `EMPTY_TRIE_ROOT` for a pure clear (`ws:179–190`). F7 governs agreement with the source traversal (W8).
  4. Traverse `account_changes.items()` in first-write order (`EthState` R6). Select the root computed in step 1 if present, otherwise `EMPTY_TRIE_ROOT` for a clear, otherwise the address-cache entry with `EMPTY_TRIE_ROOT` as the fallback. This root selection makes no account read. Pass the value and selected root to `mpt_set`. A `None` value deletes the account (`ws:192–200`, `incremental_mpt.py:405–442`).
  5. Return the state root from `mpt_root(state_mpt)` (`ws:202`, `fork.py:325`).
- W7. **History condition.** Step 4's default means EELS's root depends on which addresses were looked up earlier. `EthState` guarantees every address in `accountChanges` was looked up (`AccountWritesLookedUp`, `EthState` R32). Under that condition, at concrete Id with its stable hash interpretation, looking the account up again (deterministic, and certain to succeed because it succeeded before) gives the same storage root; the Id prototype does so and needs no mutable cache. This is a reachable-value argument, not a generic stateful/failing-query effect equivalence (Q55).
- W8. **Order.** Preserve account first-write order and both storage-address and storage-slot first-write orders in BlockDiff. Step 1 partitions each ordered slot list into nonzero writes followed by zero writes, preserving order within each group. No map iteration substitutes for those lists. Step 3's storage-root-only rewrites of present accounts are conjectured to commute, but this needs proof for every accepted encoding, **including failures and observations**, before choosing a deterministic set order. Cross-address independence does not alone establish identical failure priority. This is F7 (open): `storageClears` has no clear order, so either prove the commutation or add a clear order to `BlockDiff` (`EthState` §7.5). A prototype's traversal (storage-address order, then the remaining clears in key order) is not adopted, and a first-clear order alone does not reproduce Python set iteration. The account, storage-address and slot orders are settled by B1.
- W9. **Typed witness failures are O4** and become `false` (`stateless.py:294`): missing root preimage, malformed reachable node, stub on a lookup/update path or collapsing onto a stub, missing code, and leaf-decoding failures (`EthStateCommit` SC5–SC6). Underlying Q55 query-monad failures propagate in their original channel until the caller's owning adapter; no new O4/O11/O12 projection is supplied.
- W10. **Cache refinement** (ARCHITECTURE §7). Removing `_decoded_secure_tries` changes only cost under the concrete Id comparison with stable interpreted values. W7 permits re-lookup in place of `_storage_root_cache` on reachable traces. Generic query effects, successful-result lifetime and first failure need separate Q55 refinement premises.
- W11. **Decode timing** (B4, D19). At a W2 trigger, eagerly decode everything reachable from the root. If no access or replay triggers a storage root, a malformed node reachable only from that root gives no witness error. If root computation reaches W6 step 2, it decodes the account trie even without an earlier account read (`fork.py:325`). Precomputation is permitted only after proving that its errors surface at the reference's triggers with the reference's precedence and observations (B15), and after measuring the extra work. The concrete Id prototype uses a `Thunk (Except …)` for the account trie and decodes storage tries per query. The storage-trie memo is open (F6). F6 must specify its ownership, lifetime and triggers while keeping cache mechanics outside semantic state. Per-query decoding is a DEBT candidate (D18).

## 3. EELS source map

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `forks/amsterdam/witness_state.py::build_code_db` | 33–35 at `59c1473d` | `STFSpec.StateWitness.CodeDB`, `CodeDB.map`, `CodeDB.Authentic`, `CodeDB.build` | Implemented. The array fold queries each complete byte string in input order and inserts it under the returned key. A later equal answer replaces the earlier value. Empty input produces an empty table. |
| `forks/amsterdam/witness_state.py::WitnessState` | 67–81 at `59c1473d` | `WitnessBackend` | W1 construction and W10/W11 cache refinement remain open. |
| `forks/amsterdam/witness_state.py::WitnessState._get_decoded_secure_trie` | 83–94 at `59c1473d` | `WitnessBackend.accountTrie` and storage read decoding | W2 secured root acquisition. Storage memo open (F6). |
| `forks/amsterdam/witness_state.py::WitnessState.get_account_optional` | 96–110 at `59c1473d` | `….getAccount?` | W3 decode, key hash, lookup, then SC5 on a present leaf. Backend operation remains open. |
| `forks/amsterdam/witness_state.py::WitnessState.get_storage` | 112–127 at `59c1473d` | `….getStorage` | W4 account prerequisite, empty-root return, then decode, key hash, lookup and SC6 on a present leaf. Backend operation remains open. |
| `forks/amsterdam/witness_state.py::WitnessState.get_code` | 129–137 at `59c1473d` | `….getCode` | W5 sentinel and direct code DB access. Backend operation remains open. |
| `forks/amsterdam/witness_state.py::WitnessState.compute_state_root` | 139–202 at `59c1473d` | `….stateRoot` | W6 replays the complete diff and returns the state root. Backend operation remains open. |

EthStateless owns the guest producer for W1. EthCommit owns `build_node_db` and the trie decoder and lookup used by W2–W4. EthStateCommit owns `_decode_account_from_leaf` and storage-leaf decoding (SC5–SC6).

**External semantics.** `ethereum_rlp.rlp` decodes leaves (`EthStateCommit`). Python dicts preserve insertion order in W6 steps 1 and 4. Step 3 follows Python's hash-dependent set order. F7 requires agreement in failures and observations as well as roots (W8).

## 4. Tests

- **EEST fixture area:** `amsterdam/eip8025_optional_proofs` (96 files): `test_witness_validation_state.py` (missing storage proof node, missing absent-slot proof leaf, missing delete auxiliary node, missing sender, absent-account and failed-call-target account nodes, extra unused node, unsorted but complete), `test_witness_validation_codes.py` (missing codes incl. 7702 markers and system contracts; extra and unsorted codes), `test_witness_state_{reads,writes,deletes,replay_order}.py`, `test_witness_headers.py`. Every other `blockchain_tests` area runs through this backend when executed as zkevm stateless fixtures.
- **EELS unit tests:** `tests/json_loader/test_witness_state.py` (`TestBuildNodeDb`, `TestBuildCodeDb`, `TestGetAccountOptional`, `TestGetStorage`, `TestGetCode`, `TestComputeStateRoot`, `TestCanonicalSecureTrieValidation`).
- **Historical corpus observation (recorded 2026-09-29).** A full `tests-zkevm@v21.0.0` corpus run found 234 inputs that reached an unresolved stub in `_trie_lookup` (`ws:73`) [executed at `e1a316a0`].
- **Code database.** `STFSpec/Conformance/StateWitness/CodeDBCallerProofs.lean` checks complete map construction, reconstruction and replacement, the separate predicate and the bare `Monad`/`KeccakQuery` builder through the library facade. `CodeDBGuards.lean` checks six complete tables from the pinned EELS builder [executed at `59c1473d`]. The inputs include empty input, empty code, duplicate code and byte lengths of 136 and 137. A stateful oracle checks the complete query trace and the final table when distinct byte strings receive equal keys.
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
  accountTrie : Thunk (Except WitnessError Ref)   -- Id prototype only; Id.run decoder via the existing TrieError/WitnessError adapter obligation
  -- Id prototype storage tries: Id.run decoder per query; per-root memo open (F6)
def WitnessBackend.build (nodes : NodeDB) (codes : CodeDB) (root : Hash32) (consts : HashConsts) : WitnessBackend
def WitnessBackend.WF (w : WitnessBackend) : Prop   -- Id; complete obligations specified below
-- WF requires both concrete DB authentication predicates, coherent consts and
-- accountTrie.get equality to the existing TrieError/WitnessError adaptation of
-- Id.run (decodeRoot w.consts.emptyTrieRoot w.nodes w.stateRoot) (Q55).
-- build must establish all these obligations; the adapter/decoder are unimplemented.
def WitnessBackend.toPreState (w : WitnessBackend) : PreState Id   -- displayed record is the Id prototype
-- Historical tuple-return proposal. The backend helper contract is open (§10).
def computeStateRootAndTrieChanges (w : WitnessBackend) (d : BlockDiff) : Id (Except WitnessError (Hash32 × List InternalNode))

-- the theorems are stated at m := Id (Models is at PreState Id, D5)
theorem WitnessBackend.models (w) (σ) (hwb : WitnessBackend.WF w) (hwf : MathState.WF σ) (hc : CodeAuthentic σ)
    (hr : mathStateRoot σ = w.stateRoot) :
    Models w.toPreState σ ∨ (StateCollision w.nodes w.codes.map.toList σ).isSome
theorem WitnessBackend.progress_lookup (w) (a) (hwb : WitnessBackend.WF w) : LookupAvailable w a → ∃ r, w.toPreState.getAccount? a = .ok r
theorem WitnessBackend.progress_root (w) (d) (hwb : WitnessBackend.WF w) : UpdatesAvailable w d → ∃ r, w.toPreState.stateRoot d = .ok r
theorem WitnessBackend.refines_eels : ...   -- under AccountWritesLookedUp, same results as WitnessState on the same call sequence
```

The provider factory receives `consts` from its caller (F20); it does not acquire it. `WitnessBackend.build` stores that record, and `toPreState`/root/lookup consumers read `w.consts` through their existing backend argument, with local EELS notation rather than an additional constants argument. Establishing DB authenticity and constants/oracle coherence is still W1, not a consequence of the factory parameter alone.

Q57 binds the contextual lookup agreement to `ModelsLookups w.consts w.toPreState σ`.
The binary full `Models` theorem retains EthStateCommit's concrete `constsId`
interpretation; `WitnessBackend.WF` supplies `w.consts = constsId` to rewrite its
lookup conjunct to the stored record. This does not weaken authentication, the
Id-run decoder/thunk premise, arbitrary structurally WF/code-authentic model
quantification, root agreement or the collision alternative.

**Generic decoder action lifetime (Q55; unimplemented).** The displayed
`WitnessBackend` record is only the Id prototype, not a representation of a
generic `PreState m`. Its full WF contract requires `NodeDB.Authentic keccak256 w.nodes`,
`CodeDB.Authentic keccak256 w.codes`, `w.consts = Id.run HashConsts.query`,
and the thunk equality after the
existing TrieError-to-WitnessError adaptation of
`Id.run (decodeRoot w.consts.emptyTrieRoot w.nodes w.stateRoot)`; success premises
use that explicit Id-run expression. Defining/proving the adapter remains open.
A future generic backend runs the complete decoder action at W2, including all
eligible pre-RLP occurrence queries. `Thunk (m (Except WitnessError Ref))` stores
an action value: forcing and running it again repeats effects, rather than caching
an executed result. Successful-result ownership/lifetime, first-failure sequencing
and F6 behavior must be specified/proved before choosing that representation.
Read caches are distinct from W6's fresh storage/account decodes. The caller's
existing constants record is threaded unchanged; no decoder acquires it.

The previously required generic public entry targets remain visible below;
`…` denotes the backend parameter whose generic representation/lifetime remains
unspecified, not a new public record or adapter. These targets are independent
of the Id-only record displayed above and remain unimplemented:

```lean
-- {m : Type → Type} [Monad m] [KeccakQuery m]
WitnessBackend.toPreState : … → PreState m
-- Historical tuple-return proposal. The backend helper contract is open (§10).
computeStateRootAndTrieChanges : … → BlockDiff →
    m (Except WitnessError (Hash32 × List InternalNode))
```


## 6. Data structures

| Type | Representation | Invariant | Persistence | Complexity |
|---|---|---|---|---|
| `NodeDB`, `CodeDB` | `Std.HashMap`, built linearly | `NodeDB.Authentic`/`CodeDB.Authentic` (keys are hashes of values; separate predicates, F4) | read-only shared | build expected O(n) + one keccak per entry |
| account trie | `Thunk (Except WitnessError Ref)` (prototype form) | Id-only value equals the existing error adaptation of `Id.run (decodeRoot emptyTrieRoot nodes stateRoot)` | forced once, then shared | one eager Id decode; B15 completed-node sharing unselected; lookup O(64) node steps |
| storage tries | none yet: decoded per query | each Id decode equals the existing error adaptation of `Id.run (decodeRoot emptyTrieRoot nodes h)` | — | O(path-expanded reachable occurrences) **per Id query**; costs and F6 sharing remain open |
| root computation | `EthCommit.IncrementalMPT` per changed trie | as `EthCommit` | functional, linear use | O(u · d) node rebuilds for `u` updates |

Per-query storage decoding repeats work that EELS caches by root (`ws:87–94`). The per-root memo that would remove it is F6 (open; a DEBT candidate, D18): it must preserve the B4 triggers and B15 precedence and keep cache mechanics outside semantic state.

## 7. Contract and laws

- [C] **Code database (W1).** `build_eq_reference` proves equality to the ordered list fold for every `Monad` and `KeccakQuery`. At `Id`, `authentic_build_id` proves `CodeDB.Authentic keccak256` for every input array. `lookup_build_id` proves that any raw table lookup returns the last input whose digest equals the key, or `none` when no digest matches. The proofs are private and reuse the pure `NodeDB` model and its map laws. The executable fold uses `CodeDB` and its own query and insertion step.
- [C] **Agreement up to collision:** `WitnessBackend.models` — from `EthCommit.decode_agreement` on the account trie and on each storage trie, plus `EthStateCommit`'s leaf round trips; `WitnessBackend.WF` supplies node/code authentication, coherent constants and the Id-run decoder/thunk agreement through the existing error adapter; `ModelsCode` follows from its code-DB clause. Q57's stored-record lookup conjunct follows by the §5 coherence rewrite on the Models branch. These premises apply to arbitrary backend records, not only to records returned by `build`.
- [C] **Progress / data availability.** `LookupAvailable w a` requires
  successful eager account-root decoding (including off-path nodes) and a
  resolved lookup path. When the lookup returns a leaf, that leaf must decode
  successfully. Storage lookup additionally requires successful eager decoding
  of its triggered storage root and a resolved slot path. When the slot lookup
  returns a leaf, that leaf must decode successfully.
  `UpdatesAvailable w d` requires `BlockDiff.WF` and read-before-write. In the W6
  replay order, each reached replay or read trigger requires successful eager
  decoding (W6 and W2). Every reached lookup path, every insertion or deletion
  path and the remaining sibling of each collapsing branch must resolve, and
  every leaf value inspected must decode successfully.
  This includes the account lookups reached in W6 steps 1 and 3. An empty slot
  map in step 1 or a pure clear in step 3 can still lead to a stub. The lookup
  then fails before it can inspect a leaf or proceed to a mutation (W3 and W9).
  A resolved path alone is insufficient when eager decoding finds a malformed
  off-path node. Authenticated absence is success (ARCHITECTURE §5.3).
- [R] **Concrete Id refinement to EELS:** under concrete Id, coherent constants and pinned-host premises, for any sequence of provider calls made by `EthBlock` execution satisfying `AccountWritesLookedUp`, each call's result (value, or failure) equals EELS's; hence the guest's boolean is the same (W9, W11).
- [C] **Id cache laws:** the account-trie thunk's value equals the adapted Id-run on-demand decoding; re-lookup equals the cached storage root under W7. Any storage-trie memo (F6, open) must equal per-query decoding under its stated interpretation, including error precedence (B15); generic action/result reuse additionally proves Q55 effects and ownership/lifetime.
- [C] **Order laws:** step-3 commutation (W8; F7, open) and step-1 independence still need proofs. Slot iteration uses the diff's stored order, filtered into the nonzero and zero groups, so no insert/delete group commutation premise is required by the working interface.

### Informal correctness argument

**Claim.** On the reachable execution trace, successful witness answers and ordered root updates agree with the full-state model or yield an explicit collision, while unavailable data produces the reference failure.

**Premises.** WitnessBackend.WF (authenticated node/code dictionaries, coherent HashConsts and account thunk), initial root agreement, code authenticity of σ, the full code/node preimage set, EthCommit lenient decoding laws, immutable pre-state queries, and read-before-write for changed accounts.

**Argument.** Build node and code dictionaries in input order with the reference's duplicate-key policy. Lookup authenticates the relevant path and updates the account storage-root cache. On a reachable trace, read-before-write records a storage root for every explicitly changed account. When replay uses that cache entry, the concrete Id provider can repeat the successful immutable read to obtain the same root (W7). Root computation processes storage addresses in the order retained in BlockDiff, with nonzero writes before zero deletions and slot order preserved within each group. It decodes the account trie afresh, applies the storage-root-only rewrites in source set order, then applies the explicit account changes in first-write order. Induct over these operations, applying the path/update agreement or extracting a collision. Preserve original raw encodings of unchanged nodes.

**Open obligations.** Establish agreement for the storage-root-only traversal for all accepted witness encodings, including failures and observations as well as roots (F7). Complete cache-history reachability and implement the collision extractor including σ's code bytes. Canonical full-state agreement is conditional; witness availability and host-resource compatibility cannot be deduced from the root alone.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthStateCommit`
- **Used by:** `EthStateless` (and `EthSecurity` in the security package).
- **Relies on:** `EthState`'s `AccountWritesLookedUp`, `BlockDiff.WF` and first-write `accountOrder`; `EthCommit`'s decoding, update semantics and agreement theorem; `EthStateCommit`'s leaf decodings.
- **Guarantees:** a `PreState` with `Models` up to collision, progress under availability, and EELS-equal accept/reject.

## 9. Open decisions

- D5 (broad scope, monad-parametric): node and code DB builds, key hashing in lookups, and root updates go through `KeccakQuery`; complete decoding follows Q55; the displayed thunk/backend is Id only, while generic `PreState m` action/result ownership remains open; the theorems are stated at `m := Id`.
- D8 (accepted): authenticated absence versus missing data.
- D19 (accepted): eager decoding from the reference's trigger (W11).
- NEW-STATE-1 (from `EthState`): resolved: DECISIONS B1 (Q29).
- NEW-WIT-1: resolved: DECISIONS B1 (Q36); only the clear order remains (F7).
- NEW-WIT-2: resolved: DECISIONS B4 (Q37): no construction-time decoding (W11).
- F6 (open): storage-trie memo ownership, lifetime and triggers (W11, §6).
- F7 (open): clear iteration order in W6 step 3 (W8).

## 10. Gaps

- **Backend construction and code access** (W1, W5). Compose the authenticated databases, parent state root and caller's constants into a backend. Implement the empty-code sentinel and missing-code error at the code access boundary.
- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **Order equivalences** (W8 step 3, which is F7, open; insert/delete groups) are unproved. A minimal example establishes step-4 order dependence [executed at `e1a316a0`]. No fixture in `tests-zkevm@v21.0.0` tests it on the account trie.
- **Generic action lifetime (Q55):** implement/prove decoder sequencing at W2, Id-run thunk agreement and its error adapter, read-cache versus fresh root-computation behavior, successful-result ownership/lifetime, first failure and F6 refinement. Stable Id value comparisons do not establish generic stateful/failing-query equivalence.
- **History condition** (W7) depends on an `EthState` invariant whose formal statement for a pure provider is not settled.
- **Storage-trie memo** (F6, open): ownership, lifetime and decode triggers are unspecified; until then storage tries are decoded per query (a DEBT candidate). Any precomputation must be shown not to reject anything EELS accepts, in particular storage tries reachable only from account leaves that EELS never reads (B4).
- **Leaf-failure fidelity.** CONTRACT O4(e) records the SC5/SC6 failures. Implement the error adapters and the order in W3–W4. X1 tracks the individual failure sites.
- **Exponential decode on DAG witnesses** (`EthCommit` C17) remains a host-resource question (DISC-004, DISC-001, O12 unresolved). The single-node RLP-nesting probes exceed guest SSZ admission and establish no admitted-guest divergence (DISC-001). Deep chains of trie nodes no longer give the recorded recursion-output divergence once every decode here is secured (Q90, below; EthCommit C17); executable memory costs remain separate. Q55's total mathematical baseline and any unselected B15 memo remain unreconciled with the remaining host-resource behavior.
- **Re-pin to `tests-zkevm@v21.0.6` (GAPS-CROSSCUTTING X16).** The two unimplemented `computeStateRootAndTrieChanges` signatures in §5 specify a tuple result. W6's `compute_state_root` returns only the state root, and `PreState.stateRoot` already returns `Hash32` on success. Resolve the public helper target separately (CONTRIBUTING §6.5). Apply Q90 in the backend by using `decodeWitnessToMpt … (secured := true)` or `decodeRoot` followed by the Q90 check. The TrieError-to-WitnessError adapter must map `.malformed .securedPathLength` to O4(b). Storage reads must use the strict SC6 decoder.
- **No fixtures** for malformed nodes, cycles, non-canonical encodings, malformed account or storage leaves, or balance overflow from witness data.
