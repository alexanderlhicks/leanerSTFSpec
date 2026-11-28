# `EthStateFull`: the full-state backend

*Status: informal specification, draft. The full-state carrier, `ofMath` and the standalone storage setter are supplied. Provider integration remains open. Date: 2026-11-27. Pin: `tests-zkevm@v21.0.6` @59c1473d. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F1, F2, F20 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D5, D9, D10, D22 · questions: B2 (Q30), Q57.*

Requirement IDs are `FS1`–`FS7`; interface findings are owned by DECISIONS §3. EELS `file:line` citations are at `59c1473d` except where marked and those listed in `STFSpec/informal/citation-remap-manual.txt`, which are still at `e1a316a0` (`tests-zkevm@v21.0.0`); verified observations are at `e1a316a0` unless marked as at `59c1473d` (GAPS-CROSSCUTTING X16).

## 1. Purpose

`EthStateFull` is the in-memory full-state implementation of `PreState` (ARCHITECTURE §5.4; D10), mirroring EELS `state_mpt.State`. It holds a complete `MathState`, answers lookups directly, and computes the post-root with `mathStateRoot`. It is used by the blockchain-test runner in `EthConformance` (fixtures carry full pre-states) and for fuzzing; the stateless guest uses `EthStateWitness` instead.

## 2. Requirements

- FS1. `State` holds an account trie (secured, default `None`), per-address storage tries (secured, default `0`) and a code store keyed by hash that is **excluded from equality** (`state_mpt.py:34–47`). In Lean the state is a `MathState` with `MathState.WF`.
- FS2. `get_code h`: `b""` for `EMPTY_CODE_HASH`, else the store entry; a missing hash raises `KeyError` (`state_mpt.py:49–57`). In Lean: `WitnessError.missing (.code h)` (B2: missing code is an error, empty code a successful value), unreachable under `CodeComplete σ` [inference for the corpus].
- FS3. `get_account_optional` is a trie lookup (`state_mpt.py:59–65`); `get_storage` is `0` without a storage trie, else a lookup whose result must be a `U256` (`state_mpt.py:67–80`). It does **not** check that the account exists; `MathState.WF` (no orphan storage) makes this unobservable.
- FS4. `compute_state_root d` (`state_mpt.py:82–120`): copy the tries; drop storage tries of `d.storage_clears`; apply `d.account_changes`; apply `d.storage_changes` (creating a trie if needed and removing it if it becomes empty); the root of the account trie with each existing account's storage root (`EMPTY_TRIE_ROOT` without a trie). `code_changes` is ignored. The Lean `stateRoot` returns `mathStateRoot (σ.apply d)` through
  `KeccakQuery` (D5) and succeeds on WF inputs at Id. Prove agreement with the
  source result under the preparation and interpretation premises of
  EthStateCommit §7.2 (Q100).
- FS5. `apply_changes_to_state` (`state_mpt.py:133–161`), used between blocks by the chain runner (`forks/amsterdam/fork.py:259`) and by `execution_engine/new_payload.py`: clears first, then accounts, then storage, then `code_store.update(code_changes)`. In Lean: `σ ↦ σ.apply d`.
- FS6. `store_code` (`state_mpt.py:164–171`) stores non-empty code under its keccak (through the oracle, D5) and returns the hash (genesis loading); `set_account` (`:174–184`); `set_storage` (`:187–206`) **asserts that the account exists**, then writes and removes empty tries; `state_root` = `compute_state_root(BlockDiff())` (`:209–213`); `close_state` (`:123–130`) releases resources and has no Lean counterpart beyond dropping the value.
- FS7. **Progress:** at Id, the planned `getAccount?`, `getStorage` and
  `stateRoot` operations succeed on well-formed inputs under the §5
  contract, including the well-formed diff for the root. `getCode` succeeds
  at the reserved empty-code hash and at hashes present in the code table
  (FS2). The standalone `setStorage` succeeds when the selected account is
  present. On absence it returns `StateError.storageOnMissingAccount`,
  including for a zero write (FS6).

## 3. EELS source map

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `state_mpt.py::State` | 34–47 | `FullState`, `FullState.ofMath` | The supplied FS1 carrier retains all three mathematical maps and their two invariant proofs. EELS excludes the code store from its dataclass equality. |
| `state_mpt.py::State.get_code` | 49 | `FullState.toPreState.getCode` | |
| `state_mpt.py::State.get_account_optional` | 59 | `….getAccount?` | |
| `state_mpt.py::State.get_storage` | 67 | `….getStorage` | |
| `state_mpt.py::State.compute_state_root` | 82 | `….stateRoot` | `mathStateRoot (σ.apply d)` |
| `state_mpt.py::close_state` | 123 | — (no-op) | resource release |
| `state_mpt.py::apply_changes_to_state` | 133 | `FullState.applyChanges` | `σ.apply d` |
| `state_mpt.py::store_code` | 164 | `FullState.storeCode` | computes and returns the hash |
| `state_mpt.py::set_account` | 174 | `FullState.setAccount` | genesis/tests |
| `state_mpt.py::set_storage` | 187–206 | `FullState.setStorage` | Supplied FS6 setter. Check account presence before writing, then erase at zero and prune the touched empty map. |
| `state_mpt.py::state_root` | 209 | `FullState.stateRoot` | |

**External semantics.** Python `dict` copy/update (value semantics in Lean); the `Trie` functions from `merkle_patricia_trie.py` (`EthCommit`).

### Implemented full-state carrier (FS1)

At `59c1473d`, `state_mpt.py:34–47` defines an account trie, per-address
storage tries and a hash-indexed code store. `STFSpec/StateFull.lean` supplies
the guided `FullState` record over `MathState`. Its two proof fields establish
structural well-formedness and raw code authenticity.
`FullState.ofMath (σ : MathState) (hwf : MathState.WF σ) (hc : CodeAuthentic σ) :
FullState` returns the supplied state and proofs by construction. It is pure
and total for these inputs. The private projection and reconstruction checks
in §4 retain the complete input state. The operational equality policy and
remaining backend operations remain open (§10).

### Implemented standalone storage setter (FS6)

`FullState.setStorage (s : FullState) (a : Address) (k : Bytes32) (v : U256) :
Except StateError FullState` checks account presence first
(`state_mpt.py:187–206` at `59c1473d`). Absence returns exactly
`.error .storageOnMissingAccount` with no returned state (R29).
On presence, write the word, erase a zero and remove the touched storage
map if empty. The source uses the default-value deletion in
`merkle_patricia_trie.py:325–338`. Private laws characterize the complete
result and selected storage map, retain every other address's optional map
and preserve the full accounts and raw code fields. The two carrier proofs
follow from EthState's structural preservation and raw code retention.

At the pin, tests with Python assertions enabled observe both missing
writes raising at the account check, before any map changes. Optimized
Python removes that check. A missing nonzero write creates orphan storage
and a missing zero succeeds with unchanged maps. Both Lean calls return
the same typed absence error.

## 4. Tests

- **Carrier (FS1):** `STFSpec/Conformance/StateFull/CarrierChecks.lean`
  verifies all three projections and reconstruction. It checks an empty
  state and a state with a present account whose nonreserved code hash is
  missing from an authentic empty code table. The latter uses the public
  mathematical account and code observers.
- **Storage setter (FS6):** `STFSpec/Conformance/StateFull/StorageChecks.lean`
  compares complete account, storage and code states for insertion,
  insertion on a present empty account, replacement, zero deletion,
  final-map pruning and zero on an empty selected map. Missing-account
  zero and nonzero writes both return the typed error. The six admitted
  source cases agree in normal and
  optimized pinned Python. The absence controls exercise the assertion
  difference in §3.
- **Planned EEST coverage.** Use this backend in `EthConformance` to check every post-state root in the 295 `blockchain_tests` and `blockchain_tests_engine` area directories in `STFSpec/informal/eest-fixture-index.txt`. Multi-block fixtures will exercise `applyChanges`.
- **EELS unit tests:** `tests/json_loader/test_genesis.py` (genesis roots via `store_code`/`set_account`/`set_storage`); `helpers/load_blockchain_tests.py` is the reference runner.
- **`core` `#guard` cases:** empty state root; a diff that clears an address and rewrites one slot (root equals building the post-state from scratch); a diff deleting an account (its storage trie dropped by the clear); `getCode` of `emptyCodeHash` and of a missing hash.
- **Differential:** `FullState.stateRoot` against `WitnessState` roots built from a complete witness of the same state (the two backends must agree).

## 5. Interface

```lean
-- public
structure FullState where
  σ : MathState
  wf : MathState.WF σ
  codeAuthentic : CodeAuthentic σ       -- EthStateCommit; not implied by structural WF
variable {m : Type → Type} [Monad m] [KeccakQuery m]      -- D5; public uses take m := Id
def FullState.toPreState (s : FullState) (consts : HashConsts) : PreState m   -- lookups are `pure`; stateRoot hashes
def FullState.applyChanges (s : FullState) (d : BlockDiff) (h : BlockDiff.WF s.σ d)
    (hc : CodeChangesAuthentic d) : FullState
def FullState.storeCode (s : FullState) (code : ByteArray) : m (Hash32 × FullState)
def FullState.setAccount (s : FullState) (a : Address) (acc : Option Account)
    (h : MathState.WF (s.σ.setAccount a acc)) : FullState -- raw deletion alone does not clear storage
def FullState.setStorage (s : FullState) (a : Address) (k : Bytes32) (v : U256) : Except StateError FullState
def FullState.stateRoot (s : FullState) (consts : HashConsts) : m Hash32
def CodeComplete (σ : MathState) : Prop -- every account-referenced nonempty code hash is available
def FullState.ofMath (σ : MathState) (hwf : MathState.WF σ) (hc : CodeAuthentic σ) : FullState
-- constsId names Id.run (HashConsts.query (m := Id)) as in EthStateCommit §5/§7.3.
-- stated at m := Id; binary Models retains this coherent concrete record (Q57).
theorem FullState.models (s : FullState) : Models (s.toPreState constsId) s.σ
theorem FullState.progress (s : FullState) : ∀ a key d, BlockDiff.WF s.σ d → (getAccount?, getStorage, stateRoot succeed)
```

The provider factory (F20) closes over `s` and receives the caller's `consts`, returning `s.toPreState consts` in `m`. It performs no acquisition. The resulting `PreState` closures retain that same record for empty-code and root observations; their operations need no parallel constants input. `FullState` itself contains no constants field, so `toPreState` and the separate `stateRoot` helper retain their necessary data parameter.

## 6. Data structures

`MathState` (nested `ExtTreeMap`s, `EthState`). Persistence: read-only during a block (shared by the `PreState` closures); updated linearly between blocks. Complexity: lookups O(log n); `stateRoot` rebuilds `mathStateRoot` **from scratch**, O(N·L) for N entries and key length L plus one keccak per hashed node — the same asymptotics as EELS's `patricialize`, acceptable for fixtures but not for mainnet-size states. An incremental variant (`EthCommit.buildMpt` once, then `mptSet` per diff) is a later representation replacement against the same `Models` contract.

## 7. Contract and laws

- [C] `ModelsLookups consts (s.toPreState consts) s.σ` at Id: by the observer definitions for every supplied record, with no acquisition. Full binary `Models` and its `ModelsCode` clause remain at `constsId` (Q57), so the execution-context lookup premise follows under concrete record coherence. `ModelsCode`: every returned `(h, c)` has `keccak256 c = h`, from `CodeAuthentic`; `storeCode` computes the hash and `applyChanges` requires `CodeChangesAuthentic`. Authentication and `CodeComplete` are separate: completeness ensures progress for account-referenced code.
- [C] `ModelsRoot`: the mathematical target is
  `stateRoot d = mathStateRoot (σ.apply d)` (FS4). The source can reach the
  same finite raw map through different insertion histories. Prove the
  commuting equation with the preparation and interpretation premises in
  EthStateCommit §7.2 (Q100).
- [C] `applyChanges` preserves `WF` given `BlockDiff.WF`; `s.toPreState.stateRoot d = .ok (stateRoot (applyChanges s d))` (with the required WF/authenticity proofs).
- [T] Progress FS7 requires the §5 proof for the account, storage and root
  operations. Code lookup progress uses the availability premise in FS2.
  The supplied setter's success requires account presence, which structural
  well-formedness alone does not imply (FS6, §3).

### Informal correctness argument

**Claim.** A structurally well-formed, code-authentic full state implements Models and executes all admissible account/storage/root operations; code lookup additionally needs availability of referenced code.

**Premises.** EthStateCommit laws, MathState.WF, CodeAuthentic, CodeComplete when code progress is required, and a reachable well-formed diff with authentic code changes.

**Argument.** Account and storage lookup are direct finite-map observations with the specified absent defaults. Code lookup returns empty code for the empty-code hash, and otherwise returns the stored bytes or the named missing-code failure. Applying a diff follows the same clear/delete/write equations as MathState.apply; induction over entries preserves structural well-formedness under the supplied update premises. Authentic new code preserves CodeAuthentic. Root computation uses the defining canonical two-level trie construction, so its result is the mathematical root of the updated state. Taking successful-answer equations gives Models; taking existence of the required map entries gives progress. These are distinct deductions. A raw account deletion is not automatically a valid FullState update because it can leave orphaned storage.

**Open obligations.** Make the progress domain and CodeComplete explicit
in every caller and prove apply preservation. Integrate the SC4 fold
supplied by EthStateCommit §3 into the provider and prove the source boundary
and `ModelsRoot` (EthStateCommit §7.2).
Equality of states may omit the code store operationally, but proofs using
code must retain its authenticity and availability hypotheses.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthStateCommit`
- **Used by:** `EthConformance`.
- **Seams:** a `PreState` for `executeBlock`; `applyChanges` for multi-block fixtures.

## 9. Open decisions

- D5 (broad scope, monad-parametric): `toPreState` returns `PreState m`; `storeCode` and `stateRoot` hash through the oracle; `Models` and the progress theorem are stated at `m := Id`.
- D10 (accepted): included.
- D22: the state is read-only within a block, so the persistence rule does not bind; trees are kept for `=`-reasoning.
- NEW-STATE-2: resolved: DECISIONS B2 (Q30) (FS2).

## 10. Gaps

- **Backend integration:** §3 supplies the carrier, `ofMath` and the
  standalone storage setter. Provider construction, lookups, root
  computation, the full diff operation, other updates and operational
  equality remain open.

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- `CodeComplete σ` (every account's code hash is stored) is assumed for fixtures, not checked.
- `MathState.WF` for fixture pre-states (no orphan storage, no zero values) is an inference from `set_storage`'s assertion and genesis loading.
- Full recomputation of the root per block has no measured cost on the corpus; mainnet-size use would need the incremental variant.
- The full-state backend must classify missing code as a backend fault and discharge `CodeComplete` for any successful fixture pre-state; the stateful fixture runner reports the resulting validity separately from its warning-only EEST exception-label mapping (EthConformance R3, DECISIONS Q9).
