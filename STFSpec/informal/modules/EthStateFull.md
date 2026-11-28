# `EthStateFull`: the full-state backend

*Status: informal specification, draft. The full-state carrier, `ofMath`, account and storage setters and code insertion are supplied. Provider integration remains open. Date: 2026-11-28. Pin: `tests-zkevm@v21.0.6` @59c1473d. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F1, F2, F20, F21 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D5, D9, D10, D22 · questions: B2 (Q30), Q57.*

Requirement IDs are `FS1`–`FS7`; interface findings are owned by DECISIONS §3. EELS `file:line` citations are at `59c1473d` except where marked and those listed in `STFSpec/informal/citation-remap-manual.txt`, which are still at `e1a316a0` (`tests-zkevm@v21.0.0`); verified observations are at `e1a316a0` unless marked as at `59c1473d` (GAPS-CROSSCUTTING X16).

## 1. Purpose

`EthStateFull` is the in-memory full-state implementation of `PreState` (ARCHITECTURE §5.4; D10), mirroring EELS `state_mpt.State`. It holds a complete `MathState`, answers lookups directly, and computes the post-root with `mathStateRoot`. It is used by the blockchain-test runner in `EthConformance` (fixtures carry full pre-states) and for fuzzing; the stateless guest uses `EthStateWitness` instead.

## 2. Requirements

- FS1. `State` holds an account trie (secured, default `None`), per-address storage tries (secured, default `0`) and a code store keyed by hash that is **excluded from equality** (`state_mpt.py:34–47`). In Lean the state is a `MathState` with `MathState.WF`.
- FS2. `get_code h`: `b""` for `EMPTY_CODE_HASH`, else the store entry; a missing hash raises `KeyError` (`state_mpt.py:49–57`). In Lean: `WitnessError.missing (.code h)` (B2: missing code is an error, empty code a successful value), unreachable under `CodeComplete σ` [inference for the corpus].
- FS3. `get_account_optional` is a trie lookup (`state_mpt.py:59–65`); `get_storage` is `0` without a storage trie, else a lookup whose result must be a `U256` (`state_mpt.py:67–80`). It does **not** check that the account exists; `MathState.WF` (no orphan storage) makes this unobservable.
- FS4. `compute_state_root d` (`state_mpt.py:82–120`): copy the tries; drop storage tries of `d.storage_clears`; apply `d.account_changes`; apply `d.storage_changes` (creating a trie if needed and removing it if it becomes empty); the root of the account trie with each existing account's storage root (`EMPTY_TRIE_ROOT` without a trie). `code_changes` is ignored. It must equal `mathStateRoot (σ.apply d)`, computed through the oracle (D5), and never fail on WF inputs.
- FS5. `apply_changes_to_state` (`state_mpt.py:133–161`), used between blocks by the chain runner (`forks/amsterdam/fork.py:259`) and by `execution_engine/new_payload.py`: clears first, then accounts, then storage, then `code_store.update(code_changes)`. In Lean: `σ ↦ σ.apply d`.
- FS6. `store_code` (`state_mpt.py:164–171`) computes Keccak on the complete
  code bytes and returns the digest. It replaces the raw code entry at that digest
  when the digest differs from `EMPTY_CODE_HASH`. F21 gives the Lean operation
  its insertion-only certificate (§§5/7). `set_account` (`:174–184`)
  changes the selected account and retains storage and code.
  `FullState.setAccount` packages that result with the supplied WF proof.
  `set_storage` (`:187–206`) **asserts that the
  account exists**, then writes and removes empty tries. `state_root` calls
  `compute_state_root(BlockDiff())` (`:209–213`). `close_state` (`:123–130`)
  releases resources. In Lean, drop the value.
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
| `state_mpt.py::store_code` | 164–171 | `FullState.storeCode` | Supplied F21 operation and complete projection law (§§5/7). The reserved digest returns the original carrier. Other answers install the complete bytes at the certified digest. |
| `state_mpt.py::set_account` | 174–184 | `FullState.setAccount` | Supplied FS6 setter over EthState's raw account update. The caller supplies structural WF of the result. |
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

### Implemented standalone account setter (FS6)

`FullState.setAccount` packages the result of the raw `MathState.setAccount`
operation and the supplied structural proof. It reuses the carrier's code
authenticity proof because the code map is unchanged. A supplied account
is present even when it has default values. `none` erases the account
while retaining its storage map. EELS `src/ethereum/state_mpt.py:174–184`
and `src/ethereum/merkle_patricia_trie.py:325–338`.

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

### Implemented code insertion (FS6, F21)

`STFSpec/StateFull.lean` supplies `FullState.storeCode` and
`FullState.storeCode_project` at the exact §5 types. The operation uses
the explicit certified-action bind. The continuation returns the whole
input carrier at the supplied reserved hash. For a nonreserved answer,
it inserts the complete bytes and packages the preserved structural
proof and the authentication proof for the new table. The proof uses
the returned digest certificate at the written key and the original
table's proof at every other key. The ordinary projection proof uses
the complete `observes` equality and `LawfulMonad`. The caller supplies
the hash constants and certified action.

## 4. Tests

- **Carrier (FS1):** `STFSpec/Conformance/StateFull/CarrierChecks.lean`
  verifies all three projections and reconstruction. It checks an empty
  state and a state with a present account whose nonreserved code hash is
  missing from an authentic empty code table. The latter uses the public
  mathematical account and code observers.
- **Account setter (FS6):** `STFSpec/Conformance/StateFull/AccountChecks.lean`
  checks the exact raw option and carrier equations and the structural
  proof boundary. The complete finite snapshots cover insertion of a
  default-shaped account and one with unavailable code, replacement with
  retained storage, deletion with no selected storage and raw deletion
  with selected slots still visible. Eight authenticated source probes
  in each Python mode compare the complete maps before and after
  each call, including the retained orphan map and its account restored
  by a raw insertion.
- **Storage setter (FS6):** `STFSpec/Conformance/StateFull/StorageChecks.lean`
  compares complete account, storage and code states for insertion,
  insertion on a present empty account, replacement, zero deletion,
  final-map pruning and zero on an empty selected map. Missing-account
  zero and nonzero writes both return the typed error. The six admitted
  source cases agree in normal and
  optimized pinned Python. The absence controls exercise the assertion
  difference in §3.
- **Code insertion (FS6, F21):** `STFSpec/Conformance/StateFull/CodeInsertionChecks.lean`
  compares the digest and complete raw maps for insertion, repeat and
  the concrete reserved skip. The observing controls use a selected
  reserve whose authentic entry already exists. They check whole
  carrier retention, the query preimage and trace, and propagation
  of the selected typed error and Option absence. A private lawful
  observing proof uses the public whole-action projection equation.
  Six authenticated source probes in each Python mode check the complete
  maps before, during and after the query. They include the original
  query exception and a synthetic nonreserved answer. That answer tests
  the Python write branch only. F21's nonreserved certificate requires
  the concrete code digest (§7).
- **EEST:** all `blockchain_tests` and `blockchain_tests_engine` areas (295 area directories in `STFSpec/informal/eest-fixture-index.txt`) run through this backend in `EthConformance`, checking every post-state root; multi-block fixtures exercise `applyChanges`.
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
def FullState.storeCode {m : Type → Type} [Monad m] [KeccakQuery m]
    (s : FullState) (consts : HashConsts) (code : ByteArray)
    (answer : m {h : Hash32 //
      h ≠ consts.emptyCodeHash → Id.run (KeccakQuery.keccak (m := Id) code) = h})
    (observes : Subtype.val <$> answer = KeccakQuery.keccak (m := m) code) :
    m (Hash32 × FullState)

theorem FullState.storeCode_project {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (s : FullState) (consts : HashConsts) (code : ByteArray)
    (answer : m {h : Hash32 //
      h ≠ consts.emptyCodeHash → Id.run (KeccakQuery.keccak (m := Id) code) = h})
    (observes : Subtype.val <$> answer = KeccakQuery.keccak (m := m) code) :
    (fun result : Hash32 × FullState ↦ (result.1, result.2.σ)) <$>
        s.storeCode consts code answer observes =
      (do
        let h ← KeccakQuery.keccak (m := m) code
        pure (h, if h = consts.emptyCodeHash then s.σ
          else {s.σ with code := s.σ.code.insert h code}))

def FullState.setAccount (s : FullState) (a : Address) (acc : Option Account)
    (h : MathState.WF (s.σ.setAccount a acc)) : FullState -- deletion retains the selected storage map
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

- [C] `ModelsLookups consts (s.toPreState consts) s.σ` follows at Id from the
  observer definitions for every supplied record. Full binary `Models` and
  its unary `ModelsCode` clause use the concrete interpretation (Q57), so
  the execution-context lookup premise requires coherence with `constsId`.
  `CodeAuthentic` gives the digest equation `keccak256 c = h` for
  successful nonreserved answers `(h, c)`. FS2 gives the reserved
  empty answer at the coherent hash (EthStateCommit SC7).
  `applyChanges` requires
  `CodeChangesAuthentic`. Code lookup progress for account references
  requires the separate `CodeComplete` premise.
- [C] `ModelsRoot`: `stateRoot d = mathStateRoot (σ.apply d)` by definition; the EELS commuting equation (FS4) is that `compute_state_root` computes this value.
- [C] `applyChanges` preserves `WF` given `BlockDiff.WF`; `s.toPreState.stateRoot d = .ok (stateRoot (applyChanges s d))` (with the required WF/authenticity proofs).
- [T] FS7 covers the planned account and storage lookups and root operation
  under the §5 contract. Code lookup progress uses the availability premise
  in FS2. The supplied storage setter requires a present account for success
  (FS6, §3).

### Full-state account updates (FS6)

For a supplied `FullState`, inserting any account preserves structural WF.
Erasing an account preserves WF exactly when the old storage map has no
entry at that address. The raw update retains storage at the selected
address and every other address. A retained map at an erased address would
violate the account-presence clause. The caller supplies the proof on the
resulting state in both cases. The private conformance client proves
these conditions and checks that the setter packages the entire raw state
with the supplied proof and the preserved authentication proof.
Code lookup availability remains a separate premise.

### Full-state code insertion (FS6, F21)

The operation takes the caller's `HashConsts` and explicitly binds the
certified `answer`. Its effects follow the supplied monad's bind. When the
continuation receives `consts.emptyCodeHash`, it returns that digest and the
original complete `FullState`. At another digest it uses the conditional
proof to establish authentication of the new entry. It returns that digest
and the carrier with the complete code bytes stored at that key, replacing
any prior entry there. It retains the accounts, storage and every other raw
code entry. The only branch test is equality with the supplied reserved hash.

The `observes` premise equates the entire action obtained by erasing the
certificate with the actual `KeccakQuery.keccak` action on these bytes.
Only `storeCode_project` adds `LawfulMonad`. It projects the entire result
action to the digest and mathematical state and equates it with binding the
actual query and choosing the same raw result. Constructing the executable
certified action and proving its erasure are caller obligations.

Correspondence to EELS `src/ethereum/state_mpt.py:164–171` requires the
concrete hash interpretation and a coherent caller-supplied
`emptyCodeHash`. A raw reserved answer needs no proof about the concrete
digest because it leaves the code store intact.

### Informal correctness argument

**Claim.** A structurally well-formed, code-authentic full state implements Models and executes all admissible account/storage/root operations; code lookup additionally needs availability of referenced code.

**Premises.** EthStateCommit laws, MathState.WF, CodeAuthentic, CodeComplete when code progress is required, and a reachable well-formed diff with authentic code changes.

**Argument.** Account and storage lookup are direct finite-map observations with the specified absent defaults. Code lookup returns empty code for the empty-code hash, and otherwise returns the stored bytes or the named missing-code failure. Applying a diff follows the same clear/delete/write equations as MathState.apply; induction over entries preserves structural well-formedness under the supplied update premises. Authentic new code preserves CodeAuthentic. Root computation uses the defining canonical two-level trie construction, so its result is the mathematical root of the updated state. Taking successful-answer equations gives Models; taking existence of the required map entries gives progress. These are distinct deductions. A raw account deletion is not automatically a valid FullState update because it can leave orphaned storage.

**Open obligations.** Make the progress domain and CodeComplete explicit in every caller, prove apply preservation, and fix the hash-relative root fold in collision cases. Equality of states may omit the code store operationally, but proofs using code must retain its authenticity and availability hypotheses.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthStateCommit`
- **Used by:** `EthConformance`.
- **Seams:** a `PreState` for `executeBlock`; `applyChanges` for multi-block fixtures.

## 9. Open decisions

- D5 (broad scope, monad-parametric). `toPreState` returns `PreState m`
  and `stateRoot` hashes through the oracle. F21 governs how `storeCode`
  uses its certified Keccak action. `Models` and the progress theorem
  are stated at `m := Id`.
- D10 (accepted): included.
- D22: the state is read-only within a block, so the persistence rule does not bind; trees are kept for `=`-reasoning.
- NEW-STATE-2: resolved: DECISIONS B2 (Q30) (FS2).

## 10. Gaps

- **Backend integration:** §3 supplies the carrier, `ofMath` and the
  standalone account and storage setters. Provider construction, lookups, root
  computation, the full diff operation, caller integration for account
  updates and operational equality remain open.

- **Full-state code insertion:** §§3–5 and §7 supply the F21 action,
  complete projection law and local conformance. Caller construction,
  a common certificate adapter, availability and backend progress remain
  open.

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- `CodeComplete σ` (every account's code hash is stored) is assumed for fixtures, not checked.
- `MathState.WF` for fixture pre-states (no orphan storage, no zero values) is an inference from `set_storage`'s assertion and genesis loading.
- Full recomputation of the root per block has no measured cost on the corpus; mainnet-size use would need the incremental variant.
- The full-state backend must classify missing code as a backend fault and discharge `CodeComplete` for any successful fixture pre-state; the stateful fixture runner reports the resulting validity separately from its warning-only EEST exception-label mapping (EthConformance R3, DECISIONS Q9).
