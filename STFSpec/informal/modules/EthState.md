# `EthState`: state semantics, the pre-state contract, transaction and block overlays

*Status: informal specification, draft; §3 lists the supplied declarations and §10 the remaining work. Date: 2026-11-23. Pin: `tests-zkevm@v21.0.6` @59c1473d. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F1, F2, F7, F19, F20 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D2, D5, D8, D9, D14, D16, D18, D22, D23, D25 · questions: B1 (Q29/Q36), B2 (Q30), B14 (Q31), F7, Q57, Q58, Q84, Q85.*

Line references are to the pinned source under `src/ethereum/` (`state.py`, and `forks/amsterdam/state_tracker.py` abbreviated `st:`). "[verified]" means read in the pinned source and, where marked, executed against the pinned `ethereum_types`/`ethereum_rlp`; "[inference]" means a conclusion from reading that no test or proof yet backs. EELS `file:line` citations are at `59c1473d` except where marked and those listed in `STFSpec/informal/citation-remap-manual.txt`, which are still at `e1a316a0` (`tests-zkevm@v21.0.0`); verified observations are at `e1a316a0` unless marked as at `59c1473d` (GAPS-CROSSCUTTING X16).

## 1. Purpose

`EthState` is the **semantic** state layer (ARCHITECTURE §2, layer L2). It defines accounts, the `PreState` record of lookup operations and its lookup contract `ModelsLookups`, the mathematical state `MathState` and its diff application, the block diff `BlockDiff`, and the two overlays that EELS keeps in `state_tracker.py`: the per-transaction state (split per D23 into a snapshot-reachable revertible component and linearly threaded observations) and the per-block state. It owns the read/write/clear/rollback laws that the VM, SSTORE gas and the BAL builder rely on. It must not see hashed nodes, RLP, roots or witness decoding (D16); the root and code-hash clauses of the contract live in `EthStateCommit` (D20).

## 2. Requirements

### 2.1 Accounts and constants

- R1. `Account` has exactly `nonce : Nat`, `balance : U256`, `codeHash : Hash32` (`state.py:36–43`). The nonce is EELS `Uint` (unbounded); no overflow check exists in the tracker (`st:696–712`). Nonce limits (EIP-2681) are transaction validation, owned by `EthBlock`.
- R2. `emptyCodeHash` is `HashConsts.emptyCodeHash` (`EthBase`; D5, DECISIONS §3): a keccak-derived constant acquired by the caller under F20 through `HashConsts.query` (`EthHash`) and carried in `BlockState.consts`. `EthState` cannot import `EthHash` and never hashes; it receives the record as data. At `m := Id` its value is the literal `0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470` (`state.py:30`, `keccak256(b"")`) [verified value by execution], held in `HashConsts.literals` (`EthBase`); `EthHash` checks that `HashConsts.query` at `Id` yields `HashConsts.literals` (`EthHash` §7). Below, `emptyCodeHash` refers to that field; definition bodies use local EELS notation `EMPTY_CODE_HASH` projected from their constants/state context (F20).
- R3. `emptyAccount consts = {nonce := 0, balance := 0, codeHash := consts.emptyCodeHash}` for `consts : HashConsts` (`state.py:46–50`). A non-existent account (`none`) is distinct from `emptyAccount` (`state.py:12–13`) and every operation must preserve the distinction.

### 2.2 `BlockDiff`

- R4. `BlockDiff` carries `accountChanges : Address → Option (Option Account)` (a change to `none` deletes), `storageChanges : Address → Bytes32 → U256` (a change to `0` deletes), `codeChanges : Hash32 → Bytes`, `storageClears : Set Address` (`state.py:55–83`), plus the three replay orders that B1 requires and the reference carries implicitly as dict insertion order: `accountOrder` (first write of each changed account), `storageAddressOrder` and, per address, `storageSlotOrder` (§5, §7.5). `storageClears` carries no order (F7, open; §7.5).
- R5. **Application order** (`state.py:73–83`; `state_mpt.py:145–161`): for an address in `storageClears` the pre-existing storage is dropped *before* `storageChanges` is applied, so post-clear writes start from empty storage. Account changes and code changes are independent overwrites.
- R6. **Account-change order is observable** [verified by reading, and by executing the pinned `incremental_mpt` on a two-operation example: delete-then-insert raises `HashedNode cannot be witnessed`, insert-then-delete succeeds; not in ARCHITECTURE]. `WitnessState.compute_state_root_and_trie_changes` applies `account_changes` in Python dict iteration order (`witness_state.py:303–309`), with insertions and deletions interleaved, and a deletion that collapses a branch onto an unresolved sibling fails (`incremental_mpt.py:780–790`) while the same deletion after an insertion under that branch does not. The dict order is the order of **first write in the block**: `st:836–837` assigns into `block.account_writes` (existing keys keep their position), and a transaction's `account_writes` is ordered by its first `set_account` (`st:454`; `copy_tx_state`/`restore_tx_state` preserve order, `st:765`, `st:794`). So `BlockDiff` must carry the first-write order of account changes (B1), or the witness backend's accept/reject behaviour differs from EELS. Storage-address and slot orders are preserved too (B1); whether the clear iteration order is observable is open (F7, §7.5).

### 2.3 The `PreState` record and `ModelsLookups`

- R7. `PreState m` is a record of four operations (`state.py:86–133`; D9), generic in the hash monad `m` (D5): `getAccount?`, `getStorage`, `getCode`, `stateRoot`, each returning `m (Except WitnessError _)` (D8). A witness lookup hashes its key, so the pre-state lives in the oracle monad (F1). The raw record accepts any `m : Type → Type` without a Monad premise. Downstream sequencing operations require `[Monad m]`; `EthState` never needs `KeccakQuery`, which stays in `EthHash`. Public entry points use `m := Id`. `getStorage` returns `0` for an unset key (`state.py:102–108`); `getCode` returns the empty byte array for `emptyCodeHash` (`state.py:110–116`); `stateRoot d` computes the post-root without changing the pre-state (`state.py:118–133`): the record is immutable, and `m` carries only keccak queries.
- R8. `ModelsLookups consts ps σ` is stated for `ps : PreState Id` and an explicit caller-supplied `consts : HashConsts` (Q57). Every successful account, storage and code answer agrees with the corresponding mathematical observer, **including account absence**; code has no successful absent case (R9). The code clause uses `σ.code? consts h`, including the supplied reserved hash. Arbitrary supplied records and raw MathStates are admitted: no WF, authenticity, availability, root or constants/oracle coherence premise is imposed. Errors are unconstrained; backend progress is separate (ARCHITECTURE §5.3). `ModelsCode` and `ModelsRoot` remain in `EthStateCommit`; generic-monad coupling remains open under D5.
- R9. The EELS `get_code` protocol method has **no absent result**: missing code is a `KeyError` in both backends (`state_mpt.py:57`, `witness_state.py:137`). So (B2, adopted 2026-09-28; a revision of D9) `getCode : Hash32 → m (Except WitnessError ByteArray)`. **Missing code is an error; empty code is a successful value** (`emptyCodeHash` ↦ the empty byte array). There is no `.ok none` case.
- R10. The tracker **does not cache pre-state answers**: every read that falls through the overlays calls the provider again (`st:137`, `st:259`, `st:295`, `st:324`). With a deterministic provider (any `PreState Id`), a repeated call returns the same result, so this is a cost question only. The witness provider nonetheless has side effects in EELS (decoding and a storage-root cache); `EthStateWitness` shows they are not observable except through the history condition of R32.

### 2.4 Reads and their observation side effects

Reads select the transaction or pre-transaction block view as listed below (§7.1)
and record observations as follows [verified line by line]:

| Operation (EELS) | Lines | Returns | Observations recorded |
|---|---|---|---|
| `get_pre_state_account_optional` | `st:107–137` | block write, else pre-state (skips tx writes) | `accountReads += a` |
| `get_pre_state_account` | `st:140–171` | as above, `none ↦ emptyAccount` | as above |
| `get_account_optional` | `st:174–197` | tx write, else as `get_pre_state_account_optional` | `accountReads += a` (added twice on fall-through; idempotent) |
| `get_account` | `st:200–225` | as above, `none ↦ emptyAccount` | as above |
| `get_code(h)` | `st:228–259` | `""` if `h = emptyCodeHash`; tx code write; block code write; else pre-state | `codeReads += h` before the pre-state call; no account read |
| `get_storage` | `st:262–295` | precedence R11 | `storageReads += (a, k)` **always**, even when a write answers |
| `get_storage_original` | `st:298–324` | R12 | **none** |
| `get_transient_storage` | `st:327–349` | tx transient value, default `0` | none |
| `account_exists`, `account_deployable` | `st:352–380` | predicates over `get_account(_optional)` | `accountReads += a` |
| `account_exists_and_is_empty`, `is_account_alive` | `st:383–431` | one current optional lookup, then compare a present account with the empty account | observations of that lookup |

The hash-only `getCode` action follows `state_tracker.py:252–259`: test
emptyCodeHash, transaction code writes and block code writes, in that order.
Each bypass skips observation insertion and the provider; a stored empty byte string
is a write hit. Fall-through inserts the hash before one provider call, and repeated
fall-through calls the provider again without memoization. A provider failure is
propagated, never defaulted. Source mutation before failure is distinct from the
absence of a returned failed Lean StateM state; generic base effects need their own
refinement. The action and laws are supplied in §3 and §7.1.

- R11. **Storage precedence** (`st:284–295`): transaction slot write → transaction clear (`0`) → block slot write → block clear (`0`) → pre-state. A clear suppresses only lower layers: writes made after the clear in the same layer remain visible.
- R12. **Original value** (`st:317–324`): `0` if `a ∈ createdAccounts`; otherwise block slot write → block clear (`0`) → pre-state. Transaction writes and clears are skipped. It records no observation.
- R13. `account_deployable` is false iff `nonce ≠ 0` or `codeHash ≠ emptyCodeHash` (`st:376–380`); it does not look at storage. `is_account_alive` is `exists ∧ ≠ emptyAccount` (`st:430–431`).

### 2.5 Writes

- R14. `set_account` (`st:434–454`) writes the transaction layer with **no read** and no storage effect. Setting `none` deletes the account but not its storage.
- R15. `set_storage` (`st:457–481`) first requires `get_account_optional a ≠ none` (an `assert`, which records an account read) and then writes the slot, including `0`. The assert is unreachable from SSTORE [inference: the current target exists while its code runs], but the Lean operation must return `StateError.storageOnMissingAccount` rather than assume it.
- R16. `destroy_storage` (`st:528–549`): every pending transaction write for `a` is first **converted into a storage read** (`storageReads += (a, k)` for each written key), then the address's transaction writes are dropped and `a` is added to the transaction `storageClears`. The read conversion persists even if the clear is later reverted (reads are not snapshotted).
- R17. `destroy_account` = `destroy_storage` then `set_account a none` (`st:484–501`). `clear_account_preserving_balance` = `destroy_storage`, then `modify_state` setting `nonce := 0`, `codeHash := emptyCodeHash` (`st:504–525`); if the balance is zero the result is destroyed by R18.
- R18. `modify_state a f` (`st:601–613`): read `get_account a` (so `none ↦ emptyAccount`), apply `f`, `set_account`, then if `account_exists_and_is_empty a` (a second read) `destroy_account a`. Consequently touching a non-existent account with a zero-value change writes `none` and adds `a` to `storageClears`.
- R19. `move_ether` (`st:616–647`) applies the sender update then the recipient update, each through `modify_state`. The sender update fails if `balance < amount` (`AssertionError`, `st:639–640`). **The recipient update and `create_ether` (`st:650–670`) fail on `U256` overflow**: `ethereum_types` `U256.__add__` raises `OverflowError` [verified by execution]. A wrapping Lean `U256.add` would deviate; the operations must use checked addition and return `StateError.balanceOverflow`. On honest chains this is unreachable (total supply); witness-supplied balances make it reachable, as argued in the failure ledger (maintained outside this repository) (`st:644`, `st:668`), so it is an O13 fault (R29).
- R20. `set_account_balance` and `increment_nonce` go through `modify_state` (`st:673–712`).
- R21. `set_code a code` (`st:715–738`) computes `h = keccak256 code`, records `codeWrites[h] := code` only if `h ≠ emptyCodeHash`, then `modify_state a (codeHash := h)`. In Lean the operation takes the code **and its hash** (ARCHITECTURE §5.3, code-hash ownership); callers compute the hash through `KeccakQuery` (D5: newly installed code hashes) and establish `h = keccak256 code` and `EthStateCommit` owns the agreement law. The order of effects (code write, then the account read/write/possible destroy) must be preserved.
- R22. `mark_account_created` (`st:552–571`) adds the complete address to `createdAccounts`. Its membership survives source rollback (`st:559–561`, `st:772`).
- R23. `set_transient_storage` (`st:574–598`) writes the transaction layer; writing `0` removes the key. Transient storage is keyed by `(Address, Bytes32)` (`st:102–104`) and is part of the revertible component.

### 2.6 Snapshot, revert and lifecycle

- R24. `copy_tx_state` (`st:744–777`) snapshots **exactly** `account_writes`, `storage_writes` (one level deep), `code_writes`, `storage_clears` and `transient_storage`; it **shares** `created_accounts`, `storage_reads`, `account_reads`, `code_reads` and the parent. `restore_tx_state` (`st:780–798`) reinstates exactly those five fields. EELS assigns the snapshot's dicts directly, so a snapshot is used at most once (LIFO); the persistent Lean representation removes that restriction.
- R25. `incorporate_tx_into_block` (`st:804–858`), in this order: (1) the BAL builder is updated from the unmerged transaction and block states (`st:828`, owned by `EthBlock`); (2) the three read sets are unioned into the block's (`st:831–833`); (3) account writes overwrite block writes, keeping first-write order (`st:836–837`); (4) for each transaction clear, the address is added to the block clears **and its block storage writes are dropped** (`st:839–841`); (5) transaction storage writes are merged slot-wise (`st:843–846`); (6) code writes are merged (`st:848`); (7) the transaction state is reset: writes, clears, transient storage and `createdAccounts` emptied, fresh read sets (`st:850–858`).
- R26. `extract_block_diff` (`st:861–881`) copies the four complete effect fields. Q85 supplies the raw B1 adaptation: both global orders use `WriteOrder.toList`, and the slot-index map is mapped through that observer with its domain unchanged. No filtering, repair, WF or history premise is imposed. EELS aliases the source dicts/clear set; pure Lean preserves their values under the typed finite nonaliasing source bridge, without modeling later mutable alias effects.
- R27. `track_ancestor_access b o` (`st:884–905`) stores `some o` for an absent cursor and keeps the greater offset when one is present. The standalone action accepts every nonnegative offset, including zero. Pinned BLOCKHASH calls it after successful history lookup (`vm/instructions/block.py:47–63`). The cursor is in the block state held by the current transaction, outside its revertible fields (D23).
- R28. A throwaway transaction state is used for the system-contract code pre-check (`fork.py:691–702`): its observations are discarded, but its pre-state calls still happen, so a witness failure there still rejects the block. The Lean API must allow a transaction state that is never incorporated.

### 2.7 Failure behaviour

- R29. Tracker operations report typed failures through `StateM m`'s `ExceptT StateError` layer; `StateError` wraps `WitnessError` from the provider and adds `balanceUnderflow`, `balanceOverflow` and `storageOnMissingAccount`. In the guest, all of them become `successful_validation = false` (`stateless.py:294`, `except Exception`). Witness errors are O4 (`STFSpec/informal/CONTRACT.md` §4). The three state errors fall under **O13** (enumerated deterministic reference faults: the existing output, one named constructor each, no catch-all; D14). `balanceOverflow` is argued reachable (R19). `balanceUnderflow` (`st:639–641`) and `storageOnMissingAccount` (the `assert` at `st:478`, R15) are unresolved in the ledger: each keeps its named constructor, and is either shown reachable (an O13 member) or proved unreachable. `StateError` is frozen once this module's ledger entries close (B14).
- R30. Failure must be **propagated, not defaulted**: a failed pre-state lookup must never be turned into "absent" or `0` (D8).
- R31. All operations are non-recursive or structurally recursive, so none has a host-dependent reference site (O12). A static call-graph pass agrees: the call-graph cycles it finds in `state_tracker.py` are name artefacts, not recursion.
- R32. **History condition for the witness root** (cross-module): EELS's witness root uses a storage-root cache filled only by account lookups (`witness_state.py:106–109`, `:197`). The tracker guarantees that every address in `accountChanges` was looked up in the pre-state earlier in the block: `set_account` is reached only from `modify_state`/`destroy_account` (`st:611–613`, `st:500–501`; no other caller in `forks/amsterdam/`), each preceded by `get_account`, and the first write of an address in the block necessarily falls through to `pre_state.get_account_optional` (`st:137`). `EthState` must state and prove this as the invariant `AccountWritesLookedUp` (§7.4); `EthStateWitness` consumes it.

## 3. EELS source map

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `state.py::EMPTY_CODE_HASH` | 30 | `emptyCodeHash` | `HashConsts.emptyCodeHash` (`EthBase`, R2); `Id` value `HashConsts.literals`, checked in `EthHash` |
| `state.py::Account` | 36–43 | `STFSpec.State.Account` | Value seam implemented in `State/Account.lean`: unbounded `Nat` nonce, `U256` balance and complete `Hash32` code hash; constructor/eta/ext laws and ordinary field equality. `Conformance/State/AccountGuards.lean` covers full fields, huge nonce and zero/maximum balance. No runtime fault or tracker effect is introduced. |
| `state.py::EMPTY_ACCOUNT` | 46–50 | `STFSpec.State.emptyAccount` | Supplied `HashConsts` gives nonce zero, balance `U256.zero` and exactly `consts.emptyCodeHash`; three projection laws. Total for arbitrary constants; pinned value correspondence requires coherent F20 constants. Full-hash/alternative-constant and absence-versus-present guards are in `Conformance/State/AccountGuards.lean`. |
| `state.py::BlockDiff` | 55–83 | `STFSpec.State.BlockDiff` (seven raw fields; §5/§7) | **implemented raw value seam**: four EELS effect fields plus three B1 metadata fields; all finite raw inputs; constructor preserves complete payloads without effects/failures; ordinary component laws (§7) and complete-field guards/native oracle (§4). EELS default-empty construction is deferred. No application, WF or history claim. |
| `state.py::PreState` | 86 | `PreState m` | implemented raw carrier; source/law/test rows below (§3/§7), generic in `m` (D5/D9) |
| `state.py::PreState.get_account_optional` | 94 | `PreState.getAccount?` | supplied action; carrier support below (§3/§7) |
| `state.py::PreState.get_storage` | 102 | `PreState.getStorage` | supplied action; carrier support below (§3/§7) |
| `state.py::PreState.get_code` | 110 | `PreState.getCode` | supplied nonoptional action (B2); carrier support below (§3/§7) |
| `state.py::PreState.compute_state_root` | 118 | `PreState.stateRoot` | supplied action; carrier support below (§3/§7); contract `ModelsRoot` in `EthStateCommit` |
| `forks/amsterdam/state_tracker.py::BlockState` | 44–73 | `STFSpec.State.BlockState m` | **Supplied raw carrier:** exact thirteen §5 fields, arbitrary type constructor without Monad; nine source fields plus F20 constants and three B1 order indexes. Complete private clients/controls below; no tracker semantics; initialization is supplied separately below. |
| `forks/amsterdam/state_tracker.py::TransactionState` | 78–104 | `STFSpec.State.TxState m` | Supplied raw block/revertible/observation assembly below (D22/D23/B1 adaptation), including hash-only code observations. The separate `TxState.new` supplies fresh defaults below. Tracker and caller integration remain open. |
| `forks/amsterdam/state_tracker.py::get_pre_state_account_optional` | 107–137 | `getPreStateAccountOptional` | **Discharged bounded action:** Monad-only block/pre-state read, exact branch/error equations and Id framing/membership/model laws below. |
| `forks/amsterdam/state_tracker.py::get_pre_state_account` | 140–171 | `getPreStateAccount` | **Discharged bounded wrapper:** one optional action, absence defaulted from retained constants; five laws below. |
| `forks/amsterdam/state_tracker.py::get_account_optional` | 174–197 | `getAccountOptional` | **Discharged bounded action:** transaction entry priority, delegated pre-transaction fallback and six laws below. |
| `forks/amsterdam/state_tracker.py::get_account` | 200–225 | `getAccount` | **Discharged bounded wrapper:** one current optional action, absence defaulted from initial retained constants; five laws below. |
| `forks/amsterdam/state_tracker.py::get_code` | 228–259 | `getCode` | **Discharged bounded action:** hash-only priority, fall-through observation and five laws below. |
| `forks/amsterdam/state_tracker.py::get_storage` | 262 | `getStorage` | Standalone action supplied (§3/§7.1, R11) |
| `forks/amsterdam/state_tracker.py::get_storage_original` | 298–324 | `getStorageOriginal` | **Supplied standalone action:** created-account membership, block slot write, block clear, then the retained storage provider. Private equations and controls appear below. |
| `forks/amsterdam/state_tracker.py::get_transient_storage` | 327–349 | `getTransientStorage` | **Discharged read:** transaction transient lookup with a zero default and a complete action law below. |
| `forks/amsterdam/state_tracker.py::account_exists` | 352–369 | `accountExists` | Supplied wrapper over `getAccountOptional` (§7.1). |
| `forks/amsterdam/state_tracker.py::account_deployable` | 372 | `accountDeployable` | Supplied, R13. |
| `forks/amsterdam/state_tracker.py::account_exists_and_is_empty` | 383–410 | `accountExistsAndIsEmpty` | **Implemented:** current optional read and a complete comparison with the supplied empty account. |
| `forks/amsterdam/state_tracker.py::is_account_alive` | 413–431 | `isAccountAlive` | **Implemented:** current optional read and a complete comparison with the supplied empty account. |
| `forks/amsterdam/state_tracker.py::set_account` | 434–454 | `setAccount` | **Discharged standalone action:** whole account option and B1 order update; private laws in §§7.1/7.5. |
| `forks/amsterdam/state_tracker.py::set_storage` | 457 | `setStorage` | |
| `forks/amsterdam/state_tracker.py::destroy_account` | 484–501 | `destroyAccount` | **Supplied standalone action:** clear target storage, then record the account tombstone (§7.5). |
| `forks/amsterdam/state_tracker.py::clear_account_preserving_balance` | 504–525 | `clearAccountPreservingBalance` | **Supplied standalone action:** run R16 before R18, retaining the exact balance. |
| `forks/amsterdam/state_tracker.py::destroy_storage` | 528–549 | `destroyStorage` (ARCHITECTURE's `clearStorage`) | **Discharged standalone action:** pending slot keys become reads. The action erases the target patch and slot index, applies `WriteOrder.erase` to the address index, and records the clear. Private laws and typed controls below. |
| `forks/amsterdam/state_tracker.py::mark_account_created` | 552–571 | `markAccountCreated` | **Supplied standalone action:** insert the complete address into the transaction's created-account set. Private run and retention equations (§7), facade guards and bounded source comparisons (§4). |
| `forks/amsterdam/state_tracker.py::set_transient_storage` | 574–598 | `setTransientStorage` | **Discharged write:** insert or erase one full transient key and retain all other fields. |
| `forks/amsterdam/state_tracker.py::modify_state` | 601–613 | `modifyState` | **Supplied standalone action:** defaulted lookup, fallible callback, account write and second read before conditional R17 destruction (§7.5). |
| `forks/amsterdam/state_tracker.py::move_ether` | 616 | `moveEther` | checked add |
| `forks/amsterdam/state_tracker.py::create_ether` | 650 | `createEther` | checked add |
| `forks/amsterdam/state_tracker.py::set_account_balance` | 673 | `setAccountBalance` | |
| `forks/amsterdam/state_tracker.py::increment_nonce` | 696 | `incrementNonce` | |
| `forks/amsterdam/state_tracker.py::set_code` | 715 | `setCode` | takes the hash |
| `forks/amsterdam/state_tracker.py::copy_tx_state` | 744–777 | `copyTxState (t : TxState m) : TxRevertible` | Supplied for arbitrary m without a class premise. Selects the entire revertible record, including B1 metadata, without traversal or provider calls. |
| `forks/amsterdam/state_tracker.py::restore_tx_state` | 780–798 | `restoreTxState (snap : TxRevertible) : StateM m Unit` | Supplied under Monad m. One underlying pure returns unit with the saved revertible record and the current block and observations. No typed failure or provider call. |
| `forks/amsterdam/state_tracker.py::incorporate_tx_into_block` | 804 | `incorporateTxIntoBlock` | BAL hook in `EthBlock` |
| `forks/amsterdam/state_tracker.py::extract_block_diff` | 861–881 | `extractBlockDiff` | **Discharged raw extraction slice:** complete effects and Q85 metadata equations below; no reachable/history/WF claim. |
| `forks/amsterdam/state_tracker.py` `get_witness_ancestors` | 903 at `e1a316a0` | — | Historical mapping. The tracker helper was removed in execution-specs PR #3653. Host witness construction is covered by `EXCLUDED.md` and Q7. |
| `forks/amsterdam/state_tracker.py::track_ancestor_access` | 884–905 | `STFSpec.State.trackAncestorAccess` in `STFSpec/State/AncestorAccess.lean`, exported by State | **Supplied:** private complete Monad-only action, maximum cursor and retained-field equations. The action returns unit through one underlying `pure`. Five whole-offset histories and retained-state/provider controls in §4. |

`state.py` is claimed item by item above; no item of either file is left unclaimed.

**External semantics.** `ethereum_types.numeric.U256` (add/sub raise on overflow/underflow; the tracker relies on raising, R19), `Uint` (unbounded, `Nat`), `ethereum_types.bytes.Bytes`/`Bytes20`/`Bytes32` (fixed-width constructors, owned by `EthBase`), `ethereum_types.frozen.modify` (functional update of a frozen dataclass: in Lean, record update) and `slotted_freezable` (immutability; no Lean counterpart needed). `EthBase` owns the representations; this module requires checked `U256` addition/subtraction returning `Option`/`Except`.

### Implemented hash-only code read

`State/Code.lean`, exported by State, supplies the read and its four operational
laws. `State/TransactionView.lean` supplies the model law using its private code-map
equation and the public block, application and lookup laws.

| Source at the pin | Lean declaration and domain | Value, effects and failures | Laws and validation |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/state_tracker.py:228–259` | `getCode {m : Type → Type} [Monad m] (h : Hash32) : StateM m ByteArray` on arbitrary supplied carriers and constants | Return empty bytes for the supplied reserved hash. Otherwise prefer present transaction writes, then present block writes, including empty bytes. On each miss insert the queried hash and call the supplied provider once. Wrap its exact error as `StateError.witness`, with no returned state. | **Discharged for this action:** `getCode_action`, `getCode_error`, `getCode_frames`, `getCode_mem`, `getCode_model` (§7.1). Private facade clients and the finite controls in §4 check these interfaces and observations. |

### Supplied transaction-state initialization

| Source at the pin | Lean declaration | Effects | Laws and tests |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/state_tracker.py:78–104`, used at `fork.py:540,697,748,1104` | `TxState.new (b : BlockState m) : TxState m` in `STFSpec/State/TransactionInitialization.lean`, exported by State | Class-free construction over the complete supplied block. Empty transaction maps, clear set, observations and created accounts. Both global order indexes are `WriteOrder.empty` and per-address slot order is absent. | A private complete equation verifies every default and retention of the entire supplied block. The private facade controls and direct source comparison cover the defaults (§4). |

### Implemented original storage read

| Source at the pin | Lean declaration and domain | Ordered effects and failures | Laws and validation |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/state_tracker.py:298–324` | `getStorageOriginal : Address → Bytes32 → StateM m U256` in `State/StorageOriginal.lean`. Requires only `Monad m` and accepts raw transactions. | Created membership returns zero first. Otherwise a block slot entry returns its value, including zero. A missed entry at a cleared address returns zero. The remaining branch calls `t.block.preState.getStorage a k` once. Success returns the whole input transaction. A provider error returns the complete `StateError.witness` payload without a transaction. | Private complete branch equations and the guided conditional `Id` model equation (§7.1). Finite effect, frame and source controls appear in §4. |

### Implemented optional pre-transaction account read

`State/PreStateAccount.lean` supplies the first StateM tracker action. It inserts
`a` into transaction account reads before inspecting block writes. A stored
`tombstone` returns none without a provider call. A missing entry invokes the
retained `t.block.preState.getAccount? a` once on every invocation, including
repeated reads. Transaction writes, other provider actions and hashing are skipped.

| Source at the pin | Lean declaration and domain | Ordered effects and failures | Laws and validation |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/state_tracker.py:107–137` | `getPreStateAccountOptional {m : Type → Type} [Monad m] (a : Address) : StateM m (Option Account)`; arbitrary supplied raw states/accounts/providers, with no other class or validity premise | Insert transaction account-read membership; select block replacement/tombstone, else call the retained account provider once. Preserve exact optional account or wrap the exact typed failure as StateError.witness; failure returns no transaction state (R29/R30). | **Discharged:** `getPreStateAccountOptional_of_block`, `_of_missing`, `_error`, `_frames`, `_mem`, `_model` (§7.1). Private facade clients retain complete block/rev/provider functions/constants and unrelated observations. Native/interpreted complete 66-case controls and strict-reader regressions are in §4. |

The generic laws are action equations, without interpreting an arbitrary Monad's
effects. Success framing, membership, exact provider error and model content are
at Id. The model theorem retains §7.1's initial MathState.WF and ModelsLookups
premises and successful execution, using only account agreement and existing public
block view/application/extraction laws. There is no memoization, backend, State-to-VM
lift, rollback or full-state refinement claim.

### Implemented defaulted pre-transaction account read

`getPreStateAccount` runs the optional action once and defaults only `none` to
`emptyAccount t.block.consts`, using the initial retained context. Present accounts,
the entire successful state and every typed failure are retained. The wrapper adds
no observation insertion, provider call, hashing or acquisition of constants.

| Source at the pin | Lean declaration and domain | Ordered effects and failures | Laws and validation |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/state_tracker.py:140–171` | `getPreStateAccount {m : Type → Type} [Monad m] (a : Address) : StateM m Account`; every raw supplied state, account, provider and constants | Run `getPreStateAccountOptional a` once; map successful absence to the initial context's empty account, retain present values and exact success state, propagate errors unchanged with no returned failed state | **Discharged:** `getPreStateAccount_action`, `_error`, `_frames`, `_mem`, `_model` (§7.1). Private facade clients and independent complete native/interpreted 81-case controls (§4). |

The generic action equation retains its literal bind/pure structure and requires no
LawfulMonad. The Id model law uses exactly the existing initial WF, ModelsLookups
and success premises. Concrete source agreement additionally requires the typed
source/dependency bridge and an F20-coherent empty-code hash. Raw constants remain
unrestricted mathematical inputs and do not imply equality to source EMPTY_ACCOUNT.

### Implemented current optional account read

`State/AccountOptional.lean`, exported by State, implements only this current-account
operation. The defaulted `getAccount` wrapper below consumes its public laws.

| Source at the pin | Lean declaration and domain | Value/effects and failures | Laws and validation |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/state_tracker.py:174–197`, delegating to `:107–137` | `getAccountOptional {m : Type → Type} [Monad m] (a : Address) : StateM m (Option Account)` | Insert the queried transaction account read first; an original transaction entry returns its exact Option, including a tombstone. A miss delegates to getPreStateAccountOptional on the marked state, retaining its second insertion and block/provider priority. No defaulting or memoization. Typed provider errors are wrapped without a returned failed transaction state. | **Discharged for this slice:** exactly six ordinary action/error/frame/membership/model laws (§7.1). Private facade clients consume them without owner unfolding; complete 248-case native/interpreted controls and 233 coherent original-source comparisons are specified in §4. |

The two generic action laws require only Monad and retain literal complete actions;
no LawfulMonad, generic success inversion or raw duplicate-insert identity is used.
Id frames retain the entire block and revertible record, including arbitrary
providers, constants and metadata, plus unrelated observations. The model law
retains exactly the initial WF/ModelsLookups/success domain and consumes only the
public transaction account-view law and pre-transaction contracts. Other trackers, actual providers,
source error adapters, lifetimes, reachable history, full-State and cost gates remain open.

### Implemented defaulted current account read

`State/AccountDefault.lean`, exported by State, supplies `getAccount`. It runs the
current optional action once and defaults successful absence using the initial
`t.block.consts`. It preserves every present account, the exact success state and
the exact error on failure.

| Source at the pin | Lean declaration and domain | Ordered effects and failures | Laws and validation |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/state_tracker.py:200–225`, delegating to `:174–197` | `getAccount {m : Type → Type} [Monad m] (a : Address) : StateM m Account`; every raw supplied state, account, provider and constants | One current optional action; default only none to emptyAccount at the initial constants, preserve present accounts and exact next state, propagate the exact StateError without a returned failed state (R29/R30) | **Discharged:** exactly `getAccount_action`, `_error`, `_frames`, `_mem`, `_model` (§7.1). Private facade clients consume only public laws. Complete independent 248-case native/interpreted and 233 coherent original-source controls are in §4. |

The generic action law is literal bind/pure equality under Monad only. Id frame,
membership and model proofs consume the optional public laws; the model domain is
exactly initial MathState.WF, supplied-record ModelsLookups and success. No provider
or hashing action is added. Concrete source agreement requires the typed source
bridge and F20-coherent empty-code constants. Arbitrary constants remain permitted
mathematical inputs. Other trackers, generic coupling and whole-State gates remain open.

### Implemented account deployability

`State/AccountDeployable.lean` exports `accountDeployable` through State.

| Source at the pin | Lean declaration and domain | Ordered effects and failures | Laws and validation |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/state_tracker.py:372–380`, delegating to `:200–225` | `accountDeployable {m : Type → Type} [Monad m] (a : Address) : StateM m Bool` on arbitrary supplied transaction states | Run `getAccount` once. On success, test for a zero nonce and equality with the full contextual empty code hash. Return the read's complete resulting transaction with the test, or propagate its exact error (R29). | The action, predicate and model equations are private (§7.1). Section 4 records the interpreted and pinned-source controls. |

### Implemented transient storage read

| Source at the pin | Lean declaration and domain | Value, effects and failures | Law and validation |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/state_tracker.py:327–349` | `getTransientStorage {m : Type → Type} [Monad m] (a : Address) (k : Bytes32) : StateM m U256` in `State/TransientStorage.lean`, for every raw transaction state | Read the whole word at `(a, k)` in the transaction transient map. Return zero when the key is absent. Return the original transaction state through the base `pure` without a provider call, observation or typed failure. | **Discharged:** the complete `getTransientStorage_action` law (§7.1), a private facade client and the ten typed cases in §4. |

### Implemented transient storage write

| Source at the pin | Lean declaration and domain | Value, effects and failures | Laws and validation |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/state_tracker.py:574–598` | `setTransientStorage {m : Type → Type} [Monad m] (a : Address) (k : Bytes32) (v : U256) : StateM m Unit` in `State/TransientStorageWrite.lean`, for every raw transaction state | Set the complete `(a, k)` entry in the transaction transient map. A zero word erases the entry, including an explicitly stored zero. Return unit and the updated state through a single base `pure`. All other fields are retained. | **Discharged:** private complete action, framing, lookup and Id read-after-write proofs (§7.1 and §7.2), with ten paired cases (§4). |

### Implemented current storage read

| EELS source | Lean operation and domain | Ordered result and effects | Proof and test evidence |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/state_tracker.py:262–295` | `getStorage {m : Type → Type} [Monad m] (a : Address) (k : Bytes32) : StateM m U256` on arbitrary raw states and supplied providers | Mark `(a,k)`. Select the transaction slot, transaction clear, block slot, block clear or retained provider in R11 order. Present writes include zero. Repeat the provider call on every fall-through. Wrap its complete error as `StateError.witness` (R29/R30). | Private five-branch equations under `Monad`. Private `Id` whole-state, read-membership, exact error and conditional transaction-view proofs (§7.1). Facade guards and bounded native/interpreted comparisons with pinned source are in §4. |

### Implemented account existence check

| Source at the pin | Lean declaration and domain | Value, effects and failures | Laws and validation |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/state_tracker.py:352–369` | `accountExists {m : Type → Type} [Monad m] (a : Address) : StateM m Bool` | Run the current optional read once. A present account, including an empty one, yields true. Absence yields false. The read supplies the complete success state or error. | Private action and model proofs (§7.1). Paired Lean controls and pinned source cases (§4). |

### Implemented standalone ordered account write

`State/SetAccount.lean`, exported by `State.lean`, supplies R14 at
`src/ethereum/forks/amsterdam/state_tracker.py:434–454`.
`setAccount {m : Type → Type} [Monad m] (a : Address) (account : Option Account) :
StateM m Unit` inserts the whole option in the transaction map and records its
address with the existing `WriteOrder.record` (B1). It returns one base `pure`
of the successful unit and updated state. The action records no read, issues
no provider call and leaves storage writes and clears intact. The private
action, frame, model and local order proofs are specified in §§7.1/7.5.
`SetAccountNativeTests.lean` and the differential driver cover the finite
cases in §4.

### Implemented standalone transaction storage clear

| Source at the pin | Lean declaration and domain | Value, effects and failures | Laws and validation |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/state_tracker.py:528–549` with `ethereum-types 0.4.1` | `STFSpec.State.destroyStorage {m : Type → Type} [Monad m] (a : Address) : StateM m Unit`, exported by State from `STFSpec/State/DestroyStorage.lean` | Every raw transaction is accepted. The action visits only the target's pending slot map and adds its keys, including explicit zero writes, to the reads. It erases the target patch and slot index, applies `WriteOrder.erase` to the address index, and inserts the clear. It returns success through one underlying `pure` and calls no provider. | **Discharged for the standalone action.** Private action, branch, membership, frame and local address-order laws in §7.5. Complete guards and authenticated typed source comparisons in §4. |

The source comparison matches ordered dictionaries and read membership. Lean
also admits independent raw order indexes. The action uses the actual patch to
select keys and the existing raw erasure policy to update metadata.

### Implemented standalone account destruction

| Source at the pin | Lean declaration and domain | Value, effects and failures | Laws and validation |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/state_tracker.py:484–501` | `STFSpec.State.destroyAccount {m : Type → Type} [Monad m] (a : Address) : StateM m Unit`, exported by State from `STFSpec/State/DestroyAccount.lean` | On every raw transaction, sequence `destroyStorage a` and `setAccount a none`. The first action clears storage and records pending slot keys as reads. The second records the account tombstone in first-write order. Neither action consults the provider. | Private literal run, complete Id, read membership, order, retained-field and snapshot clauses in §7.5. Facade guards and pinned comparisons in §4. |

### Implemented standalone account modification

| Source at the pin | Lean declaration and domain | Value, effects and ordered failures | Laws and validation |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/state_tracker.py:601–613` | `STFSpec.State.modifyState {m : Type → Type} [Monad m] (a : Address) (f : Account → Except StateError Account) : StateM m Unit`, exported by State from `STFSpec/State/ModifyState.lean` | Read through `getAccount`, then call the supplied update. Either failure returns the complete nominal error through StateM. Success writes the account, runs the actual `accountExistsAndIsEmpty` read and conditionally runs R17. | Private literal Monad action, exact Id branches, second-read and snapshot equations in §7.5. Facade controls and pinned comparisons in §4. |

### Implemented balance-preserving account clear

| Source at the pin | Lean declaration and domain | Value, effects and ordered failures | Laws and validation |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/state_tracker.py:504–525` | `STFSpec.State.clearAccountPreservingBalance {m : Type → Type} [Monad m] (a : Address) : StateM m Unit`, exported by State from `STFSpec/State/ClearAccountPreservingBalance.lean` | Run R16 before the R18 lookup. Set the nonce to zero and the code hash to the input block's supplied empty-code hash. Retain the exact balance and code table. Zero balance reaches R18's conditional R17 destruction. StateM propagates the complete reached error. | Private literal bind, exact Id continuation, emptiness and R24 restoration in §7.5. Facade controls and pinned comparisons in §4. |

### Implemented current account emptiness and liveness

`State/AccountEmptiness.lean` exports both predicates through State. Each
uses the successful lookup's retained block constants (F20).

| Source at the pin | Lean declaration and domain | Value, effects and failures | Validation |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/state_tracker.py:383–410`, calling `:174–197` | `accountExistsAndIsEmpty {m : Type → Type} [Monad m] (a : Address) : StateM m Bool` | Run getAccountOptional once. On presence, return whether the complete account equals emptyAccount for the retained block constants. On absence, return false. Keep the exact returned transaction on success and the exact StateError on failure. | Private action, framing and model controls in §4/§7.1. |
| `src/ethereum/forks/amsterdam/state_tracker.py:413–431`, calling `:174–197` | `isAccountAlive {m : Type → Type} [Monad m] (a : Address) : StateM m Bool` | Run getAccountOptional once. On presence, return whether the complete account differs from emptyAccount for the retained block constants. On absence, return false. Keep the exact returned transaction on success and the exact StateError on failure. | Private action, framing and model controls in §4/§7.1. |

### Implemented raw transaction state and state monad

`State/TxState.lean`, exported by State, supplies exactly the three §5 fields
and the existing `StateM` transformer alias. At the current pin `59c1473d`,
`src/ethereum/forks/amsterdam/state_tracker.py:89` supplies the parent block;
`:90–104` supplies the transaction fields partitioned by D22/D23, with B1 indexes
in TxRevertible and F20 constants in BlockState. No Python TxObs, TxRevertible or
StateM counterpart is asserted. BlockState and TxObs carry hash-only codeReads,
matching the source fields (:70,98). This is nominal raw assembly; it supplies
no current-EELS full-state refinement.

| Source/support at the pin | Lean declaration and domain | Value/effects and failures | Validation and limits |
|---|---|---|---|
| `state_tracker.py:78–104`; D22/D23/B1/F20 partition above | `TxState (m : Type → Type)` with exactly `block : BlockState m`, `rev : TxRevertible`, `obs : TxObs`, in order | Every whole supplied field retained for arbitrary m, without class, WF or coherence premises. Pure construction/projection, no initialization, normalization, provider call, hashing or failure | Private facade `TxStateCallerProofs.lean`: exact constructor/projection types and arity, complete construction/reconstruction and three independent field replacements. No authored public law or instance. |
| Lean transformer wiring, §5/R29; no EELS operation | `StateM (m : Type → Type) := StateT (TxState m) (ExceptT StateError m)` | Raw alias requires no class. Running has exactly `TxState m → m (Except StateError (α × TxState m))`; an error returns no transaction state. Underlying m effects have no rollback claim | Private clients check the complete alias/run type and arbitrary base action retention, including a contravariant constructor without a Monad. Id sequencing checks pure/put/get and complete successful value/state or exact supplied StateError, including a nested WitnessError after put. |

These ordinary private clients establish nominal composition and transformer
wiring. The separate `TxState.new` supplies fresh transaction defaults (§3 below).
The copy/restore/incorporation context at `state_tracker.py:744–858` binds the
partition. Caller initialization, observation lifetimes, tracker errors, provider
coherence and the remaining §10 integration gates stay open.

### Implemented raw revertible transaction carrier

`State/TxRevertible.lean`, exported by `State.lean`, supplies exactly the eight
raw fields in §5 order. This is the D22/D23/B1 adaptation of the revertible part
of `src/ethereum/forks/amsterdam/state_tracker.py:78–104`; the copied/restored
families are visible at `:744–798`. It implements no source tracker operation.

| Source/support | Lean declaration and type | Domain, effect/failure and status | Clients and controls |
|---|---|---|---|
| `state_tracker.py:78–104,744–798`; D22/D23/B1 split and explicit indexes | `STFSpec.State.TxRevertible : Type`; `TxRevertible.mk` takes exactly the eight complete §5 fields, in order | **Discharged raw carrier:** every finite supplied map/set and raw WriteOrder, including tombstones, zero writes, empty inner maps, arbitrary bytecode, missing/extra slot indexes and disagreeing forward/reverse metadata. Construction retains all values without validation, normalization, lookup, hashing, effects or failure. No domain/proof/provider/monad field. | Private `Conformance/State/TxRevertibleCallerProofs.lean` imports the State facade: exact full constructor type, whole eight-field projection/reconstruction and each independent update retaining the other seven fields; complete kernel controls described in §4. |

Only ordinary generated structure infrastructure is public; no authored public
law, default, instance, factory or operation is added by the carrier. The separate
mathematical transaction view below owns a Lean-private `asDiff`. The separate
R24 operations use the whole carrier. Persistence cost, tracker/source refinement
and S1/S2/W1 remain open. Observation hash support (Q84, EthBase §3), provider/cache
lifetime (F6), clear replay order (F7), F11 and the remaining §10 obligations stay
separate.

### Implemented raw transaction observation carrier

`State/TxObs.lean` supplies exactly the four raw fields in §5, exported by State.
There is no Python TxObs class: D22/D23 partition the original TransactionState.

| Source at the pin | Lean declaration and domain | Value/effects and failures | Validation and limits |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/state_tracker.py:90,94,98,100` | `TxObs` with `accountReads : Std.HashSet Address`, `storageReads : Std.HashSet (Address × Bytes32)`, `codeReads : Std.HashSet Hash32`, `createdAccounts : Std.HashSet Address`, in that order | Every supplied raw set is retained exactly; canonical Base/Q84/Q51 and existing storage-pair dictionaries. Pure four-argument construction, no normalization, WF, operation, hash query or failure | **Supplied raw carrier:** private State-facade `TxObsCallerProofs.lean` checks whole construction/reconstruction, all four complete updates and six pairwise commutations on arbitrary raw sets. `TxObsGuards.lean` compares all four complete byte-content fields, reconstructed/equal/unequal hashes, duplicate hash events from distinct supplied addresses, both end bits in every hash byte, complements, unions, missing members and retained siblings. No authored public law or instance. |

Original source copy/restore/incorporation context is `state_tracker.py:744–858`:
observations and created accounts are shared across rollback, then read sets are
incorporated and transaction fields reset. Reading that context binds this raw
partition; it does not execute or refine those functions. Nominal presence proves
no linear ownership, monotonicity, reachability, lifecycle or whole-State result.

### Implemented account creation marker (R22)

`State/MarkAccountCreated.lean` supplies the standalone action through the
State facade. It uses the existing canonical Base address dictionaries.

| Source at the pin | Lean declaration and domain | Value, effects and failures | Validation |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/state_tracker.py:552–571` | `markAccountCreated {m : Type → Type} [Monad m] (a : Address) : StateM m Unit` for every raw `TxState m` | A single base `pure` returns typed success with `Unit` and the state after inserting the complete address into `obs.createdAccounts`. The complete block, revertible data and other observations are retained. There are no provider calls or typed failures. | Private ordinary run, retention, membership and duplicate-insertion proofs (§7). The facade guards and bounded paired executions are in §4. |

### Implemented raw block-state carrier

`State/BlockState.lean` supplies exactly the thirteen fields in §5 order, exported
by State. EELS `src/ethereum/forks/amsterdam/state_tracker.py:44–73` has nine
fields: provider (:61), account reads/writes (:62–65), storage reads/writes
(:66–69), code reads/writes (:70–71), offset (:72) and clears (:73).
Lean deliberately adds F20 `consts` and three B1 `WriteOrder` indexes, arranging
the fields as the guided overlay partition. It adds no transient/created fields.

| Source/support at the pin | Lean declaration and domain | Value/effects and failures | Validation and limits |
|---|---|---|---|
| `state_tracker.py:44–73`; F20 and B1 adaptation above | `BlockState (m : Type → Type)`, exactly the thirteen §5 fields, including `codeReads : Std.HashSet Hash32`; no class premise | Every complete supplied PreState function record, arbitrary constants, maps, sets, order metadata and optional Nat offset is retained. Pure thirteen-argument construction/projection; no operation, normalization, WF, hash query or failure | **Supplied raw carrier:** private `BlockStateCallerProofs.lean` checks exact constructor/projection types, whole construction/eta/component reconstruction, all thirteen complete updates and 78 disjoint commutations for arbitrary m. A contravariant type-constructor client needs no Monad. `BlockStateGuards.lean` checks complete independent framed observations, hash-only deduplication and retained parents/siblings. No authored public law, default or instance. |

The copy/restore/incorporation context at `state_tracker.py:744–858` binds the
partition but supplies no implementation of those functions. The finite controls
execute supplied synthetic callbacks only, retaining complete observed arguments,
success/error tags and payloads. They execute no original Protocol body or tracker
function. Constants acquisition/coherence is a caller obligation; storing the
record performs no protocol hash. Nominal construction proves no block/transaction
sharing, linear ownership, history, monotonicity, provider progress or source-function
equivalence. D22/D23, F7, D5, S1/S2/W1 and C1–C4 remain open at integration.

### Implemented block-state initialization

`State/BlockInitialization.lean`, exported by State, supplies exactly the following
operation and its explicit F20 public law. EELS `state_tracker.py:44–73` uses empty
dict/set factories and None; the production `fork.py:301` supplies the pre-state.
These defaults are source-checked by static reading, without original runtime execution.
F20 constants and the three B1 indexes are deliberate guidance adaptations.

| Source/support at the pin | Lean declaration and domain | Value/effects and ordered failures | Law and deterministic validation |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/state_tracker.py:44–73`, used at `fork.py:301`; F20/B1 | `BlockState.new {m : Type → Type} (ps : PreState m) (consts : HashConsts) : BlockState m`, with no class premise | Whole arbitrary ps and consts retained; every write/clear/read collection empty, both global order indexes WriteOrder.empty, per-address slot indexes absent, oldestAncestorOffset none. Pure total construction, no provider call, acquisition, coherence check, normalization or failure | **Supplied:** ordinary `BlockState.new_consts`; private owner whole-result reduction proves every default and whole arbitrary provider retention. `BlockInitializationCallerProofs.lean` checks exact class-free signature and consumes only that public law; `BlockInitializationGuards.lean` supplies complete independent interpreted `#guard` controls (§4). |

Only `new_consts` is an authored public law for this operation. Default-field and
whole-provider facts stay private to the implementation owner; external component
proofs do not unfold new or access owner helpers. Additional stable consumer laws
remain open until a named consumer needs a separately reviewed contract. This slice
establishes no acquisition/coherence, provider progress, reachable WF/history,
transaction sharing/ownership, lifecycle, resource or whole-State result.

### Implemented logical block read sets

`State/ReadSets.lean`, exported by State, supplies exactly two logical predicate
views and their two ordinary membership iff laws. Informal `Set` here means a
mathematical predicate; no new set provider, class, instance or dependency is used.

| Source/support at the pin | Lean declaration and domain | Value/effects and ordered failures | Law and deterministic validation |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/state_tracker.py:62,832`; BAL consumption `block_access_lists.py:843–845` | `BlockState.accountReadSet {m : Type → Type} (b : BlockState m) : Address → Prop`, class-free | Exactly membership in b.accountReads on every raw block; no effects or failure | **Supplied:** `BlockState.accountReadSet_iff`; private facade clients use both directions, with whole-field independence; `ReadSetsGuards.lean` compares complete independent membership vectors (§4). |
| `src/ethereum/forks/amsterdam/state_tracker.py:66,831`; BAL consumption `block_access_lists.py:839–841` | `BlockState.storageReadSet {m : Type → Type} (b : BlockState m) : (Address × Bytes32) → Prop`, class-free | Exactly whole-pair membership in b.storageReads, including both complete keys; no effects or failure | **Supplied:** `BlockState.storageReadSet_iff`; private arbitrary-key and non-Monad clients plus complete interpreted `#guard` controls (§4). |

These are static field projections, not incorporation or BAL construction. Original
source correspondence assumes complete typed key interpretation. Static source reading
executes no original tracker function. Enumeration, sorted output, codeReadSet, raw
HashSet extensionality, ownership/monotonicity and lifecycle remain outside this seam.

### Implemented raw block-diff extraction (Q85)

`State/BlockExtraction.lean`, exported by State, supplies exactly one operation
and seven ordinary whole-field laws (§7). Every raw `BlockState m` is admitted,
including malformed independent order indexes; `m : Type → Type` needs no class.

| Source/support at the pin | Lean declaration and domain | Value/effects and ordered failures | Laws and deterministic validation |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/state_tracker.py:861–881`; `src/ethereum/state.py:60–83`; B1/Q85 | `extractBlockDiff {m : Type → Type} (b : BlockState m) : BlockDiff` | Copies the complete four effect fields. Both global orders use the existing raw `WriteOrder.toList`; domain-preserving map applies it to every supplied slot index. No provider/constants/read-set/offset use, hash, normalization, failure or handler. | **Discharged for this slice:** exactly the seven `extractBlockDiff_` laws in §7. Private public-facade `BlockExtractionCallerProofs.lean` clients and complete independent numerical/list `BlockExtractionGuards.lean` controls (§4). |

Static source binding verifies the four assignments; EELS has no malformed
separate-index runtime to compare. This is no original-runtime equivalence or
mutable alias-identity claim. First-write history uses `state_tracker.py:836–846`
and remains a separate integration obligation. All raw tombstones, zeros, empty
patches, arbitrary code and clear membership survive. The three B1 indexes lose
their raw next/forward fields through the existing observer; full index retention
is not claimed. Q58's structural premises and full-WF/history/F7 obligations remain
separate. No application equality supplies witness failure/observation agreement.

### Implemented mathematical block view

`State/BlockView.lean`, exported by State, composes the two existing public
operations exactly; it adds no new source runtime function or domain policy.

| Source/model support at the pin | Lean declaration and domain | Value/effects and ordered failures | Law and deterministic validation |
|---|---|---|---|
| Mathematical composition of `src/ethereum/forks/amsterdam/state_tracker.py:861–881`, `src/ethereum/state.py:60–83`, and `src/ethereum/state_mpt.py:133–161`; no standalone Python view function | `BlockState.view {m : Type → Type} (σ₀ : MathState) (b : BlockState m) : MathState` | Every finite raw state and block carrier, without class, WF or history premise. Exactly `σ₀.apply (extractBlockDiff b)`; no provider action, constants acquisition, hashing, normalization or failure. | **Discharged for this slice:** ordinary `BlockState.apply_extractBlockDiff` (§7.2). Private facade clients derive the complete application result, all three raw-field and observer equations, arbitrary metadata/unused-field independence and the contravariant class-free signature. `BlockViewGuards.lean` supplies independent complete numerical/list controls (§4). |

The view inherits raw mathematical application's deletion, clear-before-write,
zero-erasure, touched-empty pruning and code replacement behavior. Replay metadata
is forgotten by apply; malformed/missing/present-empty/extra Q85 metadata remains an
admitted input. Mathematical equality supplies no witness failure/observation or
mutable-alias agreement. S1/S2/W1, full WF/history, F7, actual tracker/lifecycle and
resource/readiness gates remain open. Static source reading grounds composition;
interpreted `#guard` controls compare mathematical models (no native runner or
external comparison is committed for this slice), without original-source numerical
or EEST execution.

### Implemented mathematical transaction view

`State/TransactionView.lean`, exported by State, supplies the existing §5/§7.1
composition on arbitrary raw inputs. Its `TxRevertible.asDiff` is Lean-private in
that owning module; it is not a new public raw-diff interface.

| Source/model support at the pin | Lean declaration and domain | Value/effects and failures | Law and validation |
|---|---|---|---|
| Mathematical composition of transaction effects `src/ethereum/forks/amsterdam/state_tracker.py:78–104`, block extraction `:861–881`, and application `src/ethereum/state_mpt.py:133–161`; no standalone Python view function | `TxState.view {m : Type → Type} (σ₀ : MathState) (t : TxState m) : MathState` | Every finite raw state and transaction carrier, without class, WF, provider, constants-coherence or history premises. Exactly `(t.block.view σ₀).apply t.rev.asDiff`; no provider action, hashing, normalization or failure | **Discharged mathematical slice:** exactly one public ordinary `TxState.view_account?_eq` law (§7.2), consumed by `getAccountOptional_model`. Private construction, complete application, raw-field and metadata support proofs stay in the owner. Private facade clients use only the public account law, including an arbitrary non-Monad constructor; complete native/interpreted 118-case controls and strict normal/-O readers are in §4. |

The private conversion copies whole accountWrites, storageWrites, codeWrites and
storageClears, retaining tombstones, zero writes and empty patches. Account and
storage-address metadata use existing `WriteOrder.toList` directly. Slot metadata
maps every existing address to its index's `toList`, preserving the entire domain:
missing remains missing, present-empty remains present-empty and extra entries
remain present. There is no filtering, repair, synthesized metadata or traversal
from zero to `next`. Only transient writes are omitted. Whole private construction
and optional slot-map proofs establish this exact transport; mathematical apply
ignores metadata. This internal completion does not extend Q85's public contract.

Both layers use the existing raw apply semantics, including account deletion
without storage clear, clear-before-write, local zero deletion, touched-empty
pruning, untouched malformed storage and raw code overwrites. View construction
traverses supplied reverse-map and slot-index entries, and application retains its
existing costs. No O(1), C1–C4, full WF/reachable history, witness/replay agreement,
backend, guest or readiness result follows.

### Implemented internal order support

`STFSpec/State/WriteOrder.lean` supplies this bounded internal component.
The source map records tracker operation status. The standalone account write,
storage clear, R24 snapshot and restore, and raw extraction have separate rows.
The component laws have no error or hashing channel. Python dictionary
correspondence requires the pinned host and dependency interpretation.
Whole-tracker refinement remains open.

| Source / model item | Lean declaration and public type | Domain, value/effects and failures | Laws and deterministic validation |
|---|---|---|---|
| Mathematical finite maps (no EELS `MathState` class) | `MathState` with `accounts : ExtTreeMap Address Account`, `storage : ExtTreeMap Address (ExtTreeMap Bytes32 U256)`, `code : ExtTreeMap Hash32 ByteArray` | Every raw finite triple; exact fields, no normalization, effects or failure | **Discharged:** constructor, reconstruction and raw extensionality laws (§7); raw extensionality requires whole optional inner-map equality and raw code lookup equality at every hash, including the reserved hash. |
| `state.py:94–100`, `state_mpt.py:59–66` | `MathState.account? : MathState → Address → Option Account` | Raw lookup; `none` differs from `some (emptyAccount consts)`; no effects/failure | `account?_eq_lookup`; empty/present/huge-nonce/max-balance and all-hash-byte cases in `Conformance/State/MathStateGuards.lean` and `MathStateNativeTests`. |
| `state.py:102–108`, `state_mpt.py:67–80`, `merkle_patricia_trie.py:341–347` | `MathState.storageAt : MathState → Address → Bytes32 → U256` | Missing outer or inner lookup returns zero; present raw zero is retained; no account guard, effects or failure | `storageAt_eq_lookup`, `storageAt_of_storage_none`, `storageAt_of_slot_none`, `storageAt_of_slot_some`; absent/empty/zero/orphan/nonzero/max and complete key-byte cases. |
| `state.py:110–116`, `state_mpt.py:49–57`, `forks/amsterdam/witness_state.py:129–137` | `MathState.code? : MathState → HashConsts → Hash32 → Option ByteArray` | Supplied `emptyCodeHash` returns `some ByteArray.empty` before raw lookup, even with hidden bytes; other hashes retain raw `none`/empty/nonempty distinction. No hash acquisition or effects/failure. Provider `KeyError` on missing nonreserved code remains a separate B2 error, never a successful absent provider answer. Concrete source comparison requires caller-coherent F20 constants. | `code?_empty`, `code?_of_ne`, `code?_congr_consts`; arbitrary/nonliteral constants, unrelated-field variation and hidden reserved entry guards. |
| Structural model invariant, motivated by `state_mpt.py:187–206` and `merkle_patricia_trie.py:325–338` cleanup | `MathState.WF : MathState → Prop` | Exactly nonzero stored values, nonempty stored inner maps, and storage-domain inclusion in accounts; no code clause, account-value restriction or runtime wrapper. | `wf_iff`, `wf_empty`, `wf_storage_value_ne_zero`, `wf_storage_nonempty`, `wf_storage_account_present`, `storageAt_zero_of_account_none`, `storageAt_zero_iff`, `storage_present_iff_exists_nonzero`. Three independent omission proofs exercise each clause. |

The public laws in §7 have arbitrary public-map/key/value/constants clients in
`Conformance/State/MathStateCallerProofs.lean`. The three-clause invariant supplies no
code authenticity or completeness. `hidden_code_counterexample` proves that even two
WF states may be raw-unequal while every observer at fixed constants agrees.
`math-state-native-tests` compares complete raw maps and optional/value answers against
a separate finite association-list oracle, including actual reconstructed keys,
differing insertion orders and retained parent/sibling maps. This is finite functional
evidence, with no tracker, backend/root, EEST, resource or C1–C4 claim.

### Implemented raw mathematical diff application

`State/Apply.lean` supplies `MathState.apply : MathState → BlockDiff → MathState`
on every finite raw input, without WF or history premises. Persistent clear/change
folds do not scan the complete pre-state. The three metadata fields are ignored.

| Source / model item | Lean declaration | Domain, value/effects and failures | Laws and deterministic validation |
|---|---|---|---|
| `state_mpt.py:133–161` clear, account, storage and code phases; `merkle_patricia_trie.py:325–347` defaults | `MathState.apply` | Clears precede writes; raw account deletion preserves storage; each changed address starts from its post-clear map or empty. Written zero erases, nonzero inserts; only a touched resulting empty inner map is removed. All raw code, including reserved and empty entries, is overwritten. Total, pure; no account guard, hashing or failure. | Whole optional account/storage/code lookup laws, three observer equations, identity/effect congruence, field/address/slot frames and cleanup laws below. `ApplyCallerProofs` consumes the §7 laws on arbitrary inputs; `ApplyGuards` and `ApplyNativeTests` compare complete output with an independent finite association-list model. |

Concrete reference correspondence uses typed finite nonaliasing source dictionaries,
account default `None`, storage default `U256(0)`, pinned fixed-width/Uint/U256
interpretation and caller-coherent F20 constants. Missing nonreserved source code
raises `KeyError`, distinct from the mathematical `none` answer. The bounded probe
executes only unchanged selected application/trie/getter bodies; no hash/root,
tracker, witness, host-resource or arbitrary-object correspondence follows.

### Implemented raw provider carrier support

The following raw carrier support implements no provider operation or backend.
`src/ethereum/state.py:86–133` supplies the Protocol field shape; its ellipsis bodies have
no executable operation to differentially compare. Witness-error constructors are the
Lean-only nominal shapes of §5. Source attribution does not assert lookup/root execution.

| Source/support | Lean declarations and domain | Preserved value/effects | Ordinary laws | Evidence |
|---|---|---|---|---|
| `state.py:86–133` Protocol shape (D9/D5/B2) | `PreState (m : Type → Type)` with the exact four §5 fields, arbitrary supplied functions and raw BlockDiff; no Monad premise | Each complete supplied action/function is retained unchanged, including every result/error tag and input. No lookup, default, bypass, hashing or root semantics | Exactly `PreState.getAccount?_mk`, `getStorage_mk`, `getCode_mk`, `stateRoot_mk`, `eta`, `ext`, `ext_apply` | Generic public-only `PreStateCallerProofs`; complete supplied callbacks in `PreStateGuards`; `scripts/PreStateNativeTests.lean` |
| Lean nominal support, §5 | `WitnessItem.node/code/leaf`, `WitnessError.missing/malformed/unresolved` | Every supplied Hash32 and nested item tag is retained; no adapter, decoder or outcome projection | Ordinary generated constructor/recursor/injectivity support, without an equality/BEq/order/hash instance | Every constructor and complete 32-byte payload, with an independent tagged byte-list expectation |
| Lean nominal support, §5/R29 (no EELS StateError class or operation) | `StateError.witness : WitnessError → StateError`, `balanceUnderflow`, `balanceOverflow`, `storageOnMissingAccount`; every supplied WitnessError and the three nullary values | Pure construction/elimination retains the complete supplied witness value; nullary tags carry no payload. No actions, effects, failures or outcome adapter | Ordinary generated constructor/recursor/injectivity support; private arbitrary-payload retention and distinct-tag structural examples; no custom public law or instance | `Conformance/State/StateErrorGuards.lean` and `scripts/StateErrorNativeTests.lean`: all outer/nested tags and complete 32-byte payloads, every byte position, including first and last |

`State/PreState.lean` imports the EthState error owner and BlockDiff only.
`State/WitnessError.lean` imports Base.FixedBytes only. Arbitrary-m action equality is ordinary
Lean equality, without an effect-equivalence interpretation. The coarse errors are not frozen;
their §10 refinement obligations remain open. `State/StateError.lean` imports only
`State/WitnessError.lean` and is exported by the State aggregate. R15/R19/R29 cite future
operation uses, without implementing them. `ModelsLookups` supplies Q57 lookup
agreement; actual providers and full-model/contextual tracker proofs remain open.

### Implemented bounded structural preservation (Q58)

`State/Structural.lean` supplies one logical predicate and the ordinary
laws in §7.4, exported through `State.lean`. The laws quantify every finite raw state
and diff; only the preservation law assumes initial structural WF. There is no
runtime enumeration, decision procedure, effect, failure or metadata normalization.

| Source / model item | Lean declaration and public type | Domain, effect and status | Laws and deterministic validation |
|---|---|---|---|
| Sufficient structural premises motivated by `state_mpt.py:133–161,187–206` and `merkle_patricia_trie.py:325–347`; not a separate EELS operation | `BlockDiff.StructuralPremises : MathState → BlockDiff → Prop` | **Discharged:** exactly deletion-tombstone-to-clear and raw storage-change-address-to-post-account presence, including empty patches and zero writes. No initial WF, code, account-value or metadata restriction. Pure logical contract; no failure/handler. | `structuralPremises_iff`, `structuralPremises_storage_clear`, `structuralPremises_account_present`; private arbitrary clients in `StructuralCallerProofs.lean`, omission/empty/zero counterexamples in `StructuralGuards.lean`. |
| Structural consequence of clear-before-write, zero deletion and touched-empty pruning at those sources | `MathState.wf_apply_of_structuralPremises` | **Discharged:** initial `MathState.WF σ` and `BlockDiff.StructuralPremises σ d` imply all three output WF clauses. Callers establish both premises; this is not reachable extraction. | Public Apply slot/account/inner-map laws and MathState WF laws; private proofs of independent premise omissions, malformed initial zero/empty/orphan states, deletion with clear and clear/reintroduction. |
| Effect-only predicate congruence; replay metadata is B1 guidance | `BlockDiff.structuralPremises_congr_effects` | **Discharged:** equality of accountChanges, storageChanges, codeChanges and storageClears implies predicate iff, with no metadata equality premise. | Public `apply_congr_effects`; private arbitrary clients and complete finite observations for missing/present-empty/extra/duplicate/foreign metadata. No full optional-map policy is selected. |

### Implemented supplied-record lookup agreement

`State/ModelsLookups.lean` supplies exactly the R8/Q57 proposition, exported by State.
It consumes the raw PreState carrier and MathState's public observers, with no new
public helper, law, instance or decision procedure. Its three success implications
are the complete definition; roots and errors impose no condition.

| Source/support | Lean declaration and domain | Value/effects and failures | Validation and limits |
|---|---|---|---|
| Lean model relation for `state.py:94–116` Protocol shape; `state_mpt.py:49–80` and `forks/amsterdam/witness_state.py:129–137` observers (Q57) | `ModelsLookups : HashConsts → PreState Id → MathState → Prop` | Every supplied record/provider and finite raw state; exact optional account, storage word and `some code` agreement on success. Supplied reserved hash bypasses raw code. Errors unconstrained; no root, WF, hashing, authenticity, availability or coherence premise, operation or failure handler. | **Supplied definition:** private ordinary symbolic `ModelsLookupsCallerProofs` and positive/negative `ModelsLookupsGuards`, wired through EthConformance. No executable EELS Prop body exists to compare; provider/backend modeling, contextual tracker laws and full-model projection remain open. |

The predicate's arbitrary-record domain does not assert correspondence to concrete
EELS hashes without F20 coherence. Private supplied callbacks establish whole-predicate
positive cases, error-only vacuity and wrong-success rejection; they provide no
production provider, progress, root/authentication, resource or release result.

## 4. Tests

- **Balance-preserving account clear controls.** `ClearAccountPreservingBalanceControls.lean`
  checks funded, empty and absent accounts, explicit zero and nonzero slots,
  the input block's raw empty-code hash, and exact R24 restoration. The pinned
  source observes the first clear and read conversion before the account
  lookup, including when the provider throws. The interpreted and compiled
  State facade compares complete successes and the reached nominal failure.

- **Standalone R27 controls:** `AncestorAccessChecks.lean` checks five
  histories and 20 updates, including absence, explicit zero, equal/decreasing
  offsets and offsets above 256. It checks the cursor and transaction
  sentinels through the public action with zero provider calls. The same
  histories are paired with the pinned tracker in isolated normal and
  optimized Python. BLOCKHASH admission and composed rollback remain open.

- **Original storage read:** `Conformance/State/StorageOriginalGuards.lean` runs
  eleven cases with distinct full-width addresses and slots, including pairs that
  differ only at the high bit. Cases cover created-account priority, block writes
  including explicit zero, block clears, absent and empty maps, and wrong addresses
  and slots. The provider records exact arguments and call counts. Success checks
  all retained data fields and samples each retained provider action. Failure
  checks the full typed witness error and absence of a returned transaction.
  Focused native and interpreted runs compare values and provider calls against
  the pinned EELS function in isolated normal and optimized Python. The Python
  failure case checks propagation of the thrown object and unchanged source
  fields. The Lean case separately checks the typed error representation.

- **EEST fixture areas** (`STFSpec/informal/eest-fixture-index.txt`): `cancun/eip1153_tstore`, `ported_static/stEIP1153_transientStorage` (transient storage, reset per transaction); `cancun/eip6780_selfdestruct`, `amsterdam/eip8246_selfdestruct_no_burn` (created accounts, clears, `clear_account_preserving_balance`); `ported_static/stSStoreTest`, `istanbul/eip2200_net_gas_metering`, `ported_static/stRefundTest` (current versus original values); `ported_static/stRevertTest`, `stZeroCallsRevert`, `stCallCreateCallCodeTest` (snapshot/revert); `spurious_dragon/eip161_state_trie_clearing`, `ported_static/stEIP158Specific` (empty-account destruction in `modify_state`); `ported_static/stCreate2`, `stCreateTest`, `stInitCodeTest` (creation over storage-only accounts); `amsterdam/eip7928_block_level_access_lists` (211 files; persistent observations, write→read conversion); `amsterdam/eip8025_optional_proofs` (witness reads in reverted calls: `test_witness_state_reads.py`, `test_witness_headers.py` for `track_ancestor_access` in reverted calls); `prague/eip2935_historical_block_hashes_from_state`; `shanghai/eip4895_withdrawals` (`create_ether`); `prague/eip7702_set_code_tx` (`set_code`, `get_pre_state_account`); `amsterdam/eip8037_state_creation_gas_cost_increase`, `eip8038_state_access_gas_cost_increase`.
- **EELS unit tests:** none target `state_tracker.py` at the pin. `tests/json_loader/test_optimized_state.py` (`test_storage_key`, `test_resurrection`) concerns an older optimized state and is not normative here.
- **`core` `#guard` cases** (typical, edge, adversarial), over a `PreState` built from a small `MathState`:
  - precedence ladder: each of the five layers answering in turn; write after clear in the same transaction; block clear with a transaction write; transaction clear over a block write;
  - original value: created account returns `0` although the pre-state has a value; block clear returns `0`; transaction writes ignored; no storage read recorded;
  - `destroyStorage` after two writes: both keys appear in `storageReads`; after revert, the writes return but the reads stay;
  - `modifyState` on a non-existent account with a zero change: account change `none` and a clear;
  - `moveEther` insufficient balance and recipient overflow at `2^256 − 1` both fail;
  - `setCode` with empty code: no code write, `codeHash = emptyCodeHash`;
  - snapshot/revert nested three deep, with observations monotone;
  - `incorporateTxIntoBlock` of a transaction that cleared an address with block writes: the block writes vanish, post-clear writes survive; first-write order of `accountOrder` preserved when a later transaction rewrites an early address;
  - an always-error provider: every fall-through read fails and no read defaults (R30).
- **Implemented R24 controls:** `TransactionSnapshotChecks.lean` checks both
  signatures and the complete action through the State facade. Its three nested
  snapshots compare every revertible field after each LIFO restore, including
  tombstones, a zero write, an empty inner map, raw order metadata and transient
  values. An erroring provider records any invocation. All four observation sets
  and the ancestor cursor retain their latest values. The focused pinned EELS
  comparison exercises the shared fields and the LIFO sequence. Separate Lean
  guards cover the B1 metadata and reuse of a saved snapshot.
- **Implemented current storage controls:** `CurrentStorageGuards.lean` uses the
  State facade with a tracing provider. It checks both clears, zero writes,
  absent addresses, empty inner maps, wrong keys and repeated fall-through.
  It also checks the complete wrapped error and compares every non-read field
  in successful states, probing the retained provider callbacks at fixed
  inputs. Additional guards compare an `Id` provider built from a small
  `MathState` and the transaction-view observer in all five branches.
  Bounded native and interpreted comparisons cover 400 histories of two
  reads each against the authenticated pinned source, normally and with
  `-O`. The comparisons check both created-account membership choices,
  full-width common-suffix addresses and keys, complete shared state fields,
  exact provider arguments and changing answers on repeated successful calls.
  The Python provider checks that the inserted read is already present,
  including on failure. Lean returns the complete typed failure without a
  transaction. The finite comparison uses a supplied synthetic provider in
  both implementations with a corresponding error payload.
- **Account existence controls** in `STFSpec/Conformance/State/AccountExistsGuards.lean`
  check ten cases, each run twice. The cases cover transaction and block entries,
  tombstones, present empty accounts, absence at the provider and exact typed
  provider failure. The guards check provider call addresses and counts, success
  read membership and retained fixture fields. The same ten cases execute
  pinned EELS in normal and optimized Python. The source checks also observe
  the optional call, read order and full transaction and block snapshots.
- **Implemented standalone storage clear controls.** `STFSpec/Conformance/State/DestroyStorageGuards.lean`
  checks the action through the State facade. Sixteen cases cross absent, empty,
  zero-only and nonlexical three-slot patches with an existing clear and an
  existing read. Each case clears twice, checking the whole block and transaction,
  complete raw indexes, read membership and the single underlying `pure` trace.
  The providers return distinct errors if called. Two additional Lean guards
  cover a mismatched reverse address entry with a ghost slot and an absent patch
  with orphan metadata. Both authenticated isolated Python modes (normal and
  `-O`) execute 32 standalone calls. Their complete finite state projections,
  including dictionary order, agree with the native and interpreted Lean runs.
  The source comparison uses typed, nonaliasing patches and canonical numeric
  observations of fixed-width keys and words. The raw Lean index cases have no
  independent source representation.
- **Standalone account destruction controls.** `DestroyAccountControls.lean`
  checks the State facade with absent and present-empty patches, explicit zero
  and nonzero writes, an existing account and an existing tombstone. The
  controls repeat destruction and restore a snapshot. The private ordinary
  clients compare the complete transaction, check the two underlying action
  returns in order and verify the exact reads kept by restoration. Five
  comparable finite states cover these same storage cases and preexisting
  reads in both authenticated pinned Python modes and both interpreted and
  compiled Lean. The private source observer records the two EELS calls and
  the complete transaction before and after destruction.
- **Standalone account modification controls.** `ModifyStateControls.lean`
  uses the State facade to test provider failure, callback failure,
  absent-account defaulting, modification to empty and nonempty updates.
  The complete reversible fields and observation controls cover first-write
  order, distinct supplied empty-code constants, explicit zero slot reads
  and snapshot restoration. The original pinned source observations record
  the defaulted read, callback, account write, second read and conditional
  R17 operations. Both pinned modes supply five complete successful frame
  pairs and one callback failure for the interpreted and compiled facade.
- **Implemented defaulted-account controls:** `PreStateAccountDefaultCallerProofs.lean`
  consumes the five public wrapper laws through the State facade, including complete
  provider/function/constants retention. `pre_state_account_default_inputs.json`
  preserves the 66 optional-account inputs with independent constants/classification
  fields and adds 15 raw-constant mathematical cases. The constants differ from
  supplied present-account hashes in those cases, distinguishing absence defaulting
  from normalization of a present account. `PreStateAccountDefaultNativeTests.lean`
  runs the actual wrapper natively and interpreted, with the complete field, trace,
  error and sequential-composition recipe described below. The separate strict reader
  `pre_state_account_default_differential.py` checks all 81 complete observations
  against independently frozen `pre_state_account_default_expected.json` values.
  Target/source-reader regressions run normally and with -O. The authenticated
  `pre_state_account_default_source.py --eels EELS --check-target TARGET --report REPORT`
  calls the actual pinned wrapper on only the 66 coherent cases, normally and with -O,
  retaining both wrapper/optional source bodies and the authentication/wait evidence
  described below. It directly compiles the shared source-only import helper and its
  reader; each actual probe worker returns its own compiled-source authentication.
  Accepted altered normal/opt1 caches are exercised through this worker entry point. The 15 raw-constant cases make no source-equivalence claim.
  The separate optional-account producer still executes and checks all original 66 cases.
- **Implemented transient storage read controls.** `TransientStorageCallerProofs.lean`
  checks the exact public type and consumes the complete action law.
  `transient_storage_inputs.json` gives ten input cases with twelve reads per run.
  They cover explicit zero and absence, a maximal word, first- and last-byte
  differences in each key component, and repeated hits and misses. Each case
  supplies conflicting persistent storage writes and nonempty observations.
  `scripts/TransientStorageNativeTests.lean` emits each full answer, read call trace,
  and all initial and returned state data, including raw order indexes and constants.
  It samples each retained provider action outside the read trace. The ordinary
  action law gives equality of the complete supplied provider functions.
  `transient_storage_differential.py` checks the native and interpreted streams
  against an independent integer model. `transient_storage_source.py` compares the
  same answers, traces and source fields with the actual pinned tracker in normal
  and optimized Python. Each worker compiles source directly and returns its own
  authentication. A fail-on-access provider and identity checks cover the retained
  source context.
- **Implemented transient storage write controls.** `TransientStorageWriteChecks.lean`
  checks the exact public type and complete private action and framing equations
  through the State facade. Ten interpreted cases compare the full transient map
  and read result after each of two writes. They cover overwrites, missing and
  explicitly zero entries, a maximal word and pairs that differ in a high or low
  byte. The guards track provider calls and observe retained persistent writes,
  observations and disagreeing raw order indexes. The bounded comparison at
  `59c1473d` executes these recipes on the pinned tracker in normal and optimized
  Python and checks both full maps and read results. It also checks the source
  tracker fields and provider identity after each write.
- **Implemented optional-account controls:** `PreStateAccountCallerProofs.lean`
  consumes only public action/framing/membership/model laws. The input-only
  `pre_state_account_inputs.json` has 66 cases distinguishing missing entries,
  tombstones, present-empty/full accounts, conflicting transaction writes, all
  address bytes, complete balances/hashes and nonces above 2^400. The supplied
  lawful StateT trace base records exact provider address/order/count; unexpected
  storage/code/root calls leave distinct sentinels. Actual StateM do-composition
  tests repeated changing provider answers and stops at the first error. Every
  successful output includes all nonfunction block fields, all revertible fields,
  unrelated observation fields and semantic account-read membership. Private
  ordinary clients separately retain complete provider functions by equality.
  `scripts/PreStateAccountNativeTests.lean` runs natively and through Lean's
  interpreter. `pre_state_account_differential.py` admits only the complete stream
  against frozen independent integer/list values in `pre_state_account_expected.json`;
  parser regressions run normally and with -O. The public
  `pre_state_account_source.py --eels EELS --check-target TARGET --report REPORT`
  reproduces pinned source normal/-O probes on actual BlockState/TransactionState
  carriers and instrumented providers. It invokes the clone's `.venv/bin/python`
  directly with -I/-B, adding -O for the second mode. Each worker compiles source
  bytes directly without consulting bytecode caches and rejects sourceless imports;
  each actual probe returns its own authentication and compiled-source hashes.
  Timestamp-valid altered normal/opt1 caches are regression-tested with an
  out-of-catalogue address, alongside sourceless-cache rejection. It checks the exact
  clean
  pinned Git source, actual imported files/interpreter and pinned installed versions
  with every hashed distribution RECORD entry, retaining complete original child
  streams and actual waits. Installed integrity does not certify independently
  downloaded wheel provenance. It compares optional values, reads and calls and
  checks source field retention. Source-reader/authentication regression tests run
  normally and with -O without importing EELS; they supply no source execution credit.
  The provider's sequence returns none then some providerAccount. Twice composes
  reads and stops on error. Typed errors use case modulo seven: missing node/code/leaf,
  malformed node/code/leaf, then unresolved, with providerAccount.codeHash payloads.
  Probe exceptions are instrumentation, not a Python-to-WitnessError adapter.
  Failed Lean runs return no state; the source's mutation before failure is
  recorded separately. Code-set fixture segments are sorted complete hash numerical
  values; the nonempty sets contain providerAccount.codeHash. No complete source-to-Lean
  state projection is supplied. These controls establish no backend/root,
  snapshot/lifetime, EEST guest, S2, F7, B14 or cost/readiness result.
- **Implemented R14 controls:** `scripts/SetAccountNativeTests.lean` runs the same
  six input histories (31 writes) natively and interpreted. Cases include insert
  and overwrite, repeated tombstones, empty and nonempty account values, full-width
  addresses with equal suffixes and a deletion over live storage. The reader checks
  every account field, both order maps and the counter, ordered keys, provider-call
  trace and the complete finite block, storage, code, observation and transient
  projections before and after every write. Two raw disagreeing index histories
  exercise the existing `record` behavior without applying a Python order claim.
  The other four histories (25 writes), including a sparse well-formed index with
  a large counter, compare the complete common projection with authentic pinned
  `set_account` in both direct isolated Python modes. The source worker checks
  unit return, parent/provider identity and absence of provider calls. The driver
  records original child waits, streams, exact source and input identities and
  pinned installed dependency integrity.
- **Implemented current optional account controls:** private
  `AccountOptionalCallerProofs.lean` uses only the six public laws for exact generic
  action signatures, full block/rev/provider/constants retention, semantic membership,
  exact errors and the unchanged initial-model domain. `AccountOptionalNativeTests.lean`
  executes the public operation on all 248 `account_optional_inputs.json` recipes,
  natively and interpreted. Every successful step emits the complete Option account,
  semantic reads and retained flat frame; failure emits the exact typed error with
  null state/frame. `account_optional_expected.json` was independently derived and
  frozen before new target output. The retained-frame recipe/layout reuses the
  accepted defaulted pre-transaction fixture, with current priority/effects and all
  fields independently derived. Coverage includes the transaction/block/provider
  priority matrix, tombstones suppressing failures, present-empty versus absent,
  full/huge fields, existing membership, huge raw order records, every supplied
  error constructor/payload and changing-provider repeated reads without caching.
  `account_optional_source.py` executes the original pinned get_account_optional
  and fallback on real typed carriers for the 233 coherent recipes, normally and
  with -O. It directly compiles the shared source-only import helper and reader;
  each actual probe worker returns its own compiled-source authentication. Accepted
  altered normal/opt1 caches are exercised through this worker entry point.
  The other 15 arbitrary-constant cases are mathematical controls only.
  `account_optional_source_expected.json` independently freezes complete meaningful
  retained source fields, answers, provider calls and read membership; source set-add
  instrumentation also distinguishes one insertion from two. Provider-observed reads
  verify marking before the call. Source failed-read snapshots remain separate from
  Lean's absent returned failed state. Reports authenticate clean pinned source bytes,
  imports, direct interpreter flags/version, pinned dependencies and installed RECORD
  integrity, preserving every original child stream and consumed wait. Exception
  sentinels are fixture instrumentation, with no production WitnessError adapter.
  Strict target/source readers and their normal/-O regression suites enforce complete
  counts, order, schemas, exact number types and all payloads, rejecting duplicate,
  missing, trailing or noninteger data. Whole function equality is provided by the
  ordinary frame law; finite tracing callbacks are controls only. No full-State,
  actual backend, generic source/monad coupling, S1/S2, WF/history, F7, EEST/guest,
  fuel, cost or readiness claim follows.
- **Implemented defaulted current account controls:** private
  `AccountDefaultCallerProofs.lean` consumes all five public laws, preserving whole
  block/rev, all four provider functions, constants and unrelated observations.
  `AccountDefaultGuards.lean` distinguishes raw-constant absence from present zero
  accounts and retains huge nonce/full balance/hash fields. The actual getAccount
  wrapper runs on all 248 `account_default_inputs.json` recipes natively and
  interpreted. Independently derived `account_default_expected.json` freezes every
  answer field, exact typed error, provider callback, semantic read membership and
  complete retained frame before implementation or target/source execution. The flat
  frame serialization follows the accepted current optional harness; its expected
  values are derived directly from input-only recipes. The 15 raw-constant cases
  retain supplied present accounts while defaulting None to zero nonce/balance and
  exactly constsEmptyCodeHash. Changing-provider repetitions execute again.
  `account_default_source.py` executes original get_account on 233 coherent recipes,
  normally and with -O, comparing all meaningful source fields against independently
  frozen `account_default_source_expected.json`. Its stop-after-first-error recipe
  policy observes 354 wrapper calls, 33 provider calls and 438 read additions per
  mode. The probe records the source read set after a provider failure. The Lean
  error carries only the typed failure. Each actual probe worker uses the shared
  source-only import policy and returns authentication with the hashes of the source
  bytes it compiled. The driver checks the pin, imports, interpreter, dependency
  versions and installed RECORD integrity. Its report retains the original child
  streams and consumed waits. Strict target/source readers and normal/-O regressions reject
  incomplete counts/order/framing, duplicate/missing/extra keys, changed payloads,
  optional-shaped answers and noninteger numeric types. These bounded controls
  establish no production error adapter, backend progress, generic D5 coupling,
  S1/S2, lifecycle/history, guest/EEST, host-resource, cost or whole-State readiness.
- **Implemented deployability controls:** private `AccountDeployableGuards.lean`
  checks the facade type, results and exact provider traces over two calls per
  case. The ten concrete cases cover transaction and block tombstones, present
  empty accounts, full balance at zero nonce, a nonce above 256 bits, a code hash
  changed in its high byte, provider absence, a provider hit and a provider
  failure. Successful controls compare account-read membership and retained
  storage writes. The error control checks the precise witness-error variant and
  full hash. Two additional controls use a supplied empty code hash. Directly
  executing pinned `account_deployable` in both isolated Python modes checks
  20 calls per mode for the same ten concrete cases. These source observations
  check the one defaulted read, its provider and read-addition order, the Boolean
  or original exception and retained fields. The paired Lean controls compare
  results and provider calls. On source failure the source records its attempted
  reads, while the Lean error contains only its typed payload.
- **Implemented hash-only code read controls:** `CodeCallerProofs.lean` uses all
  five public laws through the State facade. `CodeReadNativeTests.lean` executes
  `getCode` natively and interpreted on the 85 frozen input-only
  `code_read_inputs.json` recipes. The independent `code_read_differential.py`
  reader checks every returned byte, provider call, typed error and successful
  read set, plus all retained fields, including raw order indexes and constants.
  Finite probes check each of the four retained provider functions. The frame law
  supplies whole function equality. Repeated successful attempts use the returned
  state and repeated failed attempts use the supplied initial state.
  `code_read_source.py` runs the pinned operation on real source carriers with
  a traced dictionary provider for 68 coherent recipes. It compares all shared
  retained values, call arguments, successful bytes and read sets in both Python
  modes. The provider records membership and the insertion count at the call.
  A missing dictionary entry records the exact `KeyError` key and source read
  membership separately from the absent failed Lean state. The correspondence
  is limited to these fixture errors. Each actual source worker records directly
  compiled identities, interpreter flags, pinned dependencies and installed
  RECORD integrity. The driver retains each original stream and consumed wait.
  The other 17 recipes cover alternate supplied constants and typed Lean errors.
  Strict readers and their negative controls run in both Python modes.
- **Implemented account emptiness and liveness controls.**
  `AccountEmptinessControls.lean` checks each literal action through the State
  facade and proves exact Id success and failure, presence partition and
  transaction-view agreement on the §7.1 domain. The interpreted guard covers
  tombstones, a supplied nonstandard empty-code hash, and nonempty accounts
  that differ in nonce, balance or one bit at either end of the code hash.
  The focused native and interpreted runs agree on 266 cases per predicate,
  comparing complete answers, provider traces, read sets and returned
  nonfunction fields against the current optional account recipe and its
  single-field and supplied-constant extensions across all three lookup levels.
  Authenticated normal and optimized runs of pinned EELS agree with Lean on
  answers, provider calls and successful reads for 245 coherent cases per
  predicate. The source controls also check frame retention, one current
  optional lookup per predicate call, and read insertions, including before
  provider failure. Lean failure returns no state. The other 21 cases per
  predicate exercise nonstandard supplied constants in Lean.
- **Implemented mathematical transaction-view controls:** private
  `TransactionViewCallerProofs.lean` imports only the State facade and consumes the
  sole public account law, checking arbitrary-m and non-Monad signatures, tombstones
  and transaction misses. `scripts/TransactionViewNativeTests.lean` executes actual
  public block and transaction views on `transaction_view_inputs.json` natively
  and interpreted. `transaction_view_model.py` checks all 118 complete raw results
  against independently frozen integer/list maps in `transaction_view_expected.json`.
  Accounts, nested storage and raw code retain every key, full payload, zero and
  empty inner map or code byte string. Cases distinguish deletion without clear, clear/rewrite,
  missing versus present-empty, zero deletion, orphan and untouched malformed
  storage, touched-empty pruning, raw reserved code and block/transaction precedence.
  Six ignoredVariant families supply nonempty contradictory forward/reverse metadata,
  gaps, duplicate/stale reverse keys, missing/empty/extra slot indexes, huge `next`,
  transient zero/nonzero writes, unrelated observations, independent constants and
  typed sentinel-failure providers. The view never queries them; private ordinary
  construction/slot-domain proofs cover exact internal metadata transport without
  exposing the helper to tests. Strict-reader regressions run normally and with -O,
  rejecting framing/count/order/schema/field/type/payload errors, including boolean
  or noninteger numbers. These are finite mathematical model-agreement controls;
  no standalone Python view exists and no source differential, operational history,
  backend, guest, WF or cost claim follows.
- **Implemented mathematical block-view cases:** private
  `BlockViewCallerProofs.lean` clients use only the public view equation, seven
  extraction laws and public application/observer laws. `BlockViewGuards.lean`
  compares 1,598 complete framed observations from 94 independent numerical/list
  recipes. Cases cover deletion without clear, clear/rewrite, orphan/zero/empty
  patches, untouched empty/zero maps, reserved and empty code, every 20/32-byte key
  position, huge nonce/counter/offset and insertion permutations. Independent
  changes to provider/constants/read sets/offset and all three metadata fields
  leave the result equal; retained parents and effect-changing siblings keep
  complete maps. Complete raw map framing retains absent versus present-empty
  storage and all payload bytes. The interpreted `#guard` full-output comparisons
  are mathematical composition controls (native and independent external
  comparisons are out of tree: nothing for them is committed, so they cannot be
  reproduced from this repository), without an original Python view oracle, source
  runtime, replay/failure-order, EEST or cost claim.
- **Implemented extraction cases (Q85):** all tests are private. `BlockExtractionCallerProofs.lean` consumes only the seven laws, `BlockDiff.ext`, public Std/order laws and `MathState.apply_congr_effects`: exact class-free/contravariant signature, complete reconstruction, optional lookup, arbitrary discarded-field independence and ordered-observer congruence. `BlockExtractionGuards.lean` compares 1,560 complete framed actual/expected observations from 120 numerical/list recipes: nine raw order entries at each index (seven distinct cases; two entries repeat the first, well-formed case), six absent/present-empty/extra slot-map cases, all 20/32-byte positions, full code bytes, huge nonce/counter, tombstones/zero/empty patches, insertion permutations, retained parents/siblings and independent provider/constants/read-set/offset variations. Every seven-field observation includes full payloads; separate optional tags distinguish none from some []. Seven field-omission sensitivity controls check the observer. The interpreted `#guard` full-output comparison (no native runner is committed for this slice) is bounded functional evidence, with no EELS malformed-index runtime, tracker/backend/EEST, resource or cost claim.
- **Implemented Account value cases:** `Conformance/State/AccountGuards.lean` observes the complete nonce, numeric balance and all code-hash bytes. Cases include zero, maximum balance, nonce `2^1024+17`, unequal first/last hash bytes, arbitrary supplied empty-code hashes, reconstruction/equality and `none` versus `some (emptyAccount consts)`. `Conformance/State/AccountCallerProofs.lean` consumes the public constructor/eta/ext and empty-field laws. Pinned Account/EMPTY_ACCOUNT fidelity is checked by reading the pinned source at `state.py:36–50`, conditional on coherent F20 constants; these guards do not execute state_tracker or EEST guest fixtures.
- **Implemented mathematical-state cases:** `Conformance/State/MathStateGuards.lean` proves independent zero/empty-inner/orphan omissions and the WF hidden-code counterexample. Its full-field/key guards and clients of the §7 laws compile through `EthConformance`. `scripts/MathStateNativeTests.lean` compares complete raw maps, optional account/code answers and storage words with a finite association-list oracle; cases include arbitrary constants, reserved raw entries, huge nonce/max balance, all indexed key bytes, reconstructed equal keys, insertion order and retained siblings. No runtime universe enumeration or tracker/EEST execution is claimed.
- **Implemented raw BlockDiff cases:** `Conformance/State/BlockDiffCallerProofs.lean` names arbitrary public callers of the §7 laws. `Conformance/State/BlockDiffGuards.lean` and `scripts/BlockDiffNativeTests.lean` compare all seven fields against an independent finite association-list oracle: complete fixed-width keys, unbounded nonce, maximum balance, absent/deleted/empty/replacement accounts, zero writes and empty/orphan storage maps, empty/duplicate/foreign/permuted metadata, reserved and other hashes with arbitrary complete code, insertion-order variation and retained parent/sibling values. Complete interpreted/native observations include every byte, value, presence tag and list occurrence. These comparisons exercise the raw value contract from `state.py:55–83` and B1 guidance; they execute no tracker/backend operation or EEST guest fixture.
- **Implemented raw TxRevertible cases:** private facade clients in
  `Conformance/State/TxRevertibleCallerProofs.lean` check the exact full constructor
  type, arbitrary complete construction/reconstruction and all eight independent
  whole-field replacements. Ordinary kernel controls compare complete eight-field
  observations with explicit byte-list/value expectations: empty/all-nonempty records,
  full 20/32-byte keys/hashes, repeated arbitrary code and present empty code,
  account tombstone and huge-nonce/maximum-balance replacement, zero/maximum storage
  and transient values, present empty inner storage, independent clears, missing/extra
  slot indexes, malformed inverse maps and huge sparse or insufficient counters.
  Retained parent and independent account/transient/clear children are checked.
  Each field's independent empty replacement changes the complete observation.
  Observations use public Base/Std APIs and retain every raw order-map entry;
  they assert no tracker execution, source runtime, snapshot/restore or cost bound.
- **Implemented raw TxState/StateM clients:** private
  `Conformance/State/TxStateCallerProofs.lean` checks exact type/constructor/field
  arities for arbitrary m, complete three-field construction/reconstruction and
  each replacement retaining both complete siblings. A contravariant type
  constructor exposes hidden class constraints. Complete alias/run types and
  arbitrary underlying actions are retained without classes. Id pure/put/get
  controls compare whole returned values and states; supplied StateError and
  nested WitnessError controls preserve the exact error after a put, with no
  returned state. Arbitrary provider fields admit all raw irregular metadata.
  These are ordinary Lean wiring proofs, without protocol differential, tracker
  rollback/lifetime, underlying-effect rollback or current-EELS refinement claims.
- **Implemented raw application cases:** `Conformance/State/ApplyCallerProofs.lean` consumes the §7 laws on arbitrary inputs. The independent association-list model in `ApplyGuards.lean`, emitted completely by `ApplyNativeTests.lean --dump`, covers deletion without clear, orphan writes, untouched versus touched empty inners, unwritten stored zero, clear then rewrite, explicit zero erasure, raw reserved-code replacement with arbitrary observer constants, and duplicate/foreign/reversed metadata. Complete raw inputs/outputs, optional tags, indexed 20/32-byte keys, huge nonces, U256 words, full code and retained parent/sibling values are observed. Finite source application comparison retains the typed/default/nonaliasing premises above; these checks establish no WF preservation, history, root or EEST result.

- **Implemented raw PreState cases:** public-only arbitrary-m clients consume all
  seven carrier laws without a Monad premise. `PreStateGuards` and
  `scripts/PreStateNativeTests.lean` compare all 126 complete callback families
  unconditionally; `--dump` emits complete arguments and results. They compare these
  with independent expectations: all nominal error/item tags and 32-byte payloads,
  account absence versus present-empty/huge-nonce/max-balance, storage zero versus
  error, empty code versus error, exact root bytes versus error, every raw diff field
  and unusual metadata, and retained parent/sibling callbacks. These carrier tests
  execute no pinned Protocol body or backend/root/hash semantics.
- **Implemented nominal StateError cases:** private arbitrary-WitnessError construction/
  elimination examples retain the supplied value and distinguish all four outer tags.
  `StateErrorGuards` owns the shared complete case corpus and observers, reused by
  `scripts/StateErrorNativeTests.lean`; both compare complete independent
  tagged byte-list expectations for 340 cases: missing/malformed node, code and leaf,
  unresolved hash, zero/max/mixed hashes and high/low changes at every one of 32 positions,
  including first and last byte positions. The runner checks all 340 cases unconditionally;
  `--dump` emits every complete actual/expected pair. Leaves and the three nullary state errors
  carry no invented hash. The native dump emits full actual/expected values. Test
  observers stay in EthConformance; no production equality/repr/default/order/hash/coercion
  instance is installed for the carrier. There is no nominal EELS operation to differentially run.
- **Implemented BlockState controls:** private State-facade clients quantify arbitrary
  m and complete fields, including whole PreState functions, with no Monad/hash-query
  premise. Complete independent finite numeric recipes compare all thirteen framed
  payloads: all four constants' 32 bytes, account tombstones/huge nonces/max balances,
  storage zero/nonzero/empty inners, raw malformed/gapped/duplicate reverse-order
  occurrences and unbounded counters, arbitrary code, independent read/clear sets,
  and None/Some 0/huge offsets. Every 20/32-byte position and high bits, reconstructed
  equal keys/duplicates and independent pair components are covered. Every field
  replacement retains every other complete field; retained parents/siblings and
  seven synthetic callback-error families retain complete values and errors.
  These interpreted `#guard` observations are bounded functional controls (no native
  runner is committed for this slice), with no EELS operation, generic effect
  interpretation or resource claim.
- **Transaction-state initialization controls:** `TransactionInitializationChecks.lean`
  verifies complete class-free construction from raw supplied parents. It checks
  four parent cursors, retained parent tombstones and read sentinels, all nine
  empty source collections and the B1 index defaults. Direct comparison in the
  two isolated pinned Python modes also checks that mutating all nine fields in
  one source transaction leaves a sibling transaction's defaults intact.

- **Implemented BlockState initialization controls:** private class-free facade
  clients include a contravariant type constructor with no installed Monad and
  derive complete constant-byte retention through new_consts. Owner-private
  ordinary reduction retains the whole arbitrary provider, beyond any finite
  callback observations. The private BlockInitializationGuards corpus has 138
  provider/constants inputs and 1,104 actual/expected entries (eight per input,
  three of which repeat an earlier observation of the same input; across inputs
  474 entries are distinct, because sibling/provider observations depend only
  on the 33 seeds and constants only on the 132 records): all eleven
  empty/default outputs, both maps and zero counters in B1 indexes, all four
  constants independently through every 32-byte position, arbitrary/incoherent
  records, complete callback inputs/results/error payloads, None versus Some 0,
  and retained providers/constants/parents/siblings. Independent literal empty
  frames and numeric byte recipes supply expectations. Interpreted `#guard`
  execution inspects complete public outputs (no native runner is committed for
  this slice); no external proof client unfolds new, no raw HashSet equality
  follows from membership, and no original Python allocation identity or
  lifetime/cost theorem is claimed.
- **Implemented logical-read-set controls:** private facade clients check all four
  exact class-free types, both directions of each public iff and a contravariant
  type constructor without Monad. Public record updates and only the iff laws prove
  each view independent of every other field. `ReadSetsGuards.lean` compares 176
  complete actual/independent expected vectors with query IDs and every queried
  20/32-byte key: empty/nonempty, duplicates/reconstruction, insertion permutations,
  same address/different slot and same slot/different address, low/high/mixed
  changes at every byte, leading zeros, each irrelevant field, None/Some 0/huge
  offsets and retained parents/siblings. Canonical dictionaries exercise distinct
  keys sharing low hash bits, without a new Hashable instance or a distribution
  claim. Runtime controls transport existing Std membership decidability through the
  public iff laws, adding no decidability API. The interpreted `#guard` output (no
  native runner is committed for this slice) is finite membership evidence; it
  implies no raw-set equality, Python iteration/allocation identity, tracker
  operation, BAL sorting or cost result.
- **Implemented TxObs controls:** private generic clients use whole raw field equality,
  without inferring raw HashSet equality from membership. Complete guards observe
  every 20/32-byte key, every byte position, high bits, both pair components
  independently, equal reconstructed keys, duplicate insertion, union, missing
  membership, independent account-read/created sets and retained parents/siblings.
  These are finite controls for the raw carrier.
- **Implemented account creation marker cases (R22).**
  `Conformance/State/MarkAccountCreatedGuards.lean` checks the exact Monad-only
  run through the State facade. Four interpreted histories cover empty and
  populated initial sets, repeated marks, zero, a high-bit address paired with
  a low address sharing its suffix, and the maximum 160-bit address. The guards
  check every intermediate set and an unchanged base trace. Separate compiled
  Lean and isolated normal and optimized EELS probes at `59c1473d` compare
  eleven marks on four histories, including the value fields of both source
  carriers. The EELS probes check that the transaction keeps its parent and
  provider and that the mark makes zero provider calls. The Lean probe also
  checks the retained B1 indexes, F20 constants and provider actions. The
  compiled probe and source comparison are recorded out of tree.
- **Property tests:** random operation sequences against the reference model of §7.1 (the commuting equations as executable checks); snapshot/revert against a naive deep-copy implementation; differential comparison with EELS `state_tracker` through a Python harness on random sequences (bug-finding only).
- **Implemented lookup-agreement cases (Q57):** private ordinary symbolic clients
  consume each complete successful answer and publicly specified observer law. Guards
  prove whole-predicate agreement for arbitrary raw states and supplied root functions;
  success witnesses retain optional accounts, zero defaults and exact nonreserved bytes.
  Negative cases reject absent/present-empty confusion, wrong storage/code successes and
  nonreserved code success at raw absence. Raw zero/nonzero/orphan/empty-inner storage,
  hidden reserved bytes, unrelated constants-field variation, different reserved records,
  always/selective errors (including reserved-code errors), and arbitrary successful/error
  roots are covered. These proof guards use no native universal-Prop oracle or new runner.
- **Implemented Q58 cases:** private symbolic clients cover the §7.4 laws.
  `StructuralGuards.lean` proves independent premise omissions and initial-WF necessity
  for zero/empty-inner/orphan states, raw empty/zero patch presence at absent accounts,
  and sufficient-but-not-necessary premises. Complete raw guards cover surviving storage,
  deletion with/without clear, clear/reintroduction, zero last-slot pruning, empty patches
  with/without clear, account replacement before writes, arbitrary code and unusual metadata.
  These logical/finite cases do not execute tracker, backend/root or guest operations.

## 5. Interface

Core §3/§4/§5/§7 now supplies nominal `VmFault.state` consuming this actual StateError, retaining the complete nested WitnessError. This adds no state operation, lift or diagnostic/outcome adapter; R29/B14 obligations remain open.

Reference field order, widths and inherited records are catalogued in [REFERENCE-RECORDS](../REFERENCE-RECORDS.md), generated from the exact pin. Wire-schema owners must use those layouts and prove their codec instances. Runtime records may use the explicit abstraction below; omitted fields or `…` remain implementation blockers, not implicit freedom to choose semantics.

All public unless marked internal. `Except` failures use `StateError`. Account and
emptyAccount values, internal WriteOrder support, raw MathState observers, raw
BlockDiff values and raw mathematical application are implemented and pure; the raw
MathState record and structural `WF` are also supplied. The raw PreState carrier and
coarse nominal WitnessItem/WitnessError values are supplied without a Monad premise.
The nominal StateError carrier in §5/R29, raw four-field TxObs carrier and raw
thirteen-field BlockState carrier are also supplied. BlockState.new and its explicit
F20 new_consts law and raw extraction with its seven Q85 laws are supplied
separately below. Logical account/storage predicate views and their two iff laws,
and the mathematical BlockState.view with its application equation (§3/§7.2), are
also supplied. TxState.view and exactly its account observer law are supplied
separately (§3/§7.2); its raw conversion remains Lean-private. The tracker source
map in §3 records which operations are supplied. The raw eight-field TxRevertible
carrier is supplied without operations, defaults, instances or authored public laws
(§3/§7). The raw three-field TxState and exact StateM alias are supplied without
class premises or authored public laws in the carrier module; their nominal boundary
supplies no source refinement. The separate class-free `TxState.new` initializes
fresh transaction data over the whole supplied block (§3/§4).
The bounded structural predicate and preservation laws are supplied
(§3/§7.4). MathState mutation, diff WF/history/reachable preservation and actual
PreState providers remain unimplemented targets.
The R8 lookup relation is supplied as ModelsLookups (§3/§5). The EELS default-empty BlockDiff
convenience constructor remains deferred (§10).

**Observation-key provider (Q84).** The supplied TxObs and BlockState raw Std fields use
Base's canonical named `Address.instHashable` and `Bytes32.instHashable`, plus
Q51's unchanged Hash32 dictionary. Existing product support combines these with
`mixHash`; no State-local or pair-specific instance, new parameter or carrier field
is added. EthBase §3/§5 owns the complete 20/32-digit models and ordinary equations.
Bytes32 includes FixedBytes 32 aliases; nominal Address supplies no FixedBytes 20
support. Base support alone supplies no State carrier; the bounded TxObs carrier is
implemented separately (§3), as are raw BlockState, both standalone
initializers and the nominal TxState/StateM assembly.
The two codeReads fields use hash-only Q51 keys. Only storageReads uses the
Address/Bytes32 product dictionary.

```lean
-- public types
structure Account where
  nonce : Nat
  balance : U256
  codeHash : Hash32
def emptyAccount (consts : HashConsts) : Account      -- R3; HashConsts from EthBase (R2)

inductive WitnessItem | node (h : Hash32) | code (h : Hash32) | leaf   -- coarse, commitment-agnostic
inductive WitnessError
  | missing (what : WitnessItem)      -- O4(a), O4(d)
  | malformed (what : WitnessItem)    -- O4(b), leaf decoding, cycles
  | unresolved (h : Hash32)           -- O4(c): lookup or update meets a hashed stub
inductive StateError
  | witness (e : WitnessError) | balanceUnderflow | balanceOverflow | storageOnMissingAccount

structure BlockDiff where
  accountChanges : Std.ExtTreeMap Address (Option Account)
  -- Reachable extraction: first-write order, no duplicates (B1/§7.4–§7.5).
  accountOrder   : List Address                 -- raw constructor admits any list
  storageChanges : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)
  -- Reachable extraction: first appearance after the last removal.
  storageAddressOrder : List Address             -- raw constructor admits any list
  -- Reachable extraction: per-address first-write order; restart after a clear.
  storageSlotOrder : Std.ExtTreeMap Address (List Bytes32) -- raw lists admit any occurrences
  codeChanges    : Std.ExtTreeMap Hash32 ByteArray
  storageClears  : Std.ExtTreeSet Address        -- no clear order (F7, open)

-- D5: arbitrary type constructor for the raw carrier; downstream sequencing needs Monad only
structure PreState (m : Type → Type) where
  getAccount? : Address → m (Except WitnessError (Option Account))
  getStorage  : Address → Bytes32 → m (Except WitnessError U256)
  getCode     : Hash32 → m (Except WitnessError ByteArray)          -- B2: missing code is an error
  stateRoot   : BlockDiff → m (Except WitnessError Hash32)
variable {m : Type → Type} [Monad m]

-- the mathematical model (public, may be unfolded)
structure MathState where
  accounts : Std.ExtTreeMap Address Account
  storage  : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)
  code     : Std.ExtTreeMap Hash32 ByteArray
def MathState.account? (σ) (a : Address) : Option Account
def MathState.storageAt (σ) (a : Address) (k : Bytes32) : U256        -- default 0
def MathState.code? (σ) (consts : HashConsts) (h : Hash32) : Option ByteArray  -- consts.emptyCodeHash ↦ some empty
def MathState.WF (σ) : Prop           -- no zero values, no empty inner maps, storage keys ⊆ account keys
def MathState.apply (σ) (d : BlockDiff) : MathState                  -- R5
def BlockDiff.StructuralPremises (σ : MathState) (d : BlockDiff) : Prop := -- Q58
  (∀ a : Address, d.accountChanges[a]? = some none → a ∈ d.storageClears) ∧
  (∀ a : Address, d.storageChanges[a]?.isSome = true → (σ.apply d).account? a ≠ none)
def BlockDiff.WF (σ) (d) : Prop       -- §7.4; optional slot-order-map domain still open
def ModelsLookups (consts : HashConsts) (ps : PreState Id) (σ : MathState) : Prop := -- R8/Q57
  (∀ a o, ps.getAccount? a = .ok o → σ.account? a = o) ∧
  (∀ a k v, ps.getStorage a k = .ok v → σ.storageAt a k = v) ∧
  (∀ h code, ps.getCode h = .ok code → σ.code? consts h = some code)

-- Internal persistent order index: replacing it changes only this component's laws.
structure WriteOrder (K : Type) [Ord K] [Std.TransOrd K] where
  next : Nat
  positions : Std.ExtTreeMap K Nat
  keysByPosition : Std.ExtTreeMap Nat K
def WriteOrder.empty : WriteOrder K
def WriteOrder.record : WriteOrder K → K → WriteOrder K -- existing key keeps its position
def WriteOrder.erase : WriteOrder K → K → WriteOrder K
def WriteOrder.toList : WriteOrder K → List K           -- ascending live position, not sorted key
-- Raw type and operations require only Ord K and Std.TransOrd K.
def WriteOrder.WF (r : WriteOrder K) : Prop :=
  (∀ k p, r.positions[k]? = some p ↔ r.keysByPosition[p]? = some k) ∧
  (∀ p k, r.keysByPosition[p]? = some k → p < r.next)
def WriteOrder.Agrees (r : WriteOrder K) (writes : Std.ExtTreeMap K V) : Prop :=
  ∀ k, r.positions[k]?.isSome = writes[k]?.isSome

-- overlays (D22 persistent trees; D23 split)
-- supplied raw carrier only; operational invariants/lifetimes remain targets
structure TxRevertible where  -- snapshot-reachable, worst-case persistent; no WF imposed
  accountWrites : Std.ExtTreeMap Address (Option Account)
  accountOrder  : WriteOrder Address
  storageWrites : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)
  storageAddressOrder : WriteOrder Address
  storageSlotOrder : Std.ExtTreeMap Address (WriteOrder Bytes32)
  codeWrites    : Std.ExtTreeMap Hash32 ByteArray
  storageClears : Std.ExtTreeSet Address
  transient     : Std.ExtTreeMap (Address × Bytes32) U256
structure TxObs where                 -- linear, never reverted within a transaction
  accountReads   : Std.HashSet Address
  storageReads   : Std.HashSet (Address × Bytes32)
  codeReads      : Std.HashSet Hash32
  createdAccounts : Std.HashSet Address
-- Supplied raw carrier: no Monad premise; the following record itself does no sequencing.
structure BlockState (m : Type → Type) where
  preState : PreState m
  consts   : HashConsts                 -- supplied by the caller (R2, F20)
  accountWrites : Std.ExtTreeMap Address (Option Account)
  accountOrder  : WriteOrder Address
  storageWrites : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)
  storageAddressOrder : WriteOrder Address
  storageSlotOrder : Std.ExtTreeMap Address (WriteOrder Bytes32)
  codeWrites    : Std.ExtTreeMap Hash32 ByteArray
  storageClears : Std.ExtTreeSet Address
  accountReads  : Std.HashSet Address
  storageReads  : Std.HashSet (Address × Bytes32)
  codeReads     : Std.HashSet Hash32
  oldestAncestorOffset : Option Nat
-- Supplied raw assembly and alias, without any class premise or source-refinement claim.
structure TxState (m : Type → Type) where
  block : BlockState m                 -- only trackAncestorAccess writes it during a transaction
  rev   : TxRevertible
  obs   : TxObs
abbrev StateM (m : Type → Type) := StateT (TxState m) (ExceptT StateError m)

-- Supplied initialization requires no Monad or other class premise.
def BlockState.new {m : Type → Type} (ps : PreState m) (consts : HashConsts) : BlockState m
theorem BlockState.new_consts {m : Type → Type} (ps : PreState m) (consts : HashConsts) :
  (BlockState.new ps consts).consts = consts
def TxState.new (b : BlockState m) : TxState m -- supplied, class-free

-- reads (R10–R13)
def getPreStateAccountOptional {m : Type → Type} [Monad m]
    (a : Address) : StateM m (Option Account) -- supplied, Monad only
def getPreStateAccount {m : Type → Type} [Monad m]
    (a : Address) : StateM m Account -- supplied, Monad only
def getAccountOptional (a : Address) : StateM m (Option Account)
def getAccount {m : Type → Type} [Monad m]
    (a : Address) : StateM m Account -- supplied, Monad only
def getCode {m : Type → Type} [Monad m] (h : Hash32) : StateM m ByteArray
def getStorage {m : Type → Type} [Monad m]
    (a : Address) (k : Bytes32) : StateM m U256 -- supplied, Monad only
def getStorageOriginal {m : Type → Type} [Monad m]
    (a : Address) (k : Bytes32) : StateM m U256 -- supplied, Monad only
def getTransientStorage {m : Type → Type} [Monad m]
    (a : Address) (k : Bytes32) : StateM m U256 -- supplied, Monad only
def accountExists (a : Address) : StateM m Bool
def accountDeployable {m : Type → Type} [Monad m]
    (a : Address) : StateM m Bool -- supplied, Monad only
def accountExistsAndIsEmpty {m : Type → Type} [Monad m] (a : Address) : StateM m Bool
def isAccountAlive {m : Type → Type} [Monad m] (a : Address) : StateM m Bool
-- writes (R14–R23)
def setAccount {m : Type → Type} [Monad m] (a : Address) (account : Option Account) : StateM m Unit
def setStorage (a : Address) (k : Bytes32) (v : U256) : StateM m Unit
def destroyStorage {m : Type → Type} [Monad m]
    (a : Address) : StateM m Unit -- supplied, Monad only
def destroyAccount {m : Type → Type} [Monad m]
    (a : Address) : StateM m Unit -- supplied, Monad only
def clearAccountPreservingBalance {m : Type → Type} [Monad m]
    (a : Address) : StateM m Unit -- supplied
def markAccountCreated {m : Type → Type} [Monad m] (a : Address) : StateM m Unit
def setTransientStorage {m : Type → Type} [Monad m]
    (a : Address) (k : Bytes32) (v : U256) : StateM m Unit -- supplied, Monad only
def modifyState {m : Type → Type} [Monad m]
    (a : Address) (f : Account → Except StateError Account) : StateM m Unit -- supplied
def moveEther (src dst : Address) (amount : U256) : StateM m Unit
def createEther (a : Address) (amount : U256) : StateM m Unit
def setAccountBalance (a : Address) (amount : U256) : StateM m Unit
def incrementNonce (a : Address) : StateM m Unit
def setCode (a : Address) (code : ByteArray) (codeHash : Hash32) : StateM m Unit   -- caller: codeHash = keccak256 code
-- snapshots and lifecycle (R24–R28)
def copyTxState (t : TxState m) : TxRevertible                         -- snapshot
def restoreTxState (snap : TxRevertible) : StateM m Unit               -- revert
def incorporateTxIntoBlock (t : TxState m) : BlockState m × TxState m      -- BAL hook runs before, in EthBlock
def extractBlockDiff {m : Type → Type} (b : BlockState m) : BlockDiff -- Q85, no class premise
def trackAncestorAccess {m : Type → Type} [Monad m] (offset : Nat) : StateM m Unit

-- model views (public, for laws)
def BlockState.view {m : Type → Type} (σ₀ : MathState) (b : BlockState m) : MathState
  -- exactly σ₀.apply (extractBlockDiff b), supplied without a class premise
theorem BlockState.apply_extractBlockDiff {m : Type → Type}
    (σ₀ : MathState) (b : BlockState m) : σ₀.apply (extractBlockDiff b) = b.view σ₀
def TxState.view {m : Type → Type} (σ₀ : MathState) (t : TxState m) : MathState
  -- exactly (t.block.view σ₀).apply t.rev.asDiff; supplied without class premises
theorem TxState.view_account?_eq {m : Type → Type}
    (σ₀ : MathState) (t : TxState m) (a : Address) :
    (t.view σ₀).account? a = match t.rev.accountWrites[a]? with
      | some account => account
      | none => (t.block.view σ₀).account? a
def TxState.originalAt (σ₀) (t) (a) (k) : U256
private def TxRevertible.asDiff (r : TxRevertible) : BlockDiff       -- owning view module
def BlockDiff.merge (d₁ d₂ : BlockDiff) : BlockDiff                  -- incorporate's rule, R25
-- Read-only BAL views; they expose source semantics, never container layout.
def preTxAccount (t : TxState m) (a : Address) : m (Except StateError (Option Account))   -- falls through to the pre-state
def preTxStorage (t : TxState m) (a : Address) (k : Bytes32) : m (Except StateError U256)
def TxState.accountWritesInOrder : TxState m → List (Address × Option Account)
def TxState.storageWritesInOrder : TxState m → List (Address × List (Bytes32 × U256))
-- Supplied logical membership views, without class premises or a Set provider.
def BlockState.accountReadSet {m : Type → Type} (b : BlockState m) : Address → Prop
def BlockState.storageReadSet {m : Type → Type} (b : BlockState m) :
  (Address × Bytes32) → Prop
theorem BlockState.accountReadSet_iff {m : Type → Type} (b : BlockState m) (a : Address) :
  BlockState.accountReadSet b a ↔ a ∈ b.accountReads
theorem BlockState.storageReadSet_iff {m : Type → Type} (b : BlockState m)
    (pair : Address × Bytes32) : BlockState.storageReadSet b pair ↔ pair ∈ b.storageReads
```

## 6. Data structures

| Type | Representation | Model | Abstraction | Invariant | Persistence | Complexity |
|---|---|---|---|---|---|---|
| `Account` | structure | itself | identity | — | value | O(1) |
| `BlockDiff` | `ExtTreeMap`s + account/address/slot order lists | seven exact raw fields; reachable extraction supplies replay invariants separately | whole optional lookups, exact metadata and clear membership | raw constructor admits any value; reachable extraction must enumerate each map domain exactly once and restart slot order after a clear (§7.4/§7.5) | value; read-only after extraction | raw fields retained; extraction traverses supplied live order entries and maps slot-index values once, with no next-range scan; composed measurements outstanding |
| `WriteOrder K` | two persistent `ExtTreeMap`s and a `Nat` counter | duplicate-free list of keys | `toList` in position order | intrinsic `WF`: exact inverse and position bound; separate `Agrees`: associated write domain | snapshot-reachable | required analytical bounds: O(log n) tree-path work for record/erase, O(n) live-entry extraction, O(1) saved-root selection (excluding comparison and reclamation costs); no range(next) scan; C1/C4 integration measurements open |
| `MathState` | nested `ExtTreeMap`s | finite maps with defaults | `account?`, `storageAt`, `code?` | `WF` | value | O(log n) lookups |
| `TxRevertible` | nested persistent `ExtTreeMap`/`ExtTreeSet` (D22) | a `BlockDiff` layered over the block view, plus transient map | `asDiff`, `transient` | WriteOrder observers enumerate live first writes for accounts, storage addresses and slots; clears ⊆ addresses; inner maps are post-clear writes only | **snapshot-reachable: worst-case persistent** | read O(log A + log S); write O(log A + log S) path copy; snapshot O(1); revert O(1) plus reclamation of the discarded version; `destroyStorage` O(s) for `s` pending writes of that address |
| `TxObs` | four raw `Std.HashSet` fields supplied | finite sets | `toList` as sets; whole supplied raw fields retained | no raw invariant; monotonicity is a future operation obligation | **linear-only** (never inside a snapshot, D23) | insert expected O(1), merge expected O(m), conditional on suitable distribution and linear ownership; resize/collision/allocation and aggregate costs remain unmeasured (ARCHITECTURE §5.0/C1–C4) |
| `BlockState` | supplied raw thirteen-field record: provider/constants, persistent writes/clears/order indexes, three HashSets and optional Nat offset | itself for raw construction; new retains provider/constants and initializes eleven defaults; supplied `BlockState.view` = `σ₀.apply (extractBlockDiff b)` plus observations | exact raw projections; logical account/storage membership; supplied `extractBlockDiff` and `BlockState.view`, future semantic sets | no raw invariant; post-clear/history and coupled order/value invariants belong to future operations | intended linear between transactions, read-only/shared during one; raw presence proves neither | raw fields retained; incorporation target O(w · log n) for `w` writes, with ARCHITECTURE §5.0 union caveat; construction/allocation/retention and C1–C4 remain unmeasured |

Q84 supplies canonical component dictionaries for all three observation-key domains.
Support collisions preserve actual equality and duplicates; they supply no distribution
bound. D22 still covers all revertible writes/clears/order indexes/transient storage,
and D23 keeps observations/createdAccounts linear outside snapshots. Block read sets
are shared read-only during transactions; support does not establish merge ownership.
The supplied raw TxObs and BlockState constructors enforce none of these lifetime/ownership rules.
Arbitrary raw representations are retained; D23 is an operation/integration obligation,
not a theorem from record presence. D22 persistent writes are unchanged.

Observation sets could become `TreeSet`s if `EthBlock` needs sorted output directly; the BAL builder sorts separately (ARCHITECTURE §5.6). EELS's `copy_tx_state` deep-copies all writes (O(n) per call frame); the persistent representation makes it O(1), which is the performance motivation for D22.

## 7. Contract and laws

**Observation-set proof boundary (Q84).** Base's complete numeric/byte injectivity
and two named model equations per new domain, together with public Std
member/insert/union/duplicate and lookup/overwrite laws, supply functional key support
without distinct hashes. Raw Std types retain their dictionary parameters: consumers
construct sets using the same canonical names. Same-name/model replacement after
recompilation should preserve public-law proof source, without reusing old binaries;
concurrent dictionaries need explicit identity/transport or rehashing. No client unfolds
private fixed-byte fields or buckets. Membership agreement alone does not assert raw
HashSet equality. Actual State observations use their semantic set model. The raw
TxObs and BlockState constructors preserve their supplied sets. The separate
logical read views and their two iff laws below expose only membership. Lean iteration is not Python set order,
and F7 still covers replay failures and observations as well as roots.

**Raw TxObs contract.** The exact §5 constructor/projections preserve every supplied
whole set, including arbitrary raw representations. Private ordinary clients prove
four-argument construction, eta, complete component reconstruction, all four
updates retaining the other three fields, six disjoint update commutations and
account-read/created-account separation. Public Base reconstruction/equality and
Std insert/member/union/duplicate laws are used for all three key domains; no
membership-to-raw-equality principle, dictionary parameter or public helper law is
added. R24 leaves the whole supplied observation record outside the snapshot.
Incorporation, default-empty construction, linear threading and monotonicity
remain future implementation/proof work.

**Account creation marker (R22).** The private run equation gives one base
`pure` whose payload is exactly typed success with `Unit` and the input state
after the one set insertion. On `Id` success, substituting the original
created-account set into the result recovers the complete original transaction.
The private set proofs show that a post-insertion member is the supplied address
or an old member, and that repeating the insertion preserves membership. These
proofs use the canonical Base address dictionaries and ordinary Std set laws.

**Raw BlockState contract.** Exactly the thirteen §5 fields are supplied for every
`m : Type → Type`, without Monad or KeccakQuery. Whole supplied functions/constants/
maps/sets/order indexes/offsets remain exact, including incoherent constants,
tombstones, ordinary storage zero values, empty inner maps, arbitrary raw metadata
and None/Some 0/huge offsets. These are raw inputs, not admission/reachability claims.
Private complete construction/projection/eta/component/update/commutation clients
exercise only public record/provider/Base/Std boundaries. There is no authored
public law, helper, instance, default or observer for the raw carrier. The separate
BlockState.new operation initializes exactly the guided empty maps/sets, WriteOrder.empty
indexes and none offset while retaining ps and consts. Its sole public law is
new_consts, with no premises beyond the supplied data. Private owner reduction proves
the entire constructor result and provider retention. Further public consumer-law
basis, context-sharing/coherence, snapshot integration, incorporation and other
tracker laws remain open.

**Raw TxState/StateM contract.** Exactly the three §5 fields and transformer alias
are supplied, without Monad, Functor, KeccakQuery, LawfulMonad, WF or coherence
premises. Whole arbitrary BlockState, TxRevertible and TxObs values are retained;
constructor/projection/reconstruction and independent replacements need only the
raw public records. No authored public law or instance is added. Private facade
clients check these properties, including a non-Monad type constructor. StateM
runs to `m (Except StateError (α × TxState m))`; failure contains only StateError,
without transaction state. Sequencing requires Monad only in clients, with Id
controls for complete pure/put/get/error results. This establishes no tracker
rollback or interpretation of underlying effects. The separate `TxState.new`
supplies fresh defaults (§3). Caller initialization, context acquisition and
coherence, observation lifetime and monotonicity, StateError semantics and
freezing, and current-pin refinement remain open.

**Logical block read-set contract.** For every arbitrary `m : Type → Type`, raw
block b and complete key, accountReadSet b a iff a belongs to b.accountReads;
storageReadSet b pair iff the entire pair belongs to b.storageReads. These are exactly
accountReadSet_iff and storageReadSet_iff. No Monad, WF, provider, constants-coherence,
account/storage consistency or reachability premise occurs. Every other field is
unrestricted. Public-law clients use the iff laws; private runtime controls transport
existing raw-membership decidability through the public iff laws.
There is no public decidability/iteration API, codeReadSet or equality law for raw
HashSets. These projections neither add observations nor implement tracker reads,
merge, monotonicity, ordering or lifecycle.

**Raw extraction contract (Q85).** Exactly these seven whole-field laws are supplied,
for every `b : BlockState m` without a class or validity premise:

```lean
theorem extractBlockDiff_accountChanges (b : BlockState m) :
  (extractBlockDiff b).accountChanges = b.accountWrites
theorem extractBlockDiff_storageChanges (b : BlockState m) :
  (extractBlockDiff b).storageChanges = b.storageWrites
theorem extractBlockDiff_codeChanges (b : BlockState m) :
  (extractBlockDiff b).codeChanges = b.codeWrites
theorem extractBlockDiff_storageClears (b : BlockState m) :
  (extractBlockDiff b).storageClears = b.storageClears
theorem extractBlockDiff_accountOrder (b : BlockState m) :
  (extractBlockDiff b).accountOrder = WriteOrder.toList b.accountOrder
theorem extractBlockDiff_storageAddressOrder (b : BlockState m) :
  (extractBlockDiff b).storageAddressOrder = WriteOrder.toList b.storageAddressOrder
theorem extractBlockDiff_storageSlotOrder (b : BlockState m) :
  (extractBlockDiff b).storageSlotOrder =
    b.storageSlotOrder.map (fun _ r => WriteOrder.toList r)
```

Missing slot metadata stays missing; present empty stays some []; extra entries,
duplicate/foreign reverse values, gapped positions and entries beyond next survive.
Forward-only entries remain invisible under the existing observer, rather than
being reconstructed. Full raw indexes are not preserved. Provider functions,
constants, three read sets and the ancestor offset are discarded independently.
Whole-result, optional lookup, congruence, application and independence clients
stay private. Raw extraction adds no extra helper, view, WF or history interface;
the separate mathematical block view is supplied in §3/§7.2.
Full optional-map WF is still open under Q58; Q85 selects only raw extraction.

**Account value seam.** (R1–R3)

`State/Account.lean` supplies `Account.nonce_mk`, `balance_mk`, `codeHash_mk`, `eta` and `ext`, together with ordinary `DecidableEq` from the public fields. The record is its own model; its constructors add no nonce cap, state validity predicate, hash acquisition or codec. For every supplied `consts`, `emptyAccount_nonce`, `emptyAccount_balance` and `emptyAccount_codeHash` preserve zero, `U256.zero` and exactly `consts.emptyCodeHash`. Absence is `none : Option Account`, distinct from a present empty account. These value laws supply no tracker operation, state/error invariant or lifecycle refinement.

### Raw mathematical-state observer laws

The raw laws hold for every finite raw state, without `WF`:

| Laws | Claim and premises |
|---|---|
| `accounts_mk`, `storage_mk`, `code_mk`, `eta` | Construction preserves each whole map; reconstruction preserves the state. |
| `ext`, `ext_lookup` | Raw field equality, or equality of all optional lookups, determines state equality. Inner storage maps and every raw code hash are compared whole. |
| `account?_eq_lookup`, `storageAt_eq_lookup` | Account lookup is optional; storage defaults either missing layer to zero. |
| `storageAt_of_storage_none`, `storageAt_of_slot_none`, `storageAt_of_slot_some` | The stated absent/present lookup premise determines the exact storage answer, retaining raw zero. |
| `code?_empty`, `code?_of_ne` | The supplied reserved hash returns empty bytes; every other hash retains its raw optional lookup. |
| `code?_congr_consts` | Equal empty-code fields suffice for equal code observations; other supplied constant fields are irrelevant. |

The structural laws expose only the stated storage invariant:

| Laws | Claim and premises |
|---|---|
| `wf_iff` | `WF` is equivalent to exactly the three clauses below. |
| `wf_empty` | The triple of empty raw maps is structurally well formed. |
| `wf_storage_value_ne_zero`, `wf_storage_nonempty`, `wf_storage_account_present` | Under `WF` and the relevant present lookup, eliminate each storage clause. |
| `storageAt_zero_of_account_none` | Under `WF`, an absent account has zero observed storage. |
| `storageAt_zero_iff` | Under `WF`, zero observation is equivalent to slot absence in every present inner map. |
| `storage_present_iff_exists_nonzero` | Under `WF`, raw address storage is present exactly when some observed slot is nonzero. |

`WF` is exactly:

1. Every value in every present inner map is unequal to `U256.zero`.
2. Every present inner map has `isEmpty = false`.
3. Every storage address has `accounts[a]?.isSome = true`.

Under `WF`, `storageAt a k = U256.zero` iff every inner map stored at `a` lacks `k`;
raw storage presence at `a` iff some observed slot is nonzero. No `WF` code condition
is added. Fixed-constants observer equality does not determine the raw state: the
reserved-hash bypass hides raw code entries even under `WF`. Missing nonreserved
mathematical code is `none`, distinct from `some ByteArray.empty` and from B2's
provider failure. There is no public empty-state operation, setter, normalization or
new equality/order instance. Raw application is supplied below; other mutation and
reachable preservation remain open.

### Raw BlockDiff value seam (R4, B1)

`State/BlockDiff.lean` supplies exactly seven fields in §5 order. Every finite raw input is
admitted: account-map absence is no change, stored `none` is deletion and stored `some Account`
is complete replacement; zero writes, present empty inner maps, arbitrary code and every
supplied metadata occurrence are retained. `storageClears` supplies membership only, without a
replay order. No raw constructor promises §7.4 WF, account-read history, hash authenticity or a
first-write trace.

The ordinary public laws retain arbitrary supplied fields:

| Laws | Claim and premises |
|---|---|
| `BlockDiff.{accountChanges,accountOrder,storageChanges,storageAddressOrder,storageSlotOrder,codeChanges,storageClears}_mk` | Each constructor projection preserves its complete supplied field. |
| `eta` | Reconstruction from every raw field preserves the diff. |
| `ext` | Equality of every complete raw field determines diff equality. |
| `ext_lookup` | Equality of whole optional account, inner-storage-map, slot-list and code lookups, exact global order lists and clear membership determines diff equality. |
| `{accountChanges,storageChanges,storageSlotOrder,codeChanges}_mk_lookup` | Construction preserves each whole optional lookup. |
| `storageClears_mk_mem` | Constructor clear membership is exactly supplied set membership. |

All constructor laws quantify arbitrary supplied fields. `ext_lookup` imposes no
validity or history premises and no payload equality instance. Existing public Std
extensionality uses the lawful complete Address/Bytes32/Hash32 comparison providers.

### Raw mathematical application laws (R5)

All eighteen laws quantify arbitrary raw states, diffs and keys, with no WF/history
premise. `apply_accounts_lookup`, `apply_storage_lookup`, `apply_code_lookup`
determine the complete raw output: account changes use outer optional replacement;
storage uses post-clear inner maps, zero erasure and touched-empty pruning; code
changes override every raw hash. `apply_account?_eq`, `apply_storageAt_eq`,
`apply_code?_eq` supply the observer equations; the code equation retains arbitrary
supplied constants and the reserved-hash bypass.

`apply_of_no_changes` and `apply_congr_effects` give identity and equality from the
four equal effect fields alone. `apply_accounts_of_no_changes`,
`apply_storage_of_no_changes`, `apply_code_of_no_changes` frame complete fields.
`apply_storage_of_untouched`, `apply_storage_of_deleted_account_without_clear`,
`apply_storage_of_clear_no_writes`, `apply_storage_of_empty_writes` distinguish
untouched raw inners, deletion independence and touched-empty cleanup.
`apply_storage_slot_of_write_zero`, `apply_storage_slot_of_write_ne_zero`,
`apply_storage_slot_of_no_write` expose slot erasure, insertion and the post-clear
frame. The laws use expanded public Std expressions, not additional public model
helpers. They supply no `BlockDiff.WF`, reachable preservation or replay order.

### Raw provider carrier seam (R7, D8/D9, B2)

The four exact `PreState` fields and the seven ordinary laws named in §3 are supplied
without a Monad premise. Projection laws retain entire functions; `eta` reconstructs the
record; `ext` consumes equality of all four functions; `ext_apply` consumes pointwise
equality of complete actions at every input. Neither equality law interprets action effects.
The nominal WitnessItem/WitnessError constructors add no backend or diagnostic adapter.
The supplied `ModelsLookups` relation is described in §3/§5; progress, code/root
agreement and error refinement remain separate.

### Raw revertible transaction carrier

The supplied `TxRevertible` is its eight raw fields (§5), with the existing Base
key/provider instances inferred unchanged. Its constructor/projections and generated
structure infrastructure retain whole maps, sets and WriteOrder records for arbitrary
inputs. No authored public law or instance is supplied. Private arbitrary facade
clients check complete construction, reconstruction and each independent field update.
Raw `WriteOrder.WF` and `Agrees` are not carrier premises; malformed or disagreeing
indexes remain stored unchanged. Transient writes and clear membership are independent
of account/storage/code writes and order metadata. The mathematical view owns the
Lean-private conversion specified in §3/§7.1. R24 supplies snapshot and restore,
with the private equations in §7.2. Runner rollback integration and the
transaction lifecycle contracts remain open.

### 7.1 Model and commuting equations

Fix `t : TxState Id` and σ₀ with `MathState.WF σ₀` and
`ModelsLookups t.block.consts t.block.preState σ₀` (R8/Q57). All participating
transaction/block contexts retain that same initial supplied record and provider;
constructor/context preservation remains F20. The model of `t` is the triple
(`t.view σ₀`, `t.originalAt σ₀`, `t.rev.transient`) together with the observation sets.
The supplied Lean-private `TxRevertible.asDiff` copies the four effect fields whole
and uses the exact direct ordered observers/domain-preserving map in §3. Both layers
use the same `apply`; their mathematical composition requires no premises. The
tracker model equations below use the initial WF, ModelsLookups and success
premises. The standalone R11 action is supplied. The separate public
storage-precedence laws for SSTORE remain open (§7.2).
Per operation, under success (`op t = .ok (x, t')`) [C]:

- `getStorage a k` (supplied, private laws): `x = (t.view σ₀).storageAt a k`.
  Independently of the model premises, success returns the full input with the
  single raw `storageReads.insert (a,k)` update. A pair is a member afterwards
  iff it equals `(a,k)` or was a member before. The five branch equations
  assume only `Monad`. The fall-through equation binds the retained provider
  action and passes the mapped result to `pure`. A typed provider error maps to
  `StateError.witness`. At `Id`, failure returns that exact error without a
  transaction. The mathematical proof uses the two view applications and
  the storage clause of `ModelsLookups`.
- `getStorageOriginal a k` (proved privately): `x = if a ∈ t.obs.createdAccounts then 0 else (t.block.view σ₀).storageAt a k`, `t' = t`. The proof uses the block-view application and extraction laws and the storage clause of `ModelsLookups`. Its domain retains the initial `MathState.WF` premise.
- `getAccountOptional a`: `x = (t.view σ₀).account? a`, `accountReads += a`. `getPreStateAccountOptional a`: `x = (t.block.view σ₀).account? a`.
- `getCode h` (supplied): `getCode_model` gives `(t.view σ₀).code? t.block.consts h = some x` under the initial WF, ModelsLookups and Id success premises. The separate membership law records a provider read when neither write layer holds `h` and `h ≠ emptyCodeHash`.
- `setStorage a k v`: `t'.view σ₀ = (t.view σ₀).setStorage a k v`; `destroyStorage a`: `… .clearStorage a` and `storageReads' = storageReads ∪ {(a,k) | k ∈ dom t.rev.storageWrites[a]}`.
- `setAccount a o` (supplied): the private complete Id view equation keeps
  storage and code and updates only the account map of `t.view σ₀`. It inserts
  the whole account for `some account` and erases the address for `none`.
  Raw application gives this equation for all `σ₀` under the success premise,
  without initial MathState.WF or ModelsLookups.
- `setTransientStorage a k v`: `transient' = transient.insert (a,k) v` (erase if `v = 0`).
- Invariant preservation of `TxRevertible`'s order-list invariant for every write.
- **Progress** [T]: every operation terminates; a read fails only if the provider call it makes fails, or by R15/R19.

The original storage read has four private complete run equations for arbitrary
`Monad m`. The first three return one `pure` with the selected value and the
original transaction. The final equation sequences the retained storage action,
then returns the value and input transaction or the wrapped error. The two public
storage precedence laws required by §7.2 for SSTORE composition remain open.

The private R14 run equation quantifies arbitrary `Monad m` and returns
`pure (.ok ((), t'))` with precisely the paired fields from §3 updated. The
private Id success and frame equations retain the whole block and observation
records, all storage fields and indexes, code writes, clears and transient data.
The raw lookup at `a` is `some o`, including `some none` for a tombstone.
At every other key it is the original lookup.

The optional pre-transaction account action is discharged by these public laws:

| Law | Complete contract |
|---|---|
| `getPreStateAccountOptional_of_block` | Arbitrary Monad: a present block entry returns that exact Option Account and the accountReads insertion, without a provider call. |
| `getPreStateAccountOptional_of_missing` | Arbitrary Monad: a missing block entry gives exactly one retained provider account action, mapping success to the inserted state and error to StateError.witness. |
| `getPreStateAccountOptional_error` | Id: missing block entry and exact provider error imply that exact wrapped failure, with no returned transaction state. |
| `getPreStateAccountOptional_frames` | Id success: complete block and rev plus storageReads, codeReads and createdAccounts remain equal. |
| `getPreStateAccountOptional_mem` | Id success: b is a post account-read member iff b=a or b was a prior member. No raw-set equality or duplicate-insert identity is asserted. |
| `getPreStateAccountOptional_model` | On precisely the initial WF/ModelsLookups/success domain above, the answer is the account observer of the initial transaction's block view. |

The defaulted pre-transaction wrapper supplies exactly these five public laws:

| Law | Complete contract |
|---|---|
| `getPreStateAccount_action` | Arbitrary Monad: literal bind over the optional action once, mapping `.ok (o,u)` to `pure (.ok (o.getD (emptyAccount t.block.consts),u))` and `.error e` to `pure (.error e)`. No Monad algebra or generic-effect interpretation is assumed. |
| `getPreStateAccount_error` | Id: missing block entry and exact retained provider failure imply that exact StateError.witness payload, without a returned state. |
| `getPreStateAccount_frames` | Id success: complete block and rev plus storageReads, codeReads and createdAccounts remain equal. |
| `getPreStateAccount_mem` | Id success: post account-read membership iff the queried address or previous membership. No raw duplicate-insert identity. |
| `getPreStateAccount_model` | Exactly the initial WF/ModelsLookups/success domain above: `account = ((t.block.view σ₀).account? a).getD (emptyAccount t.block.consts)`. |

The current optional action supplies exactly these six public laws:

| Law | Complete contract |
|---|---|
| `getAccountOptional_of_tx` | Arbitrary Monad: a transaction entry returns that exact Option Account and once-marked state, including tombstones, suppressing block/provider work. |
| `getAccountOptional_of_missing` | Arbitrary Monad: a transaction miss equals the complete getPreStateAccountOptional action on the once-marked state. Its second insertion and literal underlying effects remain intact. |
| `getAccountOptional_error` | Id: transaction and block misses plus exact provider error imply that exact StateError.witness payload, with no returned state. |
| `getAccountOptional_frames` | Id success: complete block/rev and storageReads/codeReads/createdAccounts remain equal, without WF or provider premises. |
| `getAccountOptional_mem` | Id success: b is a post account-read member iff b=a or b was a prior member; no raw duplicate-insert identity. |
| `getAccountOptional_model` | Exactly the initial MathState.WF/ModelsLookups/success domain above: account equals `(t.view σ₀).account? a`, using public TxState.view_account?_eq and the pre-transaction model law. |

The standalone R27 action sets the block cursor to the supplied offset
when absent and to the greater of the old and new offsets otherwise. The
private run equation has one underlying `pure` of the complete successful
result. A second private equation recovers the original transaction by
substituting its old cursor into that result. Caller history bounds and
actual runner rollback compose separately.

The defaulted current-account wrapper supplies exactly these five public laws:

| Law | Complete contract |
|---|---|
| `getAccount_action` | Arbitrary Monad: literal bind over getAccountOptional once, mapping `.ok (o,u)` to `pure (.ok (o.getD (emptyAccount t.block.consts),u))` and `.error e` to `pure (.error e)`. No LawfulMonad or generic-effect interpretation. |
| `getAccount_error` | Id: transaction and block misses plus the exact retained provider failure imply that exact StateError.witness payload, with no returned transaction state. |
| `getAccount_frames` | Id success: complete block and rev plus storageReads, codeReads and createdAccounts remain equal. |
| `getAccount_mem` | Id success: post account-read membership iff the queried address or previous membership. No raw duplicate-insert identity. |
| `getAccount_model` | Exactly the initial MathState.WF/ModelsLookups/success domain above: `account = ((t.view σ₀).account? a).getD (emptyAccount t.block.consts)`. |

Private deployability proofs give the literal `Monad` action and the exact
success and error equations at `Id`. The success result is true exactly when
the account has zero nonce and its full code hash equals
`t.block.consts.emptyCodeHash`. The predicate uses those two fields. The model
proof applies `getAccount_model` under its initial WF, ModelsLookups and
successful-read premises. The same condition then applies to the transaction
view's account with the existing absence default. Concrete source agreement
uses the F20-coherent empty code hash.

The hash-only code action supplies these five public laws.

| Law | Complete contract |
|---|---|
| `getCode_action` | For any Monad, the whole run returns empty bytes and the initial state at the supplied reserved hash, then exact bytes and the initial state on transaction or block hits. Otherwise it inserts the hash and calls the provider once, returning its bytes and the marked state or wrapping its exact error. |
| `getCode_error` | At Id, a nonreserved hash missing from both overlays and an exact provider error yield that error wrapped in `StateError.witness`, with no returned state. |
| `getCode_frames` | At Id success, the complete block and revertible records and the accountReads, storageReads and createdAccounts sets equal their initial values. |
| `getCode_mem` | At Id success, a hash is in the final codeReads iff it was already a member or it is the queried hash, which is nonreserved and missing from both write maps. |
| `getCode_model` | Given initial `MathState.WF`, `ModelsLookups` at the initial constants and provider, and Id success with bytes `code`, `(t.view σ₀).code? t.block.consts h = some code`. |

The transient storage read supplies one complete action law for every raw
`t : TxState m` and `[Monad m]`. The law has no initial-state or provider premise.

| Law | Complete contract |
|---|---|
| `getTransientStorage_action` | `((getTransientStorage a k).run t).run` equals `pure (.ok ((t.rev.transient[(a, k)]?).getD U256.zero, t))`. The base action is a single `pure` and returns the entire original state. |

The transient storage write supplies the R23 action on every raw transaction
state with Monad alone. Its private complete run equation returns unit and
the transaction state with just the selected `rev.transient` entry updated,
under a single `pure`. Replacing that map with the original map reconstructs
the complete original state. Private lookup laws give absence for an erased
key, the supplied word for an inserted key and the original lookup for every
distinct key. These equations use the supplied key comparison and have no
provider, well-formedness or observation premise.

The private `accountExists` action equation uses only Monad. It binds the optional
action once and tests presence in the successful pair. At Id the exact result
equation maps only the value and preserves the complete state or error. Under
the same initial WF, ModelsLookups and optional-success premises, the Boolean
equals `((t.view σ₀).account? a).isSome`.

Private controls for `accountExistsAndIsEmpty` and `isAccountAlive` check a
literal bind over one `getAccountOptional` action for arbitrary Monad. An
error propagates unchanged. Success preserves the complete returned state
and classifies presence with the retained block constants. At Id, the same
constants are present in the input block by `getAccountOptional_frames`.
Under the initial WF, ModelsLookups and successful lookup premises above,
the private model controls classify `(t.view σ₀).account? a` with those
constants. Exactly one predicate holds for each present account.

### 7.2 Derived laws (proved once on the model, D25) [C], [R]

- **Transaction account observation (supplied):** `TxState.view_account?_eq` gives
  `(t.view σ₀).account? a = match t.rev.accountWrites[a]? with
  | some account => account | none => (t.block.view σ₀).account? a` on every raw
  input and arbitrary m, without any class or validity premise. This is the only
  public transaction-view law, for the `getAccountOptional_model` consumer.
  Whole construction/application, metadata, other observers and support stay private.
- **Read-after-write:** `setStorage a k v; getStorage a k` returns `v`; same for accounts and code writes. The transient instance is supplied privately at Id on every raw state: a read after `setTransientStorage a k v` returns `v` and the complete written state. The proof uses the existing action equation for `getTransientStorage`.
- **Frame:** a write to `(a,k)` leaves `getStorage a' k'` unchanged for `(a',k') ≠ (a,k)`; writes never change `getStorageOriginal`.
- **Clear suppression:** after `destroyStorage a`, `getStorage a k = 0` until `(a,k)` is written again in the same transaction; later writes are visible. At block level: a transaction clear hides all earlier block writes of `a`, and later transactions see only the post-clear writes.
- **Storage precedence** (R11) and **original precedence** (R12) as the two separate public laws ARCHITECTURE §5.3 requires; `created ⇒ original = 0`.
- **Snapshot/revert:** R24 saves and restores the complete `rev`. Private clients
  verify that any restore keeps the current `obs` and `block` unchanged. In
  particular, `createdAccounts` and `block.oldestAncestorOffset` survive it.
  Monotonicity across sequences of other tracker operations remains a separate
  obligation.
- **Split invisibility:** for every EELS operation, projecting (`rev`, `obs`, `block`) back to an EELS `TransactionState` gives the EELS result [R].
- **Lifecycle:** `(incorporateTxIntoBlock t).1.view σ₀ = t.view σ₀` (the transaction view becomes the block view); transient storage and `createdAccounts` are empty in the returned transaction state; block read sets are the unions. This rests on `(σ.apply d₁).apply d₂ = σ.apply (d₁.merge d₂)`.
- **Diff law:** `BlockState.apply_extractBlockDiff` discharges exactly
  `σ₀.apply (extractBlockDiff b) = b.view σ₀` definitionally, for every raw σ₀/b
  and arbitrary m without class premises. The separate
  `BlockDiff.WF σ₀ (extractBlockDiff b)` target remains open (§7.4).
- **Observation laws for the BAL and witness:** every `(a,k)` whose pending transaction write is dropped by `destroyStorage` is in `storageReads` from then on (write→read conversion; a write dropped by `restoreTxState` leaves no read, R24); every account written through `modifyState` was read in the same transaction.

### 7.3 Pre-state contract obligations

- [C] `ModelsLookups consts ps σ₀` concerns one fixed record/provider and is *used* by every read equation above; it does not quantify a provider's answers over unrelated records.
- [R] Callers never see `PreState` internals; backends prove full binary `Models` (`EthStateCommit`), plus progress (ARCHITECTURE §5.3). Its lookup conjunct supplies the contextual premise when the execution record is coherent with the concrete Id record. An always-error provider satisfies `ModelsLookups consts ps σ₀` vacuously; `errors_vacuous` in `ModelsLookupsGuards.lean` proves this for arbitrary raw states, errors and root functions, distinguishing agreement from progress.

### 7.4 Invariants exported to other libraries

- **Bounded structural contract (Q58; supplied).** `BlockDiff.StructuralPremises σ₀ d` consists exactly of (i) every raw deletion tombstone clearing storage, and (ii) a present post-account at every raw `storageChanges` address. Raw presence includes empty patches and explicit zero writes. For every finite raw σ₀ and d, initial `MathState.WF σ₀` plus these premises suffices for `MathState.WF (σ₀.apply d)`. Metadata, code bytes and account fields are arbitrary. The premises are sufficient, not necessary: deleting an account with no initial storage can preserve WF without a clear; an empty patch at an absent account violates (ii) even when the output has no storage there.

Exactly five ordinary structural laws are supplied in `State/Structural.lean`.
The signatures below summarize their contract without reproducing Lean proofs:

```lean
theorem BlockDiff.structuralPremises_iff (σ : MathState) (d : BlockDiff) :
  BlockDiff.StructuralPremises σ d ↔
    (∀ a : Address, d.accountChanges[a]? = some none → a ∈ d.storageClears) ∧
    (∀ a : Address, d.storageChanges[a]?.isSome = true → (σ.apply d).account? a ≠ none)
theorem BlockDiff.structuralPremises_storage_clear (σ : MathState) (d : BlockDiff)
    (hp : BlockDiff.StructuralPremises σ d) (a : Address)
    (hd : d.accountChanges[a]? = some none) : a ∈ d.storageClears
theorem BlockDiff.structuralPremises_account_present (σ : MathState) (d : BlockDiff)
    (hp : BlockDiff.StructuralPremises σ d) (a : Address)
    (hs : d.storageChanges[a]?.isSome = true) : (σ.apply d).account? a ≠ none
theorem MathState.wf_apply_of_structuralPremises (σ : MathState) (d : BlockDiff)
    (hwf : MathState.WF σ) (hp : BlockDiff.StructuralPremises σ d) :
    MathState.WF (σ.apply d)
theorem BlockDiff.structuralPremises_congr_effects (σ : MathState) (d e : BlockDiff)
    (ha : d.accountChanges = e.accountChanges) (hs : d.storageChanges = e.storageChanges)
    (hc : d.codeChanges = e.codeChanges) (hcl : d.storageClears = e.storageClears) :
    BlockDiff.StructuralPremises σ d ↔ BlockDiff.StructuralPremises σ e
```

- **Full diff WF remains open.** `BlockDiff.WF σ₀ d` [C] requires the structural clauses above and account, storage-address and per-address slot lists enumerating raw write domains without duplicate actual keys. Account enumeration includes tombstones, storage-address enumeration includes empty patches, and slot enumeration includes zero writes. The optional `storageSlotOrder` map's missing/extra-entry policy remains unspecified; no defaulted or exact-domain completion is selected by Q58. Enumeration also does not establish actual first-live-write history (§7.5). Reachable extraction must establish full WF separately; EELS `set_account(..., None)` alone does not clear storage or read the account. Neither StructuralPremises nor full static WF proves the history condition below.
- `AccountWritesLookedUp` [R] (R32): every address in `accountChanges` was the argument of a successful `preState.getAccount?` call during the block. As a Lean statement it is the equivalent observable property "every address in `b.accountWrites` is in `b.accountReads` and its first read fell through to the provider"; it is stated over an instrumented execution in the proof library, since a pure provider cannot record calls.

### 7.5 Internal order-index laws and State order

The implemented internal `WriteOrder` contract has fourteen ordinary laws. Raw
laws require only Ord/TransOrd; lawful laws additionally require LawfulEqOrd on
actual K equality. All finite `WF` records are admitted, including huge/gapped
positions; no density, counter-width, key-width or whole-State reachability
premise is imposed. Malformed and nonlawful records retain their concrete raw
behavior, without repair or a universal lawful list claim.

| Laws | Exact component claim and hypotheses |
|---|---|
| `toList_empty`, `wf_empty` | Raw empty traversal is [] and both WF clauses hold |
| `record_of_present`, `erase_of_absent` | Raw optional lookup some p / none implies exact whole-record no-op |
| `next_record`, `next_erase` | Raw counter is if forward isSome then next else next+1 / unchanged |
| `wf_record`, `wf_erase` | Lawful + WF implies WF after the operation |
| `mem_toList_iff`, `toList_nodup` | Lawful + WF: membership iff forward isSome=true; no duplicate actual keys |
| `toList_record` | Lawful + WF: if forward isSome then retain list else append [k] |
| `toList_erase` | Lawful + WF: exactly `(toList r).filter (fun a => compare k a != .eq)` |
| `agrees_record_insert` | Lawful + Agrees r writes: Agrees (record r k) (writes.insert k v), arbitrary V, no WF |
| `agrees_erase_erase` | Lawful + Agrees r writes: Agrees (erase r k) (writes.erase k), no WF |

`WF` and `Agrees` are separate: a tombstone None and a zero payload remain
present writes. The two maps and next must be saved with the associated write
root; selecting a saved version can lower next relative to a discarded child.
Whole inner clear discards that inner index. Later recreation starts empty.
The standalone clear supplies the private equations below. The remaining
integration laws cover slot recreation, snapshots and incorporation.

For `destroyStorage a` (R16), the private run equation returns the updated
transaction and unit with one underlying `pure`. If the target patch is absent,
the original read set is returned. If it is present, the action folds over that
patch to insert every key. The executable takes the read set from the transaction
before the fold so the fold can reuse exclusive buckets. A private ordinary
equality identifies the whole result with the record-update reference (D25).
For any `(b, k)`, membership in the resulting reads
holds exactly when it was already present or `b = a` and `k` occurs in the
original patch. These facts use no order premise.

The other private equations give the whole erased patch and slot maps, the
address index after `WriteOrder.erase`, and the clear set after insertion.
They give absence of the two target entries and membership in the clear set.
The complete block, account and code writes, account index, transient writes
and other observations are retained. For the address index alone, its prior
`WF` and `Agrees` with the prior storage map imply `WF` and `Agrees` with
the resulting storage map.

For `destroyAccount a` (R17), the private literal run equation binds the
result of the clear first and passes its complete successful transaction to
the account write. At Id, the resulting transaction has the R16 storage
updates and the R14 tombstone and account order update. The complete block,
other account and storage entries, code writes, transient storage, account
and code reads, and creation marks are retained. Storage reads include
exactly the original observations and the target's pending slot keys.
Account and storage-address indexes preserve their prior `WF` and `Agrees`
under the corresponding local premises. Restoring the entry snapshot
restores all revertible fields and keeps the reads recorded by destruction.

For `modifyState a f` (R18), the literal Monad action runs the
defaulted lookup before applying the callback. At Id, a failed
provider read or callback returns the exact StateM error. After a
successful callback, the complete transaction from the lookup is passed
to the write. The second, current emptiness read observes the just-written
account through the transaction overlay and needs no additional provider
call. It uses the supplied block constants. The nonempty branch keeps that
transaction. The empty branch passes it to R17, which records the tombstone
and observes the dropped pending slots. The existing R24 restore then
reinstates the saved revertible record and retains the observations.
The source records the first account read before a callback exception.
The existing Lean StateM error result carries only the nominal error.

For the balance-preserving clear, the literal Monad action passes the
transaction returned by R16 to the actual R18 update. Its callback keeps
the balance and resets the nonce and hash with the empty-code hash
supplied in the input block. The resulting account is empty exactly when
its retained balance is zero. R18 owns the second storage clear and
tombstone in that case. The Id equation propagates the reached nominal
error after the completed R16 action. The original source retains its
first clear and observations in place. On successful Lean execution,
R24 restores the complete saved revertible record and retains the
observations recorded by R16 and R18.

- Preserve account first-write order, storage-address order, and each slot's first-write order. `record` appends a new key and leaves an existing key in place. Clearing storage removes that address's pending writes and both storage order indexes, converts dropped transaction writes into reads, and resets subsequent slot order. Incorporation removes cleared block entries before folding new transaction writes in their recorded order. Snapshots restore all three indexes with the writes; extraction emits forward-order lists once. `MathState.apply` forgets replay order, but operational witness refinement cannot. `BlockDiff` carries **no clear order**, so the witness root replay's iteration over `storageChanges ∪ storageClears` (a Python set; `EthStateWitness` W6 step 3) is **open (F7)**: prove that step-3 rewrites commute, including failures and observations, or add a clear order to `BlockDiff`. A prototype's traversal is not adopted, and a first-clear order alone does not reproduce Python set iteration. Independence of insert/delete group order is not assumed.

### Informal correctness argument

**Claim.** For reachable execution traces, overlay operations refine the reference's state lifetimes, preserve observations across rollback, and extract a diff with the ordering and invariants required by the backends.

**Premises.** Initial structural well-formedness and `ModelsLookups` for the fixed initial supplied record/provider (§7.1); successful provider answers where requested; the caller protocol that reads accounts before changing them; invariant-preserving storage/account updates; ordered-container observer laws.

**Argument.** Induct on the sequence of state operations. A lookup first checks the top overlay; a storage clear suppresses every lower layer, including the pre-state. Each branch therefore has the specified logical value. A write records its first live position using WriteOrder; repeated writes update only the value, while clearing storage removes its write positions and converts pending writes to observations. Snapshots retain precisely TxRevertible, so restoring them reverts writes, clears, order metadata and transient storage but leaves TxObs intact. Incorporation applies clears before the recorded incoming writes and keeps the block's first-write positions. Induction on these ordered folds establishes the extracted diff equation and each list/map consistency invariant. For Q58's separate raw structural claim, zero writes erase slots and touched empty maps are pruned; untouched maps retain initial WF. Changed-storage addresses have post-accounts by clause (ii); at an untouched, uncleared storage address, clause (i) rules out account deletion. This establishes the three structural WF clauses without metadata or code assumptions. The separate read-before-write induction is on callers' reachable traces: raw setAccount does not establish it by itself.

**Open obligations.** Formalise reachability, every caller's read-before-write and balance preconditions, and storage-order metadata through all clear/restore/merge paths. An arbitrary raw diff or raw deletion need not satisfy BlockDiff.WF. Snapshot persistence requires worst-case bounds independently of these semantic laws.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Internal support supplied:** `WriteOrder` and its component laws (§7.5); actual Address/Bytes32 clients use EthBase's lawful comparison and byte inverse seams. Future consumers preserve WF and Agrees together and use ordered State observers; no external overlay seam is supplied by this component.
- **Depends on:** `EthBase`
- **Used by:** `EthVmCore` (and through it the instructions, precompiles and runner), `EthStateCommit`, and transitively `EthBlock`, the backends and the guest.
- **Mathematical block view supplied:** the view and its exact application equation
  compose existing public operations on every raw input (§3/§7.2). Complete private
  public-law clients and finite model controls add no tracker/WF/history/replay,
  provider/progress, D5/F20 or resource/readiness guarantee.
- **Mathematical transaction view supplied:** §3/§7.1/§7.2 supplies the class-free
  composition and only its account observer law. Callers use that law; the raw
  conversion and all other construction/support facts remain owner-private.
  Finite complete model controls supply no operational or readiness refinement.
- **Raw extraction supplied (Q85):** the class-free operation and seven complete equations are in §3/§7; full ordered-write integration/WF/history remains separate.
- **Raw transaction assembly supplied:** TxState and the exact StateM alias are
  owned by §3/§5/§7. Their private complete clients supply no tracker operation or
  rollback/lifetime proof or current-pin full-state agreement.
- **Seams provided:** the `PreState` record (the block-execution seam, ARCHITECTURE
  §2); `StateM` operations with model laws for opcode proofs; the supplied raw
  `extractBlockDiff` (Q85) for `EthBlock` (state root, BAL, witness generation),
  with reachable WF/history separate. The two supplied class-free logical block read
  views and membership iff laws provide exact raw account/storage membership; BAL
  construction/sorting and tracker observation accumulation remain separate.
- **Constants context (F20).** `BlockState.new` preserves the supplied record:
  `(BlockState.new ps consts).consts = consts`. State operations read it through their
  existing `TxState`/`BlockState` context; they receive no parallel constants argument.
  Pure helpers without that context (`emptyAccount`, `MathState.code?`) retain their
  necessary data parameter and EELS-named local notation. The constructor equality is
  supplied as BlockState.new_consts, for arbitrary m and constants without a class
  premise. The pre-transaction and current optional account framing laws retain
  the complete block context. The standalone R22 marker retains that context
  (§7). Caller acquisition and coherence and other context-preservation
  obligations remain open.
- **Relies on:** execution's supplied `consts` and `ps : PreState Id` satisfy `ModelsLookups consts ps σ₀` for an appropriate structurally WF σ₀. Concrete full `Models ps σ₀` supplies this lookup premise when the execution record is coherent with its concrete Id record; the provider-factory type alone does not establish F20 coherence. `EthBase` supplies checked `U256` add/sub, lawful `compare` on `Address`/`Bytes32`/`Hash32` keys (D2), the orderings for `(Address × Bytes32)` keys and `LawfulEqCmp Address` (F19), and the `HashConsts` record (R2).
- **Guarantees:** the laws of §7; `BlockDiff.WF` and `AccountWritesLookedUp` for `EthStateCommit`/`EthStateWitness`; the first-write order in `BlockDiff.accountOrder`.
- **Ordering contract with `EthBlock`:** `update_builder_from_tx` runs on the unmerged states immediately before `incorporateTxIntoBlock` (R25(1)); `EthState` does not import the builder.

## 9. Open decisions

- D2 (key representation): `compare` cost on `Address`, `Bytes32`, `Hash32` and on the pair key `(Address × Bytes32)` of transient storage and read sets. The orderings themselves are defined in `EthBase` (F19, adopted).
- D5 (broad scope, monad-parametric): `PreState m`, `StateM m`; `emptyCodeHash` from `HashConsts` (R2, R7). Open: the `ModelsLookups` coupling at generic `m`.
- D8 (accepted): all provider results are `Except WitnessError`; R30 forbids defaulting.
- D9 (accepted; revised by B2 and D5): `PreState m` is a record; `getCode` returns `m (Except WitnessError ByteArray)` (R9).
- D16 (accepted): no commitment imports; `emptyCodeHash` arrives as `HashConsts` data (R2).
- D18 (accepted): the `HashSet` observation sets are used linearly and have expected O(1) bounds, which is performance-appropriate for never-reverted sets (D23). Adversarial hash collisions are a known expected-bound caveat; record them if a workload shows them.
- D22 (accepted): persistent trees for `TxRevertible`; a journal later only by replacement.
- D23 (accepted): observation sets and `createdAccounts` outside the snapshot; `oldestAncestorOffset` joins them (it is on `BlockState` in EELS but written during transactions).
- D25 (accepted): model-based laws of §7.
- NEW-STATE-1: resolved: DECISIONS B1 (Q29).
- NEW-STATE-2: resolved: DECISIONS B2 (Q30).
- NEW-STATE-3: resolved: CONTRACT O13 (DECISIONS §3); constructors freeze per B14 (Q31) (R29).
- F7 (open): clear iteration order in the witness root replay (§7.5).
- Q57: supplied-record lookup agreement follows R8/§5/§7.1; full Models stays at the concrete Id interpretation in EthStateCommit. Generic D5/X7 coupling remains open.
- The logical block read views in §3/§5/§7 select no new set/order policy;
  decidability, enumeration and additional consumers are outside their two-law API.
- Q84: canonical Base observation-key dictionaries and the unchanged raw Std field handoff are in §5/§7. Raw TxObs, BlockState and TxState/StateM are supplied separately (§3);
  tracker operations, lifetimes, ownership and costs remain separate obligations.
- F20: initialization supplies only the explicit new_consts law; a broader stable
  consumer-law basis requires a named consumer and separate contract review. Acquisition,
  coherence and preservation through future contexts/operations remain open.
- Mathematical BlockState.view follows the existing §5/§7.2 composition; its
  supplied equation selects no new domain or policy. Full WF/history and operational
  witness agreement remain separate.
- Mathematical TxState.view follows the existing §5/§7.1 composition. Its private
  direct metadata transport selects no public normalization policy or new Q85
  disposition. The account and code model laws use the transaction view. Additional
  observer laws need their own consumers.
- Q85: raw extraction follows the §7 direct observer/domain-preserving equations; the disposition is owned by DECISIONS. Full WF, history and F7 remain separate.
- Q58: the bounded structural predicate and laws in §7.4; full optional slot-order-map policy, replay history and reachability remain open.

## 10. Gaps

- **Bounded component support:** §3 records the supplied standalone account reads
  and predicates, code read, storage reads, account write, storage clear, transient
  read and write, snapshot and restore, fresh initialization, creation marker and
  ancestor recording. Sections 4 and 7 give their tests and law domains. Caller
  integration and remaining tracker operations stay open. Account and
  supplied empty-account values, internal
  WriteOrder support, raw MathState with its pure observers and structural WF, raw
  BlockDiff values, raw mathematical application, the raw four-operation PreState
  carrier, coarse nominal WitnessItem/WitnessError and StateError values, the raw
  eight-field TxRevertible carrier, bounded structural preservation, supplied-record
  ModelsLookups, the raw four-field TxObs and thirteen-field BlockState carriers,
  plus block initialization and its explicit F20
  new_consts law, plus logical account/storage read views and their two exact
  membership iff laws, raw extraction and its seven Q85 laws, and the mathematical
  BlockState.view with its exact application equation, mathematical TxState.view
  with its account observer law and private conversion, plus raw three-field
  TxState and the StateM transformer alias, are supplied (§3/§5/§7). The
  owning laws and test rows specify their domains. MathState mutation, diff
  WF/history/reachable preservation, actual provider operations, other contextual
  tracker/full-model proofs, other StateError operation/adapter semantics and freezing,
  witness diagnostic refinement, other tracker effects/errors, ordered-write integration,
  reachability, integration of snapshots with the runner, acquisition/coherence,
  future context preservation and operational source refinement remain open.
  Additional public
  initialization consumer laws await a named consumer and separately reviewed
  contract. The EELS default-empty BlockDiff convenience constructor remains deferred.
  These component contracts do not change whole-State readiness.
- **Raw TxState/StateM boundary:** §3/§4/§5/§7 supplies nominal assembly of the
  complete providers and the exact state/error transformer order, with
  private ordinary wiring clients only. Hash-only codeReads matches the pin;
  current-pin full-state refinement remains open.
  Caller initialization and coherence, the remaining tracker operations,
  observation lifetimes, other StateError semantics and freezing, S1/S2/W1,
  generic D5, F6/F7/F11 and C1–C4 remain open.
- **Raw TxRevertible boundary:** §3/§4/§5/§7 supplies storage and private complete
  clients for the carrier; the separate mathematical transaction view and private
  conversion are supplied in §3/§7.1/§7.2. Standalone initialization and R24
  snapshot and restore are supplied. Caller integration, transient storage
  lifetime (including the transaction-end reset), other tracker
  operations and observations, write/clear/order coupling, Reachable,
  AccountWritesLookedUp, errors/adapters and provider progress remain open.
  TxObs/BlockState's specified HashSet fields use the Q84 canonical Address/Bytes32
  dictionaries (EthBase §3); no replacement dictionary is chosen.
  S1/S2/W1, F6/F7/F11, generic D5 and C1–C4 are not discharged by raw fields or finite
  retained-value controls. Whole-State readiness is unchanged.
- **Order-index integration:** §7.5 supplies the internal `WriteOrder` laws
  and the local laws for R14 account writes, R16 storage clear, R17 account
  destruction and R18 modification. R24 retains saved order and value roots
  together. Incorporation,
  reachable extraction and the coupled WF and Agrees invariants remain open.
  Reachable, AccountWritesLookedUp, S1/S2 and composed C1/C4 remain open.
  Finite retained-version controls leave persistence throughput, host memory
  and zkVM resource gates open.
- **Balance-preserving account clear supplied.** §§3/4/5/7.5 own the
  standalone R16–R18 action and complete local controls. Caller integration,
  production providers and world effects, fault projection and composed
  State invariants remain open.
- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **Account-change order** (R6) is preserved by ARCHITECTURE §5.3 and B1; its refinement proof and a committed account-trie regression input remain outstanding. The order-dependence claim is from reading `incremental_mpt.py:746–790` and `witness_state.py:199–200`; no fixture exercises an account-trie collapse whose success depends on order (`eip8025_optional_proofs/test_witness_state_replay_order.py` covers the storage trie's insert-before-delete order only). A regression input must be built.
- **State errors under O13** (R29): `balanceOverflow` is argued reachable in the ledger from the pinned `U256` semantics [verified by execution] but has no fixture; honest-chain unreachability is an argument, not a proof. `balanceUnderflow` and `storageOnMissingAccount` are unresolved failure-ledger entries. `StateError` cannot be frozen (B14) until they close.
- **Clear order** (F7, open; §7.5): no clear order in `BlockDiff`, and no proof that the witness step-3 iteration is unobservable.
- **Generic-`m` contract:** `ModelsLookups` and the §7 laws are stated at `PreState Id`; their coupling for a generic oracle monad is open (D5).
- **Supplied-record lookup support (Q57):** the R8/§5 definition and ordinary private
  positive/negative guards are supplied (§3/§4). The contextual account law at the
  retained BlockState record is supplied for the pre-transaction and current optional
  account actions (§7.1). The standalone current storage read uses the storage
  clause in its private transaction-view proof. Other contextual reads and
  full-model lookup projection under concrete Id coherence remain open.
  The provider and constants still come from the supplied block context.
- **Bounded structural support (Q58):** StructuralPremises and its §7.4 laws are supplied
  (§3). Full BlockDiff.WF optional slot-order-map missing/extra-entry policy, replay
  history/reachability, AccountWritesLookedUp and F7 remain open.
- **`AccountWritesLookedUp`** (R32) is argued from a grep of `forks/amsterdam/` callers of `set_account`; it needs a Lean statement that is meaningful for a pure provider (currently only an instrumented-execution formulation is sketched) and a proof across system transactions, withdrawals and the throwaway pre-check state (R28).
- **`BlockDiff.WF` (ii)** is an inference; in particular 7702 delegation and creation paths must be checked to never leave storage changes for an absent account.
- **Unreachability of the assertion in R15** is inferred.
- **`WitnessError` granularity:** the coarse constructors here must be refined together with `EthCommit`/`EthStateWitness` and the O4 sub-cases; CONTRACT owns the outcome, EthState owns the shared error type, and EthCommit/EthStateWitness supply the site-specific adapters (D14).
- **Observation-set representation (Q84):** Base's canonical functional key
  support is supplied (EthBase §3). EthState §3 supplies the raw TxObs and
  BlockState carriers and the standalone R22 marker as separate declarations.
  Their nominal TxState/StateM assembly with hash-only codeReads is supplied in §3.
  Actual key distributions, construction/duplicates/resizing/allocation, linear
  ownership, retention and C1–C4 remain unmeasured (ARCHITECTURE §5.0). Sorted BAL
  output remains EthBlock's; the hand-off type and F7 failure/observation replay
  obligations are not settled by support or iteration order.
- **`Std` costs:** `ExtTreeMap` has no proved height/cost theorem; incorporate's merge relies on a fold whose cost is analytical only.
- **Frame accumulators** (warm sets, logs, refunds, `accounts_to_delete`) are *not* in `state_tracker.py` and are specified by `EthVmCore`; the §6 lifetime table's rows for them are not re-checked here.
- **Proof strategy** for the split-invisibility law (§7.2) needs a formal EELS-shaped reference state to compare against; none is planned yet.
- **EEST coverage** of write→read conversion is only indirect (through BAL fixtures); no unit tests exist upstream for `state_tracker.py`.
- **Re-pin to `tests-zkevm@v21.0.6` (GAPS-CROSSCUTTING X16; line citations in this item are at `59c1473d` unless marked).** `apply_body` no longer calls `track_ancestor_access` after the EIP-2935 system call (PR #3657); BLOCKHASH still does, as reflected in R27. `code_reads` and `oldest_ancestor_offset` are read only by the excluded host witness builder (`stateless_host_exec_witness.py`), so the source carrier-shape and ancestor-tracking deltas change no guest output [V by reading].
