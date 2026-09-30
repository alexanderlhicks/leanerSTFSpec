# `EthState`: state semantics, the pre-state contract, transaction and block overlays

*Status: informal specification, draft. Date: 2026-09-30. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F1, F2, F7, F19, F20 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D2, D5, D8, D9, D14, D16, D18, D22, D23, D25 · questions: B1 (Q29/Q36), B2 (Q30), B14 (Q31), F7.*

Line references are to the pinned source under `src/ethereum/` (`state.py`, and `forks/amsterdam/state_tracker.py` abbreviated `st:`). "[verified]" means read in the pinned source and, where marked, executed against the pinned `ethereum_types`/`ethereum_rlp`; "[inference]" means a conclusion from reading that no test or proof yet backs.

## 1. Purpose

`EthState` is the **semantic** state layer (ARCHITECTURE §2, layer L2). It defines accounts, the `PreState` record of lookup operations and its lookup contract `ModelsLookups`, the mathematical state `MathState` and its diff application, the block diff `BlockDiff`, and the two overlays that EELS keeps in `state_tracker.py`: the per-transaction state (split per D23 into a snapshot-reachable revertible component and linearly threaded observations) and the per-block state. It owns the read/write/clear/rollback laws that the VM, SSTORE gas and the BAL builder rely on. It must not see hashed nodes, RLP, roots or witness decoding (D16); the root and code-hash clauses of the contract live in `EthStateCommit` (D20).

## 2. Requirements

### 2.1 Accounts and constants

- R1. `Account` has exactly `nonce : Nat`, `balance : U256`, `codeHash : Hash32` (`state.py:42–49`). The nonce is EELS `Uint` (unbounded); no overflow check exists in the tracker (`st:715–731`). Nonce limits (EIP-2681) are transaction validation, owned by `EthBlock`.
- R2. `emptyCodeHash` is `HashConsts.emptyCodeHash` (`EthBase`; D5, DECISIONS §3): a keccak-derived constant acquired by the caller under F20 through `HashConsts.query` (`EthHash`) and carried in `BlockState.consts`. `EthState` cannot import `EthHash` and never hashes; it receives the record as data. At `m := Id` its value is the literal `0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470` (`state.py:36`, `keccak256(b"")`) [verified value by execution], held in `HashConsts.literals` (`EthBase`); `EthHash` checks that `HashConsts.query` at `Id` yields `HashConsts.literals` (`EthHash` §7). Below, `emptyCodeHash` refers to that field; definition bodies use local EELS notation `EMPTY_CODE_HASH` projected from their constants/state context (F20).
- R3. `emptyAccount consts = {nonce := 0, balance := 0, codeHash := consts.emptyCodeHash}` for `consts : HashConsts` (`state.py:52–56`). A non-existent account (`none`) is distinct from `emptyAccount` (`state.py:12–13`) and every operation must preserve the distinction.

### 2.2 `BlockDiff`

- R4. `BlockDiff` carries `accountChanges : Address → Option (Option Account)` (a change to `none` deletes), `storageChanges : Address → Bytes32 → U256` (a change to `0` deletes), `codeChanges : Hash32 → Bytes`, `storageClears : Set Address` (`state.py:61–89`), plus the three replay orders that B1 requires and the reference carries implicitly as dict insertion order: `accountOrder` (first write of each changed account), `storageAddressOrder` and, per address, `storageSlotOrder` (§5, §7.5). `storageClears` carries no order (F7, open; §7.5).
- R5. **Application order** (`state.py:79–89`; `state_mpt.py:145–161`): for an address in `storageClears` the pre-existing storage is dropped *before* `storageChanges` is applied, so post-clear writes start from empty storage. Account changes and code changes are independent overwrites.
- R6. **Account-change order is observable** [verified by reading, and by executing the pinned `incremental_mpt` on a two-operation example: delete-then-insert raises `HashedNode cannot be witnessed`, insert-then-delete succeeds; not in ARCHITECTURE]. `WitnessState.compute_state_root_and_trie_changes` applies `account_changes` in Python dict iteration order (`witness_state.py:303–309`), with insertions and deletions interleaved, and a deletion that collapses a branch onto an unresolved sibling fails (`incremental_mpt.py:787–797`) while the same deletion after an insertion under that branch does not. The dict order is the order of **first write in the block**: `st:855–856` assigns into `block.account_writes` (existing keys keep their position), and a transaction's `account_writes` is ordered by its first `set_account` (`st:473`; `copy_tx_state`/`restore_tx_state` preserve order, `st:784`, `st:813`). So `BlockDiff` must carry the first-write order of account changes (B1), or the witness backend's accept/reject behaviour differs from EELS. Storage-address and slot orders are preserved too (B1); whether the clear iteration order is observable is open (F7, §7.5).

### 2.3 The `PreState` record and `ModelsLookups`

- R7. `PreState m` is a record of four operations (`state.py:92–139`; D9), generic in the hash monad `m` (D5): `getAccount?`, `getStorage`, `getCode`, `stateRoot`, each returning `m (Except WitnessError _)` (D8). A witness lookup hashes its key, so the pre-state lives in the oracle monad (F1). `EthState` only mentions `m` (`[Monad m]`); it never needs `KeccakQuery`, which stays in `EthHash`. Public entry points use `m := Id`. `getStorage` returns `0` for an unset key (`state.py:108–114`); `getCode` returns the empty byte array for `emptyCodeHash` (`state.py:116–122`); `stateRoot d` computes the post-root without changing the pre-state (`state.py:124–139`): the record is immutable, and `m` carries only keccak queries.
- R8. `ModelsLookups ps σ` is stated for `ps : PreState Id` (D5); the coupling for a generic `m` is open (D5, `EthSecurity`). Every `.ok` answer of `getAccount?`, `getStorage` and `getCode` agrees with `σ`, **including absence** (for accounts, `.ok none` means σ has no account; code has no absent case, R9). Errors are unconstrained (they are the backend's progress obligation, ARCHITECTURE §5.3). The code clause is lookup agreement only; hash agreement (`ModelsCode`) and the root clause (`ModelsRoot`) are in `EthStateCommit`.
- R9. The EELS `get_code` protocol method has **no absent result**: missing code is a `KeyError` in both backends (`state_mpt.py:57`, `witness_state.py:213`). So (B2, adopted 2026-09-28; a revision of D9) `getCode : Hash32 → m (Except WitnessError ByteArray)`. **Missing code is an error; empty code is a successful value** (`emptyCodeHash` ↦ the empty byte array). There is no `.ok none` case.
- R10. The tracker **does not cache pre-state answers**: every read that falls through the overlays calls the provider again (`st:150`, `st:278`, `st:314`, `st:343`). With a deterministic provider (any `PreState Id`), a repeated call returns the same result, so this is a cost question only. The witness provider nonetheless has side effects in EELS (decoding and a storage-root cache); `EthStateWitness` shows they are not observable except through the history condition of R32.

### 2.4 Reads and their observation side effects

Every read returns the value of the **current transaction view** (§7.1) and records observations as follows [verified line by line]:

| Operation (EELS) | Lines | Returns | Observations recorded |
|---|---|---|---|
| `get_pre_state_account_optional` | `st:120–150` | block write, else pre-state (skips tx writes) | `accountReads += a` |
| `get_pre_state_account` | `st:153–184` | as above, `none ↦ emptyAccount` | as above |
| `get_account_optional` | `st:187–210` | tx write, else as `get_pre_state_account_optional` | `accountReads += a` (added twice on fall-through; idempotent) |
| `get_account` | `st:213–238` | as above, `none ↦ emptyAccount` | as above |
| `get_code(h, a)` | `st:241–278` | `""` if `h = emptyCodeHash`; tx code write; block code write; else pre-state | `codeReads += (a, h)` **only** when the pre-state is consulted; no account read |
| `get_storage` | `st:281–314` | precedence R11 | `storageReads += (a, k)` **always**, even when a write answers |
| `get_storage_original` | `st:317–343` | R12 | **none** |
| `get_transient_storage` | `st:346–368` | tx transient value, default `0` | none |
| `account_exists`, `account_deployable`, `account_exists_and_is_empty`, `is_account_alive` | `st:371–450` | predicates over `get_account(_optional)` | `accountReads += a` |

- R11. **Storage precedence** (`st:303–314`): transaction slot write → transaction clear (`0`) → block slot write → block clear (`0`) → pre-state. A clear suppresses only lower layers: writes made after the clear in the same layer remain visible.
- R12. **Original value** (`st:336–343`): `0` if `a ∈ createdAccounts`; otherwise block slot write → block clear (`0`) → pre-state. Transaction writes and clears are skipped. It records no observation.
- R13. `account_deployable` is false iff `nonce ≠ 0` or `codeHash ≠ emptyCodeHash` (`st:395–399`); it does not look at storage. `is_account_alive` is `exists ∧ ≠ emptyAccount` (`st:449–450`).

### 2.5 Writes

- R14. `set_account` (`st:453–473`) writes the transaction layer with **no read** and no storage effect. Setting `none` deletes the account but not its storage.
- R15. `set_storage` (`st:476–500`) first requires `get_account_optional a ≠ none` (an `assert`, which records an account read) and then writes the slot, including `0`. The assert is unreachable from SSTORE [inference: the current target exists while its code runs], but the Lean operation must return `StateError.storageOnMissingAccount` rather than assume it.
- R16. `destroy_storage` (`st:547–568`): every pending transaction write for `a` is first **converted into a storage read** (`storageReads += (a, k)` for each written key), then the address's transaction writes are dropped and `a` is added to the transaction `storageClears`. The read conversion persists even if the clear is later reverted (reads are not snapshotted).
- R17. `destroy_account` = `destroy_storage` then `set_account a none` (`st:503–520`). `clear_account_preserving_balance` = `destroy_storage`, then `modify_state` setting `nonce := 0`, `codeHash := emptyCodeHash` (`st:523–544`); if the balance is zero the result is destroyed by R18.
- R18. `modify_state a f` (`st:620–632`): read `get_account a` (so `none ↦ emptyAccount`), apply `f`, `set_account`, then if `account_exists_and_is_empty a` (a second read) `destroy_account a`. Consequently touching a non-existent account with a zero-value change writes `none` and adds `a` to `storageClears`.
- R19. `move_ether` (`st:635–666`) applies the sender update then the recipient update, each through `modify_state`. The sender update fails if `balance < amount` (`AssertionError`, `st:658–659`). **The recipient update and `create_ether` (`st:669–689`) fail on `U256` overflow**: `ethereum_types` `U256.__add__` raises `OverflowError` [verified by execution]. A wrapping Lean `U256.add` would deviate; the operations must use checked addition and return `StateError.balanceOverflow`. On honest chains this is unreachable (total supply); witness-supplied balances make it reachable, as argued in the failure ledger (maintained outside this repository) (`st:663`, `st:687`), so it is an O13 fault (R29).
- R20. `set_account_balance` and `increment_nonce` go through `modify_state` (`st:692–731`).
- R21. `set_code a code` (`st:734–757`) computes `h = keccak256 code`, records `codeWrites[h] := code` only if `h ≠ emptyCodeHash`, then `modify_state a (codeHash := h)`. In Lean the operation takes the code **and its hash** (ARCHITECTURE §5.3, code-hash ownership); callers compute the hash through `KeccakQuery` (D5: newly installed code hashes) and establish `h = keccak256 code` and `EthStateCommit` owns the agreement law. The order of effects (code write, then the account read/write/possible destroy) must be preserved.
- R22. `mark_account_created` (`st:571–590`) adds to `createdAccounts`, which is **not** reverted (`st:578–580`, `st:791`).
- R23. `set_transient_storage` (`st:593–617`) writes the transaction layer; writing `0` removes the key. Transient storage is keyed by `(Address, Bytes32)` (`st:115–117`) and is part of the revertible component.

### 2.6 Snapshot, revert and lifecycle

- R24. `copy_tx_state` (`st:763–796`) snapshots **exactly** `account_writes`, `storage_writes` (one level deep), `code_writes`, `storage_clears` and `transient_storage`; it **shares** `created_accounts`, `storage_reads`, `account_reads`, `code_reads` and the parent. `restore_tx_state` (`st:799–817`) reinstates exactly those five fields. EELS assigns the snapshot's dicts directly, so a snapshot is used at most once (LIFO); the persistent Lean representation removes that restriction.
- R25. `incorporate_tx_into_block` (`st:823–877`), in this order: (1) the BAL builder is updated from the unmerged transaction and block states (`st:847`, owned by `EthBlock`); (2) the three read sets are unioned into the block's (`st:850–852`); (3) account writes overwrite block writes, keeping first-write order (`st:855–856`); (4) for each transaction clear, the address is added to the block clears **and its block storage writes are dropped** (`st:858–860`); (5) transaction storage writes are merged slot-wise (`st:862–865`); (6) code writes are merged (`st:867`); (7) the transaction state is reset: writes, clears, transient storage and `createdAccounts` emptied, fresh read sets (`st:869–877`).
- R26. `extract_block_diff` (`st:880–900`) returns the block's writes, storage writes, code writes and clears as a `BlockDiff`; EELS aliases the dicts, which is unobservable in Lean.
- R27. `track_ancestor_access b o` (`st:925–946`) sets `oldestAncestorOffset := max`. It writes the **block** state during transaction execution (BLOCKHASH, `vm/instructions/block.py:61`; EIP-2935 at `fork.py:868`), so it is a persistent observation that survives reverts. `get_witness_ancestors` (`st:903–922`) is host-side witness construction; with offset `0` it would return every header (`[-0:]`), but callers only pass offsets ≥ 1 [inference from `block.py:48–62`, `fork.py:868–871`].
- R28. A throwaway transaction state is used for the system-contract code pre-check (`fork.py:732–744`): its observations are discarded, but its pre-state calls still happen, so a witness failure there still rejects the block. The Lean API must allow a transaction state that is never incorporated.

### 2.7 Failure behaviour

- R29. Every operation fails in `StateM m`'s `ExceptT StateError` layer; `StateError` wraps `WitnessError` from the provider and adds `balanceUnderflow`, `balanceOverflow` and `storageOnMissingAccount`. In the guest, all of them become `successful_validation = false` (`stateless.py:303`, `except Exception`). Witness errors are O4 (`STFSpec/informal/CONTRACT.md` §4). The three state errors fall under **O13** (enumerated deterministic reference faults: the existing output, one named constructor each, no catch-all; D14). `balanceOverflow` is argued reachable (R19). `balanceUnderflow` (`st:658–660`) and `storageOnMissingAccount` (the `assert` at `st:497`, R15) are unresolved in the ledger: each keeps its named constructor, and is either shown reachable (an O13 member) or proved unreachable. `StateError` is frozen once this module's ledger entries close (B14).
- R30. Failure must be **propagated, not defaulted**: a failed pre-state lookup must never be turned into "absent" or `0` (D8).
- R31. All operations are non-recursive or structurally recursive, so none has a host-dependent reference site (O12). A static call-graph pass agrees: the call-graph cycles it finds in `state_tracker.py` are name artefacts, not recursion.
- R32. **History condition for the witness root** (cross-module): EELS's witness root uses a storage-root cache filled only by account lookups (`witness_state.py:173–176`, `:301`). The tracker guarantees that every address in `accountChanges` was looked up in the pre-state earlier in the block: `set_account` is reached only from `modify_state`/`destroy_account` (`st:630–632`, `st:519–520`; no other caller in `forks/amsterdam/`), each preceded by `get_account`, and the first write of an address in the block necessarily falls through to `pre_state.get_account_optional` (`st:150`). `EthState` must state and prove this as the invariant `AccountWritesLookedUp` (§7.4); `EthStateWitness` consumes it.

## 3. EELS source map

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `state.py::EMPTY_CODE_HASH` | 36 | `emptyCodeHash` | `HashConsts.emptyCodeHash` (`EthBase`, R2); `Id` value `HashConsts.literals`, checked in `EthHash` |
| `state.py::Account` | 42 | `Account` | nonce `Nat` |
| `state.py::EMPTY_ACCOUNT` | 52 | `emptyAccount` | |
| `state.py::BlockDiff` | 61 | `BlockDiff` | adds the three replay orders (B1) |
| `state.py::PreState` | 92 | `PreState m` | record of operations (D9), generic in `m` (D5) |
| `state.py::PreState.get_account_optional` | 100 | `PreState.getAccount?` | |
| `state.py::PreState.get_storage` | 108 | `PreState.getStorage` | |
| `state.py::PreState.get_code` | 116 | `PreState.getCode` | missing code is an error (B2) |
| `state.py::PreState.compute_state_root` | 124 | `PreState.stateRoot` | contract `ModelsRoot` in `EthStateCommit` |
| `forks/amsterdam/state_tracker.py::BlockState` | 57 | `BlockState` | |
| `forks/amsterdam/state_tracker.py::TransactionState` | 91 | `TxState` = `TxRevertible` + `TxObs` | D23 split |
| `forks/amsterdam/state_tracker.py::get_pre_state_account_optional` | 120 | `getPreStateAccountOptional` | |
| `forks/amsterdam/state_tracker.py::get_pre_state_account` | 153 | `getPreStateAccount` | |
| `forks/amsterdam/state_tracker.py::get_account_optional` | 187 | `getAccountOptional` | |
| `forks/amsterdam/state_tracker.py::get_account` | 213 | `getAccount` | |
| `forks/amsterdam/state_tracker.py::get_code` | 241 | `getCode` | |
| `forks/amsterdam/state_tracker.py::get_storage` | 281 | `getStorage` | |
| `forks/amsterdam/state_tracker.py::get_storage_original` | 317 | `getStorageOriginal` | |
| `forks/amsterdam/state_tracker.py::get_transient_storage` | 346 | `getTransientStorage` | |
| `forks/amsterdam/state_tracker.py::account_exists` | 371 | `accountExists` | |
| `forks/amsterdam/state_tracker.py::account_deployable` | 391 | `accountDeployable` | |
| `forks/amsterdam/state_tracker.py::account_exists_and_is_empty` | 402 | `accountExistsAndIsEmpty` | |
| `forks/amsterdam/state_tracker.py::is_account_alive` | 432 | `isAccountAlive` | |
| `forks/amsterdam/state_tracker.py::set_account` | 453 | `setAccount` | |
| `forks/amsterdam/state_tracker.py::set_storage` | 476 | `setStorage` | |
| `forks/amsterdam/state_tracker.py::destroy_account` | 503 | `destroyAccount` | |
| `forks/amsterdam/state_tracker.py::clear_account_preserving_balance` | 523 | `clearAccountPreservingBalance` | |
| `forks/amsterdam/state_tracker.py::destroy_storage` | 547 | `destroyStorage` (ARCHITECTURE's `clearStorage`) | write→read conversion |
| `forks/amsterdam/state_tracker.py::mark_account_created` | 571 | `markAccountCreated` | |
| `forks/amsterdam/state_tracker.py::set_transient_storage` | 593 | `setTransientStorage` | |
| `forks/amsterdam/state_tracker.py::modify_state` | 620 | `modifyState` | `f` may fail |
| `forks/amsterdam/state_tracker.py::move_ether` | 635 | `moveEther` | checked add |
| `forks/amsterdam/state_tracker.py::create_ether` | 669 | `createEther` | checked add |
| `forks/amsterdam/state_tracker.py::set_account_balance` | 692 | `setAccountBalance` | |
| `forks/amsterdam/state_tracker.py::increment_nonce` | 715 | `incrementNonce` | |
| `forks/amsterdam/state_tracker.py::set_code` | 734 | `setCode` | takes the hash |
| `forks/amsterdam/state_tracker.py::copy_tx_state` | 763 | `copyTxState` (`snapshot`) | O(1) |
| `forks/amsterdam/state_tracker.py::restore_tx_state` | 799 | `restoreTxState` (`revert`) | |
| `forks/amsterdam/state_tracker.py::incorporate_tx_into_block` | 823 | `incorporateTxIntoBlock` | BAL hook in `EthBlock` |
| `forks/amsterdam/state_tracker.py::extract_block_diff` | 880 | `extractBlockDiff` | |
| `forks/amsterdam/state_tracker.py::get_witness_ancestors` | 903 | `getWitnessAncestors` | host-side; generic list slice |
| `forks/amsterdam/state_tracker.py::track_ancestor_access` | 925 | `trackAncestorAccess` | |

`state.py` is claimed item by item above; no item of either file is left unclaimed.

**External semantics.** `ethereum_types.numeric.U256` (add/sub raise on overflow/underflow; the tracker relies on raising, R19), `Uint` (unbounded, `Nat`), `ethereum_types.bytes.Bytes`/`Bytes20`/`Bytes32` (fixed-width constructors, owned by `EthBase`), `ethereum_types.frozen.modify` (functional update of a frozen dataclass: in Lean, record update) and `slotted_freezable` (immutability; no Lean counterpart needed). `EthBase` owns the representations; this module requires checked `U256` addition/subtraction returning `Option`/`Except`.

## 4. Tests

- **EEST fixture areas** (`STFSpec/informal/eest-fixture-index.txt`): `cancun/eip1153_tstore`, `ported_static/stEIP1153_transientStorage` (transient storage, reset per transaction); `cancun/eip6780_selfdestruct`, `amsterdam/eip8246_selfdestruct_no_burn` (created accounts, clears, `clear_account_preserving_balance`); `ported_static/stSStoreTest`, `istanbul/eip2200_net_gas_metering`, `ported_static/stRefundTest` (current versus original values); `ported_static/stRevertTest`, `stZeroCallsRevert`, `stCallCreateCallCodeTest` (snapshot/revert); `spurious_dragon/eip161_state_trie_clearing`, `ported_static/stEIP158Specific` (empty-account destruction in `modify_state`); `ported_static/stCreate2`, `stCreateTest`, `stInitCodeTest` (creation over storage-only accounts); `amsterdam/eip7928_block_level_access_lists` (202 files; persistent observations, write→read conversion); `amsterdam/eip8025_optional_proofs` (witness reads in reverted calls: `test_witness_state_reads.py`, `test_witness_headers.py` for `track_ancestor_access` in reverted calls); `prague/eip2935_historical_block_hashes_from_state`; `shanghai/eip4895_withdrawals` (`create_ether`); `prague/eip7702_set_code_tx` (`set_code`, `get_pre_state_account`); `amsterdam/eip8037_state_creation_gas_cost_increase`, `eip8038_state_access_gas_cost_increase`.
- **EELS unit tests:** none target `state_tracker.py` at the pin. `tests/json_loader/test_optimized_state.py` (`test_storage_key`, `test_resurrection`) concerns an older optimized state and is not normative here.
- **`core` `#guard` cases** (typical, edge, adversarial), over a `PreState` built from a small `MathState`:
  - precedence ladder: each of the five layers answering in turn; write after clear in the same transaction; block clear with a transaction write; transaction clear over a block write;
  - original value: created account returns `0` although the pre-state has a value; block clear returns `0`; transaction writes ignored; no storage read recorded;
  - `destroyStorage` after two writes: both keys appear in `storageReads`; after revert, the writes return but the reads stay;
  - `modifyState` on a non-existent account with a zero change: account change `none` and a clear;
  - `moveEther` insufficient balance and recipient overflow at `2^256 − 1` both fail;
  - `setCode` with empty code: no code write, `codeHash = emptyCodeHash`;
  - `getCode` reads recorded only when the pre-state answers; `getCode` of `emptyCodeHash` never calls the provider (use an always-error provider);
  - snapshot/revert nested three deep, with observations monotone;
  - `incorporateTxIntoBlock` of a transaction that cleared an address with block writes: the block writes vanish, post-clear writes survive; first-write order of `accountOrder` preserved when a later transaction rewrites an early address;
  - an always-error provider: every fall-through read fails and no read defaults (R30).
- **Property tests:** random operation sequences against the reference model of §7.1 (the commuting equations as executable checks); snapshot/revert against a naive deep-copy implementation; differential comparison with EELS `state_tracker` through a Python harness on random sequences (bug-finding only).

## 5. Interface

Reference field order, widths and inherited records are catalogued in [REFERENCE-RECORDS](../REFERENCE-RECORDS.md), generated from the exact pin. Wire-schema owners must use those layouts and prove their codec instances. Runtime records may use the explicit abstraction below; omitted fields or `…` remain implementation blockers, not implicit freedom to choose semantics.

All public unless marked internal. `Except` failures use `StateError`.

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
  accountOrder   : List Address                 -- first-write order, no duplicates (B1)
  storageChanges : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)
  storageAddressOrder : List Address             -- first appearance after the last removal
  storageSlotOrder : Std.ExtTreeMap Address (List Bytes32) -- per-address first-write order
  codeChanges    : Std.ExtTreeMap Hash32 ByteArray
  storageClears  : Std.ExtTreeSet Address        -- no clear order (F7, open)

-- D5: generic in the hash monad; EthState needs only [Monad m], never the hash-query class of EthHash
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
def BlockDiff.WF (σ) (d) : Prop       -- §7.4
def ModelsLookups (ps : PreState Id) (σ : MathState) : Prop          -- R8; generic-m coupling open (D5)

-- Internal persistent order index: replacing it changes only this component's laws.
structure WriteOrder (K : Type) [Ord K] [Std.TransOrd K] where
  next : Nat
  positions : Std.ExtTreeMap K Nat
  keysByPosition : Std.ExtTreeMap Nat K
def WriteOrder.empty : WriteOrder K
def WriteOrder.record : WriteOrder K → K → WriteOrder K -- existing key keeps its position
def WriteOrder.erase : WriteOrder K → K → WriteOrder K
def WriteOrder.toList : WriteOrder K → List K           -- ascending position, not sorted key

-- overlays (D22 persistent trees; D23 split)
structure TxRevertible where          -- snapshot-reachable, worst-case persistent
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
  codeReads      : Std.HashSet (Address × Hash32)
  createdAccounts : Std.HashSet Address
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
  codeReads     : Std.HashSet (Address × Hash32)
  oldestAncestorOffset : Option Nat
structure TxState (m : Type → Type) where
  block : BlockState m                 -- only trackAncestorAccess writes it during a transaction
  rev   : TxRevertible
  obs   : TxObs
abbrev StateM (m : Type → Type) := StateT (TxState m) (ExceptT StateError m)

def BlockState.new (ps : PreState m) (consts : HashConsts) : BlockState m
def TxState.new (b : BlockState m) : TxState m

-- reads (R10–R13)
def getPreStateAccountOptional (a : Address) : StateM m (Option Account)
def getPreStateAccount (a : Address) : StateM m Account
def getAccountOptional (a : Address) : StateM m (Option Account)
def getAccount (a : Address) : StateM m Account
def getCode (codeHash : Hash32) (a : Address) : StateM m ByteArray
def getStorage (a : Address) (k : Bytes32) : StateM m U256
def getStorageOriginal (a : Address) (k : Bytes32) : StateM m U256
def getTransientStorage (a : Address) (k : Bytes32) : StateM m U256
def accountExists (a : Address) : StateM m Bool
def accountDeployable (a : Address) : StateM m Bool
def accountExistsAndIsEmpty (a : Address) : StateM m Bool
def isAccountAlive (a : Address) : StateM m Bool
-- writes (R14–R23)
def setAccount (a : Address) (acc : Option Account) : StateM m Unit
def setStorage (a : Address) (k : Bytes32) (v : U256) : StateM m Unit
def destroyStorage (a : Address) : StateM m Unit
def destroyAccount (a : Address) : StateM m Unit
def clearAccountPreservingBalance (a : Address) : StateM m Unit
def markAccountCreated (a : Address) : StateM m Unit
def setTransientStorage (a : Address) (k : Bytes32) (v : U256) : StateM m Unit
def modifyState (a : Address) (f : Account → Except StateError Account) : StateM m Unit
def moveEther (src dst : Address) (amount : U256) : StateM m Unit
def createEther (a : Address) (amount : U256) : StateM m Unit
def setAccountBalance (a : Address) (amount : U256) : StateM m Unit
def incrementNonce (a : Address) : StateM m Unit
def setCode (a : Address) (code : ByteArray) (codeHash : Hash32) : StateM m Unit   -- caller: codeHash = keccak256 code
-- snapshots and lifecycle (R24–R28)
def copyTxState (t : TxState m) : TxRevertible                         -- snapshot
def restoreTxState (snap : TxRevertible) : StateM m Unit               -- revert
def incorporateTxIntoBlock (t : TxState m) : BlockState m × TxState m      -- BAL hook runs before, in EthBlock
def extractBlockDiff (b : BlockState m) : BlockDiff
def trackAncestorAccess (offset : Nat) : StateM m Unit
def getWitnessAncestors (headers : List ByteArray) (offset : Option Nat) : List ByteArray

-- model views (public, for laws)
def BlockState.view (σ₀ : MathState) (b : BlockState m) : MathState   -- σ₀.apply (extractBlockDiff b)
def TxState.view (σ₀ : MathState) (t : TxState m) : MathState         -- (b.view σ₀).apply t.rev.asDiff
def TxState.originalAt (σ₀) (t) (a) (k) : U256
def TxRevertible.asDiff (r : TxRevertible) : BlockDiff               -- internal
def BlockDiff.merge (d₁ d₂ : BlockDiff) : BlockDiff                  -- incorporate's rule, R25
-- Read-only BAL views; they expose source semantics, never container layout.
def preTxAccount (t : TxState m) (a : Address) : m (Except StateError (Option Account))   -- falls through to the pre-state
def preTxStorage (t : TxState m) (a : Address) (k : Bytes32) : m (Except StateError U256)
def TxState.accountWritesInOrder : TxState m → List (Address × Option Account)
def TxState.storageWritesInOrder : TxState m → List (Address × List (Bytes32 × U256))
def BlockState.accountReadSet : BlockState m → Set Address
def BlockState.storageReadSet : BlockState m → Set (Address × Bytes32)
```

## 6. Data structures

| Type | Representation | Model | Abstraction | Invariant | Persistence | Complexity |
|---|---|---|---|---|---|---|
| `Account` | structure | itself | identity | — | value | O(1) |
| `BlockDiff` | `ExtTreeMap`s + account/address/slot order lists | final writes together with replay order | lookup values and ordered iteration | each list enumerates its map's domain exactly once; slot order restarts after a clear | read-only after extraction | build O(n log n) |
| `WriteOrder K` | two persistent `ExtTreeMap`s and a `Nat` counter | duplicate-free list of keys | `toList` in position order | maps are inverse bijections; every position is `< next`; domain equals the associated write map | snapshot-reachable | record/erase O(log n), list extraction O(n); no linear list filtering per clear |
| `MathState` | nested `ExtTreeMap`s | finite maps with defaults | `account?`, `storageAt`, `code?` | `WF` | value | O(log n) lookups |
| `TxRevertible` | nested persistent `ExtTreeMap`/`ExtTreeSet` (D22) | a `BlockDiff` layered over the block view, plus transient map | `asDiff`, `transient` | WriteOrder observers enumerate live first writes for accounts, storage addresses and slots; clears ⊆ addresses; inner maps are post-clear writes only | **snapshot-reachable: worst-case persistent** | read O(log A + log S); write O(log A + log S) path copy; snapshot O(1); revert O(1) plus reclamation of the discarded version; `destroyStorage` O(s) for `s` pending writes of that address |
| `TxObs` | `Std.HashSet`s | finite sets | `toList` as sets | monotone within a transaction | **linear-only** (never inside a snapshot, D23) | insert expected O(1) (not worst-case, ARCHITECTURE §5.0); merge O(m) |
| `BlockState` | as `TxRevertible` plus read sets and `oldestAncestorOffset` | a `BlockDiff` over σ₀ plus observation sets | `extractBlockDiff`, sets | as above; storage writes of a cleared address are post-clear only | linear between transactions; read-only (shared) during one | incorporate O(w · log n) for `w` transaction writes; `Std` `union` caveat (ARCHITECTURE §5.0): implement by folding the smaller transaction map, not `mergeWith` over the block map |

Observation sets could become `TreeSet`s if `EthBlock` needs sorted output directly; the BAL builder sorts separately (ARCHITECTURE §5.6). EELS's `copy_tx_state` deep-copies all writes (O(n) per call frame); the persistent representation makes it O(1), which is the performance motivation for D22.

## 7. Contract and laws

### 7.1 Model and commuting equations

Fix σ₀ with `MathState.WF σ₀` and `ModelsLookups ps σ₀` (so the laws are stated at `m := Id`, R8). The model of a transaction state `t` is the triple (`t.view σ₀`, `t.originalAt σ₀`, `t.rev.transient`) together with the observation sets. Define `TxRevertible.asDiff` as the diff whose clears are `storageClears` and whose changes are the writes; then **both layers use the same `apply`**, and R11 is a consequence of the definition of `apply` rather than a separate axiom. Per operation, under success (`op t = .ok (x, t')`) [C]:

- `getStorage a k`: `x = (t.view σ₀).storageAt a k`, `t'.rev = t.rev`, `t'.obs.storageReads = t.obs.storageReads ∪ {(a,k)}`.
- `getStorageOriginal a k`: `x = if a ∈ created then 0 else (t.block.view σ₀).storageAt a k`, `t' = t`.
- `getAccountOptional a`: `x = (t.view σ₀).account? a`, `accountReads += a`. `getPreStateAccountOptional a`: `x = (t.block.view σ₀).account? a`.
- `getCode h a`: `x = c` where `(t.view σ₀).code? t.block.consts h = some c`, with `codeReads += (a,h)` iff neither write layer holds `h` and `h ≠ emptyCodeHash`.
- `setStorage a k v`: `t'.view σ₀ = (t.view σ₀).setStorage a k v`; `setAccount a o`: `… .setAccount a o`; `destroyStorage a`: `… .clearStorage a` and `storageReads' = storageReads ∪ {(a,k) | k ∈ dom t.rev.storageWrites[a]}`.
- `setTransientStorage a k v`: `transient' = transient.insert (a,k) v` (erase if `v = 0`).
- Invariant preservation of `TxRevertible`'s order-list invariant for every write.
- **Progress** [T]: every operation terminates; a read fails only if the provider call it makes fails, or by R15/R19.

### 7.2 Derived laws (proved once on the model, D25) [C], [R]

- **Read-after-write:** `setStorage a k v; getStorage a k` returns `v`; same for accounts, code writes and transient storage.
- **Frame:** a write to `(a,k)` leaves `getStorage a' k'` unchanged for `(a',k') ≠ (a,k)`; writes never change `getStorageOriginal`.
- **Clear suppression:** after `destroyStorage a`, `getStorage a k = 0` until `(a,k)` is written again in the same transaction; later writes are visible. At block level: a transaction clear hides all earlier block writes of `a`, and later transactions see only the post-clear writes.
- **Storage precedence** (R11) and **original precedence** (R12) as the two separate public laws ARCHITECTURE §5.3 requires; `created ⇒ original = 0`.
- **Snapshot/revert:** `restoreTxState (copyTxState t)` after any sequence returns `rev` to exactly `t.rev`; observations are **monotone** across it (`t.obs ⊆ t'.obs` componentwise) and `createdAccounts` is kept; `block.oldestAncestorOffset` is kept.
- **Split invisibility:** for every EELS operation, projecting (`rev`, `obs`, `block`) back to an EELS `TransactionState` gives the EELS result [R].
- **Lifecycle:** `(incorporateTxIntoBlock t).1.view σ₀ = t.view σ₀` (the transaction view becomes the block view); transient storage and `createdAccounts` are empty in the returned transaction state; block read sets are the unions. This rests on `(σ.apply d₁).apply d₂ = σ.apply (d₁.merge d₂)`.
- **Diff law:** `σ₀.apply (extractBlockDiff b) = b.view σ₀` (definitional) and `BlockDiff.WF σ₀ (extractBlockDiff b)` (§7.4).
- **Observation laws for the BAL and witness:** every `(a,k)` whose pending transaction write is dropped by `destroyStorage` is in `storageReads` from then on (write→read conversion; a write dropped by `restoreTxState` leaves no read, R24); every account written through `modifyState` was read in the same transaction.

### 7.3 Pre-state contract obligations

- [C] `ModelsLookups` is preserved by nothing (it is about the provider) but is *used* by every read equation above.
- [R] Callers never see `PreState` internals; backends prove the full `Models` (`EthStateCommit`), plus progress (ARCHITECTURE §5.3). An always-error provider satisfies `ModelsLookups` vacuously; the tests use one to show that progress is a separate obligation.

### 7.4 Invariants exported to other libraries

- `BlockDiff.WF σ₀ d` [C]: (i) `d.accountChanges a = some none → a ∈ d.storageClears`; (ii) `a ∈ dom d.storageChanges → (σ₀.apply d).account? a ≠ none`; (iii) account, storage-address and slot order lists enumerate the corresponding domains without duplicates. With (i)–(ii), `σ₀.apply d` is structurally `WF`. Preservation is for **reachable block execution**, not arbitrary raw helper calls: EELS `set_account(..., None)` alone does not clear storage, and `set_account` alone does not read the account. Callers must establish these premises before exporting a WF diff or using the history theorem.
- `AccountWritesLookedUp` [R] (R32): every address in `accountChanges` was the argument of a successful `preState.getAccount?` call during the block. As a Lean statement it is the equivalent observable property "every address in `b.accountWrites` is in `b.accountReads` and its first read fell through to the provider"; it is stated over an instrumented execution in the proof library, since a pure provider cannot record calls.

### 7.5 Order

- Preserve account first-write order, storage-address order, and each slot's first-write order. `record` appends a new key and leaves an existing key in place. Clearing storage removes that address's pending writes and both storage order indexes, converts dropped transaction writes into reads, and resets subsequent slot order. Incorporation removes cleared block entries before folding new transaction writes in their recorded order. Snapshots restore all three indexes with the writes; extraction emits forward-order lists once. `MathState.apply` forgets replay order, but operational witness refinement cannot. `BlockDiff` carries **no clear order**, so the witness root replay's iteration over `storageChanges ∪ storageClears` (a Python set; `EthStateWitness` W6 step 3) is **open (F7)**: prove that step-3 rewrites commute, including failures and observations, or add a clear order to `BlockDiff`. A prototype's traversal is not adopted, and a first-clear order alone does not reproduce Python set iteration. Independence of insert/delete group order is not assumed.

### Informal correctness argument

**Claim.** For reachable execution traces, overlay operations refine the reference's state lifetimes, preserve observations across rollback, and extract a diff with the ordering and invariants required by the backends.

**Premises.** Initial structural well-formedness; successful provider answers where requested; the caller protocol that reads accounts before changing them; invariant-preserving storage/account updates; ordered-container observer laws.

**Argument.** Induct on the sequence of state operations. A lookup first checks the top overlay; a storage clear suppresses every lower layer, including the pre-state. Each branch therefore has the specified logical value. A write records its first live position using WriteOrder; repeated writes update only the value, while clearing storage removes its write positions and converts pending writes to observations. Snapshots retain precisely TxRevertible, so restoring them reverts writes, clears, order metadata and transient storage but leaves TxObs intact. Incorporation applies clears before the recorded incoming writes and keeps the block's first-write positions. Induction on these ordered folds establishes the extracted diff equation and each list/map consistency invariant. The separate read-before-write induction is on callers' reachable traces: raw setAccount does not establish it by itself.

**Open obligations.** Formalise reachability, every caller's read-before-write and balance preconditions, and storage-order metadata through all clear/restore/merge paths. An arbitrary raw diff or raw deletion need not satisfy BlockDiff.WF. Snapshot persistence requires worst-case bounds independently of these semantic laws.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthBase`
- **Used by:** `EthVmCore` (and through it the instructions, precompiles and runner), `EthStateCommit`, and transitively `EthBlock`, the backends and the guest.
- **Seams provided:** the `PreState` record (the block-execution seam, ARCHITECTURE §2); `StateM` operations with model laws for opcode proofs; `extractBlockDiff` and the read sets for `EthBlock` (state root, BAL, witness generation).
- **Constants context (F20).** `BlockState.new` preserves the supplied record: `(BlockState.new ps consts).consts = consts`. State operations read it through their existing `TxState`/`BlockState` context; they receive no parallel constants argument. Pure helpers without that context (`emptyAccount`, `MathState.code?`) retain their necessary data parameter and EELS-named local notation. This constructor/context law remains an implementation obligation.
- **Relies on:** every `PreState Id` passed to execution satisfies `ModelsLookups` for some WF σ₀ (proved by backends via `Models`); `EthBase` supplies checked `U256` add/sub, lawful `compare` on `Address`/`Bytes32`/`Hash32` keys (D2), the orderings for `(Address × Bytes32)` keys and `LawfulEqCmp Address` (F19), and the `HashConsts` record (R2).
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

## 10. Gaps

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **Account-change order** (R6) is preserved by ARCHITECTURE §5.3 and B1; its refinement proof and a committed account-trie regression input remain outstanding. The order-dependence claim is from reading `incremental_mpt.py:753–797` and `witness_state.py:303–309`; no fixture exercises an account-trie collapse whose success depends on order (`eip8025_optional_proofs/test_witness_state_replay_order.py` covers the storage trie's insert-before-delete order only). A regression input must be built.
- **State errors under O13** (R29): `balanceOverflow` is argued reachable in the ledger from the pinned `U256` semantics [verified by execution] but has no fixture; honest-chain unreachability is an argument, not a proof. `balanceUnderflow` and `storageOnMissingAccount` are unresolved failure-ledger entries. `StateError` cannot be frozen (B14) until they close.
- **Clear order** (F7, open; §7.5): no clear order in `BlockDiff`, and no proof that the witness step-3 iteration is unobservable.
- **Generic-`m` contract:** `ModelsLookups` and the §7 laws are stated at `PreState Id`; their coupling for a generic oracle monad is open (D5).
- **`AccountWritesLookedUp`** (R32) is argued from a grep of `forks/amsterdam/` callers of `set_account`; it needs a Lean statement that is meaningful for a pure provider (currently only an instrumented-execution formulation is sketched) and a proof across system transactions, withdrawals and the throwaway pre-check state (R28).
- **`BlockDiff.WF` (ii)** is an inference; in particular 7702 delegation and creation paths must be checked to never leave storage changes for an absent account.
- **Unreachability claims** (R15 assert; offset `0` in `get_witness_ancestors`) are inferences.
- **`WitnessError` granularity:** the coarse constructors here must be refined together with `EthCommit`/`EthStateWitness` and the O4 sub-cases; CONTRACT owns the outcome, EthState owns the shared error type, and EthCommit/EthStateWitness supply the site-specific adapters (D14).
- **Observation-set representation:** `HashSet` expected bounds and adversarial hash distributions are unmeasured (ARCHITECTURE §5.0); sorted output for the BAL is `EthBlock`'s, but the hand-off type is not fixed.
- **`Std` costs:** `ExtTreeMap` has no proved height/cost theorem; incorporate's merge relies on a fold whose cost is analytical only.
- **Frame accumulators** (warm sets, logs, refunds, `accounts_to_delete`) are *not* in `state_tracker.py` and are specified by `EthVmCore`; the §6 lifetime table's rows for them are not re-checked here.
- **Proof strategy** for the split-invisibility law (§7.2) needs a formal EELS-shaped reference state to compare against; none is planned yet.
- **EEST coverage** of write→read conversion is only indirect (through BAL fixtures); no unit tests exist upstream for `state_tracker.py`.
