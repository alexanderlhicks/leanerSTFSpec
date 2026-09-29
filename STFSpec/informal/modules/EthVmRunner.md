# `EthVmRunner`: message-call and create execution, child frames, precompile dispatch, termination

*Status: informal specification, draft. Date: 2026-09-29. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F1, F3, F10, F11, F12, F14 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D5, D13, D14, D17, D22, D23, D24, D26 · questions: B11/Q28, B12/Q4, B14, F11, Q6/Q20.*

Paths in `file:line` references are relative to `src/ethereum/forks/amsterdam/vm/` unless stated otherwise. "[V]" marks a claim checked by reading the pinned source; "[I]" an inference not yet checked by proof or execution.

## 1. Purpose

`EthVmRunner` (root `STFSpec.Vm.Runner`, layer L4) is the only recursive part of the VM (D17). It prepares a transaction's top-level frame (EIP-7702 authorizations, warm sets, dispatch charges), runs a frame's opcode loop by repeatedly calling `EthVmInstructions.step`, executes each child call/create request as a nested frame and applies the named resume operation to the parent, settles frames on revert and exceptional halt, performs contract-code deposit, and dispatches precompiles through a **table it receives** rather than imports. It owns the termination measure and the per-frame fuel budgets, and the checked-runner side of O11: it reports spec-internal fuel exhaustion as `InternalError`, never as EVM out-of-gas. EELS counterparts: `interpreter.py` (`process_top_level`, `create_evm`, `process_call`, `process_create`) and the transaction-level half of `eoa_delegation.py`.

## 2. Requirements

### 2.1 Top level (`process_top_level`, `interpreter.py:241–327`)

- **R-TOP-1** Build the meter `(gas_left = execution_gas_grant, reservoir = baseline = state_gas_reservoir)` (`:267–271`), take a transaction-state snapshot (`:273`), and run `createEvm`.
- **R-TOP-2** If preparation raises an `ExceptionalHalt` (`AddressCollision`, or `OutOfGasError` from any preparation charge): restore the snapshot (this also **reverts the applied delegations**), `restore_state_gas_to_entry` (refills committed and uncommitted spill), `forfeit_remaining_gas`, and return `TransactionOutput` with that error, empty logs, deletions and return data, `state_gas_left` and `tx_state_gas_used` (`:274–294`). No frame is dispatched. **Entry-meter law (F12).** Because `createEvm` returns only the error, the partially charged meter is not available. The Lean version applies both operations to the **entry** meter `(executionGasGrant, R, R)` built in R-TOP-1, where both preconditions of `restoreStateGasToEntry` hold by construction. The result equals the reference's on the partially charged meter in every field, because restore-to-entry refills every spill and resets the reservoir and baseline to `R`, forfeit zeroes `gas_left`, and preparation never changes the refund counter (so it is 0, as the EELS assert requires). The refund cast at `:285` is therefore unreachable.
- **R-TOP-3** Otherwise run `processCreate` if `tx_env.is_create`, else `processCall` (`:296–299`). A failed execution contributes no logs and no deletions (`:302–307`). `refund_counter` is converted with `U256(...)` (`:318`): a negative value raises `OverflowError` in EELS, so the Lean version must either prove non-negativity or produce `VmFault.u256Overflow .refundCounter` (EthVmCore R-EXC-2; unresolved, an O13 candidate).
- **R-TOP-4** `TransactionOutput` (`:91–121`) carries `gas_left`, `refund_counter`, `logs`, `accounts_to_delete`, `error`, `return_data` (= the frame's output), `state_gas_left`, `state_gas_used : Int`. System transactions (`fork.py:770–822`) use the same entry point with `execution_gas_grant = 30_000_000` and a reservoir of `16 · STORAGE_SET` [V].

### 2.2 Frame preparation (`create_evm`, `interpreter.py:138–238`)

In this order:
1. `call_data := ∅` for a creation, else `tx_env.data`; warm slots := `access_list_storage_keys`; warm addresses := ∅ (`:153–162`).
2. If `authorizations ≠ ()`: `accessed_authorities := setDelegation`, warm them, then `commit_state_gas` (`:165–168`), so a later failure of the *dispatched code* keeps the delegations' state gas charged.
3. Warm `coinbase`, **every precompile address of the table**, `origin`, the access-list addresses, and the target (`:171–175`).
4. Creation: if `¬account_deployable(target)` raise `AddressCollision`; if the **pre-state** account of the target (`get_pre_state_account`, not the current account) equals `EMPTY_ACCOUNT`, charge `NEW_ACCOUNT` state gas; code := `tx_env.data` (`:178–188`). This differs from the CREATE opcode, which tests `is_account_alive` of the current state.
5. Call: `charge_value_transfer_to_non_alive_account` (`:124–135`: `NEW_ACCOUNT` state gas iff `value > 0 ∧ ¬alive(recipient)`); then `resolve_delegated_code_address` (charges warm/cold and warms the delegate) and load the code of the resolved address (`:189–202`).
6. Build the depth-0 frame: `caller = origin`, `should_transfer_value = true`, not static, `disable_precompiles` from step 5 (`:205–238`).

### 2.3 EIP-7702 authorizations (`eoa_delegation.py:116–335`)

- **R-AUTH-1** `recoverAuthority` (`:116–156`) rejects `y_parity ∉ {0,1}`, `r ∉ (0, N)`, `s ∉ (0, N/2]` (`N = SECP256K1N`), then recovers from `keccak256(0x05 ‖ rlp([chain_id, address, nonce]))` and returns `keccak256(pubkey)[12:32]`. Both hashes are `KeccakQuery` calls (D5), so `recoverAuthority` returns in `m`. `SET_CODE_TX_MAGIC = 0x05`. Signature recovery is reached through the direct `EthCurve` dependency (D26, accepted). The runner calls it directly; opcode handlers do not import it.
- **R-AUTH-2** `validateAuthorization` (`:199–240`) returns `none` if `chain_id ∉ {block chain id, 0}`, `nonce ≥ 2^64 − 1`, or recovery fails; **otherwise it warms the authority first** (`:224`), then returns `none` if the authority's code is non-empty and not a designator, or its nonce differs from `auth.nonce`.
- **R-AUTH-3** `setDelegation` (`:243–335`), per authorization in order, for a valid authority: `NEW_ACCOUNT` state gas if `¬account_exists` (exists, not alive); `ACCOUNT_WRITE` (9000) execution gas once per authority not in `accounts_with_paid_writes` (and add it); if `auth.address = NULL_ADDRESS` (zero) clear the code, else charge `AUTH_BASE` state gas when the authority had no designator in the **pre-state** and none was set earlier in this transaction, and set `0xEF0100 ‖ address`; then `increment_nonce`. Any charge failure raises `OutOfGasError` (handled by R-TOP-2). It returns the recovered authorities, the updated `accounts_with_paid_writes`, and the meter as a subtype carrying `stateGasLeft ≤ stateGasBaseline`, which `commitStateGas` in §2.2 step 2 needs (F12). Precondition: `¬ is_create` (EELS `assert`, `:293`; guaranteed by transaction decoding in `EthBlock`).

### 2.4 Message call (`process_call`, `interpreter.py:401–475`)

- **R-CALL-1** The depth guard `depth > 1024 → StackDepthLimitError` (`:417–418`, outside the `try`) is **unreachable**: the top frame has depth 0 and a child is only requested when `depth < 1024` (EthVmInstructions `StepResult.call` carries the proof). The Lean runner must not re-check; the `FrameCtx.depth_le` field records the bound.
- **R-CALL-2** Snapshot the transaction state (`:420`). If `should_transfer_value ∧ value ≠ 0`: `move_ether(caller → target)` and, if `caller ≠ target`, `emitTransferLog` (EIP-7708, into this frame's logs) (`:424–437`).
- **R-CALL-3** If `code_address` is a key of the precompile table: run it unless `disable_precompiles`, in which case **nothing runs and the frame succeeds with empty output** (`:438–442`). Otherwise run the frame loop (§2.6).
- **R-CALL-4** Settlement (`:456–471`): on an exceptional halt, `restore_state_gas`, `forfeit_remaining_gas`, output := ∅; on `Revert`, `restore_state_gas` only (unspent `gas_left` returns to the parent); in both cases record the error and restore the snapshot (`:473–474`). After settlement a non-top frame satisfies `ChildSettled` (EthVmCore `L-SETTLE`).

### 2.5 Creation (`process_create`, `interpreter.py:330–398`)

- **R-CRE-1** Snapshot; `destroy_storage(target)`; `mark_account_created(target)` (not reverted by later rollbacks within the transaction, D23); `increment_nonce(target)`; run `processCall`.
- **R-CRE-2** On success, with `c = output`, in this order: `c[0] = 0xEF` → `InvalidContractPrefix` (EIP-3541); `|c| > MAX_CODE_SIZE (0x10000, EIP-7954)` → `OutOfGasError`; charge `6 · ceil32(|c|)/32` execution gas; charge `1530 · |c|` state gas. Any failure: restore the **outer** snapshot, `restore_state_gas`, `forfeit_remaining_gas`, output := ∅, record the error. Otherwise `set_code(target, c)`. On an unsuccessful `processCall`, restore the outer snapshot (`:396–397`).

### 2.6 Frame loop and children

- **R-LOOP-1** The loop calls `step` while the frame runs (`:444–452`). `.continue f'` iterates; `.stop`, `.revert`, `.halt` end the frame and go to settlement. `step` itself handles `pc ≥ |code|` and invalid opcodes (EthVmInstructions R-DSP-2).
- **R-LOOP-2** On `.call parent req h hs`: build the child context with `childCtxOfCall ctx req h` (depth + 1) and the child frame with `childFrame parent req.gas req.stateGasReservoir` (its warm sets are the parent's), run `processCall`, form the `ChildOutcome` (the `ChildSettled` proof: F11, §9), and continue with `resumeAfterCall ctx.config parent req outcome hs` (F10). On `.create`: likewise with `processCreate` and `resumeAfterCreate` (EELS: `I/system.py:140–192, 409–469`). The parent frame is suspended unchanged while the child runs.
- **R-LOOP-3 Precompile table.** `PrecompileFn m` (EthVmCore) takes `(input, meter)` and returns, in `m`, either `.ok meter' output` or `.halt e`. The table's `meter_law` guarantees that `meter'` differs from `meter` only by a `gas_left` charge. The runner **installs `meter'` as the frame meter** and sets the output, without charging again; on `.halt` it applies the ordinary frame-halt settlement (R-CALL-4). This matches EELS, whose precompiles read only `evm.call_data`, write only `evm.output` and charge only execution gas on the frame's own meter [V: `grep evm\.` over `precompiled_contracts/` finds only `call_data` and `output`, plus `charge_gas`]. ecrecover and p256verify return empty output on invalid input rather than halting (O9, EthPrecompiles). The table's key set is also the warm-set seed of §2.2 step 3.

### 2.7 Termination and fuel (ARCHITECTURE §5.5; O11; REVIEW §7 G2–G7)

- **R-TERM-1** The runner is a mutual recursion `processCreate`/`processCall`/`runFrame` with the lexicographic measure `(STACK_DEPTH_LIMIT − depth, stage, frameFuel)`, stage ranks `processCreate = 2 > processCall = 1 > runFrame = 0`, via `termination_by`. Depth is in `FrameCtx`, which handlers cannot modify; only `childCtxOf*` builds a deeper context, from a proof `depth < 1024`, so the first component strictly decreases without saturating subtraction.
- **R-TERM-2** Fuel exists only in `runFrame`. Each frame receives its own budget from a `BudgetPolicy : GasMeter → Nat` applied to the frame's **entry** meter; there is no global fuel argument. One fuel unit pays for one parent iteration, including a whole child execution and the resume. Running out yields `InternalError.fuelExhausted`, carried in a layer separate from `ExceptionalHalt` and `VmFault`.
- **R-TERM-3** The default policy is `phiBudget m = m.phi + 1` (candidate, unproved). Φ = `gas_left + state_gas_spilled + state_gas_committed_spill`.
- **R-TERM-4 Checked runner versus public function.** This library exposes `processTopLevelChecked : … → VmM m (Except InternalError (TransactionOutput × AddrSet))`, and owns `CheckedT ε m := ExceptT ε (ExceptT InternalError m)`, the checked monad the block and guest layers use (F14). There is no VM-level fallback value: `EthBlock` propagates `InternalError` to `EthStateless`, whose public `runStatelessGuest` projects it (O11). Conformance runs the checked path and reports any `InternalError` as a spec bug.

## 3. EELS source map

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `forks/amsterdam/vm/interpreter.py::TransactionOutput` | 91 | `structure TransactionOutput` | `refundCounter : Nat` after the checked conversion |
| `forks/amsterdam/vm/interpreter.py::charge_value_transfer_to_non_alive_account` | 124 | `chargeValueTransferToNonAliveAccount` | |
| `forks/amsterdam/vm/interpreter.py::create_evm` | 138 | `createEvm` | returns `Except ExceptionalHalt` inside `VmM` |
| `forks/amsterdam/vm/interpreter.py::process_top_level` | 241 | `processTopLevelChecked` | O11 checked form |
| `forks/amsterdam/vm/interpreter.py::process_create` | 330 | `processCreate` | |
| `forks/amsterdam/vm/interpreter.py::process_call` | 401 | `processCall`, `runFrame`, `runPrecompile` | the `while` loop becomes `runFrame` |
| `forks/amsterdam/vm/eoa_delegation.py::SET_CODE_TX_MAGIC` | 35 | `SET_CODE_TX_MAGIC : Bytes := 0x05` | |
| `forks/amsterdam/vm/eoa_delegation.py::NULL_ADDRESS` | 39 | `NULL_ADDRESS : Address := 0` | |
| `forks/amsterdam/vm/eoa_delegation.py::recover_authority` | 116 | `recoverAuthority` | calls `EthCurve.secp256k1Recover` directly (D26, resolving NEW-VM-5) |
| `forks/amsterdam/vm/eoa_delegation.py::validate_authorization` | 199 | `validateAuthorization` | |
| `forks/amsterdam/vm/eoa_delegation.py::set_delegation` | 243 | `setDelegation` | |

The interpreter's limits (`STACK_DEPTH_LIMIT`, `MAX_CODE_SIZE`, `MAX_INIT_CODE_SIZE`) are claimed by `EthVmCore` (`VmLimits`), and the opcode table (`instructions/__init__.py`, `Ops` with `op_implementation`) by `EthVmInstructions`; the precompile mapping (`precompiled_contracts/mapping.py`) is `EthPrecompiles`'; the runner consumes all three.

**External semantics.** `ethereum_rlp.rlp.encode` of `(U256 chain_id, Address, U64 nonce)` in `recover_authority` (EthCodec: canonical integer encoding without leading zeros); `U256(...)`/`U64` range checks (`OverflowError`); Python `set` semantics for warm sets (EthVmCore `AddrSet`). `ethereum.trace.evm_trace` events (`OpStart`, `OpEnd`, `OpException`, `PrecompileStart/End`, `EvmStop`, `TransactionEnd`) are diagnostics (ARCHITECTURE §7): they must be emitted through the event interface with the same order, but have no semantic effect.

## 4. Tests

- **EEST fixture areas:** depth and recursion: `ported_static/stCallCreateCallCodeTest`, `stDelegatecallTestHomestead`, `stSystemOperationsTest`, `stRecursiveCreate`, `stCallCodes`; creation: `stCreateTest`, `stCreate2`, `stInitCodeTest`, `stCodeSizeLimit`, `frontier/create`, `amsterdam/eip7954_increase_max_contract_size`, `amsterdam/eip7997_deterministic_factory_contract`; top frame and authorizations: `prague/eip7702_set_code_tx` (86), `amsterdam/eip2780_reduce_intrinsic_tx_gas` (`test_top_frame_charges.py`), `amsterdam/eip8037_state_creation_gas_cost_increase` (`test_state_gas_set_code.py`, `test_state_gas_reservoir.py`, `test_state_gas_system_calls.py`, `test_state_gas_cross_frame_refund.py`), `amsterdam/eip8038_*` (`test_set_code_auth_gas.py`, `test_set_code_auth_refunds.py`), `ported_static/stEIP3607`, `stTransactionTest`; revert/halt settlement: `stRevertTest`, `stZeroCallsRevert`, `stReturnDataTest`; precompile dispatch: `frontier/precompiles`, `ported_static/stPreCompiledContracts`, `stPreCompiledContracts2`, the BLS/BN/P256/KZG/modexp/blake2 areas (`prague/eip2537_bls_12_381_precompiles`, `byzantium/eip196_ec_add_mul`, `eip197_ec_pairing`, `osaka/eip7951_p256verify_precompiles`, `istanbul/eip152_blake2`, `osaka/eip7883_modexp_gas_increase`); transfer logs at frame entry: `amsterdam/eip7708_eth_transfer_logs`; time-sensitive: `stQuadraticComplexityTest`, `stAttackTest`, `paris/security`.
- **EELS unit tests:** none for `interpreter.py` or `eoa_delegation.py` at e1a316a0 [V]; `tests/json_loader/test_trace.py` checks only trace hooks.
- **`core` `#guard` cases:** top-level call to a precompile; call to an EOA delegated to a precompile (runs nothing, succeeds, empty output); delegation chain of length 2 (halts with InvalidOpcode 0xEF); preparation OOG in `setDelegation` (delegations reverted, `restoreStateGasToEntry`, all gas forfeited); create transaction to a collision address; code deposit of exactly `0x10000` and `0x10001` bytes; code starting with `0xEF`; revert in init code (parent sees revert data); value transfer to self (no transfer log); `refundCounter` negative in a child that later succeeds.
- **Adversarial:** a call chain to depth 1024 (the 1025th frame is refused by preflight, returns 0, no child); recursion with 63/64 decay to exhaustion; 10⁴ sibling calls from one parent (warm-set persistence, rope logs); inner success followed by outer revert; child halts at the first instruction; a frame with `gas_left = 0` running JUMPDEST; a test-only policy `constBudget 1` that must produce `InternalError.fuelExhausted` (and never EVM out-of-gas) to test the O11 separation.
- **Property/differential:** the checked runner under `phiBudget` and under `constBudget n` for growing `n` agree on every fixture (guarantees 2–3 empirically); budget usage never exceeds `phi + 1` per frame (G6 empirically); trace on/off yields identical outputs; compiled `lake build` executable for the linearity canary (ARCHITECTURE §7).

## 5. Interface

```lean
-- PrecompileResult, PrecompileFn, PrecompileTable and VmConfig are imported from EthVmCore.
-- Everything is generic in `{m} [Monad m] [KeccakQuery m]` (D5); public callers use `m := Id`.
-- Parameters supplied by EthFork (public); recovery calls EthCurve directly (D26).
structure RunnerEnv (m : Type → Type) [Monad m] where
  precompiles : PrecompileTable m
  vm : VmConfig

-- Internal errors (public; O11)
inductive InternalError | fuelExhausted (depth : Nat)
  -- `| invariant (what : String)` only if F11 chooses the checked option (§9); G7 must then prove it dead
abbrev CheckedResult (ε α : Type) := Except InternalError (Except ε α)
abbrev CheckedT (ε : Type) (m : Type → Type) := ExceptT ε (ExceptT InternalError m)   -- F14; `.run.run : m (CheckedResult ε α)`
abbrev RunM (m : Type → Type) := ExceptT InternalError (VmM m)
def runVmChecked (action : VmM m (Except InternalError α)) (world : VmWorld m)
    : m (CheckedResult VmFault (α × VmWorld m))  -- explicit adapter, in `m` (F14); equations in COMPOSITION.md
abbrev BudgetPolicy := GasMeter → Nat
def phiBudget : BudgetPolicy := fun m => m.phi + 1
def constBudget (n : Nat) : BudgetPolicy := fun _ => n

-- Frame results (public)
structure FrameResult where frame : Frame; output : Bytes; error : Option FrameError
def FrameResult.toChildOutcome (r : FrameResult) (h : ChildSettled r.frame r.error.isSome) : ChildOutcome
-- Pure field-preserving adapter; apply only after processCall/processCreate settles a non-top child.
-- How the runner obtains `h` is open (F11, §9).
structure TransactionOutput where
  gasLeft : Nat; refundCounter : Nat; logs : LogRope; accountsToDelete : AddrSet
  error : Option FrameError; returnData : Bytes; stateGasLeft : Nat; stateGasUsed : Int

-- The runner (public; mutual, terminating by (1024 − depth, stage, fuel))
def runFrame      (env : RunnerEnv m) (b : BudgetPolicy) (ctx : FrameCtx) (f : Frame) (fuel : Nat) : RunM m FrameResult
def processCall   (env : RunnerEnv m) (b : BudgetPolicy) (ctx : FrameCtx) (f : Frame) : RunM m FrameResult
def processCreate (env : RunnerEnv m) (b : BudgetPolicy) (ctx : FrameCtx) (f : Frame) : RunM m FrameResult
def runPrecompile (p : PrecompileFn m) (f : Frame) (input : Bytes) : m FrameResult   -- internal; installs the returned meter (R-LOOP-3)

-- Top level (public)
def chargeValueTransferToNonAliveAccount (cfg : VmConfig) (g : GasMeter) (recipient : Address) (value : U256) : VmM m (Except ExceptionalHalt GasMeter)
def createEvm (env : RunnerEnv m) (be : BlockEnvironment) (te : TransactionEnvironment)
    (paidWrites : AddrSet) (g : GasMeter) : VmM m (Except ExceptionalHalt (FrameCtx × Frame × AddrSet))
def processTopLevelChecked (env : RunnerEnv m) (b : BudgetPolicy := phiBudget)
    (be : BlockEnvironment) (te : TransactionEnvironment) (paidWrites : AddrSet) :
    VmM m (Except InternalError (TransactionOutput × AddrSet))   -- preparation failure: entry-meter law (R-TOP-2)

-- EIP-7702, transaction side (public)
def SET_CODE_TX_MAGIC : Bytes; def NULL_ADDRESS : Address
def recoverAuthority (a : Authorization) : m (Except SignatureError Address)  -- two KeccakQuery calls; EthCurve error; invalid authorization is skipped
def validateAuthorization (env : RunnerEnv m) (be : BlockEnvironment) (warmAuth : AddrSet) (a : Authorization) : VmM m (Option Address × AddrSet)
def setDelegation (env : RunnerEnv m) (be : BlockEnvironment) (te : TransactionEnvironment)
    (paidWrites : AddrSet) (g : GasMeter) :
    VmM m (Except ExceptionalHalt (AddrSet × AddrSet × {g' : GasMeter // g'.stateGasLeft ≤ g'.stateGasBaseline}))   -- F12

-- Semantic relation and fuel guarantees (public, Prop-valued; stated at m := Id)
inductive ExecKind | frameLoop | call | create
inductive Exec (env : RunnerEnv Id) (kind : ExecKind) : FrameCtx → Frame → VmWorld Id → FrameResult → VmWorld Id → Prop   -- big-step, built from Step and the resume ops
```

`Exec` is parameterised by the runner environment and entry kind, so precompile dispatch and call/create settlement are fixed rather than hidden existential choices. The call laws below use `.call`; corresponding laws are required for `.create` and the raw `.frameLoop`. `Exec` is defined by the same `step` function (through `Step`, EthVmInstructions) and the same resume operations and settlement functions; it is not a second semantics ([REVIEW §7](../REVIEW.md#7-acceptance-criteria-proof-gates-composition-cases-replacement-and-cost-checks), "Scope and evidence").

## 6. Data structures

| Type | Representation | Model | Invariant | Persistence | Cost |
|---|---|---|---|---|---|
| Runner call stack | Lean recursion (D13) | list of suspended `(FrameCtx, Frame, request)` | EVM logical depth ≤ 1024, hence ≤ 1025 active EVM frames including depth 0; each suspended parent is uniquely owned | linear | host stack includes multiple helper activations per EVM frame and must be measured |
| Transaction snapshot | `TxRevertible` value kept by `processCall`/`processCreate` | EthState model | restores only writes, clear/order metadata and transient storage; observations survive | worst-case persistent (D22) | O(1) to take; restore = select saved root |
| `PrecompileTable` | imported from EthVmCore; `match` over the 18 addresses | partial map | `lookup_iff`, `meter_law` | read-only | lookup O(log 18) or a compiled decision tree |
| `TransactionOutput` | record | — | `refundCounter` non-negative by construction (checked conversion) | value | — |
| fuel | `Nat` per frame | — | decreases by 1 per iteration | — | — |

## 7. Contract and laws

**Structural** [T]: the mutual definition is accepted by `termination_by` with the measure of R-TERM-1 (G3). No `partial`, no global fuel, no helper without its own measure.

**Settlement** [C]: after `processCall`/`processCreate` returns `r` with `r.error = some _`: for non-top frames, `ChildSettled r.frame true` (spill 0, refund 0, reservoir = baseline, committed spill 0 for non-top frames), the transaction state equals the snapshot taken at entry of that call (processCall) or of the create (processCreate), and observations are a superset of those at entry (EthState). On `r.error = none`, the non-top child satisfies `ChildSettled r.frame false`. Top-level settlement has its separate entry/committed-spill law. Halts additionally have `r.frame.gasMeter.gasLeft = 0` and `r.output = ∅`.

**Φ obligations** (G2; source-checked, unproved):
- *Frame non-increase:* for every child frame, `Φ(final meter) ≤ Φ(entry meter)`, by induction on the runner using EthVmInstructions' gas-progress lemmas, EthVmCore's Φ table and settlement (restore is Φ-neutral; forfeit decreases). Code deposit charges decrease Φ.
- *Whole-iteration progress:* every `.continue` step, and every `.call/.create` step followed by the child and the resume, decreases the parent's Φ by at least 1: `Φ(resume) = Φ(parent) + Φ(child final) ≤ Φ(parent) + req.gas ≤ Φ(before) − 100` (calls; `− 12000` for creates).
- *Top frame:* preparation charges happen before the frame's entry meter is measured; the committed spill of the top frame is included in Φ and never increases.

**Fuel guarantees** (the four of ARCHITECTURE §5.5; G4–G7), stated at `m := Id` and quantified over well-formed inputs (`Wf` frames and meters, a `VmWorld` satisfying EthState's invariants):
1. *Soundness* [T/R]: `processCall env b ctx f w = .ok (.ok r, w') → Exec env .call ctx f w r w'` for **every** policy `b`.
2. *Completeness* [T]: `Exec env .call ctx f w r w' → ∃ N, ∀ n ≥ N, processCall env (constBudget n) ctx f w = .ok (.ok r, w')`.
3. *Fuel monotonicity at fixed semantic gas* [T]: `processCall env (constBudget n) ctx f w = .ok (.ok r, w') → processCall env (constBudget (n + k)) ctx f w = .ok (.ok r, w')`; similarly for pointwise-larger policies.
4. *Fuel sufficiency* [T]: `processCall env phiBudget ctx f w ≠ .ok (.error (.fuelExhausted _), w')` for all `w'`, including executions ending in revert, exceptional halt or EVM out-of-gas; lifted to `processTopLevelChecked`. Composed at the guest (EthStateless) this gives O11's `∀ input, ∃ out, runStatelessGuestChecked input = .ok out`, provided `InternalError` has no other reachable constructor (G7; this includes `invariant` if F11 chooses the checked option).

These are separate results: 2 does not give a computable budget and 4 does not give agreement with `Exec`. No gas-monotonicity statement is claimed: more *gas* can change behaviour (GAS, 63/64 forwarding).

**Resume and depth** [C]: `childCtxOf*` produces `depth + 1 ≤ 1024`; the EELS depth guard is provably dead (R-CALL-1).

**Precompile dispatch** [C]: `processCall` on a precompile address with `disablePrecompiles = false` equals `runPrecompile` after the value transfer; with `true` it succeeds with empty output without running the precompile or code (`interpreter.py:438–442`). On success the runner installs the returned meter and output, without charging again. On halt it applies the ordinary frame-halt settlement. `meter_law` supplies the potential bound; no opcode proof depends on precompile internals.

**Authorizations** [C]: `setDelegation` fails only with `outOfGas`; on failure the caller's snapshot restore undoes every applied authorization (R-TOP-2); the `AUTH_BASE` charge is paid at most once per authority per transaction and never credited back (the EELS docstring's claim, `eoa_delegation.py:265–270`, to be proved).

**Relational view for consumers** [R]: `Exec` is deterministic; per-transaction refinement targets are `processTopLevelChecked` under `phiBudget` together with guarantee 4.

### Informal correctness argument

**Claim.** Completed checked runs implement Exec; sufficiently large fuel reproduces any finite Exec derivation; larger fuel at fixed semantic gas preserves the result. Under whole-iteration gas progress, phiBudget never exhausts internally.

**Premises.** Source-correct step/resume functions, snapshot and settlement contracts, shared precompile meter_law, bounded logical depth, and the unproved whole-CALL/CREATE potential inequality.

**Argument.** Structural termination uses the lexicographic depth/stage/fuel measure: loops decrease fuel, while child recursion decreases remaining depth. Soundness follows by induction over the checked run, appending the corresponding Step/child/settlement derivation. For completeness, a finite Exec derivation has finitely many frame iterations; choose a budget exceeding their maximum and induct over that derivation. The same induction shows monotonicity because extra fuel is observed only by the exhaustion guard. For computable sufficiency, strengthen the induction with child-final Φ ≤ child-entry Φ. Every continuing step, including a child round trip, must reduce the parent's Φ by at least one after accounting for withholding, stipends and returned gas. Thus at most entry Φ continuing iterations plus one terminal iteration are needed. Exceptional halts and reverts are terminal cases; they are semantic results, not internal fuel exhaustion. Restore only TxRevertible and retain observations.

**Open obligations.** Complete the measure, every call/create/preflight/settlement inequality and all four actual theorem statements. Numeric schedule positivity alone does not prove whole-iteration progress. Propagate InternalError through every caller before claiming the guest's O11 branch unreachable.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthVmInstructions`, `EthCurve` (secp256k1 recovery for EIP-7702 authorities, D26; the runner calls `secp256k1Recover` directly, as EELS does).
- **Used by:** `EthBlock` (`processTopLevelChecked` for user and system transactions; `TransactionOutput`), transitively `EthFork` (supplies `RunnerEnv`: the precompile table from `EthPrecompiles` and one `VmConfig`; recovery is a direct `EthCurve` call).
- **Seams:** consumes `step`, the request/resume operations and delegation resolution (EthVmInstructions), the meter and settlement laws (EthVmCore), EthState snapshot/restore and account operations; provides the transaction-level execution function and the four fuel guarantees. Cross-module invariants relied on: `EthBlock` validates the transaction before calling (intrinsic gas affordable, sender balance and nonce, `is_create → authorizations = ()`); `EthFork`'s table satisfies `lookup_iff`/`meter_law`. Guaranteed: settlement post-conditions above; `InternalError` is the only non-`VmFault` failure.

## 9. Open decisions

- **D13** (call-frame structure): recursion, EELS-shaped, is specified; an explicit continuation stack would need a measure over the whole stack. The fuel-adequacy investigation ([REVIEW §7](../REVIEW.md#7-acceptance-criteria-proof-gates-composition-cases-replacement-and-cost-checks) G2–G7) decides.
- **D5** (broad scope, monad-parametric): the runner, `recoverAuthority` and `runPrecompile` are in `m`; `CheckedT` and `runVmChecked` return in `m` (F14).
- **D14** (accepted): O8/O9/O11 as used here; the VM-internal Python faults are CONTRACT O13 members with named `VmFault` constructors (EthVmCore R-EXC-2).
- **D17**: accepted; this module is the only recursive one.
- **D22/D23**: snapshots are persistent `TxRevertible` values; `created_accounts` and read observations survive restore.
- **D24**: child logs merge as a rope append.
- NEW-VM-5: resolved by D26 (DECISIONS Q27).
- **NEW-VM-6** (DECISIONS B11, Q28): Φ + 1 remains an unproved candidate, settled by the fuel-adequacy investigation; also open is whether the fuel-indexed family for guarantees 2–3 is `constBudget n` or "all policies pointwise ≥ some policy".
- **F11** (open, choose one): how the runner produces `ChildSettled` for `toChildOutcome`. Either a decidable check whose failure raises a new `InternalError.invariant` (then proved dead with the fuel guarantees, G7; the choice of a compiled prototype of the interfaces), or a settled subtype returned by `processCall`/`processCreate`, which needs `L-SETTLE` proved inline.

## 10. Gaps

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **Termination is unproved.** The measure is a design; no Lean definition exists. G2 (whole-iteration progress), G3 (structural termination), G4–G6 (soundness, completeness/monotonicity, sufficiency) and G7 (internal-error freedom) are all "planned". The Φ argument in §7 is an inference from reading `gas.py` and the handlers.
- **Φ + 1 per frame is only a candidate.** It relies on "every continuing opcode costs ≥ 1 execution gas" and "a child returns ≤ the potential it was granted", neither proved; the stipend accounting (2300 returned through `restore_child_gas` on preflight failure, or inside `sub_call` to the child) is covered only by the inequality `transfer cost − stipend = 9000`.
- **Top-level refund sign.** `U256(gas_meter.refund_counter)` at `interpreter.py:318` requires the top frame's refund to be non-negative; unresolved (EthVmCore §10). The cast at `:285` is unreachable (R-TOP-2).
- **Host resources.** Gas and fuel do not bound Lean stack depth, allocation or zkVM cycles (ARCHITECTURE §4). 1025 nested runner activations in compiled Lean have not been measured. In the guest process the Python recursion limit is 100,000 (py_ecc raises it; `import ethereum` alone gives 12,288, `src/ethereum/__init__.py:28–30`); deeper host limits are DISC-001 territory (O12).
- **`move_ether` preconditions**: the sender-balance assertion in EthState's `move_ether` is unreachable only because of preflight checks (CALL/CREATE) and transaction validation (top level). EthVmRunner owns the CALL/CREATE caller proof; EthBlock owns the top-level admission proof; both consume EthState's checked `moveEther` contract. Record both proofs before treating the assertion as unreachable.
- **System transactions** (`fork.py:770–822`) run with 30 M execution gas and a 16-SSTORE reservoir; `phiBudget` gives ≈ 3·10⁷ fuel, which is fine as a bound but the error path (`fork.py:757–760` raises on a failed system call) belongs to EthBlock.
- **Trace schema** (ARCHITECTURE §12) is undecided; the event order of `OpStart`/`OpEnd`/`OpException`/`EvmStop` is specified only as "EELS order".
- **The `Exec` relation** is not yet defined; its exact form (big-step over frames with nested `Exec` premises for children) must be fixed before G4/G5 can be stated precisely.
- **EIP-8037 cross-frame refunds** (`test_state_gas_cross_frame_refund.py`) exercise the repay path whose Φ-neutrality is only source-checked.
- **Pre-dispatch vs dispatch rollback** (delegations kept after a dispatched failure, reverted after a preparation failure) is specified from comments and code (`gas.py:471–502`, `interpreter.py:276–282`); no targeted `#guard` exists yet.
