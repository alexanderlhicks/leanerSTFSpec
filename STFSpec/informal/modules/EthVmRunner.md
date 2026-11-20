# `EthVmRunner`: message-call and create execution, child frames, precompile dispatch, termination

*Status: informal specification, draft; selectable budget and entry-kind vocabulary, raw RunnerEnv carrier, raw output records, checked control carriers and F14 VM adapter supplied. Date: 2026-11-13. Pin: `tests-zkevm@v21.0.6` @59c1473d. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F1, F3, F8, F10, F11, F12, F14, F20 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D5, D13, D14, D17, D22, D23, D24, D26 · questions: B11/Q28, B12/Q4, B14, F11, Q6/Q20, Q83.*

Paths in `file:line` references are relative to `src/ethereum/forks/amsterdam/vm/` unless stated otherwise. "[V]" marks a claim checked by reading the pinned source; "[I]" an inference not yet checked by proof or execution. EELS `file:line` citations are at `59c1473d` except where marked and those listed in `STFSpec/informal/citation-remap-manual.txt`, which are still at `e1a316a0` (`tests-zkevm@v21.0.0`); verified observations are at `e1a316a0` unless marked as at `59c1473d` (GAPS-CROSSCUTTING X16).

## 1. Purpose

`EthVmRunner` (root `STFSpec.Vm.Runner`, layer L4) is the only recursive part of the VM (D17). It prepares a transaction's top-level frame (EIP-7702 authorizations, warm sets, dispatch charges), runs a frame's opcode loop by repeatedly calling `EthVmInstructions.step`, executes each child call/create request as a nested frame and applies the named resume operation to the parent, settles frames on revert and exceptional halt, performs contract-code deposit, and dispatches precompiles through a **table it receives** rather than imports. It owns the termination measure and the per-frame fuel budgets, and the checked-runner side of O11: it reports spec-internal fuel exhaustion as `InternalError`, never as EVM out-of-gas. EELS counterparts: `interpreter.py` (`process_top_level`, `create_evm`, `process_call`, `process_create`) and the transaction-level half of `eoa_delegation.py`.

## 2. Requirements

### 2.1 Top level (`process_top_level`, `interpreter.py:235–321`)

- **R-TOP-1** Build the meter `(gas_left = execution_gas_grant, reservoir = baseline = state_gas_reservoir)` (`:261–265`), take a transaction-state snapshot (`:267`), and run `createEvm`.
- **R-TOP-2** If preparation raises an `ExceptionalHalt` (`AddressCollision`, or `OutOfGasError` from any preparation charge): restore the snapshot (this also **reverts the applied delegations**), `restore_state_gas_to_entry` (refills committed and uncommitted spill), `forfeit_remaining_gas`, and return `TransactionOutput` with that error, empty logs, deletions and return data, `state_gas_left` and `tx_state_gas_used` (`:268–288`). No frame is dispatched. **Entry-meter law (F12).** Because `createEvm` returns only the error, the partially charged meter is not available. The Lean version applies both operations to the **entry** meter `(executionGasGrant, R, R)` built in R-TOP-1, where both preconditions of `restoreStateGasToEntry` hold by construction. The result equals the reference's on the partially charged meter in every field, because restore-to-entry refills every spill and resets the reservoir and baseline to `R`, forfeit zeroes `gas_left`, and preparation never changes the refund counter (so it is 0, as the EELS assert requires). The unsigned refund cast at `:279` is evaluated after restore/forfeit and before state usage at `:285–287`; only its overflow alternative is excluded by the zero refund. The private ordinary composition in EthVmCore §3/§7 proves this gas handoff conditional on the local partial-meter assertions and admission; deriving those assertions from actual preparation remains open.
- **R-TOP-3** Otherwise run `processCreate` if `tx_env.is_create`, else `processCall` (`:290–293`). A failed execution contributes no logs and no deletions (`:296–301`). After TransactionEnd tracing (`:303–308`), `refund_counter` is converted with `U256(...)` (`:312`), before state usage (`:318–320`). This unsigned conversion requires both `0 ≤ refundCounter` and `refundCounter < 2^256`; either violation raises `OverflowError` in EELS. The Lean version must prove both bounds or produce the existing `VmFault.u256Overflow .refundCounter` at this point (EthVmCore R-EXC-2; unresolved, an O13 candidate). Successful projection to the unchanged Nat output retains the unsigned range for reconstruction through existing Base laws (Q66). Actual normal-return range and fault reachability remain open.
- **R-TOP-4** `TransactionOutput` (`:86–116`) carries `gas_left`, `refund_counter`, `logs`, `accounts_to_delete`, `error`, `return_data` (= the frame's output), `state_gas_left`, `state_gas_used : Int`. System transactions (`fork.py:728–780`) use the same entry point with `execution_gas_grant = 30_000_000` and a reservoir of `16 · STORAGE_SET` [V].

### 2.2 Frame preparation (`create_evm`, `interpreter.py:133–232`)

In this order:
1. `call_data := ∅` for a creation, else `tx_env.data`; warm slots := `access_list_storage_keys`; warm addresses := ∅ (`:148–157`).
2. If `authorizations ≠ ()`: `accessed_authorities := setDelegation`, warm them, then `commit_state_gas` (`:160–163`), so a later failure of the *dispatched code* keeps the delegations' state gas charged.
3. Warm `coinbase`, **every precompile address of the table**, `origin`, the access-list addresses, and the target (`:166–170`).
4. Creation: if `¬account_deployable(target)` raise `AddressCollision`; if the **pre-state** account of the target (`get_pre_state_account`, not the current account) equals `EMPTY_ACCOUNT`, charge `NEW_ACCOUNT` state gas; code := `tx_env.data` (`:173–183`). This differs from the CREATE opcode, which tests `is_account_alive` of the current state.
5. Call: `charge_value_transfer_to_non_alive_account` (`:119–130`: `NEW_ACCOUNT` state gas iff `value > 0 ∧ ¬alive(recipient)`); then `resolve_delegated_code_address` (charges warm/cold and warms the delegate) and load the code of the resolved address (`:184–196`).
6. Build the depth-0 frame: `caller = origin`, `should_transfer_value = true`, not static, `disable_precompiles` from step 5 (`:199–232`). Copy `ctx.config := env.vm` and `ctx.systemAddress := env.systemAddress` (F8); these supplied immutable policy fields refine source module policy rather than new source Evm fields.

### 2.3 EIP-7702 authorizations (`eoa_delegation.py:112–321`)

- **R-AUTH-1** `recoverAuthority` (`:112–152`) rejects `y_parity ∉ {0,1}`, `r ∉ (0, N)`, `s ∉ (0, N/2]` (`N = SECP256K1N`), then recovers from `keccak256(0x05 ‖ rlp([chain_id, address, nonce]))` and returns `keccak256(pubkey)[12:32]`. Both hashes are `KeccakQuery` calls (D5), so `recoverAuthority` returns in `m`. `SET_CODE_TX_MAGIC = 0x05`. Signature recovery is reached through the direct `EthCurve` dependency (D26, accepted). The runner calls it directly; opcode handlers do not import it.
- **R-AUTH-2** `validateAuthorization` (`:191–228`) returns `none` if `chain_id ∉ {block chain id, 0}`, `nonce ≥ 2^64 − 1`, or recovery fails; **otherwise it warms the authority first** (`:216`), then returns `none` if the authority's code is non-empty and not a designator, or its nonce differs from `auth.nonce`.
- **R-AUTH-3** `setDelegation` (`:231–321`), per authorization in order, for a valid authority: `NEW_ACCOUNT` state gas if `¬account_exists` (exists, not alive); `ACCOUNT_WRITE` (9000) execution gas once per authority not in `accounts_with_paid_writes` (and add it); if `auth.address = NULL_ADDRESS` (zero) clear the code, else charge `AUTH_BASE` state gas when the authority had no designator in the **pre-state** and none was set earlier in this transaction, and set `0xEF0100 ‖ address`; then `increment_nonce`. Any charge failure raises `OutOfGasError` (handled by R-TOP-2). It returns the recovered authorities, the updated `accounts_with_paid_writes`, and the meter as a subtype carrying `stateGasLeft ≤ stateGasBaseline`, which `commitStateGas` in §2.2 step 2 needs (F12). Precondition: `¬ is_create` (EELS `assert`, `:281`; guaranteed by transaction decoding in `EthBlock`).

### 2.4 Message call (`process_call`, `interpreter.py:395–469`)

- **R-CALL-1** The depth guard `depth > 1024 → StackDepthLimitError` (`:411–412`, outside the `try`) is **unreachable**: the top frame has depth 0 and a child is only requested when `depth < 1024` (EthVmInstructions `StepResult.call` carries the proof). The Lean runner must not re-check; the `FrameCtx.depth_le` field records the bound.
- **R-CALL-2** Snapshot the transaction state (`:414`). If `should_transfer_value ∧ value ≠ 0`: `move_ether(caller → target)` and, if `caller ≠ target`, `emitTransferLog f ctx.systemAddress world.tx.block.consts.transferTopic ctx.caller ctx.currentTarget ctx.value` (EIP-7708, into this frame's logs) (`:418–431`). The address comes from the immutable context; the topic retains its F20 context path. This adds no query, guard or effect before the existing transfer.
- **R-CALL-3** If `code_address` is a key of the precompile table: run it unless `disable_precompiles`, in which case **nothing runs and the frame succeeds with empty output** (`:432–436`). Otherwise run the frame loop (§2.6).
- **R-CALL-4** Settlement (`:450–465`): on an exceptional halt, `restore_state_gas`, `forfeit_remaining_gas`, output := ∅; on `Revert`, `restore_state_gas` only (unspent `gas_left` returns to the parent); in both cases record the error and restore the snapshot (`:467–468`). After settlement a non-top frame satisfies `ChildSettled` (EthVmCore `L-SETTLE`).

### 2.5 Creation (`process_create`, `interpreter.py:324–392`)

- **R-CRE-1** Snapshot; `destroy_storage(target)`; `mark_account_created(target)` (not reverted by later rollbacks within the transaction, D23); `increment_nonce(target)`; run `processCall`.
- **R-CRE-2** On success, with `c = output`, in this order: `c[0] = 0xEF` → `InvalidContractPrefix` (EIP-3541); `|c| > MAX_CODE_SIZE (0x10000, EIP-7954)` → `OutOfGasError`; charge `6 · ceil32(|c|)/32` execution gas; charge `1530 · |c|` state gas. Any failure: restore the **outer** snapshot, `restore_state_gas`, `forfeit_remaining_gas`, output := ∅, record the error. Otherwise `set_code(target, c)`. On an unsuccessful `processCall`, restore the outer snapshot (`:390–391`).

### 2.6 Frame loop and children

- **R-LOOP-1** The loop calls `step` while the frame runs (`:438–446`). `.continue f'` iterates; `.stop`, `.revert`, `.halt` end the frame and go to settlement. `step` itself handles `pc ≥ |code|` and invalid opcodes (EthVmInstructions R-DSP-2).
- **R-LOOP-2** On `.call parent req h hs`: build the child context with `childCtxOfCall ctx req h` (depth + 1) and the child frame with `childFrame parent req.gas req.stateGasReservoir` (its warm sets are the parent's); the child context inherits `ctx.systemAddress` unchanged (F8). Run `processCall`, form the `ChildOutcome` (the `ChildSettled` proof: F11, §9), and continue with `resumeAfterCall ctx.config parent req outcome hs` (F10). On `.create`: likewise with `processCreate` and `resumeAfterCreate` (EELS: `I/system.py:133–185, 402–462`). The parent frame is suspended unchanged while the child runs.
- **R-LOOP-3 Precompile table.** `PrecompileFn m` (EthVmCore) takes `(input, meter)` and returns, in `m`, either `.ok meter' output` or `.halt e`. At Id the table's `meter_law`, via Core's `satisfiesM_id_iff` (Q83), guarantees that `meter'` differs from `meter` only by a `gas_left` charge. For arbitrary m, the action-factorization witness requires a concrete bridge through the actual dispatch/lift before making that observed-result claim. The runner **installs `meter'` as the frame meter** and sets the output, without charging again; on `.halt` it applies the ordinary frame-halt settlement (R-CALL-4). This matches EELS, whose precompiles read only `evm.call_data`, write only `evm.output` and charge only execution gas on the frame's own meter [V: `grep evm\.` over `precompiled_contracts/` finds only `call_data` and `output`, plus `charge_gas`]. ecrecover and p256verify return empty output on invalid input rather than halting (O9, EthPrecompiles). The table's key set is also the warm-set seed of §2.2 step 3.

### 2.7 Termination and fuel (ARCHITECTURE §5.5; O11; REVIEW §7 G2–G7)

- **R-TERM-1** The runner is a mutual recursion `processCreate`/`processCall`/`runFrame` with the lexicographic measure `(STACK_DEPTH_LIMIT − depth, stage, frameFuel)`, stage ranks `processCreate = 2 > processCall = 1 > runFrame = 0`, via `termination_by`. Depth is in `FrameCtx`, which handlers cannot modify; only `childCtxOf*` builds a deeper context, from a proof `depth < 1024`, so the first component strictly decreases without saturating subtraction.
- **R-TERM-2** Fuel exists only in `runFrame`. Each frame receives its own budget from a `BudgetPolicy : GasMeter → Nat` applied to the frame's **entry** meter; there is no global fuel argument. One fuel unit pays for one parent iteration, including a whole child execution and the resume. Running out yields `InternalError.fuelExhausted`, carried in a layer separate from `ExceptionalHalt` and `VmFault`.
- **R-TERM-3** The default policy is `phiBudget m = m.phi + 1` (candidate, unproved). Φ = `gas_left + state_gas_spilled + state_gas_committed_spill`.
- **R-TERM-4 Checked runner versus public function.** This library exposes `processTopLevelChecked : … → VmM m (Except InternalError (TransactionOutput × AddrSet))`, and owns `CheckedT ε m := ExceptT ε (ExceptT InternalError m)`, the checked monad the block and guest layers use (F14). There is no VM-level fallback value: `EthBlock` propagates `InternalError` to `EthStateless`, whose public `runStatelessGuest` projects it (O11). Conformance runs the checked path and reports any `InternalError` as a spec bug.

## 3. EELS source map

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `forks/amsterdam/vm/interpreter.py::TransactionOutput` | 86 | `structure TransactionOutput` | Raw carrier supplied; Nat refund preserves the guided abstraction (Q66); producer conversion/range evidence remains open |
| `forks/amsterdam/vm/interpreter.py::charge_value_transfer_to_non_alive_account` | 119 | `chargeValueTransferToNonAliveAccount` | |
| `forks/amsterdam/vm/interpreter.py::create_evm` | 133 | `createEvm` | returns `Except ExceptionalHalt` inside `VmM`; copies supplied env.vm and env.systemAddress into immutable context (F8) |
| `forks/amsterdam/vm/interpreter.py::process_top_level` | 235 | `processTopLevelChecked` | O11 checked form |
| `forks/amsterdam/vm/interpreter.py::process_create` | 324 | `processCreate` | |
| `forks/amsterdam/vm/interpreter.py::process_call` | 395 | `processCall`, `runFrame`, `runPrecompile` | loop becomes runFrame; :418–431 transfers then emits with ctx.systemAddress and F20 topic |
| `forks/amsterdam/vm/eoa_delegation.py::SET_CODE_TX_MAGIC` | 35 | `SET_CODE_TX_MAGIC : Bytes := 0x05` | |
| `forks/amsterdam/vm/eoa_delegation.py::NULL_ADDRESS` | 39 | `NULL_ADDRESS : Address := 0` | |
| `forks/amsterdam/vm/eoa_delegation.py::recover_authority` | 112 | `recoverAuthority` | calls `EthCurve.secp256k1Recover` directly (D26, resolving NEW-VM-5) |
| `forks/amsterdam/vm/eoa_delegation.py::validate_authorization` | 191 | `validateAuthorization` | |
| `forks/amsterdam/vm/eoa_delegation.py::set_delegation` | 231 | `setDelegation` | |

The interpreter's limits (`STACK_DEPTH_LIMIT`, `MAX_CODE_SIZE`, `MAX_INIT_CODE_SIZE`) are claimed by `EthVmCore` (`VmLimits`), and the opcode table (`instructions/__init__.py`, `Ops` with `op_implementation`) by `EthVmInstructions`; the precompile mapping (`precompiled_contracts/mapping.py`) is `EthPrecompiles`'; the runner consumes all three.

**External semantics.** `ethereum_rlp.rlp.encode` of `(U256 chain_id, Address, U64 nonce)` in `recover_authority` (EthCodec: canonical integer encoding without leading zeros); `U256(...)`/`U64` range checks (`OverflowError`); Python `set` semantics for warm sets (EthVmCore `AddrSet`). `ethereum.trace.evm_trace` events (`OpStart`, `OpEnd`, `OpException`, `PrecompileStart/End`, `EvmStop`, `TransactionEnd`) are diagnostics (ARCHITECTURE §7): they must be emitted through the event interface with the same order, but have no semantic effect.

### Supplied raw output records

`STFSpec/Vm/Runner/Output.lean`, exported by `STFSpec.Vm.Runner`, supplies exactly
§5's two records. They store independent complete fields without extra proof
fields, admission predicates, defaults, instances or authored public helper laws.

| Source / operation | Lean declaration and type | Domain, effects and ordered failures | Client / status |
|---|---|---|---|
| Project partition of `interpreter.py:395–469` at `59c1473d`; no source class | `FrameResult : Type`, constructor `Frame → Bytes → Option FrameError → FrameResult` | All complete frames, independent output bytes and optional complete errors; no effects or failures | Private exact constructor/projection, reconstruction and every isolated update client; supplied |
| `interpreter.py:86–116` at `59c1473d` | `TransactionOutput : Type`, constructor `Nat → Nat → LogRope → AddrSet → Option FrameError → Bytes → Nat → Int → TransactionOutput` | Every independent field value; raw rope shape and extensional set retained; signed state usage includes negatives; no effects or failures | Private complete construction/projection/reconstruction and all eight isolated update clients; supplied |

The source refund is U256 after the checked casts in R-TOP-2/R-TOP-3. This raw
Nat storage performs no cast or range check; actual source correspondence needs
the successful unsigned range and exact U256 reconstruction (Q66). Raw error
presence implies neither empty logs/deletions nor ChildSettled. Frame output and
frame.returnData are independent. The toChildOutcome adapter, actual producers,
settlement, F11 and execution/fuel/resource/readiness obligations remain open.

### Supplied mathematical budget vocabulary

| Source/model | Lean declaration | Domain, effects and failures | Validation |
|---|---|---|---|
| Project mathematical policy (§5); no EELS budget function | `BudgetPolicy := GasMeter → Nat` | Every finite raw six-field Core meter; pure callback type with no class or proof premise | Private exact-signature and ordinary callback clients |
| Project candidate (§5), consuming Core `GasMeter.phi` | `phiBudget : BudgetPolicy` | Exactly `m.phi + 1`; no meter update, query, cast, cap or failure | Private defining/positive/transport clients; signed-refund and reservoir-drain independence through public Core laws; complete finite observations |
| Project constant policy (§5); no EELS budget function | `constBudget (n : Nat) : BudgetPolicy` | Exactly `n` for every meter and every Nat, including zero; no update or failure | Private defining/callback/input-independence clients and complete finite observations |

These are the only three authored public declarations in `STFSpec.Vm.Runner.Budget`,
exported by `STFSpec.Vm.Runner`. No new public theorem is supplied. This is selectable
vocabulary only: no runner, installed default, fuel-indexed family choice or G2–G7 result.
B11/Q28 remains open as recorded in DECISIONS. The source grounding is the existing
complete Core meter and its project mathematical potential, not an original Python
budget call or differential claim.

### Supplied execution entry-kind vocabulary

| Source/model | Lean declaration | Domain, effects and failures | Validation |
|---|---|---|---|
| Project vocabulary already specified in §5; no original EELS enum or source call | `ExecKind : Type` with `frameLoop`, `call`, `create` | Exactly three nullary constructors; no parameters, effects or failures; no authored instance, default or observer | Private public-facade constructor clients, exhaustive symbolic and dependent elimination, all three match branches and all six ordered constructor inequalities |

The carrier is supplied in the Runner-owned `ExecKind` leaf and exported by the
Runner facade. Its authored public inventory is the type and three constructors;
ordinary generated inductive support is subject to the declaration policy.
No manually authored public helper or theorem is added. This supplies entry-kind
vocabulary only; it does not define `Exec` or choose its unresolved relation form.

### Supplied raw runner environment

`STFSpec/Vm/Runner/Environment.lean`, exported by `STFSpec.Vm.Runner`, supplies
exactly the existing three-field `RunnerEnv` data contract. This is a source-free
abstraction grouping Core's complete certified table and VM policy with Base's
supplied Address; it claims no new EELS operation. F8 owns the intended address
route. The carrier needs only `m : Type → Type` and `[Monad m]`; storing data
neither queries a hash nor executes an action. No default, instance, selected
policy, admission predicate or manually authored public law/factory is supplied.

| Source / operation | Lean declaration and type | Domain, effects and ordered failures | Client / status |
|---|---|---|---|
| Source-free grouping (F8) | `RunnerEnv (m : Type → Type) [Monad m] : Type` | All supplied complete table/config/address triples; storage only, no effects or failures | Private exact-type client; supplied |
| Source-free construction | `RunnerEnv.mk : PrecompileTable m → VmConfig → Address → RunnerEnv m` | Every ordered triple under Monad alone; retains whole fields, including table certificates; no validation or effects | Private constructor, complete projection and reconstruction clients; supplied |
| Source-free table projection | `RunnerEnv.precompiles : RunnerEnv m → PrecompileTable m` | Every raw environment; retains actual lookup, domain and certified actions; no execution or effects | Private complete table/update, lookup-domain and actual factorization-witness clients; supplied |
| Source-free config projection | `RunnerEnv.vm : RunnerEnv m → VmConfig` | Every raw environment; retains complete costs/stateCosts/limits, without coherence or bounds; no effects | Private complete config/update and arbitrary full-cost/zero/beyond-word limit controls; supplied |
| Source-free address projection | `RunnerEnv.systemAddress : RunnerEnv m → Address` | Every raw environment; preserves the supplied nominal address; no literal or endian conversion, effects or failures | Private complete address/update and distinct nonliteral byte-order controls; supplied |

All clients are private in
`STFSpec/Conformance/Vm/Runner/EnvironmentCallerProofs.lean` and import only the
public Runner facade. A parameterized local Id singleton supplies its actual
lookup-domain proof and successful action certificate through Core's existing
`satisfiesM_id_iff`; it is an inhabitant, not the installed Ethereum table.
The generic witness client uses the stored table's actual `meter_law`, without
observing arbitrary-monad results or strengthening Q83. Assembly, dispatch,
transformer bridges, copying into FrameCtx and all execution remain unimplemented.

**Supplied checked control carriers (source-free).** These Lean-side carriers
have no corresponding EELS runtime operation; no source execution correspondence
is asserted. EELS uses a different operational termination model.

| Source | Exact declaration | Domain, effects and failure alternatives | Private facade clients / status |
|---|---|---|---|
| None (O11 control vocabulary) | `InternalError.fuelExhausted : Nat → InternalError` | Every Nat depth, retained exactly; constructor only, no operation or effects | Arbitrary depth projection; zero and beyond-word controls; supplied |
| None (D14/F14 control shape) | `CheckedResult (ε α : Type) := Except InternalError (Except ε α)` | All Type-level error/success payloads; outer internal failure, inner rejection or success; no class premise or effects | Exact alias type/unfolding and complete three-alternative reconstruction/payload clients; supplied |
| None (F14 transformer order) | `CheckedT (ε : Type) (m : Type → Type) := ExceptT ε (ExceptT InternalError m)` | All Type-level base constructors, without Monad/hash/lawful premise; `.run.run : m (Except InternalError (Except ε α))` retains the entire base action | Exact type/unfolding, arbitrary complete action preservation and local Id composition clients; supplied |

All checked-carrier clients are private in
`STFSpec/Conformance/Vm/Runner/CheckedCallerProofs.lean`, importing only the
public Runner facade. Only `fuelExhausted` is supplied; the conditional future
`invariant` option remains reserved by F11. Actual caller propagation, execution,
budget, exhaustion-unreachability and guest projection remain open. The F14
adapter is supplied below.

**Supplied checked VM adapter (source-free; F14).** This project adapter has no
corresponding EELS function and asserts no source execution correspondence.

| Source | Exact declaration | Domain, effects and failure alternatives | Private facade clients / status |
|---|---|---|---|
| None (F14 transformer wiring) | `RunM (m : Type → Type) := ExceptT InternalError (VmM m)` in `Runner/RunChecked.lean` | All Type-level base constructors without a class premise; retains the complete VM action through `.run` | `RunCheckedCallerProofs.lean`: exact signature/unfolding and contravariant base constructor; supplied |
| None (F14 project adapter) | `runVmChecked {m : Type → Type} [Monad m] {α : Type} (action : VmM m (Except InternalError α)) (world : VmWorld m) : m (CheckedResult VmFault (α × VmWorld m))` in the same module | Every complete action, world, payload and fault; one supplied base bind followed by one pure; VM fault → `.ok (.error vf)`, internal failure → `.error i` with its world erased, success → `.ok (.ok (a, after))`. No lawful-monad, hash, WF or coherence premise | Same private client: public equation, complete Id channels/world updates, lawful effects, base failures and nonlawful map distinction; supplied, sole ordinary law `runVmChecked_eq` discharged |

## 4. Tests

- **Supplied entry-kind clients:** `ExecKindCallerProofs` imports the public Runner
  facade and privately checks all three nullary constructor types, exhaustive
  symbolic case coverage, dependent elimination into an arbitrary `Sort`, each of
  the three branch equations and all six ordered unequal-constructor pairs.
  Ordinary proofs require no equality instance. These clients are imported through
  the Conformance facade; they assert no frame/call/create execution semantics.
- **Supplied budget controls:** `BudgetGuards` checks zero, independent unit potential
  inputs, combined spills, unrelated reservoir/baseline, signed refunds and constant zero.
  `BudgetCallerProofs` supplies private all-meter defining/callback/positive/transport
  proofs without unfolding foreign semantics. `BudgetPolicyNativeTests` consumes input-only
  TSV controls and emits all six meter fields, the chosen constant and all three natural
  observations (`phi`, `phiBudget`, `constBudget`). The independent Python integer model
  `budget_policy_model.py` checks 64 complete cases: all three potential fields separately
  and combined, zero/one/beyond-word/4096-bit amounts, mutually independent reservoir and
  baseline, negative and huge positive refunds, and four constants including zero and a
  4096-bit value across multiple meters. Interpreted/native stdout is compared completely;
  the strict recursive parser rejects Bool/float/nonfinite numbers, duplicate/missing/extra
  keys, bad IDs/count/order/framing and changed payloads through actual normal/`-O` CLIs.
  These controls model only the mathematical definitions; they execute no original budget
  function and establish no runner progress or sufficiency.

- **Supplied raw-output clients:** `OutputCallerProofs` imports the public Runner
  facade and privately checks exact constructor/projection signatures, arbitrary
  complete construction/reconstruction and all eleven isolated field updates.
  `OutputControls` retains complete raw ropes and sets, all optional error
  alternatives and arbitrary opcode/String payloads, independent output/frame
  return data, nonempty logs/deletions on failure, independent gas/refund values
  above the word range and negative state usage. Ordinary proofs and public-model
  guards check storage only; no EELS execution or producer refinement is claimed.

- **Supplied runner-environment clients:** `EnvironmentCallerProofs` imports the public
  Runner facade and privately checks the exact Monad-only type/constructor/projection
  signatures, arbitrary whole-field preservation, complete reconstruction and all three
  whole-field updates retaining the other two fields. Supplied generic domain and actual
  action witnesses remain accessible through the stored table. A local Id singleton
  varies address, cost, input/output and arbitrary raw meter; the complete literal
  result retains signed refund and both spill pools. Full arbitrary GasCosts and raw
  independent state costs/limits include zero and beyond-word values. Distinct
  nonliteral addresses retain all twenty bytes and byte order. These are carrier
  controls; the actual construction/producer and runtime controls below remain
  unimplemented.

- **Supplied checked-carrier clients:** `CheckedCallerProofs` imports the public Runner
  facade and privately checks both aliases' exact Type domains without class premises,
  complete arbitrary error/success payloads, arbitrary depth and the underlying base
  action through actual `.run.run` nesting. Complete tagged observations distinguish
  internal failure (including depth zero and `2^300 + 71`), structured inner rejection
  and structured success. Actual local Id binds show that each first failure suppresses
  a later failure in the other channel, and successful binds can retain each of the
  three alternatives. These are control-carrier examples, without an EELS operation or
  runtime-runner claim.

- **Supplied checked-adapter clients:** `RunCheckedCallerProofs` imports only the
  public Runner facade. Private proofs check class-free `RunM` formation, its
  complete run shape with a contravariant base, the exact Monad-only adapter type
  and generic use of `runVmChecked_eq`. Arbitrary whole Id payloads and worlds
  cover all three channels, including StateError and nested WitnessError faults,
  changed success world and internal-result world erasure. Actual VM binds over
  lawful `StateT (List Nat) Id` retain ordered base effects on success, VM fault
  and internal failure; a VM fault suppresses later effects. Option no-result and
  arbitrary structured base Except failure remain base failures. A private
  deliberately nonlawful Monad yields mark 18 under the literal bind/pure and
  mark 107 under a map shortcut. These are ordinary proof clients of the project
  adapter, without EELS execution or rollback claims.

**F8 construction/producer controls (unimplemented).** Use a nonliteral supplied
RunnerEnv address and an independently varied F20 topic. Check successful createEvm
copying and complete logs through user/system entry, nested CALL/CREATE and
processCreate→processCall, including zero/self-transfer suppression. Keep child
success and outer revert/halt discard cases under the existing settlement contract.

- **EEST fixture areas:** depth and recursion: `ported_static/stCallCreateCallCodeTest`, `stDelegatecallTestHomestead`, `stSystemOperationsTest`, `stRecursiveCreate`, `stCallCodes`; creation: `stCreateTest`, `stCreate2`, `stInitCodeTest`, `stCodeSizeLimit`, `frontier/create`, `amsterdam/eip7954_increase_max_contract_size`, `amsterdam/eip7997_deterministic_factory_contract`; top frame and authorizations: `prague/eip7702_set_code_tx` (86), `amsterdam/eip2780_reduce_intrinsic_tx_gas` (`test_top_frame_charges.py`), `amsterdam/eip8037_state_creation_gas_cost_increase` (`test_state_gas_set_code.py`, `test_state_gas_reservoir.py`, `test_state_gas_system_calls.py`, `test_state_gas_cross_frame_refund.py`), `amsterdam/eip8038_*` (`test_set_code_auth_gas.py`, `test_set_code_auth_refunds.py`), `ported_static/stEIP3607`, `stTransactionTest`; revert/halt settlement: `stRevertTest`, `stZeroCallsRevert`, `stReturnDataTest`; precompile dispatch: `frontier/precompiles`, `ported_static/stPreCompiledContracts`, `stPreCompiledContracts2`, the BLS/BN/P256/KZG/modexp/blake2 areas (`prague/eip2537_bls_12_381_precompiles`, `byzantium/eip196_ec_add_mul`, `eip197_ec_pairing`, `osaka/eip7951_p256verify_precompiles`, `istanbul/eip152_blake2`, `osaka/eip7883_modexp_gas_increase`); transfer logs at frame entry: `amsterdam/eip7708_eth_transfer_logs`; time-sensitive: `stQuadraticComplexityTest`, `stAttackTest`, `paris/security`.
- **EELS unit tests:** none for `interpreter.py` or `eoa_delegation.py` at e1a316a0 [V]; `tests/json_loader/test_trace.py` checks only trace hooks.
- **`core` `#guard` cases:** top-level call to a precompile; call to an EOA delegated to a precompile (runs nothing, succeeds, empty output); delegation chain of length 2 (halts with InvalidOpcode 0xEF); preparation OOG in `setDelegation` (delegations reverted, `restoreStateGasToEntry`, all gas forfeited); create transaction to a collision address; code deposit of exactly `0x10000` and `0x10001` bytes; code starting with `0xEF`; revert in init code (parent sees revert data); value transfer to self (no transfer log); `refundCounter` negative in a child that later succeeds.
- **Adversarial:** a call chain to depth 1024 (the 1025th frame is refused by preflight, returns 0, no child); recursion with 63/64 decay to exhaustion; 10⁴ sibling calls from one parent (warm-set persistence, rope logs); inner success followed by outer revert; child halts at the first instruction; a frame with `gas_left = 0` running JUMPDEST; a test-only policy `constBudget 1` that must produce `InternalError.fuelExhausted` (and never EVM out-of-gas) to test the O11 separation.
- **Property/differential:** the checked runner under `phiBudget` and under `constBudget n` for growing `n` agree on every fixture (guarantees 2–3 empirically); budget usage never exceeds `phi + 1` per frame (G6 empirically); trace on/off yields identical outputs; compiled `lake build` executable for the linearity canary (ARCHITECTURE §7).

## 5. Interface

Core §3/§4/§5/§7 supplies nominal OverflowSite/VmFault values, including `.u256Overflow .refundCounter`. Both original top-level unsigned casts and their order/bounds remain obligations of R-TOP-2/R-TOP-3; checked propagation, F11 and G2–G7 remain open.

```lean
-- PrecompileResult, PrecompileFn, PrecompileTable and VmConfig are imported from EthVmCore.
-- Execution interfaces that hash are generic in `{m} [Monad m] [KeccakQuery m]` (D5).
-- The supplied raw RunnerEnv below needs only Monad; public execution callers use `m := Id`.
-- Raw storage is supplied; actual parameter assembly by EthFork remains open.
-- Recovery calls EthCurve directly (D26).
structure RunnerEnv (m : Type → Type) [Monad m] where
  precompiles : PrecompileTable m
  vm : VmConfig
  systemAddress : Address     -- Fork-owned value, supplied by the block projection (F8)

-- Internal errors and checked carriers (supplied; source-free; O11/F14)
inductive InternalError | fuelExhausted (depth : Nat)
  -- `| invariant (what : String)` only if F11 chooses the checked option (§9); G7 must then prove it dead
abbrev CheckedResult (ε α : Type) := Except InternalError (Except ε α)
abbrev CheckedT (ε : Type) (m : Type → Type) := ExceptT ε (ExceptT InternalError m)   -- F14; `.run.run : m (CheckedResult ε α)`
-- Runner monad and checked adapter (supplied; F14)
abbrev RunM (m : Type → Type) := ExceptT InternalError (VmM m)
def runVmChecked {m : Type → Type} [Monad m] {α : Type}
    (action : VmM m (Except InternalError α)) (world : VmWorld m)
    : m (CheckedResult VmFault (α × VmWorld m))  -- explicit adapter, in `m` (F14); equations in COMPOSITION.md
-- Supplied selectable vocabulary; no default installation or adequate-policy claim.
abbrev BudgetPolicy := GasMeter → Nat
def phiBudget : BudgetPolicy := fun m => m.phi + 1
def constBudget (n : Nat) : BudgetPolicy := fun _ => n

-- Frame results (raw records supplied; adapter remains unimplemented)
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
-- The table action stays in base m; Q83 does not supply a VmM/RunM transformer bridge.
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
inductive ExecKind | frameLoop | call | create   -- supplied nominal carrier only
inductive Exec (env : RunnerEnv Id) (kind : ExecKind) : FrameCtx → Frame → VmWorld Id → FrameResult → VmWorld Id → Prop   -- big-step, built from Step and the resume ops
```

`Exec` is parameterised by the runner environment and entry kind, so precompile dispatch and call/create settlement are fixed rather than hidden existential choices. The call laws below use `.call`; corresponding laws are required for `.create` and the raw `.frameLoop`. `Exec` is defined by the same `step` function (through `Step`, EthVmInstructions) and the same resume operations and settlement functions; it is not a second semantics ([REVIEW §7](../REVIEW.md#7-acceptance-criteria-proof-gates-composition-cases-replacement-and-cost-checks), "Scope and evidence").

## 6. Data structures

| Type | Representation | Model | Invariant | Persistence | Cost |
|---|---|---|---|---|---|
| Runner call stack | Lean recursion (D13) | list of suspended `(FrameCtx, Frame, request)` | EVM logical depth ≤ 1024, hence ≤ 1025 active EVM frames including depth 0; each suspended parent is uniquely owned | linear | host stack includes multiple helper activations per EVM frame and must be measured |
| Transaction snapshot | `TxRevertible` value kept by `processCall`/`processCreate` | EthState model | restores only writes, clear/order metadata and transient storage; observations survive | worst-case persistent (D22) | O(1) to take; restore = select saved root |
| `PrecompileTable` | imported from EthVmCore; `match` over the 18 addresses | partial map | `lookup_iff`, `meter_law` | read-only | lookup O(log 18) or a compiled decision tree |
| `TransactionOutput` | raw record | complete eight-field tuple | Nat refund; no word-range or field relation; producer conversion remains open (Q66) | value | fixed field storage |
| fuel | `Nat` per frame | — | decreases by 1 per iteration | — | — |

## 7. Contract and laws

**Raw output storage (supplied).** §3/§5 own exactly FrameResult and
TransactionOutput, with ordinary generated structure support. Private facade
clients retain every complete field, reconstruct both records and replace each
field independently. No settlement, relation between output and frame.returnData,
error/effect relation, refund range, hash/class premise or authored public law is
added. Source casts, actual producers, toChildOutcome and F11 remain open.

**Supplied entry-kind carrier.** `ExecKind` has exactly the three nullary
constructors specified in §5, with exhaustive dependent elimination and pairwise
disjointness checked by private ordinary facade clients. There are no parameters
and no authored instance, default or observer. No `Exec` relation or execution law is supplied;
D13/B11, F11 and G2–G7 remain open.

**Checked control storage (supplied).** §3/§5 own exactly `InternalError` with
`fuelExhausted (depth : Nat)`, `CheckedResult` and `CheckedT`, with ordinary
inductive infrastructure and no authored public law/default/instance package.
Private facade proofs preserve arbitrary complete payloads, both exact alias
unfoldings and the entire underlying `m` action without a Monad, KeccakQuery or
lawful-monad premise. Local Id binds exercise distinct short-circuit channels.
F11's optional future invariant remains unselected. Actual caller propagation,
execution, budget policy, G2–G7 and O11 guest projection remain open.

**Checked VM action routing (supplied/discharged; F14).** `RunM` is the
class-free alias in §5. The sole public law `runVmChecked_eq` is the complete
literal equation, for every supplied Monad and arbitrary whole values:

```lean
runVmChecked action world = (do
  match ← (action.run world).run with
  | .error vf => pure (.ok (.error vf))
  | .ok (.error i, _) => pure (.error i)
  | .ok (.ok a, after) => pure (.ok (.ok (a, after))))
```

One base bind runs the action and one pure returns the selected checked result.
No lawful-monad premise is required; no map replacement or successful-result
observation for arbitrary m follows. At Id the complete three routing results
hold by reduction, retaining the updated world only on success. Base failure or
absence remains in m, without reclassification as InternalError or a rollback
claim. Q83's actual precompile dispatch/lift bridge remains separate.

**Raw RunnerEnv storage (supplied).** §3/§5 own the exact three-field record,
with ordinary generated structure support and no authored public law package.
Private facade proofs retain arbitrary complete fields, reconstruct the record
and update each whole field independently, preserving the other fields exactly.
The table includes its actual domain/certification proofs; clients obtain its
existing generic factorization witness and exact Id consequence through Core's
public contract. This storage introduces no effects, hash query, failure,
coherence/global invariant, KeccakQuery or lawful-monad premise. It establishes
no successful createEvm copy, child inheritance, emission, installed-table/config
assembly, transformer/dispatch/settlement bridge, F11 or G2–G7 result.

**Supplied budget definitions.** For every raw meter `m` and every `n : Nat`,
`phiBudget m = m.phi + 1` and `constBudget n m = n` by their ordinary definitions.
The alias accepts ordinary `GasMeter → Nat` callbacks without Monad, Keccak, WF or
local proof premises. Every field is unrestricted, including signed refunds and
independent reservoir/baseline/spills. These are pure total observations, with no
failure channel or state effect. Private clients derive positivity, constant-input
independence and potential-equality transport; `addRefund_phi` and
`drainStateGasReservoir_phi` give the corresponding unused-field cases without
unfolding Core semantics. No public equation theorem, monotonicity, execution,
termination or fuel-adequacy result is added. The remaining laws below are planned.

**Context construction** [C] (F8): whenever `createEvm env be te paidWrites g` successfully returns `(ctx, f, paidWrites')`, `ctx.config = env.vm` and `ctx.systemAddress = env.systemAddress`. Both child constructors preserve `systemAddress` exactly (EthVmInstructions §7). Actual `processCall` emission reads `ctx.systemAddress`, including when `processCreate` delegates to it. Intended block assembly supplies `env = cfg.runnerEnv`; pinned-source refinement then instantiates the inherited address with Fork's pinned value and the separately coherent F20 topic. These are construction/refinement obligations, not an added admission predicate on arbitrary raw RunnerEnv/FrameCtx, Step/Exec, independent gas laws or all StateT actions. Whole-context equalities must retain the new field.

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

**Precompile dispatch** [C]: `processCall` on a precompile address with `disablePrecompiles = false` equals `runPrecompile` after the value transfer; with `true` it succeeds with empty output without running the precompile or code (`interpreter.py:432–436`). On success the runner installs the returned meter and output, without charging again. On halt it applies the ordinary frame-halt settlement. At Id, `satisfiesM_id_iff` turns `meter_law` into the successful local meter bound, including both spill pools. For generic m the actual dispatch/lift requires its own effect bridge. Settlement remains a separate proof; no opcode proof depends on precompile internals (Q83).

**Authorizations** [C]: `setDelegation` fails only with `outOfGas`; on failure the caller's snapshot restore undoes every applied authorization (R-TOP-2); the `AUTH_BASE` charge is paid at most once per authority per transaction and never credited back (the EELS docstring's claim, `eoa_delegation.py:253–258`, to be proved).

**Relational view for consumers** [R]: `Exec` is deterministic; per-transaction refinement targets are `processTopLevelChecked` under `phiBudget` together with guarantee 4.

### Informal correctness argument

**Claim.** Completed checked runs implement Exec; sufficiently large fuel reproduces any finite Exec derivation; larger fuel at fixed semantic gas preserves the result. Under whole-iteration gas progress, phiBudget never exhausts internally.

**Premises.** Source-correct step/resume functions, snapshot and settlement contracts, shared precompile meter_law, bounded logical depth, and the unproved whole-CALL/CREATE potential inequality.

**Argument.** Structural termination uses the lexicographic depth/stage/fuel measure: loops decrease fuel, while child recursion decreases remaining depth. Soundness follows by induction over the checked run, appending the corresponding Step/child/settlement derivation. For completeness, a finite Exec derivation has finitely many frame iterations; choose a budget exceeding their maximum and induct over that derivation. The same induction shows monotonicity because extra fuel is observed only by the exhaustion guard. For computable sufficiency, strengthen the induction with child-final Φ ≤ child-entry Φ. Every continuing step, including a child round trip, must reduce the parent's Φ by at least one after accounting for withholding, stipends and returned gas. Thus at most entry Φ continuing iterations plus one terminal iteration are needed. Exceptional halts and reverts are terminal cases; they are semantic results, not internal fuel exhaustion. Restore only TxRevertible and retain observations.

**Open obligations.** Complete the measure, every call/create/preflight/settlement inequality and all four actual theorem statements. Numeric schedule positivity alone does not prove whole-iteration progress. Propagate InternalError through every caller before claiming the guest's O11 branch unreachable.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Supplied entry-kind seam:** the Runner facade exports the owned `ExecKind`;
  Conformance imports its private constructor/elimination/disjointness clients.
  Consumers reuse this carrier when the prospective `Exec` interface is defined;
  its exact relation form and every execution/termination obligation remain open.
- **Supplied budget seam:** reuse the existing `EthVmCore.GasMeter` and its `phi`
  directly; the public Runner facade exports the three policies and EthConformance
  imports their private clients/guards. Callbacks accept every raw meter. No runner
  consumes a policy yet and no default is installed; B11/F11 and O11 remain open.
- **Supplied checked-carrier seam:** the Runner facade exports `InternalError`,
  `CheckedResult` and `CheckedT`; EthConformance imports their private clients. The
  F14 RunM/runVmChecked adapter and ordinary equation are supplied; actual caller
  propagation, F11 and O11 projection remain open.
- **Depends on:** `EthVmInstructions`, `EthCurve` (secp256k1 recovery for EIP-7702 authorities, D26; the runner calls `secp256k1Recover` directly, as EELS does).
- **Used by:** `EthBlock` (`processTopLevelChecked` for user and system transactions; `TransactionOutput`), transitively `EthFork` (supplies `RunnerEnv`: the precompile table from `EthPrecompiles`, one `VmConfig` and `systemAddress` through BlockConfig.runnerEnv; recovery is a direct `EthCurve` call).
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

- **Core settlement assertion boundary:** EthVmCore §3/§5/§7 supplies the raw
  ChildSettled predicate and constructive Decidable instance only. Actual non-top
  committed-spill-zero initialization/preservation, call/create settlement and
  snapshots, returned proof production, incorporation and child/resume remain open.
  This logical decision procedure chooses neither F11 production option and
  supplies no runtime check, settled executor or generic Q83 effect bridge.

- **Checked carriers are supplied:** §3/§5/§7 own the minimal source-free error/result/transformer shapes and private complete facade clients. RunM/runVmChecked and their sole ordinary routing equation are supplied in §3/§5/§7. Actual propagation through callers, execution, budgets and guest projection remain unimplemented; F11 and G2–G7 remain open. The current sole constructor does not rule out the conditional future invariant option or establish exhaustion dead.

- **Precompile interpretation (Q83):** Core supplies only the raw shared carriers,
  transparent MeterOk (Core §3/§5) and the Q83 predicate and Id law (EthVmCore §7). The
  table action stays in base m; actual lifting through VmM/RunM and their
  transformer/error order requires an explicit local bridge. Dispatch, separate halt
  settlement and potential proofs remain open. This adds no observer API, base-error
  reinterpretation, F11 choice or G2–G7 claim.

- **Raw output records are supplied:** §3/§4/§5/§7 own the exact records and
  private complete facade clients. Actual runFrame/processCall/processCreate/
  processTopLevelChecked, toChildOutcome, source refund casts/range evidence,
  settlement, F11 and every execution/fuel/resource/readiness gate remain open.

- **Raw RunnerEnv is supplied:** §3/§5/§7 own its exact three-field Monad-only storage and private complete facade clients. Actual config/table assembly and runtime transport remain open; no execution, F11, D5 coupling, fuel, resource or guest/readiness result follows.

- **F8 immutable address transport:** the local pure helper is supplied by EthVmCore §3/§7; raw `RunnerEnv.systemAddress` storage is supplied; createEvm copying, child inheritance and processCall emission remain unimplemented. Required controls use a nonliteral supplied address independently of the topic, through user/system entry, nested CALL/CREATE and processCreate→processCall, checking whole emitted logs and zero/self-transfer suppression. Include child success and outer revert/halt log discard under existing settlement rules. These controls prove no G2–G7, S2, F20 lifetime or resource result.

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **Termination is unproved.** The measure is a design; no recursive runner definition exists. Only the selectable budget declarations, the entry-kind carrier, the raw RunnerEnv and output carriers, the checked control carriers and F14 VM adapter of §3 are supplied. G2 (whole-iteration progress), G3 (structural termination), G4–G6 (soundness, completeness/monotonicity, sufficiency) and G7 (internal-error freedom) are all "planned". The Φ argument in §7 is an inference from reading `gas.py` and the handlers.
- **Φ + 1 per frame is only a candidate.** It relies on "every continuing opcode costs ≥ 1 execution gas" and "a child returns ≤ the potential it was granted", neither proved; the stipend accounting (2300 returned through `restore_child_gas` on preflight failure, or inside `sub_call` to the child) is covered only by the inequality `transfer cost − stipend = 9000`.
- **Top-level refund range.** `U256(gas_meter.refund_counter)` at `interpreter.py:312` requires `0 ≤ refund_counter ∧ refund_counter < 2^256`; the range proof/fault obligation remains unresolved (EthVmCore §10). The preparation cast at `:279` still executes, but its failure is unreachable by R-TOP-2's zero-refund argument.
- **Host resources.** Gas and fuel do not bound Lean stack depth, allocation or zkVM cycles (ARCHITECTURE §4). 1025 nested runner activations in compiled Lean have not been measured. In the guest process the Python recursion limit is 100,000 (py_ecc raises it; `import ethereum` alone gives 12,288, `src/ethereum/__init__.py:28–30`); deeper host limits are DISC-001 territory (O12).
- **`move_ether` preconditions**: the sender-balance assertion in EthState's `move_ether` is unreachable only because of preflight checks (CALL/CREATE) and transaction validation (top level). EthVmRunner owns the CALL/CREATE caller proof; EthBlock owns the top-level admission proof; both consume EthState's checked `moveEther` contract. Record both proofs before treating the assertion as unreachable.
- **System transactions** (`fork.py:728–780`) run with 30 M execution gas and a 16-SSTORE reservoir; `phiBudget` gives ≈ 3·10⁷ fuel, which is fine as a bound but the error path (`fork.py:715–718` raises on a failed system call) belongs to EthBlock.
- **Trace schema** (ARCHITECTURE §12) is undecided; the event order of `OpStart`/`OpEnd`/`OpException`/`EvmStop` is specified only as "EELS order".
- **The `Exec` relation** is not yet defined; the supplied `ExecKind` carrier settles only its entry-tag vocabulary; `Exec`'s exact form (big-step over frames with nested `Exec` premises for children) must be fixed before G4/G5 can be stated precisely.
- **EIP-8037 cross-frame refunds** (`test_state_gas_cross_frame_refund.py`) exercise the repay path whose Φ-neutrality is only source-checked.
- **Pre-dispatch vs dispatch rollback** (delegations kept after a dispatched failure, reverted after a preparation failure) is specified from comments and code (`gas.py:459–490`, `interpreter.py:270–276`); no targeted `#guard` exists yet.
