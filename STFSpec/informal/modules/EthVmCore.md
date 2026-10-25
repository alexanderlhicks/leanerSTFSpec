# `EthVmCore`: EVM frame, environments, stack, memory, 2-D gas meter, jumpdest analysis

*Status: informal specification, draft. Date: 2026-10-24. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F1, F2, F3, F8, F9, F11, F12, F20 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D1, D5, D11, D13, D14, D17, D22, D23, D24, D25, D27 · questions: B7/Q24, B8/Q1/Q26/Q43, B14/Q23, F11, Q61, Q62, Q63, Q64, Q65, Q66.*

Paths in `file:line` references are relative to `src/ethereum/forks/amsterdam/vm/` unless they start with another directory. "[V]" marks a claim checked against the pinned source by reading; "[I]" marks an inference not yet checked by execution or proof.

## 1. Purpose

`EthVmCore` (root `STFSpec.Vm.Core`, layer L3 of ARCHITECTURE §2) holds everything an opcode handler needs except the handlers themselves: the call-frame record (`Evm`, split into an immutable `FrameCtx` and a mutable `Frame`), the block and transaction environments, the operand stack, memory, the two-dimensional Amsterdam `GasMeter` with its gas *policy* records (`GasCosts`, `StateGasCosts`), the frame-exit bookkeeping (`incorporateChild`, `emitTransferLog`), the exception taxonomy, and jumpdest analysis. It also hosts the transaction-level gas arithmetic of `gas.py` (allocation, settlement, blob gas, block capacity) because those are pure functions of the gas policy. It contains no recursive child interpreter, no opcode semantics and no precompile code (D17). It is the component behind replacement exercises 1 (memory) and 3 (gas-rule patch), and it owns the per-operation laws of the gas potential Φ ([REVIEW §7](../REVIEW.md#7-acceptance-criteria-proof-gates-composition-cases-replacement-and-cost-checks) G1).

## 2. Requirements

### 2.1 Frame and environments

- **R-ENV-1** `BlockEnvironment` (`__init__.py:49–67`) must carry `chain_id : U64`, `block_gas_limit : Uint`, `block_hashes : List Hash32` (oldest first, at most 256, possibly fewer in the stateless setting: `stateless.py:254` builds it from the witness headers only), `coinbase`, `number : Uint`, `base_fee_per_gas : Uint`, `time : U256`, `prev_randao : Bytes32`, `excess_blob_gas : U64`, `parent_beacon_block_root`, `slot_number : U64`. The EELS fields `state : BlockState`, `block_access_list_builder` and `transaction_public_keys` are **not** in the Lean record: the block state is part of the VM world (§5), the BAL builder and public-key hints are never read by the VM [V: `grep` over `vm/`] and belong to `EthBlock`.
- **R-ENV-2** `TransactionEnvironment` (`__init__.py:125–148`) must carry `origin`, `recipient`, `is_create`, `data`, `value`, `gas_limit`, `effective_gas_price`, `execution_gas_grant`, `state_gas_reservoir`, `calldata_floor`, `access_list_addresses`, `access_list_storage_keys`, `blob_versioned_hashes`, `authorizations`, `index_in_block`, `tx_hash`. It is immutable during execution **except** `accounts_with_paid_writes`, which only `set_delegation` mutates (`eoa_delegation.py:310–312`); in Lean that set is threaded out of `setDelegation` (EthVmRunner), not stored mutably. `state : TransactionState` moves into the VM world.
- **R-ENV-3** `Evm` (`__init__.py:153–191`) is split: `FrameCtx` = the call parameters fixed at frame creation (`block_env`, `tx_env`, `caller`, `current_target`, `value`, `call_data`, `code_address`, `code`, `valid_jump_destinations`, `depth`, `should_transfer_value`, `is_static`, `disable_precompiles`); `Frame` = `pc`, `stack`, `memory`, `gas_meter`, `logs`, `accounts_to_delete`, `return_data`, `accessed_addresses`, `accessed_storage_keys`. EELS's `running`, `output` and `error` are replaced by the `StepResult` constructors (EthVmInstructions) and `parent_evm` is replaced by the runner's recursion (EthVmRunner). **Handlers must not be able to modify `FrameCtx`**, in particular `depth` (ARCHITECTURE §5.5, "improvement over EVMLean").
- **R-ENV-4** `BlockOutput` (`__init__.py:72–120`): the VM-visible part is the gas counters `block_gas_used`, `block_state_gas_used`, `blob_gas_used`, used by `check_block_gas_capacity`. The full record (tries, receipts, logs, requests, BAL) needs `EthCommit` and `EthBlock` types and must be declared in `EthBlock`; this module specifies only `BlockGasCounters` (D27).

### 2.2 Frame exit

- **R-INC-1** `incorporateChild parent child` (`__init__.py:194–250`) must add the child's `gas_left`, `state_gas_left`, `state_gas_spilled` and `refund_counter` to the parent's **unconditionally**, then, only if the child succeeded, call `repay_state_gas_spill` on the parent meter, append the child's logs, and union `accounts_to_delete`, `accessed_addresses` and `accessed_storage_keys`. It must be total: the three EELS `assert`s (`:227`, `:232–234`) become preconditions discharged by the runner's settlement lemmas (§7, `L-SETTLE`), never runtime checks. Because a child starts with a copy of the parent's access sets (`instructions/system.py:171–172, 440–441`) and only adds to them, the union equals the child's sets [I]; the implementation may use that (`L-WARM-MONO`).
- **R-LOG-1** `emitTransferLog` (`__init__.py:253–289`, EIP-7708) must be a no-op for amount 0, and otherwise append `Log(SYSTEM_ADDRESS, [TRANSFER_TOPIC, pad32 sender, pad32 recipient], be32 amount)` to the frame's logs. `SYSTEM_ADDRESS = 0xff…fe`. `TRANSFER_TOPIC = keccak256("Transfer(address,address,uint256)")` (`:40`) is a keccak-derived constant, so under D5 it is not a literal here: it is the `transferTopic` field of `HashConsts` (EthBase), acquired at the caller-owned F20 boundary through `HashConsts.query` (EthHash) and read from `world.tx.block.consts`. The caller projects that existing context field, with local notation `TRANSFER_TOPIC`, and passes the topic to the pure `emitTransferLog` helper. World-consuming operations read the record from that context. At `m := Id` its value is `0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef` [V: computed with the pinned EELS `keccak256`]; the check that `HashConsts.query` at `Id` equals this literal belongs to a module that can see `EthHash`.

### 2.3 Stack

- **R-STK-1** The stack holds at most 1024 words. `pop` on an empty stack must fail with `StackUnderflowError` (`stack.py:109–110`); `push` on a full stack with `StackOverflowError` (`:128–129`). Both are exceptional halts.
- **R-STK-2** `decode_single x` (`stack.py:25–53`, EIP-8024) must fail with `InvalidParameter` for `91 ≤ x ≤ 127` and otherwise return `(x + 145) mod 256`, which lies in `17…235`. `decode_pair x` (`:56–91`) must fail for `82 ≤ x ≤ 127`; otherwise with `k = x xor 143`, `(q, r) = divmod k 16`, return `(q+1, r+1)` if `q < r` else `(r+1, 29−q)`. The forbidden ranges contain `0x5B` (JUMPDEST) and `0x60–0x7F` (PUSH1–PUSH32), so jumpdest analysis need not skip these immediates [V: `runtime.py` does not].

### 2.4 Memory

- **R-MEM-1** Memory is a byte sequence whose length is always a multiple of 32 [I: every expansion adds `ceil32(end) − ceil32(size)`, `gas.py:801–811`]. `memory_write m start v` (`memory.py:20–36`) overwrites `[start, start+|v|)`; callers guarantee the window lies inside memory after expansion; an **empty** write at any `start`, even beyond the end, must be a no-op (Python slice assignment `m[s:s] = b""`). `memory_read_bytes` (`:39–60`) returns the window; an empty read at any start returns empty. `buffer_read buf start size` (`:63–83`) returns `buf[start, start+size)` right-padded with zeros to `size`, for any `start` (including `start ≥ |buf|` and `start ≥ 2^64`).
- **R-MEM-2** Expansion must be priced **before** it is performed: no handler may allocate memory before the corresponding `charge_gas` succeeds (every handler follows `calculate_gas_extend_memory` → `charge_gas` → `memory += zeros`). With `Nat` gas this bounds the allocation by the available gas.

Q62 makes alignment structural and admits read/write windows through only the local
proofs in §5. Empty reads/writes are valid at every Nat offset; check emptiness
before runtime offset narrowing or index traversal, without work proportional to
an unused huge offset. Expansion appends exactly its aligned byte increment. Raw
source reads clip and raw writes may grow outside the admitted domain
(`memory.py:20–60`); source agreement is conditional on admitted typed-source
inputs and host premises, without a new guest rejection. New frames initialize
empty memory (`interpreter.py:227`, `instructions/system.py:166,435`).

### 2.5 Gas meter (EIP-8037 two-dimensional gas)

`GasMeter` (`gas.py:270–336`) has `gas_left` (execution gas), `state_gas_left` (reservoir), `state_gas_baseline`, `refund_counter : int` (default 0), `state_gas_spilled` (default 0), `state_gas_committed_spill` (default 0). Execution and state amounts are `Nat` (`ExecutionGas`/`StateGas` are `NewType`s of `Uint`, `fork_types.py:37–39`); **`refund_counter` must be `Int`** (it goes negative within a frame, `instructions/storage.py:134`). Every function in `gas.py`, with its effect:

| Function (line) | Effect (normative) |
|---|---|
| `check_gas` (:374) | fail `OutOfGasError` iff `gas_left < a`; no mutation |
| `charge_gas_from_meter` (:391), `charge_gas` (:408) | fail iff `gas_left < a` (meter unchanged on failure); else `gas_left −= a`. `charge_gas` additionally emits a trace event (diagnostic only, §7 of ARCHITECTURE) |
| `charge_state_gas_from_meter` (:425), `charge_state_gas` (:451) | if `state_gas_left ≥ a`: reservoir `−= a`; elif `state_gas_left + gas_left ≥ a`: `r = a − state_gas_left`, reservoir := 0, `gas_left −= r`, `spilled += r`; else fail (meter unchanged). Charging 0 always succeeds |
| `commit_state_gas` (:471) | precondition `state_gas_left ≤ baseline`; `committed += spilled`, `baseline := state_gas_left`, `spilled := 0` |
| `restore_state_gas` (:505) | `gas_left += spilled`, `spilled := 0`, reservoir := `baseline`, `refund_counter := 0`. Committed spill untouched |
| `restore_state_gas_to_entry m R` (:532) | preconditions `baseline ≤ R`, `refund_counter = 0`; `gas_left += spilled + committed`, both spills := 0, reservoir := baseline := `R` |
| `tx_state_gas_used m T` (:570) | precondition `baseline ≤ T`; returns the `Int` `T − state_gas_left + spilled + committed` (may be negative) |
| `credit_state_gas_refund m a` (:606) | `x = min a spilled`; `gas_left += x`, `spilled −= x`, reservoir `+= a − x` (LIFO credit) |
| `repay_state_gas_spill` (:631) | `y = min reservoir spilled`; `gas_left += y`, reservoir `−= y`, `spilled −= y`; afterwards `reservoir = 0 ∨ spilled = 0` (a theorem, not a check) |
| `forfeit_remaining_gas` (:662) | precondition `spilled = 0`; `gas_left := 0` |
| `withhold_create_gas` (:678) | `g = max_message_call_gas gas_left`; `gas_left −= g`; returns `g` |
| `drain_state_gas_reservoir` (:701) | returns the reservoir and sets it to 0 (no 63/64 rule for state gas) |
| `restore_child_gas m g R` (:725) | `gas_left += g`, reservoir `+= R` (child never entered) |
| `calculate_memory_gas_cost s` (:749–773) | With `w = ceil32(s)/32`, return `GasCosts.MEMORY_PER_WORD*w + ⌊w²/512⌋`; ZERO is not read. The caught `ValueError` is absent under stable typed Uint/ExecutionGas-NewType bindings. Source/host correspondence retains those premises. |
| `calculate_gas_extend_memory m ws` (:776–813) | Initialize extent with literal 0 and cost with `GasCosts.ZERO`; fold in order, skip size 0 before endpoint work, and convert each nonzero start/size to unbounded Nat observations before addition. On strict rounded growth add extent and two-cost differences. Returns values without charge, append or Memory mutation. |
| `calculate_message_call_gas v g L mem extra stipend` (:816) | Select `t = GasCosts.ZERO` if `v = 0`, otherwise the passed/default-captured stipend; if `L < extra + mem`, return `(g + extra, g + t)` before subtraction/capping. Otherwise use the existing maximum on `(L − mem) − extra` and cap the request, then add extra/t to the two fields. Pure values only; the caller charges the complete applicable amount. Q64 owns the explicit Lean policy argument; §5/§7 give its supplied contract. |
| `max_message_call_gas g` (:861) | `g − ⌊g/64⌋` (EIP-150) |
| `init_code_cost n` (:879) | `(GasCosts.CODE_INIT_PER_WORD * ceil32(n)) // 32`, multiplication first (EIP-3860). This reads the word price; §5/§7 give Q64's supplied explicit-policy contract. |
| `calculate_excess_blob_gas` (:901) | from the parent's `(excess_blob_gas, blob_gas_used, base_fee_per_gas)` (zeros when absent): 0 if `excess + used < 14·2^17`; if `2^13 · base_fee > 2^17 · blob_price(excess)` return `excess + used · 7 / 21`; else `excess + used − 14·2^17` |
| `calculate_total_blob_gas` (:951) | `2^17 · \|blob_versioned_hashes\|` for blob transactions, else 0 |
| `calculate_blob_gas_price e` (:972) | `taylor_exponential(1, e, 11684671)` (`utils/numeric.py`, EthBase) |
| `calculate_data_fee` (:994) | total blob gas × blob gas price |
| `check_max_fee_per_blob_gas` (:1016) | no check without blobs; else fail iff `max_fee_per_blob_gas < price` |
| `check_block_gas_capacity` (:1053) | fail iff `min(2^24, tx_gas) > limit − block_gas_used`, or `tx_gas > limit − block_state_gas_used`, or `tx_blob_gas > 21·2^17 − blob_gas_used`, in that order |
| `allocate_evm_gas tx_gas intr` (:1120) | `available = txGas − intrinsicExecution`; `execution = min(cfg.costs.txMaxGasLimit − intrinsicExecution, available)`; reservoir `= available − execution`. Q65's supplied helper takes exactly the two local subtraction proofs in §5; source matching of the live cap is separate. |
| `settle_transaction_gas` (:1178) | `p = txGas − gasLeft − stateGasLeft`; `c = min(p/5, refund.toNat)` for U256 refund; `gasUsed = max(p − c, floor)`; `S = stateGasUsed.toNat` clamps signed state usage; `executionGasUsed = max(p − S, floor)` (EIP-7778: pre-refund); returned gas `= txGas − gasUsed`. Q66's three local bounds and source order are in §5/§7. |

- **R-GAS-1** Every EELS `assert` above is a precondition of the Lean operation, discharged by callers (§7). The Lean operations must not contain fallible checks that EELS does not have.
- **R-GAS-2** Gas amounts are unbounded `Nat`; charging is checked; no wrapping, no saturating subtraction that hides a failed check.
- **R-GAS-3** `GasCosts` and `StateGasCosts` (`gas.py:48–259`) are fields of a gas-policy record, not literals inside handlers (ARCHITECTURE §8). The record also holds every precompile pricing dependency that EELS keeps outside `GasCosts` (DECISIONS B8, F9; §5). This module defines the record types; the Amsterdam values live in `EthFork`. In the EthFork instantiation, derived constants must be computed from their components as in EELS: `CALL_VALUE = ACCOUNT_WRITE + CALL_STIPEND = 11300`, `CREATE_ACCESS = 12000`, `REFUND_STORAGE_CLEAR = (10000 + 2100)·4800/5000 = 11616`, `STORAGE_SET = 64·1530 = 97920`, `NEW_ACCOUNT = 120·1530 = 183600`, `AUTH_BASE = 23·1530 = 35190`, `EXECUTION_PER_AUTH_BASE_COST = 101·16 + 3000 + 3000 + 2·100 = 7816`, `TX_ACCESS_LIST_ADDRESS = 2900`, `TX_ACCESS_LIST_STORAGE_KEY = 2000`, `MAX_BLOB_GAS_PER_BLOCK = 21·2^17`.

### 2.6 Exceptions

- **R-EXC-1** `ExceptionalHalt` (`exceptions.py:17`) has the subclasses `StackUnderflowError`, `StackOverflowError`, `OutOfGasError`, `InvalidOpcode(code)`, `InvalidJumpDestError`, `StackDepthLimitError`, `WriteInStaticContext`, `OutOfBoundsRead`, `InvalidParameter`, `InvalidContractPrefix`, `AddressCollision`, `KZGProofError`; precompiles also raise bare `ExceptionalHalt` (`precompiled_contracts/modexp.py:34, 38, 42`). `Revert` (`:24`) is **not** an exceptional halt. The Lean type must keep one constructor per class (for traces and receipts' diagnostics) although every exceptional halt has the same effect (O8): spill restored, remaining execution gas forfeited, output empty.
- **R-EXC-2** Non-EVM failures that EELS raises from inside the VM as ordinary Python exceptions must be kept **separate** from `ExceptionalHalt` in a `VmFault` type, because the guest maps them to a failure output rather than to a halted frame (`stateless.py:303` catches `Exception`): `witness` (missing trie/code data, O4, from `EthState`), `ancestorHashUnavailable` (BLOCKHASH beyond the witness headers, a Python `IndexError`, see EthVmInstructions), `u256Overflow` (Python `OverflowError` from `ethereum_types`: an out-of-range top-level refund in `U256(refund_counter)` (`interpreter.py:285,318`; §3 preserves both checked casts and their order, with the preparation-zero argument owned by EthVmRunner R-TOP-2), or `U256(calculate_blob_gas_price(…))` in BLOBBASEFEE (`instructions/environment.py:607`)). A recipient balance exceeding 2^256−1 in `move_ether` is also an `OverflowError`; it is raised inside `EthState` and arrives as `state`. The `U256(...)` casts in NUMBER, GASLIMIT and BASEFEE cannot overflow, because the SSZ payload field widths (`uint64`, `uint64`, `uint256`) rule it out, so they have no constructor. These faults are CONTRACT **O13** members (D14): the existing invalid output, one named constructor each, never a catch-all. BLOCKHASH's `IndexError` (`instructions/block.py:58`) is witnessed by the fixture `validation_headers_missing_oldest_blockhash_ancestor`; the reachability of the others is argued in the failure ledger (maintained outside this repository). `InternalError` (O11) is a different type again (EthVmRunner).

### 2.7 Jumpdest analysis

- **R-JD-1** `validJumpDestinations code` (`runtime.py:22–69`) must equal the set of `pc < |code|` such that `code[pc] = 0x5B` and `pc` is not inside PUSH1–PUSH32 immediate data, scanning from 0 and skipping `n` bytes after an opcode `0x60 + n − 1`. Bytes that are not opcodes (for example `0xFE`, `0x0C`) advance by one. It must be defined on raw bytes: `EthVmCore` cannot import the opcode enum.

## 3. EELS source map

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `forks/amsterdam/vm/__init__.py::TRANSFER_TOPIC` | 40 | `HashConsts.transferTopic` (EthBase field), read from `world.tx.block.consts` | not a literal (D5, F2); the `Id` value is checked outside Core (R-LOG-1) |
| `forks/amsterdam/vm/__init__.py::SYSTEM_ADDRESS` | 41 | `SYSTEM_ADDRESS : Address` | EIP-7708 log emitter; also used by `EthBlock` system calls |
| `forks/amsterdam/vm/__init__.py::BlockEnvironment` | 49 | `structure BlockEnvironment` | minus `state`, BAL builder, key hints (R-ENV-1) |
| `forks/amsterdam/vm/__init__.py::BlockOutput` | 72 | `structure BlockGasCounters` here; full record in `EthBlock` | D27 |
| `forks/amsterdam/vm/__init__.py::TransactionEnvironment` | 125 | `structure TransactionEnvironment` | `state` and `accounts_with_paid_writes` threaded |
| `forks/amsterdam/vm/__init__.py::Evm` | 153 | `structure FrameCtx`, `structure Frame`, `structure Evm` | R-ENV-3 |
| `forks/amsterdam/vm/__init__.py::incorporate_child` | 194 | `incorporateChild` | total; asserts → preconditions |
| `forks/amsterdam/vm/__init__.py::emit_transfer_log` | 253 | `emitTransferLog` | EIP-7708 |
| `forks/amsterdam/vm/exceptions.py::*` | 17–139 | `inductive ExceptionalHalt`, `inductive FrameError` | all 15 items (classes and `InvalidOpcode.__init__`) |
| `forks/amsterdam/vm/gas.py::*` | 48–1243 | `GasCosts`, `StateGasCosts`, `GasMeter` and one function per EELS function (§5) | all 43 items; blob/capacity/settlement functions take plain numbers instead of `Header`/`Transaction`/`BlockOutput` |
| `forks/amsterdam/vm/memory.py::*` | 20–83 | `Memory.write`, `Memory.readBytes`, `bufferRead` | |
| `forks/amsterdam/vm/stack.py::pop` | 94–112 | `Stack.pop` | bounded typed-source domain below |
| `forks/amsterdam/vm/stack.py::push` | 115–131 | `Stack.push` | bounded typed-source domain below |
| `forks/amsterdam/vm/stack.py::decode_single` | 25–53 | `decodeSingle` | complete UInt8 domain; precise row below |
| `forks/amsterdam/vm/stack.py::decode_pair` | 56–91 | `decodePair` | complete UInt8 domain; precise row below |
| `forks/amsterdam/vm/runtime.py::get_valid_jump_destinations` | 22–69 | `validJumpDestinations`, `JumpdestMap.contains` | supplied packed/reference refinement and three ordinary laws; raw bytes, no Lean `Ops` import |
| `forks/amsterdam/vm/interpreter.py::STACK_DEPTH_LIMIT` | 84 | `abbrev STACK_DEPTH_LIMIT : Nat := 1024`; field `VmLimits.stackDepthLimit` | declared here because `FrameCtx` and the CALL/CREATE preflight need it and neither may import the runner. A literal, because the depth proofs and indexed types need a kernel-reducible value (F8); `EthFork` sets the field to it, with `vmLimits_depth := rfl` |
| `forks/amsterdam/vm/interpreter.py::MAX_CODE_SIZE` | 85 | field `VmLimits.maxCodeSize` (Amsterdam value `0x10000`, in `EthFork`) | EIP-7954; used by the runner's code deposit |
| `forks/amsterdam/vm/interpreter.py::MAX_INIT_CODE_SIZE` | 86 | field `VmLimits.maxInitCodeSize` (Amsterdam value `2 · 0x10000`, in `EthFork`) | CREATE/CREATE2 and `EthBlock` transaction validation |

### Supplied transaction allocation and settlement (Q65, Q66)

Q65 allocation is supplied with four discharged laws and the local evidence
recorded below in this section; Q66 settlement is supplied with five discharged laws.
§5 owns the exact value/proof APIs and raw result records; §7 owns their four/five
ordinary law types. Source correspondence retains stable typed numeric/class
bindings and successful host/resource premises.

| Pinned source | Declaration / domain | Effects, ordered failures and evidence |
|---|---|---|
| `src/ethereum/forks/amsterdam/vm/gas.py:1106–1152` | `EvmGasAllocation`, `allocateEvmGas`; arbitrary raw VmConfig and Nat transaction/intrinsic gas on the two local proof bounds in §5. Only intrinsic.execution is read from the source IntrinsicGasCost. | Pure complete two-field result, no meter/currency effect. Source subtracts transaction minus intrinsic at :1148 before live cap minus intrinsic at :1149, then min and residual. Failed bounds remain outside the target domain; no saturation or fabricated proof. §7's four laws are discharged; complete-result/public-law and finite source controls are supplied below in this section. |
| `src/ethereum/forks/amsterdam/vm/gas.py:1157–1243` | `TransactionGasSettlement`, `settleTransactionGas`; arbitrary Nat gas values, existing U256 refund and signed Int state usage on the three local proof bounds in §5. | Pure complete four-field result, no fee/provider or block mutation. Returned-gas subtractions precede refund/floor, then state clamp and execution subtraction before max, then final sender-return subtraction. Failed-domain cases are source-only. §7's five ordinary laws are discharged; complete local controls and public-law clients are supplied below. |

Allocation's source `TX_MAX_GAS_LIMIT` is the live Uint cap at `gas.py:162`,
distinct from `TX_MAX_TOTAL_GAS_LIMIT` at :163. Generic cfg laws do not assume a
literal, cap positivity or cap alias. Original correspondence requires the
supplied relevant cap to match the authenticated live source cap, with stable
typed inputs/numeric/class bindings and successful host/resource premises.
The ordinary direct caller validates first (`fork.py:576,620`): intrinsic versus
transaction gas, floor versus transaction gas, intrinsic versus execution cap,
floor versus execution cap (`transactions.py:675–687`), after the earlier total
cap check at :643–644. Preserve that order even though allocation ignores floor.
Admission/allocation caps must be consistent, or the caller proves the allocation
bound separately; validation under a larger cap alone is insufficient. The two
result fields flow into the environment (`fork.py:655–657`) and entry meter
(`vm/interpreter.py:267–271`), without charging intrinsic again. System
transactions supply independent grants and bypass allocation (`fork.py:791–806`).

Settlement reads no VmConfig. Its literal divisor 5 and signed-state clamp 0 stay
in the equation. U256 refund supplies its unsigned range; it does not establish
that a signed meter refund can be converted. Runner's prospective
`TransactionOutput.refundCounter : Nat` stays unchanged (EthVmRunner §5).
Successful source correspondence must retain `n < 2^256` for that Nat observation
and reconstruct a U256 with complete unsigned observation n through existing
`U256.ofNat?_eq_some_iff`, `U256.ofNat?_toNat` and `U256.toNat_lt`. Actual range
derivation and this caller bridge are unimplemented; no public adapter is added.

Ordinary unsigned `U256(r)` needs `0 ≤ r ∧ r < 2^256`
(`ethereum_types/numeric.py:44–48,611–612,690–712`), unlike Base `U256.ofInt?`,
which models signed `from_signed` (:594–608). Do not clamp negative refund with
Int.toNat or wrap it with unchecked ofNat. Both source conversions stay at their
original runner points: preparation restore/forfeit at `interpreter.py:280–282`
precedes cast :285, which precedes state-usage argument :291–293; normal
TransactionEnd tracing :309–314 precedes cast :318, which precedes state usage
:324–326. The preparation-zero argument remains EthVmRunner R-TOP-2's guidance;
no new actual caller proof or removed conversion follows. Preserve the existing
separate proof/fault obligation at each applicable cast, including the unresolved
normal return, before block settlement (`fork.py:1101–1110`). No new O13
classification or helper error is chosen. Int.toNat on signed **state usage**
instead expresses precisely the intended source `max(0, state_gas_used)` clamp.

### Supplied local transaction settlement (Q66)

`STFSpec/Vm/Core/TransactionGasSettlement.lean`, exported by `STFSpec.Vm.Core`,
supplies the unrestricted raw four-Nat carrier and exact three-proof helper in §5.
Its only direct import is Base.U256. The five ordinary laws in §7 are discharged;
no authored instance, default, policy, public conversion, extra helper or error is supplied.

The private public-law clients cover arbitrary raw construction/ext/eta and every
single-field replacement/congruence; sender conservation and ranges; both block
dimensions and their independent floor branches; capped-refund/read-set equality;
negative-state erasure and equal-positive-part congruence. They derive
`X + S = max p (F + S)` and `U + c = max p (F + c)`, with their below-floor
specializations. The sum of block dimensions exceeds transaction gas in S20/S21 and sender
gas usage in S22. Neither sum is an invariant of the raw carrier.

An entry-meter client assumes `T = I + E0 + R0`, returned sum ≤ T,
baseline ≤ R0 and explicit final potential ≤ I + E0. Through the public signed
observer equation it derives the positive-part state bound needed by settlement.
An allocation client derives the entry partition and execution grant cap through
`allocateEvmGas_eq`, then derives settlement execution ≤ the same cap, with
explicit final potential, returned, baseline and both floor bounds. These are
conditional local algebraic clients; they do not instantiate an actual Runner.

The complete handwritten catalog has S01–S44 helper calls, each with all three
proofs, followed by R01–R06 raw constructors and actual eta reconstructions.
Both interpreted and native producers call the real operation/constructor and
emit every input before/after and all four result coordinates. The strict reader
compares complete frames to those literals. Its frozen regressions comprise
184 target/source frames (4 accepted, 180 rejected) and 50 local-domain cases
(44 accepted, 6 rejected), identically under ordinary Python and `-O`, with no
EELS import in target/parser modes. Help exits 0; missing mode exits 2.

```sh
lake build transaction-gas-settlement-native-tests --wfail
lake exe check-decls TransactionGasSettlementNativeTests
lake exe transaction-gas-settlement-native-tests > .lake/transaction-gas-settlement.jsonl
python3 -B STFSpec/Conformance/Vm/Core/transaction_gas_settlement_differential.py --check-target .lake/transaction-gas-settlement.jsonl
python3 -B scripts/test_transaction_gas_settlement_output_parser.py
python3 -B -O scripts/test_transaction_gas_settlement_output_parser.py
```

The dated 2026-10-24 original-source schedule passed exactly 44 complete
helper/native/literal comparisons followed by eight source-only typed arithmetic
failures. All 52 direct unchanged-helper entries preserve complete actual inputs,
classes, context and original traceback sites; raw records are target-only. The
finite before/after captures retain whole physical modules, structural whole-file
code matches, installed RECORD/lock, runtime/compiler/native artifacts and stable
actual Uint/U256, identity NewTypes, dataclass, plain signed int, builtins/defaults
and method bindings. Marshal hashes describe this interpreter, without a byte
canonicality requirement. CPython/generated dataclass/native NewType/ambient
runtime and successful host premises remain explicit trust boundaries.

The same-line first/second initial subtraction priority is the static
left-associated source fact; a traceback does not distinguish those subexpressions.
No negative-refund constructor probe, raw source dataclass construction,
caller/provider execution, random extension or helper replay is part of this slice.
These are finite observations, not a universal source/host or actual Runner theorem.

### Supplied raw block-gas counters

`STFSpec/Vm/Core/BlockGas.lean`, exported through `STFSpec.Vm.Core`, supplies
the existing R-ENV-4 three-field projection carrier. D27 leaves the containing
full `BlockOutput` with EthBlock; there is no Python `BlockGasCounters` class.

| Pinned source | Supplied declaration / complete raw domain | Effect / laws / evidence |
|---|---|---|
| `src/ethereum/forks/amsterdam/vm/__init__.py:104,105,118`; `src/ethereum/forks/amsterdam/fork_types.py:37,39` | `BlockGasCounters.mk : Nat → Nat → U64 → BlockGasCounters`; projections `blockGasUsed`, `blockStateGasUsed`, `blobGasUsed` in that order. The first two map `block_gas_used : ExecutionGas` and `block_state_gas_used : StateGas`, each a Uint NewType; the third maps `blob_gas_used : U64`. | **Discharged** raw constructor/projections and exactly two ordinary laws, `BlockGasCounters.ext`/`BlockGasCounters.eta` (§7). All Nat/Nat/U64 records, no failure or state effect; private public-only clients and ten complete field-order guards (§4). |

The selected source fields belong to `BlockOutput` (`__init__.py:72–120`)
and are read separately by capacity checking (`gas.py:1088–1094`). Source
zero defaults are not Lean defaults or raw-record invariants. Every Nat value
is admitted, including values beyond 2^64 and 2^256; blob values retain the
existing Base.U64 domain. The record has no authored instances, factory, proof field,
limit, policy or adapter. Cumulative gas paid (`__init__.py:106`), tries,
receipt keys, logs, requests and BAL stay outside this projection. This is
field/type correspondence on intended typed source values, not a full source
constructor, mutable-object or capacity-operation refinement. Capacity arithmetic,
checked failures/precedence and actual block integration remain separate (§10).

### Supplied chronological logs and ropes

`STFSpec/Vm/Core/Logs.lean`, exported by `STFSpec.Vm.Core`, supplies the existing
raw `Log`, public `LogRope.empty/leaf/concat`, `toList` and `append` interfaces.
`Log` retains complete Address, ordered arbitrary-length `Array Hash32` and Bytes
fields; producer topic limits are not carrier premises. The six ordinary public
laws in §7 are discharged, including `Log.ext/eta`. Public constructors retain
observable raw shapes; chronological observation respects association and empty
identities without a structural append contract.

| Pinned source | Supplied declaration / domain | Complete effect and failures | Public law / evidence |
|---|---|---|---|
| `blocks.py:327–356`; `state.py:33`; `crypto/hash.py:19` | `Log` on all existing provider fields | Exact address, topic order/duplicates and every data byte; no runtime failure | `Log.ext`, `Log.eta`; arbitrary-field public-only clients and complete A/B/C/D observations |
| `vm/__init__.py:169`; `vm/interpreter.py:230`; `vm/instructions/system.py:169,438` | Public empty/leaf/concat and `LogRope.toList` on every finite raw tree | Complete chronological List, including empty leaves and repeated/shared occurrences | `toList_empty/leaf/concat`; private ordinary all-tree workstack/reference refinement and full-field controls |
| `vm/__init__.py:247`; `vm/instructions/log.py:47–80,86–90`; `vm/__init__.py:253–289` | `LogRope.append` on arbitrary ropes; singleton emission is a model client | All left log occurrences then all right; no carrier failure | `toList_append`; public-only singleton/duplicate/order clients; LOG/transfer handlers remain unsupplied |
| `vm/__init__.py:194–250`; `vm/interpreter.py:276–321` | Conditional merge/discard and output-selection model clients only | Failed children contribute no logs; top-level error selects empty output without erasing stored logs | Six complete S controls and ordinary arbitrary-log algebra; no real incorporation/frame/receipt proof |

The source correspondence here is the ordered tuple model on intended typed
immutable Log values. Optional mutable Python construction (`_frozen=False`) and
arbitrary malformed objects are outside that correspondence. There is no Python
LogRope helper to replay; accepted source text supplies the boundary. LOG's stack,
gas, expansion and static-check order, transfer HashConsts acquisition, child
settlement and receipt/bloom/block consumers remain with their existing owners.

### Supplied jump-destination analysis

`STFSpec/Vm/Core/Jumpdest.lean`, exported through `STFSpec.Vm.Core`, supplies the
abstract immutable `JumpdestMap`, the two existing operations in §5 and exactly
three ordinary public lookup equations in §7. The fast builder scans actual
Base.Bytes packed input without constructing the List reference. Private ordinary
proofs establish exact bitmap length `(code.size + 7) / 8`, local byte-update
behavior, zero padding and all-code/all-Nat refinement to a structural Boolean
membership reference. Its finite set observation is `{i | reference code i = true}`;
the out-of-code proof supplies finite support without allocating a List Nat.
The constructor, code-size field, bitmap and reference stay private.

The pinned source converts each reached byte with `Ops`, catches `ValueError` and
advances invalid bytes by one. Reached PUSH1–PUSH32 skip their declared immediate
width, including truncated suffixes; PUSH0 and DUPN/SWAPN/EXCHANGE do not skip an
extra byte. The raw-byte Lean scanner implements this behavior without an opcode
enum dependency. The committed handwritten 32-case controls retain complete code,
destination sets, logical bitmap bytes, probes and held-map snapshots. Reproduce
that self-contained target path from the repository root with fresh output paths:

```sh
DRIVER=STFSpec/Conformance/Vm/Core/jumpdest_differential.py
python3 -I -B "$DRIVER" --self-test-parser
python3 -I -B -O "$DRIVER" --self-test-parser
python3 -I -B "$DRIVER" --focused32 --emit-target /tmp/jumpdest-observer.lean
lake env lean --run /tmp/jumpdest-observer.lean > /tmp/jumpdest-frames.jsonl
python3 -I -B "$DRIVER" --focused32 --compare /tmp/jumpdest-frames.jsonl
python3 -I -B -O "$DRIVER" --focused32 --compare /tmp/jumpdest-frames.jsonl
```

The driver also reads a canonical 940-input catalog and optional source observations
with a preflight binding-catalog digest. Those artifacts and their authenticated
producing step are external, rather than supplied by this comparator. The dated
[external review of the original head](https://github.com/alexanderlhicks/leanerSTFSpec/pull/167#issuecomment-6268899065)
records the finite interpreted/native and retained-source comparisons separately.
They retain actual typed Bytes/Ops/Uint bindings and successful host premises;
those historical results are not a fresh repository source execution. Logical
bitmap output is reconstructed through public membership; private physical shape
and padding are established by the ordinary proofs. Actual code/map provenance,
cache consistency, handler ordering, compiled cost/ownership and guest obligations
remain open (§10).

### Supplied raw GasCosts data

`STFSpec/Vm/Core/GasCosts.lean`, exported through `STFSpec.Vm.Core`, supplies
exactly the existing class-plus-seven-BLS data boundary: 144 public fields in
the source/guidance order listed in §5. Type ownership is EthVmCore; Amsterdam
values and alias/derived-value coherence belong to EthFork. This supplies data,
not a complete supported pricing policy or an initialized VmConfig.

| Pinned source / guidance boundary | Declaration and domain | Effect / laws / evidence |
|---|---|---|
| `gas.py:72–259`, all 137 class fields in source order | `GasCosts` constructor/projections; 132 Nat, one signed Int refund and four existing Base.U64 fields | Raw data, no failure or state effect; ordinary `GasCosts.ext`/`GasCosts.eta`; full supplied-constructor/public-law clients |
| `precompiled_contracts/bls12_381/bls12_381_pairing.py:46`; B8/F9 | `blsPairingBase`, `blsPairingPerPair : Nat`, appended after the class fields | Independent raw scalars; values belong to EthFork |
| `precompiled_contracts/bls12_381/__init__.py:37,168`; B8/F9 | `blsG1KDiscount`, `blsG2KDiscount : Array Nat`, next in order | Arbitrary complete ordered arrays, including empty/short arrays; no index premise supplied |
| `precompiled_contracts/bls12_381/__init__.py:299–301`; B8/F9 | `blsG1MaxDiscount`, `blsG2MaxDiscount`, `blsMultiplier : Nat`, last in order | Independent raw scalars, including zero multiplier; no divisor premise supplied |

The exact total is 137 Nat, one Int, four Base.U64 and two Array Nat. The record
has no defaults, deriving/instances, proof fields, predicate, factory, additional
helper or pricing field. Nat fields are arbitrary and unbounded; refund may be
negative. Existing U64 bounds are retained without granting product-range facts.
Copied source aliases remain independent raw fields: veryLow need not equal
opcodeAdd, zero need not be 0, and callValue need not be accountWrite+callStipend.
These relationships are future fork-initialization obligations.

Exactly two ordinary laws are discharged (§7). Private public-import clients
construct the full record on 144 independently supplied arguments, consume eta
and all-field ext without unfolding provider implementations, and prove that
the complete existing `chargeGas g c.opcodeAdd` result depends only on that selected
projection and the same meter. Existing public charge laws yield exact success
updates and exclusive out-of-gas failure on their actual affordability domains.
This is a numeric charge client, not an ADD handler or an opcode-order theorem.
No 144-row projector/substitution runtime suite, record-only wire/parser/native
framework, benchmark or original imported-value acquisition is involved.

The enumerated data seam is partial B8 coverage. MODEXP's floor500 and formula
classification, module-derived MAX_BLOB_GAS_PER_BLOCK placement/checked-U64 range,
the separate StateGasCosts stored-versus-computed representation, BLS executable
index/denominator support, and the actual EthFork factory/config coherence remain
open at their owners. Those obligations block their corresponding claims, not
this raw record. Memory pricing's policy-threading disposition is owned separately
by Q63; this raw-data seam supplies no pricing function, ZERO interpretation or
32/512 choice.
Record equality proves no supported-policy, termination, resource or guest gate.

### Supplied raw VM configuration data

`StateGasCosts`, `VmLimits` and `VmConfig` supply exactly the existing raw data
contracts in §5. Core owns their types; EthFork owns actual values, derived
equations and configuration consistency. Each record has ordinary public
construction/projections and exactly two discharged ordinary laws, ext and eta
(§7). There are no defaults, deriving/instances, proof fields, predicates,
factories, additional amount/config fields or semantic helpers.

| Source / existing grouping | Supplied declaration and complete domain | Local laws and evidence |
|---|---|---|
| `src/ethereum/forks/amsterdam/vm/gas.py:56–59`; existing four-field sketch | `StateGasCosts`: costPerStateByte, bytesPerNewAccount, bytesPerStorageSet, bytesPerAuthBase, all Nat in that order. The rate field retains the explicit Nat carrier; existing Base.StateGasPerByte supplies its interpretation bridge. | Four-field constructor/projections; ordinary ext/eta; private generic full-constructor/projection/public-law clients. No failure or state effect. |
| `src/ethereum/forks/amsterdam/vm/interpreter.py:84–86`; F8 | `VmLimits`: stackDepthLimit, maxCodeSize, maxInitCodeSize, all Nat in that order. | Three-field constructor/projections and ordinary ext/eta with private generic clients; existing Stack behavior and literal-depth specialization constraints are unchanged. |
| B8, ARCHITECTURE §8; existing §5 grouping | `VmConfig`: costs : GasCosts, stateCosts : StateGasCosts, limits : VmLimits, in that order. | Complete-record constructor/projections and ordinary ext/eta. Its ext premises are actual whole GasCosts/StateGasCosts/VmLimits equalities. This is the existing Lean grouping, not a claim of an identically shaped Python class. |

All new Nat fields admit zero and arbitrary unbounded values. Raw maxInitCodeSize
need not equal twice maxCodeSize; raw stackDepthLimit need not equal the literal
depth bound. Admitting raw limits changes no existing Stack/depth behavior or
caller proof. Supplied whole GasCosts values retain every signed refund, checked
Base.U64 carrier, arbitrary BLS array and independent alias from its own data seam.

The four state inputs do not supply storageSet/newAccount/authBase observations.
Their computed-versus-independently-stored surface, universal-versus-Fork-only
equations, original-source correspondence and supported consumer domains remain
separate. No global coherence predicate, wrapper substitution or initialization
value is inferred. The source reservoir use at `src/ethereum/forks/amsterdam/fork.py:802`
is inside process_unchecked_system_transaction (:766); it does not add an amount
field to this raw-four item.

Ten private public-import clients construct every supplied record on arbitrary
typed inputs, observe every stored projection and consume all six laws. A
meaningful selected-cost client proves equality of the complete existing
chargeGas Except result for the same arbitrary meter whenever
cfg.costs.opcodeAdd agrees, without equality or coherence of unused stateCosts,
limits, other cost projections or whole configs. Explicitly varying the unused
records preserves that result. Public affordability/error laws retain the exact
whole-meter success and exclusive outOfGas domains. These are local data/charge
clients, not opcode, memory-pricing, frame or target consistency proofs.

The evidence is ordinary universal proofs, public constructor/projection clients
and declaration/axiom checks. No runtime mirror of generated projection or
substitution code, record-only native protocol/parser/benchmark, imported source
values or new oracle suite is involved. These data carriers supply construction
dependencies for Q63; its separately supplied pricing helpers and ten ordinary laws
are described below. Core/Fork values, all state amounts and consumer/coherence,
limit specialization, ordering/resource and VM/guest obligations remain open for
their corresponding claims.

### Supplied call/init-code pricing (Q64)

`CallGas.lean` supplies the two-Nat result, both pure helpers and exactly six
ordinary laws. Configurations and numeric inputs have no global WF, alias,
positivity or amount-cap premise.

| EELS source at pin | Supplied Lean declaration | Exact domain/effect/law/control entry |
|---|---|---|
| `src/ethereum/forks/amsterdam/vm/gas.py:357–371` | `MessageCallGas` | Every pair of Nat fields, cost then subCall; no defaults, proof field or invariant. `MessageCallGas.ext` and `MessageCallGas.eta` discharged; arbitrary public constructor/ext/eta clients retain both fields. |
| `src/ethereum/forks/amsterdam/vm/gas.py:816–858` | `calculateMessageCallGas` | Every cfg, U256 value and Nat gas/gasLeft/memoryCost/extraGas/selected stipend; complete pure result, no charge, state effect or new error. `calculateMessageCallGas_eq` and `calculateMessageCallGas_congr` discharged. Sixteen pinned and four generic complete-result controls, actual charge/error and public-law affordability/read-set/local-payment clients are supplied. |
| `src/ethereum/forks/amsterdam/vm/gas.py:879–899` | `initCodeCost` | Every cfg and Nat length, without a buffer or size limit; pure Nat result, multiplication before division. `initCodeCost_eq` and `initCodeCost_congr` discharged. Nine pinned and three generic complete-result controls, public-law exact-divisibility/rounding and complete checked-charge clients are supplied. |

The source reads `GasCosts.ZERO` (`gas.py:102`), the function-definition-time
captured `CALL_STIPEND` default (`:93,822`) and `CODE_INIT_PER_WORD` (`:98,897`).
The supplied scalar maximum at `gas.py:861–876`, its ordinary laws and existing
guards are reused; no duplicate implementation or legacy original replay occurs.

`CallGasCallerProofs.lean` consumes all six public laws and existing public
charge/max/ceil32 laws without unfolding providers. It proves complete result
and actual Except charge transport, default/zero/nonzero/unrelated-config
specializations, exact affordability and exclusive outOfGas, capped/retained
bounds, init word pricing and conditional local potential consequences. The
actual meter budget is used for charge affordability; all six raw meter fields,
signed refunds, reservoir above baseline and positive spill pools remain admitted.

`CallGasGuards.lean` retains all thirty-two complete hand-frozen results and six
complete actual charge witnesses. The strict `call_init_differential.py` reader
checks every input/config/result/after/type field and couples the twenty-five
pinned C/I subsets when supplied with external target/source frames and the
caller-authenticated binding digest. It does not produce or authenticate that
source baseline. The seven generic rows are target/proof-only; the nine legacy
maximum rows reuse existing guards. Normal/`-O` synthetic typed/schema/default/
framing controls are committed; consistent CRLF is an explicit reader adapter.

Reproduce the committed guards, public-law clients and strict synthetic parser
controls from the repository root:

```sh
lake build STFSpec.Conformance.Vm.Core.CallGasGuards --wfail
lake build STFSpec.Conformance.Vm.Core.CallGasCallerProofs --wfail
DRIVER=STFSpec/Conformance/Vm/Core/call_init_differential.py
python3 -I -B "$DRIVER" --self-test
python3 -I -B -O "$DRIVER" --self-test
```

The dated [external review of the original head](https://github.com/alexanderlhicks/leanerSTFSpec/pull/175#issuecomment-6271408160)
records the interpreted/native and retained-source results separately. Its original
source schedule ran once: sixteen call rows (twelve omitted/four explicit stipends)
and nine init rows. Those source observations, producing tool and provenance packet
are external to the committed reader; this is historical finite evidence rather
than an original-helper replay performed by these repository commands. The original
source LF bytes and the reader's explicit framing adaptation remain distinct.

This bounded correspondence retains stable typed runtime/dependency/callable
bindings, successful host operations and relevant current/captured-price equality.
The fixtures specialize only their relevant prices and full raw stored fields;
they are not a coherent Amsterdam config factory or arbitrary repricing experiment.
Python capture and the actual-call cfg expression remain distinct. Actual caller/
frame/target coherence, source-host generalization, payment/state spill composition,
child return/settlement, compiled/resource costs and whole G1–G7/VM/guest gates
remain open. No helper charges gas, allocates code or checks an init size limit.

### Supplied memory pricing (Q63)

| EELS source at pin | Supplied Lean declaration | Exact domain/effect/failure/model/control entry |
|---|---|---|
| `src/ethereum/forks/amsterdam/vm/gas.py:749–773` | `calculateMemoryGasCost (cfg : VmConfig) (n : Nat) : Nat` | Every cfg/n; depends only on cfg.costs.memoryPerWord. Pure Nat result, no charge/allocation/state effect or new error. MP1/MP2/MP9 discharged; complete rounding, zero-coefficient, first-quadratic-step and unrelated-config controls are supplied below. Original correspondence additionally retains actual typed bindings and successful host premises. |
| `src/ethereum/forks/amsterdam/vm/gas.py:776–813` | `calculateGasExtendMemory (cfg : VmConfig) (m : Memory) (ws : List (U256 × U256)) : ExtendMemory` | Every cfg, aligned Memory and ordered window list; arbitrary Nat coefficient/seed. Pure complete cost/extent, no append/charge/mutation or new error. MP3–MP8/MP10 discharged; complete empty, huge-empty, cross-word, permuted, subsumed, seed and huge-Nat-endpoint controls are supplied below. Raw unaligned source memory is a separate source-only domain, not an invalid Lean proof/carrier. |

The source policy reads are `GasCosts.ZERO` (`gas.py:102`) and
`GasCosts.MEMORY_PER_WORD` (`gas.py:103`). Both operations and all ten ordinary pricing laws are supplied in `MemoryGas.lean`.
The executable private structural fold follows source order; a private ordinary
rounded-maximum refinement proves the closed forms and ordered subtraction bounds.
No private model constant occurs in a public law type. Public-only private clients
use the actual Base/U256/Memory/config providers, without another provider export.

`MemoryGasGuards.lean` and `memory_gas_differential.py` retain forty-two complete
literal target rows: twenty-four pinned-policy and eighteen generic-policy controls.
They cover zero/word rounding, the first quadratic step, zero-coefficient plateaus
above that step, arbitrary seeds, irrelevant config fields, full mixed input bytes,
ordered/permuted/duplicate/subsumed windows and unbounded endpoints crossing 2^256.
The committed observer compares complete target results and unchanged inputs against
these literals; huge returned extents are priced on small memory and never allocated.
Its optional source-frame/digest inputs are caller-supplied evidence, without a
committed source producer or authentication step in this comparator. The dated
[external review of the original head](https://github.com/alexanderlhicks/leanerSTFSpec/pull/166#issuecomment-6267536592)
records the finite interpreted/native and original-source comparisons separately,
including the inherited numeric-method binding limitation. Those historical results
are not executions of a repository source recipe. Generic controls are target-only;
three unaligned raw-source predictions remain unrun source-only controls, with no
corresponding `Memory` construction. Source agreement retains stable actual typed
bindings and successful host operations, rather than arbitrary substitutions/resources.

Reproduce the committed target controls from the repository root with fresh output
paths (the emitter defines `main`, so execute it with `--run`):

```sh
DRIVER=STFSpec/Conformance/Vm/Core/memory_gas_differential.py
python3 -I -B "$DRIVER" --self-test
python3 -I -B -O "$DRIVER" --self-test
python3 -I -B "$DRIVER" --emit-guards > /tmp/memory-pricing-guards.lean
python3 -I -B "$DRIVER" --emit-lean > /tmp/memory-pricing-observer.lean
lake env lean --run /tmp/memory-pricing-observer.lean > /tmp/memory-pricing-frames.jsonl
python3 -I -B "$DRIVER" --frames /tmp/memory-pricing-frames.jsonl
python3 -I -B -O "$DRIVER" --frames /tmp/memory-pricing-frames.jsonl
```

The strict whole-frame parser accepts consistent LF or CRLF and rejects malformed
framing, classes, numeric aliases, nested shapes, whole-input changes and wrong
cost/extent fields. These local proofs/controls establish no charge/allocation,
handler/config coherence or cost gate.

### Supplied scalar immediate decoders

`STFSpec/Vm/Core/StackDecoders.lean`, exported by `STFSpec.Vm.Core`, supplies
exactly the two existing UInt8 APIs. Both use the existing nullary
`ExceptionalHalt.invalidParameter`; the complete eight-law catalog is in §7.
Arithmetic observes `UInt8.toNat`, without substituting the distinct Base U8 type.

| Pinned source | Declaration and domain | Ordered failure and complete effect | Discharged laws / controls |
|---|---|---|---|
| `vm/stack.py:25–53` | `decodeSingle : UInt8 → Except ExceptionalHalt Nat`; every byte | First reject 91≤x.toNat≤127; otherwise return (x.toNat+145)%256; no state effect or alternative error | `decodeSingle_eq`, `decodeSingle_eq_error_iff`, `decodeSingle_bounds`, `decodeSingle_injective`; all 256 complete literal guards/frames |
| `vm/stack.py:56–91` | `decodePair : UInt8 → Except ExceptionalHalt (Nat × Nat)`; every byte | First reject 82≤x.toNat≤127; otherwise xor143, quotient/remainder16, then the exact ordered pair in §7; no state effect or alternative error | `decodePair_eq`, `decodePair_eq_error_iff`, `decodePair_bounds`, `decodePair_injective`; all 256 complete literal guards/frames |

All eight laws are **discharged** by ordinary kernel proofs. Private finite
support establishes pair bounds and an inverse of the ordered payload on accepted
bytes; xor cancellation recovers actual input equality. Single bounds/injectivity
use bounded arithmetic. The public-only clients consume all eight laws, derive
successful progress on valid bytes, exclude arbitrary alternative errors and
derive bounded successor indices without unfolding either decoder.

`StackDecoderGuards.lean` compares all 512 complete literal results, including
both pair coordinates and exact invalidParameter errors. The pure
`stack_decoder_differential.py` comparator imports no reference oracle. Its strict
normal/`-O` controls reject malformed schemas/framing, booleans/floats, wrong pair
arity, duplicate/reordered/incomplete streams and changed middle results.
CLI ingestion preserves UTF-8 line bytes; positive and CRLF-negative CLI controls
run in both normal and `-O` modes.
Actual interpreted public-import target frames agree with every retained literal; this
is not a separate native executable measurement. The observed success partitions
are 219 single and 210 pair, with exact images and valid-input injectivity.

The committed comparator checks the complete 512 target/literal outcomes and does
not execute or authenticate an external source. Separate historical original-source
observations and their precise process-identity audit qualification are recorded in
[PR157 review](https://github.com/alexanderlhicks/leanerSTFSpec/pull/157#issuecomment-6243089392).
Raw negative/oversized Python arguments have no UInt8 representative. Neither these
finite controls nor ordinary scalar laws close handler/frame, compiled-cost, G1–G7,
resource, replacement, fixture/EEST or guest gates.

Reproduce the committed controls with fresh output paths. This emitter uses #eval,
so plain Lean, rather than --run, executes the observations:

```sh
DRIVER=STFSpec/Conformance/Vm/Core/stack_decoder_differential.py
python3 -B "$DRIVER" --self-test
python3 -B -O "$DRIVER" --self-test
python3 -B "$DRIVER" --emit-lean > /tmp/DecoderFrames.lean
lake env lean /tmp/DecoderFrames.lean > /tmp/decoder-frames.ndjson
python3 -B "$DRIVER" --check-frames /tmp/decoder-frames.ndjson
python3 -B -O "$DRIVER" --check-frames /tmp/decoder-frames.ndjson
```

### Supplied padded buffer read

`STFSpec/Vm/Core/Memory.lean`, exported by `STFSpec.Vm.Core`, supplies the
standalone `bufferRead` adapter and its three ordinary laws in §7. It delegates to
the existing public `Bytes.extractPadded` provider with exact `U256.toNat` operands;
there is no Memory carrier or gas effect in this operation.

| Pinned source | Declaration and domain | Complete effect and failure | Public law / evidence |
|---|---|---|---|
| `memory.py:63,82–83`; `src/ethereum/utils/byte.py:40–59` | `bufferRead (b : Bytes) (start size : U256) : Bytes`; every finite Bytes and all U256 pairs | Exact available window then zeros to size.toNat; no mathematical failure or host cap. Source casts both operands to unbounded Uint before addition. | `bufferRead_eq_extractPadded`, `bufferRead_toList`, `bufferRead_size`; private public-law clients, 32 complete-byte guards/frames and strict normal/`-O` parser controls |

All three ordinary laws are **discharged**. Base checks availability in Nat before
packed index conversion and clamps the copied endpoint within the input. Huge
unavailable offsets do not cause traversal or allocation proportional to the offset.
The output-copying O(k) algorithm shape is inferred from that existing provider;
compiled allocation, sharing and composed costs have not been measured here.

Equal successful Python execution additionally requires actual pinned builtin
bytes/U256 arguments and dependencies, representable requested width in the runtime's
Py_ssize_t domain, and successful allocation. These are correspondence premises,
not restrictions on Lean's mathematical domain or new guest outcomes (O12,
DISC-001, DISC-006). The committed public comparator checks all 32 frozen complete
byte observations and strict framing without importing a source or dependency oracle;
it has no source mode. The separate historical authenticated source comparison is
recorded in [PR153 review](https://github.com/alexanderlhicks/leanerSTFSpec/pull/153#issuecomment-6242238102),
rather than implemented by this comparator. Neither finite comparison replaces the
all-domain ordinary laws or closes host-resource gates.

Reproduce the committed controls with fresh output paths; the emitter defines main:

```sh
DRIVER=STFSpec/Conformance/Vm/Core/buffer_read_differential.py
python3 -B "$DRIVER" --self-test
python3 -B -O "$DRIVER" --self-test
python3 -B "$DRIVER" --emit-lean > /tmp/BufferReadFrames.lean
lake env lean --run /tmp/BufferReadFrames.lean > /tmp/buffer-read.ndjson
python3 -B "$DRIVER" --check-frames /tmp/buffer-read.ndjson
python3 -B -O "$DRIVER" --check-frames /tmp/buffer-read.ndjson
```

### Supplied aligned Memory (Q62)

The exact six-operation API is supplied in `STFSpec/Vm/Core/Memory.lean`; §7 owns
its ten discharged ordinary laws. Packed storage, constructor, alignment proof and
helpers stay private. Callers use the existing Base Bytes provider and public laws.

| Source/model anchor at the pin | Declaration | Domain and complete effect | Discharged laws and controls |
|---|---|---|---|
| `interpreter.py:227`, `instructions/system.py:166,435` | `Memory.empty` | Fresh empty aligned memory | `toBytes_empty`; empty initialization controls |
| §6 abstraction; source `len(memory)` | `Memory.toBytes`, `Memory.size` | Complete byte-list model and byte length; aligned carrier | `length_toBytes`, `size_mod32`; full observations |
| caller append, `instructions/memory.py:42–58,73–90,103–120,156–179` | `Memory.expand` | Only n % 32 = 0; append exactly n zero bytes | `toBytes_expand`; zero/repeated expansion |
| `memory.py:39–60` | `Memory.readBytes` | Empty or in bounds; exact immutable window | `readBytes_toList`; endpoints/retained snapshots |
| `memory.py:20–36` | `Memory.write` | Empty or in bounds; complete overwrite, preserved size and untouched bytes; actual identity for empty value | `toBytes_write`, `write_empty`, `size_write`, `readBytes_write`, `readBytes_write_disjoint`; full-memory/overlap controls |

The local proofs are erased, not new runtime source assertions or failure channels.
Typed source read start/size and write start additionally lie below 2^256; Nat-only
huge empty-window laws are not direct typed Python-call claims. Host execution
requires the existing valid dependency/argument interpretation and successful
allocation/index premises. Caller derivation and compiled ownership/cost validation remain open. No raw
constructor or representation helper is a public test ingress.

`MemoryCallerProofs.lean` consumes all ten laws and derives expansion/read sizes
and post-write read witnesses using only public equations. Its snapshot-copy client
requires only admitted source/destination windows, including arbitrary overlap;
empty-inside, both-empty and adjacent disjoint clients retain the original reads.
`MemoryGuards.lean` retains thirty-three complete literal frames. The public-import
native producer in `memory_differential.py` observes actual retained Memory/Bytes
values; normal and `-O` parsing checks all frames and ninety-nine malformed-stream
adversaries. The committed comparator checks all thirty-three target/literal frames. Its optional
`--source-frames` input can compare thirty-one caller-supplied typed-source rows,
but does not authenticate or produce that baseline; the default reports zero source
frames compared. Separate historical source-method evidence and its audit limits are
recorded in [PR155 review](https://github.com/alexanderlhicks/leanerSTFSpec/pull/155#issuecomment-6242656073).
The two empty 2^4096 cases are Lean-only. These controls establish no compiled
ownership, allocation, C1–C4, R1, caller or guest readiness.

Reproduce the committed public controls using fresh output paths:

```sh
DRIVER=STFSpec/Conformance/Vm/Core/memory_differential.py
python3 -B "$DRIVER" --self-test
python3 -B -O "$DRIVER" --self-test
python3 -B "$DRIVER" --emit-lean > /tmp/MemoryFrames.lean
lake env lean --run /tmp/MemoryFrames.lean > /tmp/memory-frames.ndjson
python3 -B "$DRIVER" --check-frames /tmp/memory-frames.ndjson
python3 -B -O "$DRIVER" --check-frames /tmp/memory-frames.ndjson
```

### Supplied bounded Stack

`STFSpec/Vm/Core/Stack.lean`, exported by `STFSpec.Vm.Core`, supplies the existing
bounded carrier and six operations below. The private constructor, Array storage and
stored size proof enforce at most 1024 existing EthBase U256 words. Only `toList`
converts/reverses the Array; pop/push/peek inspect the size and relevant cell directly.
The bound is a representation invariant, not a new guest validation rule. Source
correspondence is restricted to actual typed Python lists of size at most 1024:
original push tests equality to 1024, so oversized Python lists are outside this model.

| Pinned EELS source / model seam | Lean declaration and type | Complete domain, ordered failure and effect | Public law / test |
|---|---|---|---|
| `vm/__init__.py:163`; `vm/interpreter.py:226`; `vm/instructions/system.py:165,434` | `Stack.empty : Stack` | Empty private top-at-end Array; top-first model [] | `Stack.toList_empty`; complete empty guards |
| §6 abstraction, no separate source helper | `Stack.toList : Stack → List U256` | Complete top-first model, O(n) observer; no raw constructor | `Stack.size_eq_length_toList`, `Stack.size_le`; full ordered observations |
| source `len(stack)`, `stack.py:109,128` | `Stack.size : Stack → Nat` | Direct stored Array size, always ≤1024 | Same size/length and bound laws; 0/1/1023/1024 guards |
| `vm/stack.py:94–112` | `Stack.pop : Stack → Except ExceptionalHalt (U256 × Stack)` | Empty check precedes subtraction/read; exact underflow or removed top and complete remainder | `Stack.pop_eq_error_iff`, `Stack.pop_eq_ok_iff`; empty, mixed, duplicates and full cases |
| `vm/stack.py:115–131` | `Stack.push : Stack → U256 → Except ExceptionalHalt Stack` | Exact full check before append; overflow at 1024, otherwise entire model cons and size+1 | `Stack.push_eq_error_iff`, `Stack.push_eq_ok_iff`; near/full transitions and complete models |
| indexed reads `vm/instructions/stack.py:106–109,242–243`, model seam | `Stack.peek? : Stack → Nat → Option U256` | All Nat depths; i<size guard before index arithmetic, otherwise none; no mutation | `Stack.peek?_eq_getElem?`; all positions, exact bounds and 2^4096 |

All eight exact public laws in §7 are **discharged** by ordinary proofs. Private
model/observation injectivity establishes actual Stack equality in both directions
of the success iff laws; no public constructor, extensionality or equality instance
is supplied. The two error iff laws quantify over every ExceptionalHalt, excluding
unrelated errors. Public-only clients derive successful push availability below the
bound and successful pop availability on nonempty models by total Except case
analysis; they also prove both conditional inverses with actual original Stacks.

`StackGuards.lean` and `stack_differential.py` retain forty-one complete input/result
models, exact size/status/returned words, empty/full boundaries, duplicates, zero,
maximum/high-bit words and every intermediate of a deterministic sequence. Inputs
are built through public pushes. Strict normal/-O frame controls reject malformed
schema, boolean/float integer aliases, out-of-range words and wrong whole streams.
The source schedule is limited to original pop/push on fresh typed bounded lists;
peek is explicitly a builtin List-index adapter, not an original standalone helper.
Authenticated original comparison passed eight unchanged pop and fourteen push
calls on fresh typed bounded lists, retaining exact U256/None return classes or
exception classes/args and entire before/after models. Nineteen separately labelled
List-index adapter observations also passed. All forty-one complete Lean frames
matched; source/runtime identities remained unchanged before/after each phase.
No swap/decoder/handler, gas ordering, frame reachability, allocation benchmark,
replacement, G1/G2–G7 or guest/EEST gate is supplied by this slice.

Reproduce the committed controls from the repository root (use fresh output paths):

```sh
python3 -B STFSpec/Conformance/Vm/Core/stack_differential.py --self-test
python3 -B -O STFSpec/Conformance/Vm/Core/stack_differential.py --self-test
python3 -B STFSpec/Conformance/Vm/Core/stack_differential.py --emit-lean > /tmp/stack.lean
lake env lean /tmp/stack.lean > /tmp/stack-frames.jsonl
python3 -B STFSpec/Conformance/Vm/Core/stack_differential.py --check-frames /tmp/stack-frames.jsonl
python3 -B -O STFSpec/Conformance/Vm/Core/stack_differential.py --check-frames /tmp/stack-frames.jsonl
"$EELS/.venv/bin/python" -I -B STFSpec/Conformance/Vm/Core/stack_differential.py --preflight \
  --eels "$EELS" --wheels "$WHEELS" --output "$PREFLIGHT"
"$EELS/.venv/bin/python" -I -B STFSpec/Conformance/Vm/Core/stack_differential.py --source \
  --eels "$EELS" --wheels "$WHEELS" --output "$SOURCE_OUTPUT" --frames /tmp/stack-frames.jsonl
```

`EELS` is a clean scratch checkout at the reference pin with its private `.venv`;
`WHEELS` contains the selected raw lock-matching wheels. `PREFLIGHT` and `SOURCE_OUTPUT`
must not exist. Preflight authenticates inputs without invoking a source stack helper.
The source command checks unchanged pop/push helpers and the separately labelled
List-index adapter against all complete frames; it supplies no standalone EELS peek helper.

### Supplied local meter algebra

The following local contracts are **discharged** in `STFSpec/Vm/Core/Exceptions.lean`
and `STFSpec/Vm/Core/GasMeter.lean`, exported by `STFSpec.Vm.Core` in namespace
`STFSpec.Vm.Core`. Other declarations in the grouped inventory remain unimplemented.
This is a partial G1 discharge, without a frame, gas policy, frame settlement or runner.

| Pinned EELS source | Lean declaration and type | Domain, complete success/effect and ordered failure | Public law / test |
|---|---|---|---|
| `vm/exceptions.py:17–139`; `vm/precompiled_contracts/modexp.py:34,38,42` | `ExceptionalHalt : Type` | All twelve subclass tags with `invalidOpcode (code : UInt8)`, plus bare `precompileHalt (reason : String)`; nominal construction/elimination only, no producer or Revert implementation | Private arbitrary-payload callers; guards retain every tag, every UInt8 and complete String payloads |
| `vm/gas.py:270–336` | `GasMeter : Type` | Public fields `gasLeft stateGasLeft stateGasBaseline : Nat`, `refundCounter : Int := 0`, `stateGasSpilled stateGasCommittedSpill : Nat := 0`; every raw record admitted, including reservoir above baseline, negative refund and both positive spill pools | Complete six-field guards and default-record case |
| §5 potential (no separate EELS function) | `GasMeter.phi : GasMeter → Nat` | `gasLeft + stateGasSpilled + stateGasCommittedSpill`; excludes reservoir/baseline/refund | `chargeGas_phi`, `chargeStateGas_phi`, `commitStateGas_phi`, `restoreStateGas_phi`, `restoreStateGasToEntry_phi`, `creditStateGasRefund_phi`, `repayStateGasSpill_phi`, `forfeitRemainingGas_phi`, `withholdCreateGas_phi`, `drainStateGasReservoir_phi`, `restoreChildGas_phi`; ordinary public clients |
| `vm/gas.py:374–388` | `checkGas : GasMeter → Nat → Except ExceptionalHalt Unit` | All raw meters/amounts; check execution shortage first, returning `.error .outOfGas` iff `gasLeft < a`; otherwise `.ok ()`, no meter update | `checkGas_eq_ok_iff`, `checkGas_eq_error_iff`; zero/exact/one-over guards |
| `vm/gas.py:391–405` (numeric helper of `:408–422`) | `chargeGas : GasMeter → Nat → Except ExceptionalHalt GasMeter` | All raw meters/amounts; execution affordability precedes subtraction; success changes only `gasLeft := gasLeft - a`; shortage returns only `.outOfGas` without a preceding update | `chargeGas_of_le`, `chargeGas_eq_error_iff`, `chargeGas_phi`; exact full-record success/error guards |
| `vm/gas.py:425–448` (numeric helper of `:451–468`) | `chargeStateGas : GasMeter → Nat → Except ExceptionalHalt GasMeter` | All raw meters/amounts; reservoir affordability first: change only `stateGasLeft := stateGasLeft - a`; otherwise total affordability, let `d := a - stateGasLeft`, set execution gas to `gasLeft - d`, reservoir to zero and pending spill to `stateGasSpilled + d`; baseline/refund/committed spill unchanged. Total shortage returns only `.outOfGas` before any update | `chargeStateGas_of_le`, `chargeStateGas_of_lt`, `chargeStateGas_eq_error_iff`, `chargeStateGas_phi`, `chargeStateGas_gasLeft_le`; zero/exact/one-over for each branch and beyond-64-bit guards |
| `vm/gas.py:471–502` | `commitStateGas (m : GasMeter) (h : m.stateGasLeft ≤ m.stateGasBaseline) : GasMeter` | Exactly the local proof domain; arbitrary signed refund and both spill pools. The source assertion at :499 precedes all updates. Result `(E,R,R,q,0,C+S)` in six-field order; no runtime failure | `commitStateGas_eq`, `commitStateGas_phi`; complete-field zero/equality/negative/both-spill/beyond-word guards and authenticated original comparison |
| `vm/gas.py:505–529` | `restoreStateGas : GasMeter → GasMeter` | Every raw meter, including `R>B` and negative refund; no source assertion. Result `(E+S,B,B,0,0,C)`; committed spill retained, no failure | `restoreStateGas_eq`, `restoreStateGas_phi`, `restoreStateGas_post`; complete-field guards, public idempotence/committed-retention clients and authenticated original comparison |
| `vm/gas.py:532–567` | `restoreStateGasToEntry (m : GasMeter) (R : Nat) (h₁ : m.stateGasBaseline ≤ R) (h₂ : m.refundCounter = 0) : GasMeter` | Only these two premises, with no reservoir bound. Source assertions :555 then :558 precede all mutation. Result `(E+S+C,R,R,q,0,0)`; refund preserved under its equality proof, no runtime failure | `restoreStateGasToEntry_eq`, `restoreStateGasToEntry_phi`, `restoreStateGasToEntry_post`; complete-field guards, public composition and authenticated original comparison including ordered source-only assertion probes |
| `vm/gas.py:570–603` | `txStateGasUsed (m : GasMeter) (T : Nat) (h : m.stateGasBaseline ≤ T) : Int` | Exactly the local baseline-to-grant proof at source assertion :597; other raw fields arbitrary, reservoir may exceed baseline/grant. No mutation or runtime error; signed result `T-R+S+C`, with each amount cast before subtraction | `txStateGasUsed_eq`; twenty complete literal controls, private public-only clients and strict normal/`-O` whole frames and authenticated original comparison |
| `vm/gas.py:606–628` | `creditStateGasRefund : GasMeter → Nat → GasMeter` | Every raw meter/amount. With `x = min a S`, complete result `(E+x,R+(a-x),B,q,S-x,C)`; both subtraction bounds follow from min. No assertion, baseline cap, refund-sign/word bound or failure; B/q/C unchanged | `creditStateGasRefund_eq`, `creditStateGasRefund_phi`, `creditStateGasRefund_zero`; complete-field guards, public branch/retention/inversion clients and authenticated original comparison |
| `vm/gas.py:631–659` | `repayStateGasSpill : GasMeter → GasMeter` | Every raw meter. With `y = min R S`, complete result `(E+y,R-y,B,q,S-y,C)`; min bounds both subtractions. The source assertion :657–659 follows all assignments and holds universally; no input proof or runtime failure. B/q/C unchanged | `repayStateGasSpill_eq`, `repayStateGasSpill_phi`, `repayStateGasSpill_post`, `repayStateGasSpill_idempotent`; complete-field guards, public branch/identity clients and authenticated original comparison |
| `vm/gas.py:662–675` | `forfeitRemainingGas (m : GasMeter) (h : m.stateGasSpilled = 0) : GasMeter` | Exactly local pending-spill-zero proof; source assertion :674 precedes mutation. Complete result `(0,R,B,q,S,C)` with S=0; arbitrary B/q/C and R>B admitted. Only E changes, with no new failure | `forfeitRemainingGas_eq`, `forfeitRemainingGas_phi`; complete-field guards, actual public rollback/forfeit clients and source-only assertion probes |
| `vm/gas.py:678–698`, inlining arithmetic `:861–876` | `withholdCreateGas : GasMeter → Nat × GasMeter` | Every raw meter; save `g=E-E/64`, subtract g from E, return `(g,(E-g,R,B,q,S,C))`, grant first. Division and both subtraction bounds hold universally; no affordability premise or failure | `withholdCreateGas_eq`, `withholdCreateGas_phi`; 0/1/63/64/65/127/128/129/beyond-word complete returns, retained-share and round-trip clients; original callee binding |
| `vm/gas.py:701–722` | `drainStateGasReservoir : GasMeter → Nat × GasMeter` | Every raw meter; save R then set reservoir zero; return `(R,(E,0,B,q,S,C))`, saved value first. No 63/64 rule or baseline cap; no failure | `drainStateGasReservoir_eq`, `drainStateGasReservoir_phi`; complete zero/positive/beyond-word saved returns, retention and repeated-drain clients |
| `vm/gas.py:725–746` | `restoreChildGas : GasMeter → Nat → Nat → GasMeter` | Every raw meter and g,T : Nat; E+=g then R+=T; complete result `(E+g,R+T,B,q,S,C)`. No provenance/maximum-grant premise or failure; unbounded addition | `restoreChildGas_eq`, `restoreChildGas_phi`; independent zero/nonzero amounts, beyond-word complete addition, zero identity and withhold/drain/restore clients |
| `vm/instructions/storage.py:130,134,139`; `vm/__init__.py:242` (inline additions, no named `add_refund`) | `addRefund : GasMeter → Int → GasMeter` | Every raw meter and signed k; complete result `(E,R,B,q+k,S,C)`. No sign, word-width, baseline, spill or caller premise; no failure | `addRefund_eq`, `addRefund_phi`; complete signed/cancellation/beyond-U256 guards, public composition/reset-order clients and exact original statement projection |
| `vm/gas.py:861–876` | `maxMessageCallGas : Nat → Nat` | Every unbounded Nat g; result `g-g/64`. Division/subtraction bounds hold universally; no meter, premise or failure | `maxMessageCallGas_eq`, `maxMessageCallGas_le`; zero/rounding/beyond-word guards, public complementary-share clients and direct original helper comparison |

The charge helpers' error is an O8 exceptional halt. Existing source consumers include
`vm/interpreter.py:276` (top-level preparation), `:386` (code deposit), and `:456–474`
(call execution); their settlement, rollback and outcome projection remain outside
this kernel. Pure `Except` errors contain no mutable meter; controls separately retain
the complete original input and check that the source has not mutated it on failure.
`chargeGas`/`chargeStateGas` model the numeric helpers, excluding wrapper trace events.
The `check_gas` adapter projects only `evm.gas_meter`; its Python holder is not a complete
production EVM and introduces no public Lean frame.

`STFSpec/Conformance/Vm/Core/GasMeterCallerProofs.lean` supplies ordinary generic
public-law callers. `GasMeterGuards.lean` checks frozen complete results.
`gas_meter_differential.py` emits complete public-import observations and strictly
parses all fields, signed refunds, exception payloads and defaults normally and under
`-O`; original source comparison requires separately authenticated source/runtime
identities. These local controls establish no full VM, producer, EEST or budget claim.

The committed observer recipe uses plain Lean because the emitter contains `#eval`
commands. Choose fresh external output paths and a separate pinned source clone
with locked wheels; source modes require its unoptimized isolated interpreter:

```sh
DRIVER=STFSpec/Conformance/Vm/Core/gas_meter_differential.py
OUT=/absolute/path/to/fresh-controls
EELS=/absolute/path/to/pinned-eels
WHEELS=/absolute/path/to/locked-wheels
mkdir -p "$OUT"
python3 -B "$DRIVER" --self-test
python3 -B -O "$DRIVER" --self-test
python3 -B "$DRIVER" --emit-lean > "$OUT/GasMeterFrames.lean"
lake env lean "$OUT/GasMeterFrames.lean" > "$OUT/frames.jsonl"
python3 -B "$DRIVER" --check-frames "$OUT/frames.jsonl"
python3 -B -O "$DRIVER" --check-frames "$OUT/frames.jsonl"
"$EELS/.venv/bin/python" -I -B "$DRIVER" --preflight \
  --eels "$EELS" --wheels "$WHEELS" --output "$OUT/preflight"
"$EELS/.venv/bin/python" -I -B "$DRIVER" --source \
  --eels "$EELS" --wheels "$WHEELS" --output "$OUT/source" --frames "$OUT/frames.jsonl"
```

The catalog retains 31 numeric source-helper cases and 304 complete nominal
frames. The 256 opcode payloads are nominal constructor/serializer controls,
not exception-producer executions. Preflight executes no numeric helper;
source comparison preserves original return/error classes and all six fields.
New runtime/candidate checks and their results must be recorded for each actual run.

`GasRollbackCallerProofs.lean` consumes all eight additional ordinary public laws,
including complete-record congruence, baseline lowering, ordinary restore idempotence,
committed-spill retention and charge/commit/two-boundary potential composition.
`GasRollbackGuards.lean` freezes complete six-field cases, including both spill pools,
negative refunds, reservoir above baseline where admitted and `2^130` amounts; an actual
Lean charge/commit/charge/restore/entry sequence checks every intermediate meter.
`gas_rollback_differential.py` strictly compares 18 public-import complete frames
normally and under `-O`; its separately authenticated original schedule adds four
source-only assertion probes with exact locations and unchanged inputs. It executes
only these three original helpers. The authenticated comparison passed all 18 valid
complete meters and four source-only assertion probes, including both-false entry
assertion priority and unchanged failed inputs. No invalid Lean call is fabricated.

Reproduce this rollback slice with fresh external output paths. The emitter uses
`#eval`, so execute it with plain Lean. Keep source assertions enabled in the
separate pinned clone's interpreter and use its authenticated locked wheels:

```sh
DRIVER=STFSpec/Conformance/Vm/Core/gas_rollback_differential.py
OUT=/absolute/path/to/fresh-rollback-controls
EELS=/absolute/path/to/pinned-eels
WHEELS=/absolute/path/to/locked-wheels
mkdir -p "$OUT"
python3 -B "$DRIVER" --self-test
python3 -B -O "$DRIVER" --self-test
python3 -B "$DRIVER" --emit-lean > "$OUT/GasRollbackFrames.lean"
lake env lean "$OUT/GasRollbackFrames.lean" > "$OUT/frames.jsonl"
python3 -B "$DRIVER" --check-frames "$OUT/frames.jsonl"
python3 -B -O "$DRIVER" --check-frames "$OUT/frames.jsonl"
"$EELS/.venv/bin/python" -I -B "$DRIVER" --preflight \
  --eels "$EELS" --wheels "$WHEELS" --output "$OUT/preflight"
"$EELS/.venv/bin/python" -I -B "$DRIVER" --source \
  --eels "$EELS" --wheels "$WHEELS" --output "$OUT/source" --frames "$OUT/frames.jsonl"
```

The complete catalog retains 18 valid calls and four source-only assertion probes;
preflight executes none. Invalid proof-domain inputs remain source-only probes.
Record each actual current-candidate source/runtime result separately from these
reproduction instructions and from historical campaigns.


`GasRefundCallerProofs.lean` consumes the seven refund/repayment laws through public
imports only: complete B/q/C retention, both min branch equations, repayment identity,
zero credit, idempotence, postcondition and charge/refund/repay potential composition.
The conditional charge/refund inverse requires only local initial pending spill zero;
its explicit counterexample otherwise is retained by `GasRefundGuards.lean`.
Those guards retain all six fields for zero/min boundaries, R>B, negative refund,
both spill pools, zero execution and `2^130` values, and every intermediate in actual
Lean charge/refund/repay compositions. `gas_refund_differential.py` compares twenty
complete public-import frames normally and under `-O`, with authenticated fresh typed
original credit/repay calls and enabled repayment assertions. Source composition rows
are standalone new-helper inputs; no original charge/rollback replay is needed.
The authenticated original comparison passed all twenty complete meters: eleven credit
and nine repayment calls, every return `None`, with enabled assertions and all nine
repayment postconditions. Actual source/runtime identities remained unchanged.
Neither helper has a typed-domain failure. Negative Uint construction precedes helper
invocation; incorporation's child assertions precede parent absorption and repayment
occurs only on success (`__init__.py:225–250`). These caller boundaries remain outside
the helpers' domains and are not new helper errors or caller-reachability proofs.

Reproduce the refund/repayment slice with fresh external paths. The emitter uses
`#eval` and plain Lean. Source calls require the pinned clone's isolated,
unoptimized interpreter so repayment assertions remain enabled:

```sh
DRIVER=STFSpec/Conformance/Vm/Core/gas_refund_differential.py
OUT=/absolute/path/to/fresh-refund-controls
EELS=/absolute/path/to/pinned-eels
WHEELS=/absolute/path/to/locked-wheels
mkdir -p "$OUT"
python3 -B "$DRIVER" --self-test
python3 -B -O "$DRIVER" --self-test
python3 -B "$DRIVER" --emit-lean > "$OUT/GasRefundFrames.lean"
lake env lean "$OUT/GasRefundFrames.lean" > "$OUT/frames.jsonl"
python3 -B "$DRIVER" --check-frames "$OUT/frames.jsonl"
python3 -B -O "$DRIVER" --check-frames "$OUT/frames.jsonl"
"$EELS/.venv/bin/python" -I -B "$DRIVER" --preflight \
  --eels "$EELS" --wheels "$WHEELS" --output "$OUT/preflight"
"$EELS/.venv/bin/python" -I -B "$DRIVER" --source \
  --eels "$EELS" --wheels "$WHEELS" --output "$OUT/source" --frames "$OUT/frames.jsonl"
```

The complete catalog contains eleven credit and nine repayment calls. Preflight
executes none; each actual source comparison retains all six fields and `None`
returns, with enabled repayment postconditions. Record its current source/runtime
results separately from these instructions and from historical campaigns.

`GasTransferCallerProofs.lean` consumes all eight transfer laws through public imports:
complete untouched-field retention, retained execution E/64, forfeit idempotence,
second drain returning zero with the same meter, zero restoration and a complete
withhold/drain/restore round trip for the saved amounts. Actual ordinary and entry
rollback post laws produce the forfeit proof in clients and guards. Ordinary rollback
then forfeit retains committed spill; entry rollback uses its actual B≤T and q=0
premises. These local facts do not establish full `ChildSettled`, reachability, or that
CREATE returns its grant: collision happens after withholding and before draining
(`instructions/system.py:120–134`). Failed-call preflight restores supplied grants
before optional NEW_ACCOUNT credit (`:393–398`); completed children use incorporation.
`GasTransferGuards.lean` freezes thirty complete return/meter controls and every actual
Lean composition intermediate, including R>B, q<0, both spill pools and beyond-word
amounts. `gas_transfer_differential.py` strictly compares all thirty public-import
frames normally and under `-O`. Its source schedule calls only these four new original
helpers; withhold uses the real authenticated `max_message_call_gas` callee, without
providing its own standalone maximum operation/status; the scalar slice below owns that. Composition rows
are standalone new-helper inputs, with no original charge/refund/rollback replay.
The three source-only S>0 probes require enabled AssertionError at `vm/gas.py:674`
before mutation and retain all six unchanged fields, including when E=0; they have no
invalid Lean invocation. Valid saved returns have exact Uint class, other returns None.
The other three helpers have no typed-domain error or assertion premise.
The authenticated original comparison passed all thirty complete return/meter cases
(seven forfeits, ten withholds, six drains, seven restorations) and all three
source-only invalid forfeits. Each assertion occurred at :674 before mutation, with
every field unchanged. Runtime/source/input identities remained unchanged within
each stage; no old original helper was replayed. These are finite local controls.

Reproduce this transfer slice with fresh external output paths. Its emitter uses
`#eval` and plain Lean; source modes require the pinned clone's isolated,
unoptimized interpreter, preserving the forfeit assertion and real maximum callee:

```sh
DRIVER=STFSpec/Conformance/Vm/Core/gas_transfer_differential.py
OUT=/absolute/path/to/fresh-transfer-controls
EELS=/absolute/path/to/pinned-eels
WHEELS=/absolute/path/to/locked-wheels
mkdir -p "$OUT"
python3 -B "$DRIVER" --self-test
python3 -B -O "$DRIVER" --self-test
python3 -B "$DRIVER" --emit-lean > "$OUT/GasTransferFrames.lean"
lake env lean "$OUT/GasTransferFrames.lean" > "$OUT/frames.jsonl"
python3 -B "$DRIVER" --check-frames "$OUT/frames.jsonl"
python3 -B -O "$DRIVER" --check-frames "$OUT/frames.jsonl"
"$EELS/.venv/bin/python" -I -B "$DRIVER" --preflight \
  --eels "$EELS" --wheels "$WHEELS" --output "$OUT/preflight"
"$EELS/.venv/bin/python" -I -B "$DRIVER" --source \
  --eels "$EELS" --wheels "$WHEELS" --output "$OUT/source" --frames "$OUT/frames.jsonl"
```

The complete catalog retains thirty valid return/meter cases and three source-only
invalid forfeits. Preflight calls none. Record each actual current-candidate source
result and its runtime identities separately from historical validation records.

**External semantics.** From `ethereum_types` 0.4.1 (`reference.toml`): `Uint` (unbounded, subtraction below zero raises `OverflowError`), `U256`/`U64`/`U8` (constructor, `+` and `from_signed` raise `OverflowError` out of range; `from_be_bytes` raises `ValueError` for more than 32 bytes; `wrapping_*` wrap), `Bytes`, `Bytes32`, `ulen`. Only the `OverflowError` cases listed in R-EXC-2 are behaviourally reachable from this module's callers; the Lean `Nat`/`U256` API (EthBase) must make each one explicit rather than wrap. `ceil32` and `taylor_exponential` come from `utils/numeric.py` (EthBase). `left_pad_zero_bytes` from `utils/byte.py`.


`GasAccountingCallerProofs.lean` consumes all four signed-addition/scalar-maximum laws
without unfolding providers: all five Nat fields are retained, signed zero/composition/
inverse identities hold, and the grant plus retained share equals the input. Actual
ordinary rollback after addition discards the refund; addition after rollback retains k.
These local facts prove neither storage-history consistency nor top-level refund sign.
`GasAccountingGuards.lean` checks twelve complete signed cases, fourteen scalar cases
and every intermediate of actual addition/cancellation/reset sequences. Values include
R>B, negative refunds, both spill pools and beyond-U256 amounts. The withholding body
remains unchanged; a standalone scalar law proves no CALL affordability/stipend claim.
`gas_accounting_differential.py` emits and strictly compares all twenty-six complete
public-import frames normally and under `-O`, rejecting boolean/float substitutes,
duplicates, nonfinite values, malformed fields and complete-stream mismatches.
Its separately authenticated original schedule projects only the exact original
AugAssign AST at `vm/__init__.py:242` on distinct original typed meters and preserves
the complete child. This is not a named source function or whole incorporation replay.
The scalar schedule calls the unchanged original maximum directly. Host/compiler/runtime
and startup trust remain explicit; no old helper or transaction lifecycle is replayed.
The authenticated original comparison passed all twenty-six complete observations:
twelve signed statement projections with unchanged full children and execution returning
None, plus fourteen direct maximum calls returning the exact original Uint class.
Source/runtime identities remained unchanged before and after each separate phase.

Reproduce this accounting slice with fresh external output paths. The emitter
uses `#eval` and plain Lean. Source mode uses the pinned clone's isolated,
unoptimized interpreter and distinguishes exact statement projections from calls:

```sh
DRIVER=STFSpec/Conformance/Vm/Core/gas_accounting_differential.py
OUT=/absolute/path/to/fresh-accounting-controls
EELS=/absolute/path/to/pinned-eels
WHEELS=/absolute/path/to/locked-wheels
mkdir -p "$OUT"
python3 -B "$DRIVER" --self-test
python3 -B -O "$DRIVER" --self-test
python3 -B "$DRIVER" --emit-lean > "$OUT/GasAccountingFrames.lean"
lake env lean "$OUT/GasAccountingFrames.lean" > "$OUT/frames.jsonl"
python3 -B "$DRIVER" --check-frames "$OUT/frames.jsonl"
python3 -B -O "$DRIVER" --check-frames "$OUT/frames.jsonl"
"$EELS/.venv/bin/python" -I -B "$DRIVER" --preflight \
  --eels "$EELS" --wheels "$WHEELS" --output "$OUT/preflight"
"$EELS/.venv/bin/python" -I -B "$DRIVER" --source \
  --eels "$EELS" --wheels "$WHEELS" --output "$OUT/source" --frames "$OUT/frames.jsonl"
```

The catalog retains twelve signed statement projections and fourteen direct
maximum calls. Preflight executes none. Refund projection is not a named source
helper or whole incorporation. Record each actual comparison's complete results
and source/runtime identities separately from historical validation records.

### Supplied transaction EVM gas allocation

`STFSpec/Vm/Core/TransactionGasAllocation.lean`, exported by `STFSpec.Vm.Core`,
supplies Q65's raw carrier, helper and exactly four authored ordinary laws in §7.
The source-ordered body removes intrinsic execution, computes remaining cap,
selects the minimum and retains the complete residual. Both fields are unrestricted
Nat data; only calls carry the two local bounds. No full intrinsic record, word
bound, runtime error/default, global WF or additional authored public law is added.
Compiler-generated raw-record support is distinct from the four authored laws.

| Pinned EELS source | Lean declaration and type | Domain, complete effect and ordered failure | Public law / test |
|---|---|---|---|
| `vm/gas.py:1106–1117` | `EvmGasAllocation : Type`, raw `executionGas stateGasReservoir : Nat` | Every ordered Nat pair, without allocation provenance or bound fields | `EvmGasAllocation.ext`, `EvmGasAllocation.eta`; four complete raw controls including independently varied coordinates |
| `vm/gas.py:1120–1152`, live cap `:162`; `ethereum-types` 0.4.1 | `allocateEvmGas (cfg : VmConfig) (txGas intrinsicExecution : Nat) (hIntrinsicLeTxGas : intrinsicExecution ≤ txGas) (hIntrinsicLeCap : intrinsicExecution ≤ cfg.costs.txMaxGasLimit) : EvmGasAllocation` | Exactly both local subtraction bounds; complete execution min and residual, no mutation/error. Source transaction subtraction precedes live-cap subtraction; typed failures outside either bound have no target call | `allocateEvmGas_eq`, `allocateEvmGas_congr`; 24 complete allocation controls and 14 whole typed original comparisons |

All four laws are **discharged**. The nine private groups in
`TransactionGasAllocationCallerProofs.lean` consume public equations throughout:
raw ext/eta and varied fields; both projections; local arithmetic identities;
complete branches/boundaries/bounds; relevant-cap and constructed-meter transport;
changed-cap inequality and intrinsic-independent reservoir; complete constructed
entry/potential/signed usage; complete execution-charge branches/potential; and
reservoir/spill/error state charges with local signed-observer premises. Their
identities are local arithmetic on admitted inputs, not transaction conservation,
actual Runner construction or whole G1/G2–G7 proofs.

`TransactionGasAllocationGuards.lean` and the private native fixtures in
`scripts/TransactionGasAllocationNativeTests.lean` retain exactly 36 complete groups:
fourteen pinned-cap allocations, six arbitrary-cap allocations, four unbounded
allocations, four raw records, two same/different relevant-cap relations and six
constructed entry/execution/state charges. They preserve both allocation fields,
actual eta reconstruction, exact Bool relations, every six-field meter coordinate,
potential, signed usage and the exact outOfGas error without a successful meter.
W cases cross U64/U256 boundaries without allocating a proportional buffer.
Raw configurations supply all 144 GasCosts fields and complete state/limit data;
equal-cap controls vary unrelated costs, signed refund, BLS array, state data and
limits. No fixture is an Amsterdam factory or a default instance.

The allocation-specific reader
`STFSpec/Conformance/Vm/Core/transaction_gas_allocation_differential.py` checks
whole versioned header/36-group/end frames against independent frozen decimal
literals. Nat/Int coordinates use canonical strings and equality flags exact JSON
Bool. It rejects duplicate keys/NaN, coercions, malformed/full-value/order/count/
end/trailing and size failures. The regression suite was written before the
parser/native producer; normal and `-O` each pass 24 positive and 36 negative
controls (120 total group executions). Parser/check-target paths load no original
EELS modules. The committed native producer, declaration audit, captured stdout
reader and both parser modes are wired into CONTRIBUTING §6.3 and the core CI job.

On 2026-10-24 all 36 actual interpreted and native groups agreed with these
complete literals. One successful original schedule invoked the unchanged whole
pinned `allocate_evm_gas` exactly 17 times: fourteen successes then three typed
out-of-domain failures. All 14 complete
success pairs matched the native target; success rows 13/14 are raw-helper
successes, not validated transactions. Three genuinely typed out-of-domain failures remained
source-only: failure rows 1/3 reached `gas.py:1148`, row 2 reached `:1149`, each through
`ethereum_types/numeric.py:109` with exact OverflowError/empty message/empty args.
No target proof/error or extra source-generated Lean guard was invented for them.
The existing 36 guards and full-value comparisons are separate evidence.

The original preflight admitted actual Uint objects/plain nonnegative int internal
observations before conversion/equality; actual execution/state NewType bindings
retained their Uint supertype and identity behavior. Both complete original
IntrinsicGasCost fields, result dataclass field order/classes, callable/globals/
code/defaults, numeric methods and unchanged full inputs/context bracketed every
selected call. The live execution cap remained Uint 16777216; total cap
Uint 4294967295 was separate. Whole-file source text authentication and structural
loaded-code comparison are separate from recorded marshal digests; serialized
bytes are not assumed canonical. CPython 3.13.7, its native NewType implementation,
generated dataclass code, installed RECORD/dependencies, startup/ambient host,
orchestration, Lean compiler/kernel/runtime remain explicit trust premises.
Focused target processes met an observed child-RSS bound of 2 GiB, with 60-second
and 1-MiB stream limits; this is evidence scope, not a preventative address-space
bound or guest resource policy. Original Python retained a 512-MiB address-space
limit. No compiled cost/performance, caller/cap coherence, settlement, conservation,
VM/guest/EEST or readiness gate follows.

Reproduce local target controls with fresh output paths:

```sh
lake build transaction-gas-allocation-native-tests --wfail
lake exe check-decls TransactionGasAllocationNativeTests
lake exe transaction-gas-allocation-native-tests > .lake/transaction-gas-allocation.jsonl
python3 -B STFSpec/Conformance/Vm/Core/transaction_gas_allocation_differential.py --check-target .lake/transaction-gas-allocation.jsonl
python3 -B scripts/test_transaction_gas_allocation_output_parser.py
python3 -B -O scripts/test_transaction_gas_allocation_output_parser.py
```

## 4. Tests

- **Supplied allocation controls (Q65):** §3 owns the exact 36 complete
  guard/interpreted/native groups, nine public-law client groups, strict normal/`-O`
  parser controls, 14 whole successful original comparisons and three source-only
  typed subtraction failures. Equal-cap controls vary unrelated raw configuration;
  changed-cap and beyond-word controls retain complete results. Local entry/charge
  meters establish no actual Runner reachability or conservation.
- **Supplied settlement controls (Q66):** §3 owns the complete 44 helper and six
  raw carrier guards/interpreted/native groups, private public-law clients and
  strict normal/`-O` parser scope. Inputs cross one-fifth cap/refund/floor thresholds,
  maximum/high-bit U256 refunds, negative and beyond-word signed state and
  unbounded Nat returns. State subtraction precedes its floor even at F=T;
  failed returned/state/floor bounds remain outside the target proof domain.
  The upstream unsigned refund constructors and unchanged Runner range bridge
  remain caller obligations. No actual caller, fee/provider or readiness gate follows.

- **Supplied raw block-gas controls:** `BlockGasCallerProofs.lean` has seven
  private public-law client groups: complete construction/eta, independently
  varied all-field ext, nominal U64 observation/equality, each single-field
  replacement/congruence and nested reconstructions. `BlockGasGuards.lean` checks
  ten complete ordered
  execution/state/blob observations: zero, distinct and swapped execution/state,
  each single zero dimension, U64 maximum and unbounded Nats beyond 2^64/2^256.
  No runtime/source replay is needed for this projection-only data boundary.

- **Supplied call/init controls (Q64):** §3 owns thirty-two complete handwritten
  results, with the dated external interpreted/native and twenty-five original
  comparisons scoped in §3: zero/nonzero/maximum U256, omitted/explicit stipend, shortage/
  equality, nonzero memory/extra, 63/64/65 cap boundaries and beyond-U64 amounts.
  Init covers zero, word boundaries, wide lengths and zero/odd word prices.
  Generic raw policies vary zero seeds/defaults/selected stipends and unrelated
  fields. Public-only clients use all six laws, complete actual chargeGas
  success/exclusive errors, affordability/rounding/read-set facts and explicit
  local financing hypotheses. Six complete charge witnesses preserve negative
  refunds, reservoir above baseline and positive spill pools. The scalar maximum
  and nine legacy hand rows reuse existing guards; no old original is replayed.

- **Supplied log controls:** `LogsCallerProofs.lean` consumes only public Log/rope
  and provider laws for complete-field injectivity, eta, every observer equation,
  order, duplicates, observation identities/association/congruence, singleton
  emission, retained operands and conditional nested success/discard algebra.
  `LogsGuards.lean` retains sixteen unchanged raw/full-field controls and six
  success/discard/output controls, including empty raw shapes, repeated/shared
  subtrees and more than four topics. Native and interpreted `log-rope-bench
  --check-controls` agree on all 22 complete input/before/distractor/after/retained
  observations. These are pure model clients, not handler or frame execution.
- **Scoped native C3 (dated external evidence):** the
  [original review record](https://github.com/alexanderlhicks/leanerSTFSpec/pull/172#issuecomment-6270880143)
  records the audited `scripts/LogRopeBench.lean` artifact and 102 retained
  fresh-process measurements: three trials at 64/1024/4096/16384 for balanced,
  left/right skew, sibling accumulation, empty merges, long leaves, shared repeats
  and mixed success/discard; mixed fresh payloads add 64/1024. Every process checks
  all 22 fixed controls and full measured chronological payloads outside operation
  clocks. Generated C uses loop-based workstack/leaf traversal with no calls to
  the proof measure/reference. Timed phases separate combined construction,
  flattening, full-observation conversion and observation/output/root/fresh-child
  release; saved-parent observations remain complete and unchanged.
  The empty family shares one dynamically built `concat empty (leaf [])` across
  all appends; the shared family repeats one A/B subtree. Expanded node/log counts
  include every occurrence, while allocation and cleanup reflect actual sharing.
  Fixed A/B/C/D payloads are global; the separate mixed-payload case creates fresh
  address/topics/data. Construction includes IO-holder instrumentation and failed
  attempted-child release. Raw ns, current-thread small-allocation heartbeats and
  process RSS are diagnostics, not exact allocation bytes or peak-live heap.
  Flatten allocation counts scale with expanded nodes/logs; measured heights reach
  16385/16386 and complete cleanup succeeds on these finite cases. This evidence
  does not establish universal host stack/resource bounds or C1/C4/guest readiness.
  These are dated retained measurements, not a claim that a fresh checkout or the
  routine CI build/audit replays the measurement campaign. Timing remains manual.

- **Supplied memory pricing controls (Q63):** §3 owns the complete frozen literal,
  interpreted/native, strict CLI/parser and conditional original-source control boundary.
  The private public-only caller goals and their domains are owned by §7. Pricing tests
  compute values only; they allocate no returned extent and discharge no ordering/cost gate.

- **Supplied buffer controls:** `BufferReadGuards.lean` freezes 32 complete input,
  offset, width and output observations. `buffer_read_differential.py` embeds the
  same literals and emits public-import Lean observations without a private data
  file. Its strict whole-frame NDJSON comparison checks all input/output bytes,
  exact integer types, IDs/order/count, fields and framing under normal Python and
  `-O`; rejection controls include duplicate/missing/extra/truncated/reordered rows,
  booleans/floats and wrong middle bytes with unchanged length. Private clients use
  all three laws for zero-size actual Bytes equality, wholly unavailable and
  contained windows, and the existing Base right-padding extension law with its
  explicit window premise. Requested outputs are at most 33 bytes, including huge
  offsets near 2^64 and U256.max. U256.max with tiny width is already unavailable:
  wrapped and unbounded stops both give empty slices, so those finite controls
  cannot establish endpoint arithmetic. The all-domain bridge/List law and static
  adapter/provider/source inspection supply that guarantee. The authenticated
  original result and exact typed/whole-input observations are recorded in §3.

- **Supplied local Memory controls (Q62):** Thirty-three complete frames cover empty/zero/repeated aligned expansion, full high/interior-zero payloads, cross-word and exact-end writes, complete untouched prefixes/suffixes, both overlap directions/self-copy and retained immutable snapshots. Empty reads/writes at 2^64 and U256.max have typed source counterparts; 2^4096 is Lean-only. Public clients consume all ten laws, derive result-read witnesses and cover adjacent/either-empty disjointness. The committed producer/comparator checks all thirty-three target/literal frames under strict normal/`-O` comparison; optional external source frames are an explicit caller-supplied evidence premise (§3). Source agreement is conditional on aligned/admitted typed inputs and successful host premises; raw invalid-window behavior has no invalid proof-carrying Lean call. Caller ordering, compiled ownership/costs and guest gates remain open.

- **Supplied raw GasCosts clients:** Ordinary private public-only proofs construct the full record on independently supplied fields, use both complete ext/eta laws and derive selected opcodeAdd `chargeGas` congruence on the same arbitrary meter, with exact public success/error consequences. Arbitrary aliases, signed refund and U64/array domains are not restricted to pinned values. This validates the data seam without mirroring all 144 generated projections in runtime substitution tests; source-value/factory and supported-consumer validation remain separate.

- **Supplied scalar decoder controls:** All 256 bytes per decoder have complete literal guards and actual interpreted target/source frames. These include the boundaries 81/82, 90/91, 127/128, equal-nibble branch cases, byte255, both ordered pair coordinates and exact errors. Public-only clients exercise all eight laws, successful progress, arbitrary-error exclusion and actual input equality. Strict normal/`-O` parsing passes 81 positive and 79 rejection controls per mode; complete images, partitions and valid-input injectivity are also checked. These are local semantic controls, not native allocation, handler or guest evidence.

- **Supplied bounded Stack controls:** Forty-one complete ordered observations cover empty pop/peek, zero/max/high-bit/duplicate words, every position of a mixed model, indices exactly at size and 2^4096, sizes 1023/1024, full push overflow and pop/replacement, and all deterministic sequence intermediates. Public-only callers consume all eight laws, establish success availability/exclusion of unrelated errors and both actual-Stack conditional inverses. The strict normal/`-O` parser checks full frames and rejects boolean/float integer aliases, malformed models/words/schema, incorrect ordering and whole-model changes with unchanged size/top. Original-helper comparison is only bounded typed pop/push; peek remains a labelled List-index adapter.

`TxStateGasUsageCallerProofs.lean` consumes the single ordinary observer equation
through the public Core import. `TxStateGasUsageGuards.lean` retains twenty complete
literal meter/grant/signed-result cases; `tx_state_gas_usage_differential.py` strictly
compares the whole public-import stream normally and under `-O`. Authenticated original
comparison passed twenty direct unchanged `tx_state_gas_used` calls on fresh actual
GasMeter/Uint fields and StateGas grants, with exact builtin `int` results and every
meter field unchanged. Three source-only invalid baseline-to-grant cases preserve the
original assertion at `gas.py:597` and unchanged full inputs; no invalid Lean proof is
fabricated. Source/runtime identities remained unchanged. No original charge, rollback,
refund, transfer, settlement or transaction lifecycle is replayed.

Reproduce the transaction-usage observer with fresh external output paths:

```sh
DRIVER=STFSpec/Conformance/Vm/Core/tx_state_gas_usage_differential.py
OUT=/absolute/path/to/fresh-usage-controls
EELS=/absolute/path/to/pinned-eels
WHEELS=/absolute/path/to/locked-wheels
mkdir -p "$OUT"
python3 -B "$DRIVER" --self-test
python3 -B -O "$DRIVER" --self-test
python3 -B "$DRIVER" --emit-lean > "$OUT/TxUsageFrames.lean"
lake env lean "$OUT/TxUsageFrames.lean" > "$OUT/frames.jsonl"
python3 -B "$DRIVER" --check-frames "$OUT/frames.jsonl"
python3 -B -O "$DRIVER" --check-frames "$OUT/frames.jsonl"
"$EELS/.venv/bin/python" -I -B "$DRIVER" --preflight \
  --eels "$EELS" --wheels "$WHEELS" --output "$OUT/preflight"
"$EELS/.venv/bin/python" -I -B "$DRIVER" --source \
  --eels "$EELS" --wheels "$WHEELS" --output "$OUT/source" --frames "$OUT/frames.jsonl"
```

Use a clean pinned scratch source checkout with its private `.venv` and selected
lock-matching raw wheels. Preflight authenticates inputs without calling the helper.
Source mode compares the original observer's signed result and unchanged full meter;
its three invalid-baseline probes are source-only and supply no Lean proof. Keep
actual complete records and source/runtime identities beside each fresh run.


- **Supplied transaction-usage controls:** Twenty complete literal meter/grant/signed-result guards cover zero, exact and strict baseline-to-grant domains, arbitrary execution gas/refund, reservoir above baseline/grant, isolated and combined spills, cancellation and beyond-U256 values. Private public-only clients use the single equation to derive E/q/baseline insensitivity with separate baseline proofs, additive spills, grant growth, reservoir decrease and their order consequences, plus a valid negative witness. Strict normal/`-O` JSON parsing retains the complete input, grant, signed result and unchanged meter and rejects boolean/float aliases, malformed frames and wrong whole streams. Caller reachability and transaction conservation remain open.

- **Supplied accounting controls:** Twelve complete signed-refund cases and fourteen scalar maxima retain all fields and exact returns, including negative/cross-zero/cancellation/beyond-U256 refunds, both spills, R>B and 63/64 rounding. Public-only clients consume all four laws and derive signed composition/inverse, actual rollback/reset order and complementary grant shares. Strict normal/`-O` frames reject boolean/float aliases and malformed or wrong complete streams. Authenticated original comparison passed exact statement projection on twelve distinct typed parent/child pairs with unchanged full children, plus fourteen direct scalar helper calls. No source caller assertions or whole incorporation are replayed.

- **Supplied transfer controls:** Thirty complete return/six-field guards and strict normal/`-O` frames cover forfeit with S=0 and arbitrary signed q/positive C; withholding 0/1/63/64/65/127/128/129 and beyond-word execution gas; empty/positive/beyond-word reservoir with R>B; restoration with independently zero/nonzero amounts and unbounded addition. Public-only callers use all eight laws to derive field retention, E/64 retention, idempotence, zero identity and complete saved-amount inversion. Actual Lean withhold/drain/repeated-drain/restore and reviewed rollback/forfeit compositions retain every intermediate. Source-only invalid forfeits preserve assertion :674 and unchanged full meter; no invalid proof is synthesized in Lean. Authenticated source comparison observes original returns/classes and full fields, using only the four new original helpers and the real max callee.
- **Supplied refund controls:** `GasRefundGuards.lean` and the strict normal/`-O` complete-frame parser retain twenty full outputs and actual Lean charge/refund/repay intermediates. Public clients use all seven laws and prove the conditional inverse with local initial pending spill zero; a complete-field counterexample excludes unconditional inversion. Min boundaries, R>B, signed refund, both spills, zero execution and unbounded amounts are covered. Source calls use only the two unchanged original helpers on fresh typed meters, with expected `None`, complete fields and enabled repayment postcondition.
- **Supplied rollback controls:** the three helpers have complete-field zero/equality, signed-refund, both-spill, above-baseline (where admitted) and beyond-word cases; guards retain every intermediate meter of the two-boundary composition. Public callers consume all eight laws, without unfolding provider internals. The strict normal/`-O` parser rejects malformed/duplicate/missing/extra fields, Bool-as-Nat, bad arities, reordered/incomplete streams and wrong whole results. Original assertions are checked only in Python, with location/order and unchanged input retained; they are proof arguments in Lean.
- **Supplied charge-kernel controls:** `GasMeterGuards.lean` retains every field for zero, exact and one-over execution charges; reservoir zero/exact, first spill, exact total and one-over total; zero gas, reservoir above baseline, negative refunds, both spill pools and beyond-64-bit amounts. It checks the three zero defaults, every nominal exception tag, all UInt8 opcode payloads and complete String payloads including NUL/newline/Unicode. Public callers cover all ten laws, conditional positive-charge progress, zero-charge neutrality and execution-then-state accounting without unfolding the kernel. The strict differential parser rejects duplicate/missing/extra fields, Bool-as-Nat, wrong arities, malformed payloads and incomplete/reordered streams; compare the complete observations with authenticated original numeric helpers. Other tests below remain obligations for their unsupplied operations.
- **EEST fixture areas** (`STFSpec/informal/eest-fixture-index.txt`, `blockchain_tests/for_amsterdam/…`; the `_engine` copies carry no guest records, GAPS-CROSSCUTTING X5): gas meter and state gas: `amsterdam/eip8037_state_creation_gas_cost_increase` (268), `amsterdam/eip8038_state_access_gas_cost_increase` (88), `amsterdam/eip7778_block_gas_accounting_without_refunds` (9), `amsterdam/eip2780_reduce_intrinsic_tx_gas` (59), `amsterdam/eip7976_increase_calldata_floor_cost`, `osaka/eip7825_transaction_gas_limit_cap`; memory: `ported_static/stMemoryTest` (72), `stMemoryStressTest` (36), `stMemExpandingEIP150Calls`, `cancun/eip5656_mcopy`; call gas: `tangerine_whistle/eip150_operation_gas_costs`, `ported_static/stEIP150Specific`, `stEIP150singleCodeGasPrices`; stack limits: `ported_static/stStackTests`, `amsterdam/eip8024_dupn_swapn_exchange` (66); refunds: `ported_static/stRefundTest`, `istanbul/eip2200_net_gas_metering`; transfer logs: `amsterdam/eip7708_eth_transfer_logs` (38); blob gas: `cancun/eip4844_blobs`, `osaka/eip7918_blob_reserve_price`, `cancun/eip7516_blobgasfee`.
- **EELS unit tests:** none exercise `vm/` directly at e1a316a0 [V: `tests/json_loader/*` touches only tracing (`test_trace.py`)]. The EEST sources under `tests/amsterdam/eip8037_*` (`test_state_gas_reservoir.py`, `test_state_gas_cross_frame_refund.py`, `test_state_gas_ordering.py`) and `tests/amsterdam/eip8024_*` (`test_eip_vectors.py`) are the best specification of the meter and decoders.
- **`core` `#guard` cases** (a `#guard` evaluates only once every leaf it reaches is implemented, F16):
  - `decodeSingle`: all 256 inputs (219 valid, results exactly `17…235`, bijective on the valid range) [V: run against EELS]; `decodePair`: all 256 inputs (210 valid, `1 ≤ n ≤ 14`, `n < m ≤ 30 − n`, injective) [V: run].
  - Memory cost: `C 0 = 0`, `C 32 = 3`, `C (32·724) = 3·724 + 724²/512`; `extendMemory` on `[(2^256−1, 0)]` gives `(0, 0)`; `[(0,32),(0,64)]` equals `[(0,64)]`; a second window below the first adds nothing.

    These prospective pinned-value pricing guards specialize
    `cfg.costs.memoryPerWord = 3` and `cfg.costs.zero = 0` at use; those assumptions
    are not defaults or restrictions of either generic helper.

  - Meter: charge exactly `gas_left` (succeeds, leaves 0); charge `gas_left + 1` (fails, meter unchanged); state charge split across reservoir and `gas_left`; credit when `spilled < a` (remainder to reservoir); repay; restore after commit leaves committed spill charged; `restoreToEntry` refills both spills; negative `refund_counter` after one clear-reversal.
  - `maxMessageCallGas 64 = 63`, `63 = 63`, `0 = 0`; `calculateMessageCallGas` below `extra + mem`.
  - `settleTransactionGas`: refund capped at one fifth; floor binding both dimensions; negative `state_gas_used` clamped to 0.
- **Supplied Jumpdest controls:** 32 unchanged handwritten complete literals cover
  reached/hidden `0x5B`, PUSH1/PUSH2/PUSH32 resumption and truncation, invalid bytes,
  PUSH0, DUPN/SWAPN/EXCHANGE and bitmap boundaries. Private public-only callers
  consume all three laws to derive head/PUSH/non-PUSH behavior, true-hit bounds/byte
  identity, equal-code observations and huge-index absence. Strict normal/`-O`
  public CLI comparisons check complete code, logical bytes, sorted destinations,
  cardinality, every membership/padding bit and probe, and unchanged held maps.
  Thirty malformed complete-frame controls and seven actual LF/framing CLI cases
  per mode are synthetic observations derived from those handwritten controls.
  The canonical 940-input catalog is external: it contains the 32 handwritten
  cases, all 256 one-byte heads, 592 PUSH-width/truncation/resumption inputs,
  24 boundary patterns, 32 repeated/mixed inputs and four whole-code inputs,
  including 24 KiB and 64 KiB. The dated external review linked in §3 records
  interpreted/native/source comparisons, each target backend retaining 940 full
  frames and 2820 held/distractor/saved observations, 193328 membership/padding
  positions and 12910 probes per complete before-observation set; the original
  sets contain 120896 destination members. Those retained results are not a new
  source execution by the committed reader. Logical bytes reconstruct public
  membership; physical bitmap shape follows from the private ordinary proofs.

  - `(HashConsts.query (m := Id)).transferTopic = keccak256 "Transfer(address,address,uint256)" = 0xddf252ad…b3ef` (owned by EthHash §7, `HashConsts.query (m := Id) = HashConsts.literals`).
- **Property/differential:** random meter operation sequences against a direct `Nat` model of the six fields, checking Φ laws (§7); random window lists for `extendMemory` against the closed form; Jumpdest's ordinary all-input packed/reference proof and complete finite controls above supply its local functional slice. Random-code differential campaigns and measured 24 KiB/64 KiB linearity/compiled costs remain future checks; merely running those sizes proves no timing bound.

## 5. Interface

Reference field order, widths and inherited records are catalogued in [REFERENCE-RECORDS](../REFERENCE-RECORDS.md), generated from the exact pin. Wire-schema owners must use those layouts and prove their codec instances. Runtime records may use the explicit abstraction below; omitted fields or `…` remain implementation blockers, not implicit freedom to choose semantics.

All public unless marked internal. Names follow EELS in lowerCamelCase.

```lean
-- Environments (public)
abbrev AddrSet := Std.ExtTreeSet Address
abbrev SlotSet := Std.ExtTreeSet (Address × Bytes32)
structure BlockEnvironment where
  chainId : U64; blockGasLimit : Nat; blockHashes : Array Hash32   -- oldest first, size ≤ 256
  coinbase : Address; number : Nat; baseFeePerGas : Nat; time : U256
  prevRandao : Bytes32; excessBlobGas : U64; parentBeaconBlockRoot : Hash32; slotNumber : U64
structure TransactionEnvironment where
  origin recipient : Address; isCreate : Bool; data : Bytes; value : U256
  gasLimit effectiveGasPrice executionGasGrant stateGasReservoir calldataFloor : Nat
  accessListAddresses : AddrSet; accessListStorageKeys : SlotSet
  blobVersionedHashes : Array VersionedHash; authorizations : Array Authorization
  indexInBlock : Option Nat; txHash : Option Hash32
structure BlockGasCounters where blockGasUsed blockStateGasUsed : Nat; blobGasUsed : U64

-- Frame (public)
structure FrameCtx where
  config : VmConfig           -- immutable policy; children inherit it unchanged
  blockEnv : BlockEnvironment; txEnv : TransactionEnvironment
  caller currentTarget : Address; value : U256; callData : Bytes
  codeAddress : Option Address; code : Bytes; jumpdests : JumpdestMap
  depth : Nat; depth_le : depth ≤ STACK_DEPTH_LIMIT
  shouldTransferValue isStatic disablePrecompiles : Bool
structure Frame where
  pc : Nat; stack : Stack; memory : Memory; gasMeter : GasMeter
  logs : LogRope; accountsToDelete : AddrSet; returnData : Bytes
  accessedAddresses : AddrSet; accessedStorageKeys : SlotSet
structure Evm where ctx : FrameCtx; frame : Frame        -- the EELS-shaped view
abbrev STACK_DEPTH_LIMIT : Nat := 1024   -- a literal: depth proofs and indexed types reduce it (F8)
structure VmLimits where stackDepthLimit maxCodeSize maxInitCodeSize : Nat   -- fork parameters (§8 of ARCHITECTURE); values in EthFork
structure VmConfig where
  costs : GasCosts; stateCosts : StateGasCosts; limits : VmLimits
-- EthFork: `vmLimits_depth : vmConfig.limits.stackDepthLimit = STACK_DEPTH_LIMIT := rfl`

-- VM world threaded through handlers and the runner (public). Generic in the oracle monad `m`
-- (D5): the pre-state inside `TxState m` reads through `m`. This module never needs
-- the hash-query class of EthHash; handlers that hash (EthVmInstructions) add it.
structure VmWorld (m : Type → Type) where
  tx : TxState m             -- single owner of block, revertible writes, and observations
abbrev VmM (m : Type → Type) := StateT (VmWorld m) (ExceptT VmFault m)
inductive OverflowSite | blobBaseFee | refundCounter   -- NUMBER/GASLIMIT/BASEFEE cannot overflow (R-EXC-2)
inductive VmFault | state (e : StateError) | ancestorHashUnavailable (offset : Nat)
                  | u256Overflow (site : OverflowSite)   -- O13 members (R-EXC-2)
def liftState [Monad m] : StateM m α → VmM m α  -- run on world.tx; map every StateError to VmFault.state

-- Exceptions (public)
inductive ExceptionalHalt
  | stackUnderflow | stackOverflow | outOfGas | invalidOpcode (code : UInt8) | invalidJumpDest
  | stackDepthLimit | writeInStaticContext | outOfBoundsRead | invalidParameter
  | invalidContractPrefix | addressCollision | kzgProofError | precompileHalt (reason : String)
inductive FrameError | halt (e : ExceptionalHalt) | revert

-- Shared below both precompile implementations and the runner (D17/D27)
structure Log where address : Address; topics : Array Hash32; data : Bytes
inductive LogRope where
  | empty | leaf (logs : List Log) | concat (left right : LogRope)
def LogRope.toList : LogRope → List Log
def LogRope.append : LogRope → LogRope → LogRope
-- toList uses a work stack and reverse accumulator; avoid repeated List.append on a skew rope.

-- Stack (public; representation internal)
structure Stack                                          -- Array U256, top at the end
def Stack.toList : Stack → List U256                     -- model, top first
def Stack.empty : Stack
def Stack.size : Stack → Nat
def Stack.pop  : Stack → Except ExceptionalHalt (U256 × Stack)
def Stack.push : Stack → U256 → Except ExceptionalHalt Stack
def Stack.peek? (s : Stack) (i : Nat) : Option U256      -- i = 0 is the top
def Stack.swap? (s : Stack) (i j : Nat) : Option Stack
def decodeSingle : UInt8 → Except ExceptionalHalt Nat
def decodePair   : UInt8 → Except ExceptionalHalt (Nat × Nat)

-- Memory (public API, D11/Q62; ten ordinary laws discharged)
structure Memory                    -- private storage, constructor and alignment proof
def Memory.empty : Memory
def Memory.toBytes : Memory → List UInt8
def Memory.size : Memory → Nat
def Memory.expand (m : Memory) (n : Nat) (h : n % 32 = 0) : Memory
def Memory.readBytes (m : Memory) (s k : Nat)
    (h : k = 0 ∨ s + k ≤ m.size) : Bytes
def Memory.write (m : Memory) (s : Nat) (v : Bytes)
    (h : v.size = 0 ∨ s + v.size ≤ m.size) : Memory
-- Standalone supplied adapter; independent of the six Memory APIs
def bufferRead : Bytes → U256 → U256 → Bytes              -- supplied; independent of Memory
-- Memory pricing (supplied; pure values only)
structure ExtendMemory where cost : Nat; expandBy : Nat
def calculateGasExtendMemory (cfg : VmConfig) (m : Memory)
    (ws : List (U256 × U256)) : ExtendMemory
def calculateMemoryGasCost (cfg : VmConfig) (n : Nat) : Nat

-- Gas policy and meter (public)
structure GasCosts where            -- supplied raw data; no defaults or policy values
  base : Nat
  veryLow : Nat
  low : Nat
  mid : Nat
  high : Nat
  warmAccess : Nat
  coldAccountAccess : Nat
  coldStorageAccess : Nat
  storageWrite : Nat
  callStipend : Nat
  accountWrite : Nat
  callValue : Nat
  codeInitPerWord : Nat
  createAccess : Nat
  zero : Nat
  memoryPerWord : Nat
  fastStep : Nat
  refundStorageClear : Int
  precompileEcrecover : Nat
  precompileP256Verify : Nat
  precompileSha256Base : Nat
  precompileSha256PerWord : Nat
  precompileRipemd160Base : Nat
  precompileRipemd160PerWord : Nat
  precompileIdentityBase : Nat
  precompileIdentityPerWord : Nat
  precompileBlake2FPerRound : Nat
  precompilePointEvaluation : Nat
  precompileBlsG1Add : Nat
  precompileBlsG1Mul : Nat
  precompileBlsG1Map : Nat
  precompileBlsG2Add : Nat
  precompileBlsG2Mul : Nat
  precompileBlsG2Map : Nat
  precompileEcAdd : Nat
  precompileEcMul : Nat
  precompileEcPairingBase : Nat
  precompileEcPairingPerPoint : Nat
  perBlob : STFSpec.Base.U64
  blobScheduleTarget : STFSpec.Base.U64
  blobTargetGasPerBlock : STFSpec.Base.U64
  blobBaseCost : Nat
  blobScheduleMax : STFSpec.Base.U64
  blobMinGasPrice : Nat
  blobBaseFeeUpdateFraction : Nat
  blockAccessListItem : Nat
  txBase : Nat
  txValueCost : Nat
  txDataTokenStandard : Nat
  txDataTokenFloor : Nat
  txAccessListAddress : Nat
  txAccessListStorageKey : Nat
  txMaxGasLimit : Nat
  txMaxTotalGasLimit : Nat
  authTupleBytes : Nat
  executionPerAuthBaseCost : Nat
  limitAdjustmentFactor : Nat
  limitMinimum : Nat
  opcodeAdd : Nat
  opcodeSub : Nat
  opcodeMul : Nat
  opcodeDiv : Nat
  opcodeSdiv : Nat
  opcodeMod : Nat
  opcodeSmod : Nat
  opcodeAddmod : Nat
  opcodeMulmod : Nat
  opcodeSignextend : Nat
  opcodeLt : Nat
  opcodeGt : Nat
  opcodeSlt : Nat
  opcodeSgt : Nat
  opcodeEq : Nat
  opcodeIsZero : Nat
  opcodeAnd : Nat
  opcodeOr : Nat
  opcodeXor : Nat
  opcodeNot : Nat
  opcodeByte : Nat
  opcodeShl : Nat
  opcodeShr : Nat
  opcodeSar : Nat
  opcodeClz : Nat
  opcodeJump : Nat
  opcodeJumpi : Nat
  opcodeJumpDest : Nat
  opcodeCallDataLoad : Nat
  opcodeBlockHash : Nat
  opcodeCoinbase : Nat
  opcodePop : Nat
  opcodeMsize : Nat
  opcodePc : Nat
  opcodeGas : Nat
  opcodeAddress : Nat
  opcodeOrigin : Nat
  opcodeCaller : Nat
  opcodeCallValue : Nat
  opcodeCallDataSize : Nat
  opcodeCodeSize : Nat
  opcodeGasPrice : Nat
  opcodeTimestamp : Nat
  opcodeNumber : Nat
  opcodeGasLimit : Nat
  opcodePrevRandao : Nat
  opcodeReturnDataSize : Nat
  opcodeChainId : Nat
  opcodeSelfBalance : Nat
  opcodeBaseFee : Nat
  opcodeBlobBaseFee : Nat
  opcodeSlotNum : Nat
  opcodeBlobHash : Nat
  opcodePush : Nat
  opcodePush0 : Nat
  opcodeDup : Nat
  opcodeSwap : Nat
  opcodeDupn : Nat
  opcodeSwapn : Nat
  opcodeExchange : Nat
  opcodeTload : Nat
  opcodeTstore : Nat
  opcodeReturnDataCopyBase : Nat
  opcodeReturnDataCopyPerWord : Nat
  opcodeCallDataCopyBase : Nat
  opcodeCodeCopyBase : Nat
  opcodeMcopyBase : Nat
  opcodeMloadBase : Nat
  opcodeMstoreBase : Nat
  opcodeMstore8Base : Nat
  opcodeCopyPerWord : Nat
  opcodeExpBase : Nat
  opcodeExpPerByte : Nat
  opcodeKeccak256Base : Nat
  opcodeKeccak256PerWord : Nat
  opcodeLogBase : Nat
  opcodeLogDataPerByte : Nat
  opcodeLogTopic : Nat
  opcodeSelfDestructBase : Nat
  blsPairingBase : Nat
  blsPairingPerPair : Nat
  blsG1KDiscount : Array Nat
  blsG2KDiscount : Array Nat
  blsG1MaxDiscount : Nat
  blsG2MaxDiscount : Nat
  blsMultiplier : Nat
structure StateGasCosts where costPerStateByte bytesPerNewAccount bytesPerStorageSet bytesPerAuthBase : Nat
-- No Amsterdam values here: `EthFork` defines them (B8, F8).
structure GasMeter where
  gasLeft stateGasLeft stateGasBaseline : Nat; refundCounter : Int := 0
  stateGasSpilled : Nat := 0; stateGasCommittedSpill : Nat := 0
inductive PrecompileResult where
  | ok (meter : GasMeter) (output : Bytes)
  | halt (e : ExceptionalHalt)
-- Monadic in the oracle monad (D5): ECRECOVER hashes through the oracle (F3's pure form is not adopted).
abbrev PrecompileFn (m : Type → Type) := Bytes → GasMeter → m PrecompileResult
def MeterOk (g : GasMeter) : PrecompileResult → Prop       -- the returned meter differs only by a gas_left charge
  | .ok g' _ => g'.gasLeft ≤ g.gasLeft ∧ { g' with gasLeft := g.gasLeft } = g
  | .halt _ => True
structure PrecompileTable (m : Type → Type) [Monad m] where
  lookup : Address → Option (PrecompileFn m)
  addresses : AddrSet
  lookup_iff : ∀ a, (lookup a).isSome ↔ a ∈ addresses
  meter_law : ∀ a p i g, lookup a = some p → SatisfiesM (MeterOk g) (p i g)
  -- for every `m`; at `m := Id` it is the plain statement `p i g = .ok g' o → g'.gasLeft ≤ g.gasLeft ∧ …`
def GasMeter.phi (m : GasMeter) : Nat := m.gasLeft + m.stateGasSpilled + m.stateGasCommittedSpill
def checkGas : GasMeter → Nat → Except ExceptionalHalt Unit
def chargeGas : GasMeter → Nat → Except ExceptionalHalt GasMeter          -- charge_gas(_from_meter)
def chargeStateGas : GasMeter → Nat → Except ExceptionalHalt GasMeter     -- charge_state_gas(_from_meter)
def commitStateGas (m : GasMeter) (h : m.stateGasLeft ≤ m.stateGasBaseline) : GasMeter
def restoreStateGas : GasMeter → GasMeter
def restoreStateGasToEntry (m : GasMeter) (R : Nat) (h₁ : m.stateGasBaseline ≤ R) (h₂ : m.refundCounter = 0) : GasMeter
def txStateGasUsed (m : GasMeter) (T : Nat)
    (h : m.stateGasBaseline ≤ T) : Int
def creditStateGasRefund : GasMeter → Nat → GasMeter
def repayStateGasSpill : GasMeter → GasMeter
def forfeitRemainingGas (m : GasMeter) (h : m.stateGasSpilled = 0) : GasMeter
def withholdCreateGas : GasMeter → Nat × GasMeter
def drainStateGasReservoir : GasMeter → Nat × GasMeter
def restoreChildGas : GasMeter → Nat → Nat → GasMeter
def addRefund : GasMeter → Int → GasMeter                                 -- `refund_counter += k`
structure MessageCallGas where
  cost : Nat
  subCall : Nat

def calculateMessageCallGas (cfg : VmConfig) (value : U256)
    (gas gasLeft memoryCost extraGas : Nat)
    (stipend : Nat := cfg.costs.callStipend) : MessageCallGas

def maxMessageCallGas : Nat → Nat

def initCodeCost (cfg : VmConfig) (n : Nat) : Nat
-- transaction/block level (public; consumed by EthBlock)
def calculateExcessBlobGas (parentExcess parentUsed : U64) (parentBaseFee : Nat)
    : Except BlobGasArithmeticError U64  -- checked intermediates, in EELS order
def calculateTotalBlobGas (numBlobs : Nat) : Except BlobGasArithmeticError U64
def calculateBlobGasPrice : U64 → Nat
def calculateDataFee (excessBlobGas : U64) (numBlobs : Nat) : Nat
def checkMaxFeePerBlobGas (numBlobs : Nat) (maxFee : U256) (excess : U64) : Except BlobFeeError Unit
def checkBlockGasCapacity (env : BlockEnvironment) (c : BlockGasCounters) (txGas : Nat) (txBlobGas : U64) : Except CapacityError Unit
-- Q65 allocation and Q66 settlement are supplied locally. Exact laws: §7.
structure EvmGasAllocation where
  executionGas : Nat
  stateGasReservoir : Nat

def allocateEvmGas (cfg : VmConfig) (txGas intrinsicExecution : Nat)
    (hIntrinsicLeTxGas : intrinsicExecution ≤ txGas)
    (hIntrinsicLeCap : intrinsicExecution ≤ cfg.costs.txMaxGasLimit) :
    EvmGasAllocation

structure TransactionGasSettlement where
  gasUsed : Nat
  gasLeft : Nat
  executionGasUsed : Nat
  stateGasUsed : Nat

def settleTransactionGas
    (txGas calldataFloor gasLeft stateGasLeft : Nat)
    (refund : U256) (stateGasUsed : Int)
    (hReturned : gasLeft + stateGasLeft ≤ txGas)
    (hState : stateGasUsed.toNat ≤ txGas - gasLeft - stateGasLeft)
    (hFloor : calldataFloor ≤ txGas) : TransactionGasSettlement

-- Frame exit (public)
def ChildSettled (child : Frame) (failed : Bool) : Prop
-- Non-top child meter: committed spill = 0; if failed, spill/refund = 0 and reservoir = baseline.
-- Includes the exact successful-child side conditions of __init__.py:227,232–234 (L-SETTLE).
-- How the runner produces this proof is open (F11; EthVmRunner §9): a decidable check whose
-- failure is a runner-internal error, or a settled subtype returned by the runner. Keep it decidable.
def incorporateChild (parent : Frame) (child : Frame) (childFailed : Bool) (h : ChildSettled child childFailed) : Frame
def emitTransferLog (f : Frame) (topic : Hash32) (sender recipient : Address) (amount : U256) : Frame
  -- the caller passes `world.tx.block.consts.transferTopic` (HashConsts, D5)
def SYSTEM_ADDRESS : Address

-- Jumpdests (public)
structure JumpdestMap                                     -- abstract; constructor/fields private
def validJumpDestinations : Bytes → JumpdestMap
def JumpdestMap.contains : JumpdestMap → Nat → Bool
```

`TxState`, `TxRevertible` and `StateError` come from `EthState`. Observations live only at `world.tx.obs`, and ancestor access only at `world.tx.block.oldestAncestorOffset`. A snapshot retains only `TxRevertible`. `Log` and `LogRope` are declared here (D27/D24). Precompile types are also declared here; the producer and runner import them. `PrecompileFn m` is monadic so that ECRECOVER's public-key hash goes through `KeccakQuery` (D5); only `EthPrecompiles` needs `[KeccakQuery m]`. `meter_law` is stated with `SatisfiesM` so that it holds for every `m`; at `m := Id` it is the plain equation, and that instance is the minimum required. It holds by construction for the normal form (EthPrecompiles §5), because the meter is fixed by `chargeGas` before the monadic body runs. `BlobGasArithmeticError`, `BlobFeeError` and `CapacityError` are local errors mapped by `EthBlock`; their complete constructor lists remain a §10 obligation. These are Lean-like signatures: declarations must be ordered before their uses in Lean.

The StateGasCosts, VmLimits and VmConfig signatures above are supplied raw data
interfaces: the exact stored field order is the constructor order, and all six
ordinary ext/eta laws are discharged in §7. Complete generic public-constructor
clients inspect every field; no default value or policy-support invariant is
introduced. StateGasCosts retains exactly its four existing Nat inputs, leaving
the separate three amount observations and their coherence contract open.

Q64's two helpers are supplied in `CallGas.lean` and compute values only. Omitting the
stipend supplies the expression `cfg.costs.callStipend` as that call's argument;
its value comes from the actual cfg for the call. A fully applied call observes
only the effective selection: `cfg.costs.zero` at `value = U256.zero`, otherwise
the selected stipend. Init observes only `cfg.costs.codeInitPerWord`. Unused
prices/stateCosts/limits remain arbitrary. No config-WF, alias coherence,
positivity, amount cap or hidden Amsterdam default is required.

Python captures its omitted stipend when the function is defined. Omitted-source
agreement therefore needs the selected argument to equal that authenticated
captured value, or a source adapter passes the value explicitly. Zero-value
agreement uses the current source ZERO and init agreement uses its current
per-word price. This does not assert arbitrary repricing-timing equivalence.
The pure helper adds no error, charge/allocation, length check or child effect.

Q63's helpers compute values only. All cfg inputs are admitted; no config-WF/zero-price/gas/resource proof argument is introduced. Only memoryPerWord affects standalone cost; extension additionally observes zero, old byte size and ordered windows. Private scalar support is permitted; it is not a third public API or a policy view. Existing Core-owned record types and EthFork-owned values retain their owners; the independent StateGasCosts representation gap is not settled here.

Gas-policy-dependent helpers take `VmConfig` or the relevant cost record explicitly. Opcode handlers use `ctx.config`, and child contexts retain it. `BlockConfig` constructs the runner environment and this context from the same records. There are no free `costs` variables or hidden Amsterdam defaults in generic semantics. The current stack/depth proofs use the literal `STACK_DEPTH_LIMIT = 1024`; supporting a different limit requires changing those proofs and indexed types.

## 6. Data structures

| Type | Representation | Model and abstraction | Invariant | Persistence | Cost |
|---|---|---|---|---|---|
| `Stack` | `Array U256`, top at the end | `List U256`, top first; `α s = s.data.toList.reverse` | `size ≤ 1024` | linear-only (frame-owned; the suspended parent frame is never copied) | push/pop/peek/swap O(1) (amortised for push) |
| `Memory` | private `ByteArray` and alignment proof (D11/Q62), supplied | `List UInt8`; `toBytes` is the logical model; size counts bytes | `size % 32 = 0`; each operation takes only its §5 local proof | linear-only frame ownership; immutable read snapshots | target: expand O(n) amortised, read/write O(k); empty operations avoid offset-proportional work; compiled ownership/costs unproved |
| `bufferRead` input/output | existing immutable Base `Bytes`, no new carrier | Base padded-window model in §7 | every finite input/all U256 operands | immutable input and copied result | inferred output-proportional copying O(k), bounded source copy and Nat availability check before narrowing; compiled costs unmeasured |
| `GasMeter` | record of `Nat`/`Int` | itself (public record) | no global invariant; supplied charge/refund/repay, withhold/drain/child restoration and ordinary restore admit every raw record; other operations use only their local premises (§7) | value | O(1) per operation on `Nat`s of size < 2^64 in practice; bignum only for memory costs of huge windows |
| `LogRope` | supplied strict immutable public empty/leaf/concat tree | chronological `List Log` via `toList` | all raw shapes admitted; concat observes left before right; no mutable cache | immutable nodes; production frame ownership remains a caller obligation | append allocates one concat, O(1); workstack flatten O(expanded nodes + emitted logs), including empty/shared occurrences; finite native C3 evidence is scoped in §4 |
| `JumpdestMap` | supplied private LSB-first `ByteArray` bitmap of exactly `⌈\|code\|/8⌉` bytes | finite Nat set (= EELS `Set[Uint]` observation); private structural Boolean membership with proved finite support | only indices `< \|code\|`; padding bits false | immutable/shareable semantically; cache keyed by code hash remains outside semantic state (ARCHITECTURE §7) | target: build O(\|code\|), bounded-width lookup O(1); actual Nat magnitude, compiled allocation/ownership/costs unmeasured |
| `AddrSet`, `SlotSet` (warm sets) | `Std.TreeSet` | finite set | ordered | **worst-case persistent**: the parent's version is retained across a child and reused if the child fails (ARCHITECTURE §5.0) | insert/member O(log n); merge on success O(1) by `L-WARM-MONO` |
| `accountsToDelete` | `Std.TreeSet Address` | finite set | — | persistent (retained parent) | union O(m log(n+m)) |
| `FrameCtx` | record; `code`, `callData` shared `ByteArray` | itself | `depth ≤ 1024` | read-only | — |

## 7. Contract and laws

**Transaction-gas contracts (Q65, Q66).**

Q65's raw carrier/helper and exactly the four allocation ordinary laws below are
**supplied/discharged**; §3 owns their execution and private-client evidence.
Q66's raw carrier/helper and exactly five settlement laws are **supplied/discharged**.
Raw carriers admit every Nat pair/quadruple, without authored defaults/instances
or proof fields. Only helper arguments impose local source-success domains;
invalid-domain calls acquire no fabricated proof, runtime error or completion.

**Allocation: exactly four discharged laws.** Available gas is computed before
the remaining cap, then execution min and reservoir residual. The two bounds
protect the source subtractions; min ≤ available protects the residual without
a third premise. Separate admitted calls have their own proofs; relevant-cap
equality suffices for complete result equality without comparing proof objects,
whole configurations, other prices/state/limits or a global WF predicate.

```lean
theorem EvmGasAllocation.ext (a b : EvmGasAllocation)
    (h_executionGas : a.executionGas = b.executionGas)
    (h_stateGasReservoir : a.stateGasReservoir = b.stateGasReservoir) :
    a = b

theorem EvmGasAllocation.eta (allocation : EvmGasAllocation) :
    EvmGasAllocation.mk allocation.executionGas allocation.stateGasReservoir = allocation

theorem allocateEvmGas_eq (cfg : VmConfig) (txGas intrinsicExecution : Nat)
    (hIntrinsicLeTxGas : intrinsicExecution ≤ txGas)
    (hIntrinsicLeCap : intrinsicExecution ≤ cfg.costs.txMaxGasLimit) :
    allocateEvmGas cfg txGas intrinsicExecution hIntrinsicLeTxGas hIntrinsicLeCap =
      (let available := txGas - intrinsicExecution
       let executionGas := min (cfg.costs.txMaxGasLimit - intrinsicExecution) available
       { executionGas := executionGas
         stateGasReservoir := available - executionGas } : EvmGasAllocation)

theorem allocateEvmGas_congr (a b : VmConfig) (txGas intrinsicExecution : Nat)
    (hIntrinsicLeTxGasA : intrinsicExecution ≤ txGas)
    (hIntrinsicLeCapA : intrinsicExecution ≤ a.costs.txMaxGasLimit)
    (hIntrinsicLeTxGasB : intrinsicExecution ≤ txGas)
    (hIntrinsicLeCapB : intrinsicExecution ≤ b.costs.txMaxGasLimit)
    (hCap : a.costs.txMaxGasLimit = b.costs.txMaxGasLimit) :
    allocateEvmGas a txGas intrinsicExecution hIntrinsicLeTxGasA hIntrinsicLeCapA =
      allocateEvmGas b txGas intrinsicExecution hIntrinsicLeTxGasB hIntrinsicLeCapB
```

**Settlement: exactly five discharged ordinary laws.** In source order, p is pre-refund
usage, c is the one-fifth capped unsigned refund, then sender usage/floor is
computed before clamped state usage and pre-refund execution usage/floor. The
returned-gas proof protects both left-associated subtractions; the state proof
protects p minus clamped state **before** max; the floor proof, with the refund
cap, protects the final sender return. On typed source inputs these three bounds
describe arithmetic success; raising the floor cannot rescue state underflow.
U256 supplies refund range with no extra binder. Section variables abbreviate
the same complete arguments and introduce no public helper or theorem family.

```lean
theorem TransactionGasSettlement.ext (a b : TransactionGasSettlement)
    (hUsed : a.gasUsed = b.gasUsed) (hLeft : a.gasLeft = b.gasLeft)
    (hExecution : a.executionGasUsed = b.executionGasUsed)
    (hState : a.stateGasUsed = b.stateGasUsed) : a = b

theorem TransactionGasSettlement.eta (a : TransactionGasSettlement) :
    TransactionGasSettlement.mk a.gasUsed a.gasLeft
      a.executionGasUsed a.stateGasUsed = a

section
variable (txGas calldataFloor gasLeft stateGasLeft : Nat)
variable (refund : U256) (stateGasUsed : Int)
variable (hReturned : gasLeft + stateGasLeft ≤ txGas)
variable (hState : stateGasUsed.toNat ≤ txGas - gasLeft - stateGasLeft)
variable (hFloor : calldataFloor ≤ txGas)

theorem settleTransactionGas_eq :
    settleTransactionGas txGas calldataFloor gasLeft stateGasLeft refund stateGasUsed
      hReturned hState hFloor =
    let p := txGas - gasLeft - stateGasLeft
    let c := min (p / 5) refund.toNat
    { gasUsed := max (p - c) calldataFloor
      gasLeft := txGas - max (p - c) calldataFloor
      executionGasUsed := max (p - stateGasUsed.toNat) calldataFloor
      stateGasUsed := stateGasUsed.toNat }

theorem settleTransactionGas_gasUsed_le :
    (settleTransactionGas txGas calldataFloor gasLeft stateGasLeft refund stateGasUsed
      hReturned hState hFloor).gasUsed ≤ txGas

theorem settleTransactionGas_executionGasUsed_ge_floor :
    calldataFloor ≤
      (settleTransactionGas txGas calldataFloor gasLeft stateGasLeft refund stateGasUsed
        hReturned hState hFloor).executionGasUsed
end
```

Private public-law clients derive sender conservation, refund-independent complete
block dimensions, signed-state erasure and the separate floor branches, with the
conditional entry-meter/allocation-cap clients described in §3. In particular
`X + S = max p (calldataFloor + S)`; the sum need not equal sender gas used or be
bounded by transaction gas. No additional public law is supplied. Actual caller
bounds/config/refund bridges, universal source/host agreement, fee/provider effects
and composed progress remain open (§10).

**Raw block-gas counter data.** Exactly two ordinary laws are **discharged**
for every raw Nat/Nat/U64 record. No capacity, coherence or initialization
premise is required; equality retains all three independent dimensions.

```lean
theorem BlockGasCounters.ext (a b : BlockGasCounters)
    (hExecution : a.blockGasUsed = b.blockGasUsed)
    (hState : a.blockStateGasUsed = b.blockStateGasUsed)
    (hBlob : a.blobGasUsed = b.blobGasUsed) : a = b

theorem BlockGasCounters.eta (c : BlockGasCounters) :
    BlockGasCounters.mk c.blockGasUsed c.blockStateGasUsed c.blobGasUsed = c
```

**Raw VM configuration data.** Exactly six ordinary laws are **discharged**
for every raw record. Ext requires all four, three and three stored projection
equalities respectively; VmConfig uses actual whole-record equalities, while eta
reconstructs each complete record in constructor order. No positivity, width,
coherence, config-WF, default or Fork initialization premise is required.

```lean
theorem StateGasCosts.ext (a b : StateGasCosts)
    (h_costPerStateByte : a.costPerStateByte = b.costPerStateByte)
    (h_bytesPerNewAccount : a.bytesPerNewAccount = b.bytesPerNewAccount)
    (h_bytesPerStorageSet : a.bytesPerStorageSet = b.bytesPerStorageSet)
    (h_bytesPerAuthBase : a.bytesPerAuthBase = b.bytesPerAuthBase) : a = b

theorem StateGasCosts.eta (c : StateGasCosts) :
    StateGasCosts.mk c.costPerStateByte c.bytesPerNewAccount
      c.bytesPerStorageSet c.bytesPerAuthBase = c

theorem VmLimits.ext (a b : VmLimits)
    (h_stackDepthLimit : a.stackDepthLimit = b.stackDepthLimit)
    (h_maxCodeSize : a.maxCodeSize = b.maxCodeSize)
    (h_maxInitCodeSize : a.maxInitCodeSize = b.maxInitCodeSize) : a = b

theorem VmLimits.eta (c : VmLimits) :
    VmLimits.mk c.stackDepthLimit c.maxCodeSize c.maxInitCodeSize = c

theorem VmConfig.ext (a b : VmConfig)
    (h_costs : a.costs = b.costs)
    (h_stateCosts : a.stateCosts = b.stateCosts)
    (h_limits : a.limits = b.limits) : a = b

theorem VmConfig.eta (c : VmConfig) :
    VmConfig.mk c.costs c.stateCosts c.limits = c
```

Public-only private clients supply arbitrary constructor arguments, inspect the
complete projection tuples and consume these laws. Selected-price chargeGas
congruence requires only cfg.costs.opcodeAdd equality and the same actual meter;
it is separate from the stronger whole-field premises of VmConfig.ext. Success
retains all meter fields except the affordable execution deduction; the public
error iff law preserves the exact shortage/exclusive outOfGas result. No state
amount API, supported-policy predicate, pricing or frame coherence law follows.

**Raw GasCosts data.** Exactly two ordinary laws are **discharged** for all
raw records. Extensionality requires every one of the 144 field equalities, in
the exact §5 order; eta reconstructs every projection in that same order. Actual
Array Nat and Base.U64 equality is retained, without normalization or instances.

```lean
GasCosts.ext (a b : GasCosts)
    (h_base : a.base = b.base)
    (h_veryLow : a.veryLow = b.veryLow)
    (h_low : a.low = b.low)
    (h_mid : a.mid = b.mid)
    (h_high : a.high = b.high)
    (h_warmAccess : a.warmAccess = b.warmAccess)
    (h_coldAccountAccess : a.coldAccountAccess = b.coldAccountAccess)
    (h_coldStorageAccess : a.coldStorageAccess = b.coldStorageAccess)
    (h_storageWrite : a.storageWrite = b.storageWrite)
    (h_callStipend : a.callStipend = b.callStipend)
    (h_accountWrite : a.accountWrite = b.accountWrite)
    (h_callValue : a.callValue = b.callValue)
    (h_codeInitPerWord : a.codeInitPerWord = b.codeInitPerWord)
    (h_createAccess : a.createAccess = b.createAccess)
    (h_zero : a.zero = b.zero)
    (h_memoryPerWord : a.memoryPerWord = b.memoryPerWord)
    (h_fastStep : a.fastStep = b.fastStep)
    (h_refundStorageClear : a.refundStorageClear = b.refundStorageClear)
    (h_precompileEcrecover : a.precompileEcrecover = b.precompileEcrecover)
    (h_precompileP256Verify : a.precompileP256Verify = b.precompileP256Verify)
    (h_precompileSha256Base : a.precompileSha256Base = b.precompileSha256Base)
    (h_precompileSha256PerWord : a.precompileSha256PerWord = b.precompileSha256PerWord)
    (h_precompileRipemd160Base : a.precompileRipemd160Base = b.precompileRipemd160Base)
    (h_precompileRipemd160PerWord : a.precompileRipemd160PerWord = b.precompileRipemd160PerWord)
    (h_precompileIdentityBase : a.precompileIdentityBase = b.precompileIdentityBase)
    (h_precompileIdentityPerWord : a.precompileIdentityPerWord = b.precompileIdentityPerWord)
    (h_precompileBlake2FPerRound : a.precompileBlake2FPerRound = b.precompileBlake2FPerRound)
    (h_precompilePointEvaluation : a.precompilePointEvaluation = b.precompilePointEvaluation)
    (h_precompileBlsG1Add : a.precompileBlsG1Add = b.precompileBlsG1Add)
    (h_precompileBlsG1Mul : a.precompileBlsG1Mul = b.precompileBlsG1Mul)
    (h_precompileBlsG1Map : a.precompileBlsG1Map = b.precompileBlsG1Map)
    (h_precompileBlsG2Add : a.precompileBlsG2Add = b.precompileBlsG2Add)
    (h_precompileBlsG2Mul : a.precompileBlsG2Mul = b.precompileBlsG2Mul)
    (h_precompileBlsG2Map : a.precompileBlsG2Map = b.precompileBlsG2Map)
    (h_precompileEcAdd : a.precompileEcAdd = b.precompileEcAdd)
    (h_precompileEcMul : a.precompileEcMul = b.precompileEcMul)
    (h_precompileEcPairingBase : a.precompileEcPairingBase = b.precompileEcPairingBase)
    (h_precompileEcPairingPerPoint : a.precompileEcPairingPerPoint = b.precompileEcPairingPerPoint)
    (h_perBlob : a.perBlob = b.perBlob)
    (h_blobScheduleTarget : a.blobScheduleTarget = b.blobScheduleTarget)
    (h_blobTargetGasPerBlock : a.blobTargetGasPerBlock = b.blobTargetGasPerBlock)
    (h_blobBaseCost : a.blobBaseCost = b.blobBaseCost)
    (h_blobScheduleMax : a.blobScheduleMax = b.blobScheduleMax)
    (h_blobMinGasPrice : a.blobMinGasPrice = b.blobMinGasPrice)
    (h_blobBaseFeeUpdateFraction : a.blobBaseFeeUpdateFraction = b.blobBaseFeeUpdateFraction)
    (h_blockAccessListItem : a.blockAccessListItem = b.blockAccessListItem)
    (h_txBase : a.txBase = b.txBase)
    (h_txValueCost : a.txValueCost = b.txValueCost)
    (h_txDataTokenStandard : a.txDataTokenStandard = b.txDataTokenStandard)
    (h_txDataTokenFloor : a.txDataTokenFloor = b.txDataTokenFloor)
    (h_txAccessListAddress : a.txAccessListAddress = b.txAccessListAddress)
    (h_txAccessListStorageKey : a.txAccessListStorageKey = b.txAccessListStorageKey)
    (h_txMaxGasLimit : a.txMaxGasLimit = b.txMaxGasLimit)
    (h_txMaxTotalGasLimit : a.txMaxTotalGasLimit = b.txMaxTotalGasLimit)
    (h_authTupleBytes : a.authTupleBytes = b.authTupleBytes)
    (h_executionPerAuthBaseCost : a.executionPerAuthBaseCost = b.executionPerAuthBaseCost)
    (h_limitAdjustmentFactor : a.limitAdjustmentFactor = b.limitAdjustmentFactor)
    (h_limitMinimum : a.limitMinimum = b.limitMinimum)
    (h_opcodeAdd : a.opcodeAdd = b.opcodeAdd)
    (h_opcodeSub : a.opcodeSub = b.opcodeSub)
    (h_opcodeMul : a.opcodeMul = b.opcodeMul)
    (h_opcodeDiv : a.opcodeDiv = b.opcodeDiv)
    (h_opcodeSdiv : a.opcodeSdiv = b.opcodeSdiv)
    (h_opcodeMod : a.opcodeMod = b.opcodeMod)
    (h_opcodeSmod : a.opcodeSmod = b.opcodeSmod)
    (h_opcodeAddmod : a.opcodeAddmod = b.opcodeAddmod)
    (h_opcodeMulmod : a.opcodeMulmod = b.opcodeMulmod)
    (h_opcodeSignextend : a.opcodeSignextend = b.opcodeSignextend)
    (h_opcodeLt : a.opcodeLt = b.opcodeLt)
    (h_opcodeGt : a.opcodeGt = b.opcodeGt)
    (h_opcodeSlt : a.opcodeSlt = b.opcodeSlt)
    (h_opcodeSgt : a.opcodeSgt = b.opcodeSgt)
    (h_opcodeEq : a.opcodeEq = b.opcodeEq)
    (h_opcodeIsZero : a.opcodeIsZero = b.opcodeIsZero)
    (h_opcodeAnd : a.opcodeAnd = b.opcodeAnd)
    (h_opcodeOr : a.opcodeOr = b.opcodeOr)
    (h_opcodeXor : a.opcodeXor = b.opcodeXor)
    (h_opcodeNot : a.opcodeNot = b.opcodeNot)
    (h_opcodeByte : a.opcodeByte = b.opcodeByte)
    (h_opcodeShl : a.opcodeShl = b.opcodeShl)
    (h_opcodeShr : a.opcodeShr = b.opcodeShr)
    (h_opcodeSar : a.opcodeSar = b.opcodeSar)
    (h_opcodeClz : a.opcodeClz = b.opcodeClz)
    (h_opcodeJump : a.opcodeJump = b.opcodeJump)
    (h_opcodeJumpi : a.opcodeJumpi = b.opcodeJumpi)
    (h_opcodeJumpDest : a.opcodeJumpDest = b.opcodeJumpDest)
    (h_opcodeCallDataLoad : a.opcodeCallDataLoad = b.opcodeCallDataLoad)
    (h_opcodeBlockHash : a.opcodeBlockHash = b.opcodeBlockHash)
    (h_opcodeCoinbase : a.opcodeCoinbase = b.opcodeCoinbase)
    (h_opcodePop : a.opcodePop = b.opcodePop)
    (h_opcodeMsize : a.opcodeMsize = b.opcodeMsize)
    (h_opcodePc : a.opcodePc = b.opcodePc)
    (h_opcodeGas : a.opcodeGas = b.opcodeGas)
    (h_opcodeAddress : a.opcodeAddress = b.opcodeAddress)
    (h_opcodeOrigin : a.opcodeOrigin = b.opcodeOrigin)
    (h_opcodeCaller : a.opcodeCaller = b.opcodeCaller)
    (h_opcodeCallValue : a.opcodeCallValue = b.opcodeCallValue)
    (h_opcodeCallDataSize : a.opcodeCallDataSize = b.opcodeCallDataSize)
    (h_opcodeCodeSize : a.opcodeCodeSize = b.opcodeCodeSize)
    (h_opcodeGasPrice : a.opcodeGasPrice = b.opcodeGasPrice)
    (h_opcodeTimestamp : a.opcodeTimestamp = b.opcodeTimestamp)
    (h_opcodeNumber : a.opcodeNumber = b.opcodeNumber)
    (h_opcodeGasLimit : a.opcodeGasLimit = b.opcodeGasLimit)
    (h_opcodePrevRandao : a.opcodePrevRandao = b.opcodePrevRandao)
    (h_opcodeReturnDataSize : a.opcodeReturnDataSize = b.opcodeReturnDataSize)
    (h_opcodeChainId : a.opcodeChainId = b.opcodeChainId)
    (h_opcodeSelfBalance : a.opcodeSelfBalance = b.opcodeSelfBalance)
    (h_opcodeBaseFee : a.opcodeBaseFee = b.opcodeBaseFee)
    (h_opcodeBlobBaseFee : a.opcodeBlobBaseFee = b.opcodeBlobBaseFee)
    (h_opcodeSlotNum : a.opcodeSlotNum = b.opcodeSlotNum)
    (h_opcodeBlobHash : a.opcodeBlobHash = b.opcodeBlobHash)
    (h_opcodePush : a.opcodePush = b.opcodePush)
    (h_opcodePush0 : a.opcodePush0 = b.opcodePush0)
    (h_opcodeDup : a.opcodeDup = b.opcodeDup)
    (h_opcodeSwap : a.opcodeSwap = b.opcodeSwap)
    (h_opcodeDupn : a.opcodeDupn = b.opcodeDupn)
    (h_opcodeSwapn : a.opcodeSwapn = b.opcodeSwapn)
    (h_opcodeExchange : a.opcodeExchange = b.opcodeExchange)
    (h_opcodeTload : a.opcodeTload = b.opcodeTload)
    (h_opcodeTstore : a.opcodeTstore = b.opcodeTstore)
    (h_opcodeReturnDataCopyBase : a.opcodeReturnDataCopyBase = b.opcodeReturnDataCopyBase)
    (h_opcodeReturnDataCopyPerWord : a.opcodeReturnDataCopyPerWord = b.opcodeReturnDataCopyPerWord)
    (h_opcodeCallDataCopyBase : a.opcodeCallDataCopyBase = b.opcodeCallDataCopyBase)
    (h_opcodeCodeCopyBase : a.opcodeCodeCopyBase = b.opcodeCodeCopyBase)
    (h_opcodeMcopyBase : a.opcodeMcopyBase = b.opcodeMcopyBase)
    (h_opcodeMloadBase : a.opcodeMloadBase = b.opcodeMloadBase)
    (h_opcodeMstoreBase : a.opcodeMstoreBase = b.opcodeMstoreBase)
    (h_opcodeMstore8Base : a.opcodeMstore8Base = b.opcodeMstore8Base)
    (h_opcodeCopyPerWord : a.opcodeCopyPerWord = b.opcodeCopyPerWord)
    (h_opcodeExpBase : a.opcodeExpBase = b.opcodeExpBase)
    (h_opcodeExpPerByte : a.opcodeExpPerByte = b.opcodeExpPerByte)
    (h_opcodeKeccak256Base : a.opcodeKeccak256Base = b.opcodeKeccak256Base)
    (h_opcodeKeccak256PerWord : a.opcodeKeccak256PerWord = b.opcodeKeccak256PerWord)
    (h_opcodeLogBase : a.opcodeLogBase = b.opcodeLogBase)
    (h_opcodeLogDataPerByte : a.opcodeLogDataPerByte = b.opcodeLogDataPerByte)
    (h_opcodeLogTopic : a.opcodeLogTopic = b.opcodeLogTopic)
    (h_opcodeSelfDestructBase : a.opcodeSelfDestructBase = b.opcodeSelfDestructBase)
    (h_blsPairingBase : a.blsPairingBase = b.blsPairingBase)
    (h_blsPairingPerPair : a.blsPairingPerPair = b.blsPairingPerPair)
    (h_blsG1KDiscount : a.blsG1KDiscount = b.blsG1KDiscount)
    (h_blsG2KDiscount : a.blsG2KDiscount = b.blsG2KDiscount)
    (h_blsG1MaxDiscount : a.blsG1MaxDiscount = b.blsG1MaxDiscount)
    (h_blsG2MaxDiscount : a.blsG2MaxDiscount = b.blsG2MaxDiscount)
    (h_blsMultiplier : a.blsMultiplier = b.blsMultiplier)
    : a = b
GasCosts.eta (c : GasCosts) :
  GasCosts.mk
    c.base
    c.veryLow
    c.low
    c.mid
    c.high
    c.warmAccess
    c.coldAccountAccess
    c.coldStorageAccess
    c.storageWrite
    c.callStipend
    c.accountWrite
    c.callValue
    c.codeInitPerWord
    c.createAccess
    c.zero
    c.memoryPerWord
    c.fastStep
    c.refundStorageClear
    c.precompileEcrecover
    c.precompileP256Verify
    c.precompileSha256Base
    c.precompileSha256PerWord
    c.precompileRipemd160Base
    c.precompileRipemd160PerWord
    c.precompileIdentityBase
    c.precompileIdentityPerWord
    c.precompileBlake2FPerRound
    c.precompilePointEvaluation
    c.precompileBlsG1Add
    c.precompileBlsG1Mul
    c.precompileBlsG1Map
    c.precompileBlsG2Add
    c.precompileBlsG2Mul
    c.precompileBlsG2Map
    c.precompileEcAdd
    c.precompileEcMul
    c.precompileEcPairingBase
    c.precompileEcPairingPerPoint
    c.perBlob
    c.blobScheduleTarget
    c.blobTargetGasPerBlock
    c.blobBaseCost
    c.blobScheduleMax
    c.blobMinGasPrice
    c.blobBaseFeeUpdateFraction
    c.blockAccessListItem
    c.txBase
    c.txValueCost
    c.txDataTokenStandard
    c.txDataTokenFloor
    c.txAccessListAddress
    c.txAccessListStorageKey
    c.txMaxGasLimit
    c.txMaxTotalGasLimit
    c.authTupleBytes
    c.executionPerAuthBaseCost
    c.limitAdjustmentFactor
    c.limitMinimum
    c.opcodeAdd
    c.opcodeSub
    c.opcodeMul
    c.opcodeDiv
    c.opcodeSdiv
    c.opcodeMod
    c.opcodeSmod
    c.opcodeAddmod
    c.opcodeMulmod
    c.opcodeSignextend
    c.opcodeLt
    c.opcodeGt
    c.opcodeSlt
    c.opcodeSgt
    c.opcodeEq
    c.opcodeIsZero
    c.opcodeAnd
    c.opcodeOr
    c.opcodeXor
    c.opcodeNot
    c.opcodeByte
    c.opcodeShl
    c.opcodeShr
    c.opcodeSar
    c.opcodeClz
    c.opcodeJump
    c.opcodeJumpi
    c.opcodeJumpDest
    c.opcodeCallDataLoad
    c.opcodeBlockHash
    c.opcodeCoinbase
    c.opcodePop
    c.opcodeMsize
    c.opcodePc
    c.opcodeGas
    c.opcodeAddress
    c.opcodeOrigin
    c.opcodeCaller
    c.opcodeCallValue
    c.opcodeCallDataSize
    c.opcodeCodeSize
    c.opcodeGasPrice
    c.opcodeTimestamp
    c.opcodeNumber
    c.opcodeGasLimit
    c.opcodePrevRandao
    c.opcodeReturnDataSize
    c.opcodeChainId
    c.opcodeSelfBalance
    c.opcodeBaseFee
    c.opcodeBlobBaseFee
    c.opcodeSlotNum
    c.opcodeBlobHash
    c.opcodePush
    c.opcodePush0
    c.opcodeDup
    c.opcodeSwap
    c.opcodeDupn
    c.opcodeSwapn
    c.opcodeExchange
    c.opcodeTload
    c.opcodeTstore
    c.opcodeReturnDataCopyBase
    c.opcodeReturnDataCopyPerWord
    c.opcodeCallDataCopyBase
    c.opcodeCodeCopyBase
    c.opcodeMcopyBase
    c.opcodeMloadBase
    c.opcodeMstoreBase
    c.opcodeMstore8Base
    c.opcodeCopyPerWord
    c.opcodeExpBase
    c.opcodeExpPerByte
    c.opcodeKeccak256Base
    c.opcodeKeccak256PerWord
    c.opcodeLogBase
    c.opcodeLogDataPerByte
    c.opcodeLogTopic
    c.opcodeSelfDestructBase
    c.blsPairingBase
    c.blsPairingPerPair
    c.blsG1KDiscount
    c.blsG2KDiscount
    c.blsG1MaxDiscount
    c.blsG2MaxDiscount
    c.blsMultiplier
    = c
```

The constructor/projections are ordinary public data operations. There is no
raw-record alias, positivity, table-size or denominator invariant. Supported
consumer assumptions and fork initialization remain separate as recorded in §3.

**Stack** (model `List U256`, top first). The six-operation bounded slice supplies
exactly these eight **discharged** ordinary laws, for every Stack/word/Nat index
and every ExceptionalHalt; the carrier itself stores the bound. No reachability,
host index-width or word-validity premise is added.

```lean
Stack.toList_empty : Stack.empty.toList = []
Stack.size_eq_length_toList (s : Stack) : s.size = s.toList.length
Stack.size_le (s : Stack) : s.size ≤ 1024
Stack.pop_eq_error_iff (s : Stack) (e : ExceptionalHalt) :
  s.pop = .error e ↔ s.toList = [] ∧ e = .stackUnderflow
Stack.pop_eq_ok_iff (s t : Stack) (v : U256) :
  s.pop = .ok (v, t) ↔ s.toList = v :: t.toList
Stack.push_eq_error_iff (s : Stack) (v : U256) (e : ExceptionalHalt) :
  s.push v = .error e ↔ s.size = 1024 ∧ e = .stackOverflow
Stack.push_eq_ok_iff (s t : Stack) (v : U256) :
  s.push v = .ok t ↔ s.size < 1024 ∧ t.toList = v :: s.toList
Stack.peek?_eq_getElem? (s : Stack) (i : Nat) :
  s.peek? i = s.toList[i]?
```

Nonfull-push/nonempty-pop availability and both conditional actual-Stack inverses
are public-law client results, without private storage unfolding or additional
provider laws. `swap?` remains unsupplied: its in-bounds model swap does not yet
specify the all-input none/identity behavior.

**Scalar immediate decoders.** Exactly eight ordinary laws are **discharged**,
on every actual UInt8. `^^^` below is Nat xor, and error payloads remain nullary.

```lean
decodeSingle_eq (x : UInt8) :
  decodeSingle x =
    if 91 ≤ x.toNat ∧ x.toNat ≤ 127 then .error .invalidParameter
    else .ok ((x.toNat + 145) % 256)
decodeSingle_eq_error_iff (x : UInt8) :
  decodeSingle x = .error .invalidParameter ↔ 91 ≤ x.toNat ∧ x.toNat ≤ 127
decodeSingle_bounds (x : UInt8) (n : Nat) (h : decodeSingle x = .ok n) :
  17 ≤ n ∧ n ≤ 235
decodeSingle_injective (x y : UInt8) (n : Nat)
    (hx : decodeSingle x = .ok n) (hy : decodeSingle y = .ok n) : x = y
decodePair_eq (x : UInt8) :
  decodePair x =
    if 82 ≤ x.toNat ∧ x.toNat ≤ 127 then .error .invalidParameter
    else
      let k := x.toNat ^^^ 143
      let q := k / 16
      let r := k % 16
      .ok (if q < r then (q + 1, r + 1) else (r + 1, 29 - q))
decodePair_eq_error_iff (x : UInt8) :
  decodePair x = .error .invalidParameter ↔ 82 ≤ x.toNat ∧ x.toNat ≤ 127
decodePair_bounds (x : UInt8) (n m : Nat) (h : decodePair x = .ok (n,m)) :
  1 ≤ n ∧ n ≤ 14 ∧ n < m ∧ m ≤ 30 - n
decodePair_injective (x y : UInt8) (n m : Nat)
    (hx : decodePair x = .ok (n,m)) (hy : decodePair y = .ok (n,m)) : x = y
```

The complete equations exclude every alternative error and determine success on
the valid domain. Source U8 construction follows modulo256 for the single decoder;
xor143 stays below256, divmod uses nonzero16, and the pair increments/subtraction
stay in range. No additional checked-arithmetic fault occurs on this typed domain.
The source rows and finite comparison evidence are owned by §3.

**Memory** (Q62; model `List UInt8`). Exactly ten ordinary laws
are **discharged** in `STFSpec/Vm/Core/Memory.lean`. They are [C] boundaries for
[R] memory-opcode clients (exercise 1). No additional public helper or law is
implied by the sketches.

In M9, let `h' : v.size = 0 ∨ s + v.size ≤ (m.write s v h).size` be the
proof derived by rewriting the result size with M8 `size_write` and using h.
In M10, let `hR' : k = 0 ∨ t + k ≤ (m.write s v hW).size` be derived in the
same way from M8 and hR. These are determined proof arguments to the result read,
not new semantic premises, additional public binders or an exported support helper.
The size law is stated before both reads; proof irrelevance avoids distinguishing
witnesses. The following are informal signatures, not Lean proofs.

```lean
-- M1
Memory.toBytes_empty : Memory.empty.toBytes = []
-- M2
Memory.length_toBytes (m : Memory) : m.toBytes.length = m.size
-- M3
Memory.size_mod32 (m : Memory) : m.size % 32 = 0
-- M4
Memory.toBytes_expand (m : Memory) (n : Nat) (h : n % 32 = 0) :
  (m.expand n h).toBytes = m.toBytes ++ List.replicate n 0
-- M5
Memory.readBytes_toList (m : Memory) (s k : Nat)
    (h : k = 0 ∨ s + k ≤ m.size) :
  (m.readBytes s k h).toList = (m.toBytes.drop s).take k
-- M6
Memory.toBytes_write (m : Memory) (s : Nat) (v : Bytes)
    (h : v.size = 0 ∨ s + v.size ≤ m.size) :
  (m.write s v h).toBytes =
    m.toBytes.take s ++ v.toList ++ m.toBytes.drop (s + v.size)
-- M7
Memory.write_empty (m : Memory) (s : Nat) :
  m.write s Bytes.empty (Or.inl Bytes.size_empty) = m
-- M8
Memory.size_write (m : Memory) (s : Nat) (v : Bytes)
    (h : v.size = 0 ∨ s + v.size ≤ m.size) :
  (m.write s v h).size = m.size
-- M9; h' is derived above from M8 and h
Memory.readBytes_write (m : Memory) (s : Nat) (v : Bytes)
    (h : v.size = 0 ∨ s + v.size ≤ m.size) :
  (m.write s v h).readBytes s v.size h' = v
-- M10; hR' is derived above from M8 and hR
Memory.readBytes_write_disjoint (m : Memory) (s : Nat) (v : Bytes) (t k : Nat)
    (hW : v.size = 0 ∨ s + v.size ≤ m.size)
    (hR : k = 0 ∨ t + k ≤ m.size)
    (hD : k = 0 ∨ v.size = 0 ∨ t + k ≤ s ∨ s + v.size ≤ t) :
  (m.write s v hW).readBytes t k hR' = m.readBytes t k hR
```

M6 specifies every byte, including empty v at arbitrary s (take/drop reassemble
the original model). M7 additionally requires actual Memory equality, established
privately; no generic extensionality or representation-injectivity API is exposed.
M9/M10 explicitly include empty windows, even inside another window or beyond the
memory end. Expansion length and preservation follow from M2–M4/M8. Read-then-write
MCOPY snapshot behavior, including both overlap directions and self-copy, follows
as a public-law client derivation from immutable reads and M5/M8/M9; disjoint
retention uses M10. This adds no Memory.copy operation or extra public law.

**Padded buffer read.** Exactly these three ordinary public laws are **discharged**
for every finite Bytes and all U256 operands, without a Memory/gas/host-cap premise.
The bridge is actual Bytes equality to the existing public Base provider; the
other two laws consume its existing public List-window and size seams.

```
bufferRead_eq_extractPadded (b : Bytes) (start size : U256) :
  bufferRead b start size = Bytes.extractPadded b start.toNat size.toNat
bufferRead_toList (b : Bytes) (start size : U256) :
  (bufferRead b start size).toList =
    (b.toList.drop start.toNat).take size.toNat ++
      List.replicate (size.toNat - min size.toNat (b.size - start.toNat)) 0
bufferRead_size (b : Bytes) (start size : U256) :
  (bufferRead b start size).size = size.toNat
```

**Memory pricing (Q63).** The following exact ten ordinary laws are discharged
in `MemoryGas.lean`. Private public-only clients derive the consequences below.
This is informal contract notation, not Lean proof bodies. It introduces no
additional public helper.

No additional proof argument belongs to either helper. Let a=cfg.costs.memoryPerWord
and z=cfg.costs.zero. Both are arbitrary Nat, not fixed Amsterdam values. For
mathematical notation only, W(n)=ceil32(n)/32 and C_a(n)=a*W(n)+W(n)^2/512.
Define E(ws) as the maximum of start.toNat+size.toNat over just the windows with
size.toNat≠0; the empty filtered maximum is 0. Put F(m,ws)=ceil32(max(m.size,E(ws))).
E/F/W/C are local informal notation, not new public helpers, fields or policy views.
Each endpoint adds two unbounded Nat observations, never two U256 words.
In each extension statement r abbreviates calculateGasExtendMemory cfg m ws.

Every Memory is the existing structurally aligned carrier. Windows are every
finite ordered list of U256 pairs; scalar n is every Nat. There is no config-WF,
canonical-value, nonzero-price, gas, allocation, host-width or global-frame premise
in the pure Lean pricing functions or laws. Literal32/512 remain algorithm constants.

| ID and ordinary law | Exact statement and local domain |
|---|---|
| MP1 calculateMemoryGasCost_eq | For every cfg,n, calculateMemoryGasCost cfg n = a*(ceil32(n)/32)+(ceil32(n)/32)^2/512. ZERO is absent. |
| MP2 calculateMemoryGasCost_mono | For every cfg,n,n', n≤n' implies calculateMemoryGasCost cfg n≤calculateMemoryGasCost cfg n'. No a>0 premise or strict conclusion. |
| MP3 calculateGasExtendMemory_nil | For every cfg,m, calculateGasExtendMemory cfg m [] = {cost:=z,expandBy:=0}, the complete result. |
| MP4 calculateGasExtendMemory_zero | For every cfg,m, as,bs:List(U256 × U256) and s:U256, extension on as++[(s,0)]++bs equals extension on as++bs as an actual complete ExtendMemory result. Empty windows are skipped before endpoint work. |
| MP5 calculateGasExtendMemory_expandBy | For every cfg,m,ws, r=calculateGasExtendMemory cfg m ws implies r.expandBy=F(m,ws)-m.size. |
| MP6 calculateGasExtendMemory_cost | For the same complete domain, r.cost=z+(C_a(F(m,ws))-C_a(m.size)). The Nat subtraction is justified by F≥m.size and MP2, rather than concealing a negative source Uint subtraction. |
| MP7 calculateGasExtendMemory_aligned | For every cfg,m,ws, r.expandBy%32=0. This produces the existing Memory.expand local argument. |
| MP8 calculateGasExtendMemory_covers | For every listed (s,k)∈ws, k.toNat=0 or s.toNat+k.toNat≤m.size+r.expandBy. This covers every window and preserves the empty branch. |
| MP9 calculateMemoryGasCost_congr | If cfg.costs.memoryPerWord=cfg'.costs.memoryPerWord, then for every n, calculateMemoryGasCost cfg n=calculateMemoryGasCost cfg' n. No equality of zero, GasCosts, StateGasCosts, limits or entire configs. |
| MP10 calculateGasExtendMemory_congr | If both memoryPerWord projections agree and both zero projections agree, then for every same m,ws the complete extension results agree. No whole-config equality/WF/coherence or other price premise. |

Derived public-only clients, rather than extra required public laws:

- Scalar cost(0)=0, rounding invariance, and standard a=3 specialization follow
  from MP1 and public ceil32 laws. Zero seed is irrelevant to scalar cost.
- m.size+r.expandBy=F follows from MP5 and F≥m.size; MP7/MP8 with the existing
  Memory expansion/model/size laws yields each actual empty-or-in-bounds read/write
  premise. A write also needs actual payload-size correspondence from its caller.
- Complete size invariance for same-size Memory values follows from MP5/MP6 and
  the two existing ExtendMemory fields; it supplies no Memory equality or content
  observer. Unrelated config fields are irrelevant through MP9/MP10, not a WF proof.
- Permutation, duplication and insertion of windows whose nonempty endpoints are
  at most the prior F preserve the complete result through the filtered maximum.
  This says nothing about intermediate fold states/callee counts/time/allocations.
- For rA=ext cfg m as, mA=m.expand rA.expandBy hA (MP7), rB=ext cfg mA bs and
  r=ext cfg m (as++bs), r.expandBy=rA.expandBy+rB.expandBy and
  r.cost+z=rA.cost+rB.cost. This seed-aware addition equation requires no z=0.
  The simpler r.cost=rA.cost+rB.cost is a specialization using z=0 at theorem use.
- Empty/all-subsumed extension costs z; zero-cost neutrality needs z=0 at theorem
  use. a=0 permits positive extent with zero cost below the first quadratic step;
  the quadratic term can still increase for larger extents. No generic
  strict-growth, cost=0 iff extent=0, allocation feasibility or resource bound.

All derived clients use public Memory/Base/pricing laws. MP2 can use derived ceil32
monotonicity from existing least-multiple/bounds laws; no new Base export is needed.

Pricing retains its independent resource obligation:
- `L-MEM-BOUND` [T/S]: `chargeGas g (… + ext.cost) = .ok _ → ext.expandBy ≤ f(g)` for an explicit `f` (the quadratic inverse); this is what makes "no allocation before charge" a resource bound.

Pure price/alignment/coverage equations do not prove L-MEM-BOUND or authorize
allocation, including for huge mathematically admitted extents.

**Logs** [C], supplied ordinary laws on arbitrary raw fields and every finite rope:

```lean
Log.ext (a b : Log)
  (h_address : a.address = b.address)
  (h_topics : a.topics = b.topics)
  (h_data : a.data = b.data) : a = b
Log.eta (l : Log) : Log.mk l.address l.topics l.data = l
LogRope.toList_empty : LogRope.toList .empty = []
LogRope.toList_leaf (ls : List Log) : LogRope.toList (.leaf ls) = ls
LogRope.toList_concat (left right : LogRope) :
  LogRope.toList (.concat left right) = LogRope.toList left ++ LogRope.toList right
LogRope.toList_append (left right : LogRope) :
  LogRope.toList (LogRope.append left right) =
    LogRope.toList left ++ LogRope.toList right
```

The private legible recursive List reference is connected to the explicit pending
workstack and reverse accumulator by an ordinary generalized equality. Its private
sum of pending node-occurrence weights strictly decreases for empty/leaf removal
and concat expansion, proving total descent on all finite raw trees. Each expanded
node and leaf log occurrence is processed once, including repeated shared subtrees;
no repeated recursive List append is used by execution. Public callers use the six
laws, without unfolding providers or execution. Raw constructor equality is still
observable; no quotient/extensional/injective LogRope law or structural append
equation is exported. Mathematical occurrence cost and finite native C3 diagnostics
in §4 are separate from actual consumer ownership and general resource bounds.

**Gas meter** [C]. The supplied charge kernel has exactly ten public laws below,
proved on every raw meter and natural amount. No baseline/reservoir relation, refund
sign, spill exclusivity, schedule positivity or global `Wf` is a premise. Record-update
equations preserve all untouched fields; each subtraction has its preceding local
affordability guard. The three rollback operations additionally supply the eight laws
below on their complete local proof domains (R-GAS-1), without global `Wf`. Refund
credit and spill repayment supply seven further laws on every raw meter. The four
local transfer operations supply eight further ordinary laws below: forfeiture uses
only pending spill zero; the other three admit every raw meter and natural amount.
The remaining meter-operation equations are source-checked obligations (G1, ARCHITECTURE §5.5).

| Supplied public law | Contract |
|---|---|
| `checkGas_eq_ok_iff g a` | `checkGas g a = .ok () ↔ a ≤ g.gasLeft` |
| `checkGas_eq_error_iff g a e` | `checkGas g a = .error e ↔ g.gasLeft < a ∧ e = .outOfGas` |
| `chargeGas_of_le g a h` | With `h : a ≤ g.gasLeft`, success is exactly `{ g with gasLeft := g.gasLeft - a }` |
| `chargeGas_eq_error_iff g a e` | `chargeGas g a = .error e ↔ g.gasLeft < a ∧ e = .outOfGas` |
| `chargeGas_phi g a g' h` | Success gives `g'.phi + a = g.phi` |
| `chargeStateGas_of_le g a h` | With `h : a ≤ g.stateGasLeft`, success is exactly `{ g with stateGasLeft := g.stateGasLeft - a }` |
| `chargeStateGas_of_lt g a hR hA` | With `hR : g.stateGasLeft < a`, `hA : a ≤ g.stateGasLeft + g.gasLeft`, success is exactly `{ g with gasLeft := g.gasLeft - (a - g.stateGasLeft), stateGasLeft := 0, stateGasSpilled := g.stateGasSpilled + (a - g.stateGasLeft) }` |
| `chargeStateGas_eq_error_iff g a e` | Error iff `g.stateGasLeft + g.gasLeft < a ∧ e = .outOfGas` |
| `chargeStateGas_phi g a g' h` | Success gives `g'.phi = g.phi` |
| `chargeStateGas_gasLeft_le g a g' h` | Success gives `g'.gasLeft ≤ g.gasLeft` |

| Additional supplied public law | Contract |
|---|---|
| `commitStateGas_eq m h` | Exactly `{ m with stateGasCommittedSpill := m.stateGasCommittedSpill + m.stateGasSpilled, stateGasBaseline := m.stateGasLeft, stateGasSpilled := 0 }` |
| `commitStateGas_phi m h` | `(commitStateGas m h).phi = m.phi` |
| `restoreStateGas_eq m` | Exactly `{ m with gasLeft := m.gasLeft + m.stateGasSpilled, stateGasSpilled := 0, stateGasLeft := m.stateGasBaseline, refundCounter := 0 }` |
| `restoreStateGas_phi m` | `(restoreStateGas m).phi = m.phi` |
| `restoreStateGas_post m` | Pending spill and refund zero; reservoir equals unchanged baseline; no committed-spill-zero conclusion |
| `restoreStateGasToEntry_eq m R h₁ h₂` | Exactly `{ m with gasLeft := m.gasLeft + m.stateGasSpilled + m.stateGasCommittedSpill, stateGasSpilled := 0, stateGasCommittedSpill := 0, stateGasLeft := R, stateGasBaseline := R }`; refund unchanged |
| `restoreStateGasToEntry_phi m R h₁ h₂` | `(restoreStateGasToEntry m R h₁ h₂).phi = m.phi` |
| `restoreStateGasToEntry_post m R h₁ h₂` | Both spills and refund zero; reservoir and baseline both `R` |

Commit uses only `h : m.stateGasLeft ≤ m.stateGasBaseline`. Entry restore uses only
`h₁ : m.stateGasBaseline ≤ R` and `h₂ : m.refundCounter = 0`. Ordinary restore has
no premise and preserves committed spill even on raw meters with `R>B` or negative
refund. These three operations use only unbounded addition: no subtraction, word cast,
refund-sign assumption, spill-exclusivity assumption or new failure channel occurs.
Their local postconditions do not discharge the full `L-SETTLE` or F11 obligations.


| Supplied refund public law | Contract |
|---|---|
| `creditStateGasRefund_eq m a` | With `x = min a m.stateGasSpilled`, exactly `{ m with gasLeft := m.gasLeft + x, stateGasSpilled := m.stateGasSpilled - x, stateGasLeft := m.stateGasLeft + (a - x) }` |
| `creditStateGasRefund_phi m a` | `(creditStateGasRefund m a).phi = m.phi` |
| `creditStateGasRefund_zero m` | `creditStateGasRefund m 0 = m` |
| `repayStateGasSpill_eq m` | With `y = min m.stateGasLeft m.stateGasSpilled`, exactly `{ m with gasLeft := m.gasLeft + y, stateGasLeft := m.stateGasLeft - y, stateGasSpilled := m.stateGasSpilled - y }` |
| `repayStateGasSpill_phi m` | `(repayStateGasSpill m).phi = m.phi` |
| `repayStateGasSpill_post m` | `(repayStateGasSpill m).stateGasLeft = 0 ∨ (repayStateGasSpill m).stateGasSpilled = 0` |
| `repayStateGasSpill_idempotent m` | `repayStateGasSpill (repayStateGasSpill m) = repayStateGasSpill m` |

All four min/subtraction bounds are ordinary Nat facts. Repayment's source assertion
is a universal postcondition, as specified in §2.5, rather than a proof argument.
Both operations preserve baseline, signed refund and committed spill. A refund may
raise the reservoir above baseline; it repays only pending spill, without a new error.
Public clients derive exact charge/refund inversion under initial pending spill zero,
retaining arbitrary baseline/refund/committed spill; that conditional local fact
establishes no transaction conservation, reachability, incorporation or settlement law.

| Supplied transfer public law | Contract |
|---|---|
| `forfeitRemainingGas_eq m h` | With only `h : m.stateGasSpilled = 0`, exactly `{ m with gasLeft := 0 }` |
| `forfeitRemainingGas_phi m h` | `(forfeitRemainingGas m h).phi = m.stateGasCommittedSpill ∧ (forfeitRemainingGas m h).phi ≤ m.phi` |
| `withholdCreateGas_eq m` | Exactly `(m.gasLeft - m.gasLeft / 64, { m with gasLeft := m.gasLeft - (m.gasLeft - m.gasLeft / 64) })`, saved grant first |
| `withholdCreateGas_phi m` | `(withholdCreateGas m).2.phi + (withholdCreateGas m).1 = m.phi` |
| `drainStateGasReservoir_eq m` | Exactly `(m.stateGasLeft, { m with stateGasLeft := 0 })`, old reservoir first |
| `drainStateGasReservoir_phi m` | `(drainStateGasReservoir m).2.phi = m.phi` |
| `restoreChildGas_eq m g T` | Exactly `{ m with gasLeft := m.gasLeft + g, stateGasLeft := m.stateGasLeft + T }` |
| `restoreChildGas_phi m g T` | `(restoreChildGas m g T).phi = m.phi + g` |

Both withhold subtraction bounds are ordinary Nat facts: `E/64 ≤ E` and
`E-E/64 ≤ E`. Thus source checked Uint subtraction cannot underflow on this domain;
Nat subtraction hides no failed check. Public clients derive the exact retained share
E/64, without unfolding the provider. Draining excludes R from phi; restoration counts
only g, independently of T. Forfeit leaves arbitrary C. The saved-amount round trip is
local algebra, not an unconditional CREATE/CALL child-return or iteration-progress law.
The separately supplied `maxMessageCallGas` has its own scalar laws below;
withholding is not refactored through it.


| Supplied signed-addition/scalar public law | Contract |
|---|---|
| `addRefund_eq m k` | `addRefund m k = { m with refundCounter := m.refundCounter + k }` |
| `addRefund_phi m k` | `(addRefund m k).phi = m.phi` |
| `maxMessageCallGas_eq g` | `maxMessageCallGas g = g - g / 64` |
| `maxMessageCallGas_le g` | `maxMessageCallGas g ≤ g` |

These four laws have no premises: signed k and q are unbounded, and all five Nat
meter fields are unrestricted. The scalar subtraction bound `g/64 ≤ g` is universal.
Signed addition preserves Φ, without establishing a nonnegative refund or a valid
child merge. Public clients derive zero, composition, inverse, exact rollback/reset
order, and both complementary-share equations. No new public law or global WF is needed.

An ordinary public-only client derives `g'.phi + 1 ≤ g.phi` from `chargeGas_phi`
under `1 ≤ a`; no continuing-opcode progress or sufficient-budget result follows.
The complete nominal exception carrier supplies vocabulary only; its other producers
remain unimplemented.

**Transaction state-gas usage (Q61), supplied local observer.** The
`txStateGasUsed` observer has only the local proof argument
`h : m.stateGasBaseline ≤ T`, matching `gas.py:597` and R-GAS-1. It neither changes
the meter nor returns an error. Its one required ordinary equation is:

```lean
theorem txStateGasUsed_eq (m : GasMeter) (T : Nat)
    (h : m.stateGasBaseline ≤ T) :
    txStateGasUsed m T h =
      (T : Int) - (m.stateGasLeft : Int) +
        (m.stateGasSpilled : Int) + (m.stateGasCommittedSpill : Int)
```

The ordinary equation is discharged in `GasMeter.lean`. Cast before
subtraction: the result is signed and may be negative. All other raw fields are
unrestricted, including execution gas, refund sign and both spill pools; the
reservoir may exceed both baseline and grant. For example, `(E,R,B,q,S,C) =
(13,21,9,99,3,5)` with `T = 10` meets the premise and returns `-3`. Callers must
establish this local proof; no global `Wf`, non-negativity premise, clamp, runtime
error or bundled domain is added. Caller reachability and transaction conservation
remain separate obligations. The observer and this equation are discharged.

### Supplied call/init-code pricing laws (Q64)

All six ordinary laws below are **discharged** in `CallGas.lean`; both helpers
and the result carrier are supplied. `U256.zero` and `ceil32` are the existing public Base values/
operation. No private pricing model or extra public helper occurs in these types.

```lean
theorem MessageCallGas.ext (a b : MessageCallGas)
    (h_cost : a.cost = b.cost) (h_subCall : a.subCall = b.subCall) :
    a = b

theorem MessageCallGas.eta (r : MessageCallGas) :
    MessageCallGas.mk r.cost r.subCall = r

theorem calculateMessageCallGas_eq (cfg : VmConfig) (value : U256)
    (gas gasLeft memoryCost extraGas stipend : Nat) :
    let t := if value = U256.zero then cfg.costs.zero else stipend
    calculateMessageCallGas cfg value gas gasLeft memoryCost extraGas stipend =
      if gasLeft < extraGas + memoryCost then
        MessageCallGas.mk (gas + extraGas) (gas + t)
      else
        let q := min gas
          (maxMessageCallGas ((gasLeft - memoryCost) - extraGas))
        MessageCallGas.mk (q + extraGas) (q + t)

theorem calculateMessageCallGas_congr (cfg₁ cfg₂ : VmConfig)
    (value : U256) (gas gasLeft memoryCost extraGas stipend₁ stipend₂ : Nat)
    (h_price :
      (if value = U256.zero then cfg₁.costs.zero else stipend₁) =
      (if value = U256.zero then cfg₂.costs.zero else stipend₂)) :
    calculateMessageCallGas cfg₁ value gas gasLeft memoryCost extraGas stipend₁ =
    calculateMessageCallGas cfg₂ value gas gasLeft memoryCost extraGas stipend₂

theorem initCodeCost_eq (cfg : VmConfig) (n : Nat) :
    initCodeCost cfg n = (cfg.costs.codeInitPerWord * ceil32 n) / 32

theorem initCodeCost_congr (cfg₁ cfg₂ : VmConfig)
    (h_price : cfg₁.costs.codeInitPerWord = cfg₂.costs.codeInitPerWord)
    (n : Nat) :
    initCodeCost cfg₁ n = initCodeCost cfg₂ n
```

The affordable branch establishes both source subtraction bounds. Its q is at
most the request and available maximum; shortage returns the uncapped request
before either subtraction. Fully applied congruence compares selected effective
stipends, not unused zero/default fields or whole configs. The source-ordered
init equation is refined by a private public-law client to word pricing using
`ceil32_mod_eq_zero`; exact divisibility justifies that refinement.

Supplied private public-law clients consume the complete result and actual
`chargeGas` success/error values. With the calculator's gasLeft equal to the
meter's gasLeft, charging `result.cost + memoryCost` succeeds exactly when
`memoryCost + extraGas ≤ gasLeft`; success changes only gasLeft and shortage
returns only outOfGas. All other raw meter fields, including arbitrary signed
refund and both spill pools, remain unconstrained. Relevant-price congruence
also transports the complete checked charge; init transports
`otherCharge + initCodeCost cfg n`. These are discharged private clients, not
additional public laws or discharged source-handler obligations.

Under affordability, if t is the selected effective stipend and
A = (gasLeft − memoryCost) − extraGas, the discharged private local consequences are
`result.cost ≤ gasLeft − memoryCost`,
`result.subCall = (result.cost − extraGas) + t`,
`result.cost − extraGas ≤ gas` and `≤ maxMessageCallGas A`, and retained execution
gas at least `A / 64`. A successful charge and the explicit local hypothesis
`t + 1 ≤ memoryCost + extraGas` suffice for the corresponding private
`post.phi + result.subCall + 1 ≤ meter.phi` consequence; nonincrease needs
`t ≤ memoryCost + extraGas`. No global price/WF relation replaces those premises.
Real CALL prepays overhead/memory, may spill for state charges, then passes
current ZERO twice to the calculator. Those earlier payments, child entry/return,
failed preflight/refunds, settlement and whole continuing-iteration G2 must be
composed separately. No local arithmetic theorem closes those obligations.

The charge, three rollback, two refund, four local transfer and signed-addition/scalar equations are supplied
above. The following list retains the remaining G1 and composition obligations:
- Q64's supplied call equation gives the discharged private local affordability/
  forwarding consequences above. Actual caller derivation and paid-stipend/child
  return accounting remain G2 obligations; the pure helper alone proves no whole
  CALL-family progress or settlement result.
- **`L-SETTLE`** [C]: after `restoreStateGas` then `forfeitRemainingGas` (halt) or `restoreStateGas` alone (revert), `ChildSettled child true` holds: `stateGasSpilled = 0 ∧ refundCounter = 0 ∧ stateGasLeft = stateGasBaseline`; every non-top frame has `stateGasCommittedSpill = 0` (only `createEvm` commits). These discharge `incorporateChild`'s preconditions.
- **`L-INC`** [C]: `(incorporateChild p c failed h).gasMeter.phi = p.gasMeter.phi + c.gasMeter.phi` (the repay step preserves Φ). Together with G2's "child returns potential ≤ potential granted" this gives the cross-frame bound.
- **`L-WARM-MONO`** [C]: if `p.accessedAddresses ⊆ c.accessedAddresses` then the union is `c.accessedAddresses` (same for slots). [F] the implementation may assign.
- Settlement [C]: Q66's supplied API and five discharged laws above use exactly the three returned/state/floor bounds and a validated U256 refund. Their actual caller derivation, including the earlier checked signed-counter conversion and unchanged Runner Nat observation bridge (§3), remains unimplemented; R-EXC-2/O13 keep their existing owners.
- Transaction-level conservation [C, statement to be found]: an equation relating `txGas`, the returned `gasLeft + stateGasLeft`, `txStateGasUsed` and the gas charged; needed by `EthBlock` accounting proofs.

### Supplied jump-destination lookup equations

`Jumpdest.lean` discharges exactly these three ordinary public equations, on every
finite Base.Bytes code and every Nat index. The raw PUSH width is local to the
cons equation, not an additional API.

```lean
validJumpDestinations_contains_empty (i : Nat) :
  (validJumpDestinations Bytes.empty).contains i = false

validJumpDestinations_contains_cons (b : UInt8) (xs : List UInt8) (i : Nat) :
  let k := if 96 ≤ b.toNat ∧ b.toNat ≤ 127 then b.toNat - 95 else 0
  (validJumpDestinations (Bytes.ofList (b :: xs))).contains i =
    (if i = 0 then b == (0x5b : UInt8) else if i ≤ k then false
     else (validJumpDestinations (Bytes.ofList (xs.drop k))).contains (i - (k + 1)))

validJumpDestinations_contains_of_size_le (c : Bytes) (i : Nat)
  (hi : c.size ≤ i) :
  (validJumpDestinations c).contains i = false
```

The private ordinary packed/reference theorem covers all code and indices through
actual Base.Bytes public bridges, size-derived sufficient structural fuel, private
bit-update/frame/shape/padding facts and finite support. The reference's true-index
set is the mathematical observation of EELS's finite set; no allocated List Nat or
public reference operation is needed. Private public-law consumers derive true-hit
byte identity and bounds without unfolding provider or scanner storage. The
bounded original comparison in §3/§4 is additional source evidence, not the ordinary
all-input refinement proof. [C] A future code-hash cache separately needs cache/code
consistency (Nipkow Ch. 18 invariant).

**Transfer log** [C]: `emitTransferLog f topic s r 0 = f`; otherwise, for `f' := emitTransferLog f topic s r a`, `α f'.logs = α f.logs ++ [Log(SYSTEM_ADDRESS, [topic, pad32 s, pad32 r], be32 a)]`.

### Informal correctness argument

**Claim.** Stack, memory, logs, jump destinations and gas operations refine their public observers and preserve the frame invariants required by stepping and settlement.

**Premises.** EthBase and EthState laws; local proof arguments for commit/entry restore and caller premises for the remaining meter operations (none for the supplied charge kernel, refund/repay or ordinary restore); memory expansion aligned to words; exact Amsterdam limits/costs supplied consistently by VmConfig; explicitly checked casts and window bounds.

**Argument.** Reverse-array observation proves stack push/pop/peek equations by the final-element cases. Memory refinement uses the full M4–M6 model equations for exact zero extension and admitted window effects, with empty reads/writes handled before offset conversion. M7 is actual empty-write identity; M8 derives the result-read witnesses for M9/M10 from the original local window proofs. Immutable read values support read-then-write overlap clients. Calculate expansion and charge its cost before allocation. The supplied ordinary LogRope refinement gives toList(append a b) = toList a ++ toList b; chronological observation is invariant under association and empty identities. Public raw constructors still expose distinct tree shapes. Jump scanning induction advances by one plus the PUSH immediate length, marking only instruction bytes. Gas proofs split each operation's branch and account for all six meter fields. State-gas charges, commit, restores, refunds and repayment merely redistribute counted potential or affect the separate reservoir; execution charges decrease Φ. Child returns are explicit additions, so this local argument does not prove whole-call progress. VmWorld contains one TxState, avoiding independent observation or ancestor-cursor copies.

**Open obligations.** Prove meter premises at every caller, checked refund conversion, exact arithmetic failure cases and the compiled memory/stack cost assumptions. Memory representation replacement uses observer equations; amortised linear-container bounds must not be applied to snapshot-reachable values.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthState`
- **Used by:** `EthVmInstructions` (handlers), `EthPrecompiles` (charge execution gas through `chargeGas`; the shared precompile table type is here), transitively `EthVmRunner`, `EthBlock` (settlement, allocation, blob gas, capacity, `SYSTEM_ADDRESS`), `EthFork` (defines the Amsterdam values of `GasCosts`, `StateGasCosts` and `VmLimits`, with `vmLimits_depth := rfl`).
- **Seams:** consumes the `EthState` transaction-state API and `WitnessError`; provides the frame types, `VmM m`, `VmFault`, `STACK_DEPTH_LIMIT`, the precompile calling convention, the meter and its Φ laws. Cross-module invariants relied on: every `Frame` a handler receives satisfies `size stack ≤ 1024`, `size memory % 32 = 0`, and the meter well-formedness `Wf`; guaranteed: every operation here preserves them.

## 9. Open decisions

- **D1** (U256 representation): stack words and all handler-visible arithmetic go through `U256` observers; nothing here may depend on the stored field.
- **D11** (memory type): `ByteArray` initially; the laws in §7 are the replacement contract (exercise 1).
- **D13** (call-frame structure): determines whether `Frame` is suspended in the Lean call stack (recursive runner) or in an explicit continuation; `FrameCtx.depth_le` supports both.
- **D17**: accepted; this module is the shared vocabulary of the split.
- **D22/D23/D24**: warm sets are persistent trees; observations (`world.tx.obs`) are linear and outside snapshots; logs are a rope.
- **D25**: model-based contracts as above.
- **D5** (broad scope, monad-parametric): `VmWorld m`, `VmM m` and `PrecompileFn m`; `TRANSFER_TOPIC` is `HashConsts.transferTopic`. This module never needs the `KeccakQuery` class.
- NEW-VM-1 (VM-internal Python faults): resolved by D14 (accepted), CONTRACT O13 and DECISIONS B14 (Q23); the constructors are those of R-EXC-2, frozen once this module's failure-ledger entries close.
- NEW-VM-3: resolved by D27 (DECISIONS Q25).
- NEW-VM-4: resolved by DECISIONS B8 (Q26).
- **F11** (open): how the runner produces `ChildSettled` (EthVmRunner §9).
- **Q61**: `txStateGasUsed` uses the local baseline-to-grant proof in §5/§7; DECISIONS owns the disposition. Caller premise reachability remains an obligation.
- **Q62**: DECISIONS owns the Memory disposition; §5/§7 own the exact supplied API/ten-law contract. BufferRead remains independent; memory pricing’s policy-threading contract is owned separately by Q63.
- **Q63**: DECISIONS owns the pricing-policy disposition; §5/§7 own the two supplied VmConfig-first signatures and ten discharged ordinary laws, including local relevant-price congruence. Caller/frame/target config coherence and general source/host agreement remain separate from the bounded typed comparison in §3.

- **Q64**: DECISIONS owns the approved call/init policy/default disposition;
  §5/§7 own the supplied two-helper/result/six-law contract. Private public-law
  clients and bounded typed comparisons are supplied in §3. Caller payments,
  general source/default agreement, configuration/target coherence, settlement
  and G2 remain separate obligations.

- **Q65, Q66**: DECISIONS owns the transaction allocation/settlement dispositions;
  §5/§7 own the supplied allocation/four-law and settlement/five-law contracts.
  §3/§4 own their local proofs, private public-law clients and controls; both actual
  caller bridges remain open. Allocation policy matching and unsigned refund
  validation are separate caller obligations, not global meter invariants.

## 10. Gaps

- **Allocation and settlement are locally supplied (Q65, Q66):**
  §3/§5/§7 own the raw allocation carrier, exact two-bound helper, four discharged
  laws, nine private public-law client groups and complete finite controls. Q66 supplies
  its raw carrier/exact three-bound helper, five discharged laws, private public-law
  clients and 50 complete target groups (§3). Actual admission/allocation
  cap consistency, system-call separation, returned/state/floor derivation,
  validated unsigned refund/range reconstruction at the unchanged Runner Nat
  boundary, checked-failure precedence, fees/providers/conservation, compiled
  resources, G1/G2–G7, F11/B11 and VM/guest/EEST/readiness remain open. No finite
  source observation supplies a universal theorem or these actual caller premises.

- **Raw block-gas counter data is supplied:** §3/§5/§7 own the exact
  Nat/Nat/U64 carrier, two ordinary ext/eta laws, private public-only clients
  and ten complete-value guards. Full EthBlock.BlockOutput construction,
  block/counter coherence, capacity arithmetic and checked failures/precedence,
  actual settlement integration and counter consumers remain unimplemented here;
  the pure allocation and settlement helpers are supplied separately above. This raw data supplies no resource, G1–G7, whole VM/guest/EEST or readiness result.

- **Chronological Log/LogRope is supplied locally:** §3/§5/§7 own the complete raw
  Log, existing public rope constructors, two operations and six discharged ordinary
  laws, with private total workstack/all-tree reference refinement. Public-only
  clients and all 16+6 complete controls cover full fields/order/duplicates and model
  selection. The finite 102 native C3 measurements in §4 cover expanded traversal,
  deep/skew/shared shapes and explicit last-owner cleanup with disclosed sharing,
  IO instrumentation and metric limits. Real LOG/transfer producer ordering,
  HashConsts and topic restrictions, settled child/frame incorporation, top-level
  execution/output/receipt/bloom integration, typed source/host generalization,
  actual composed ownership, exact allocated bytes/live space and universal
  stack/resource bounds remain open. No C1/C4, G1–G7, whole VM/guest/EEST or
  readiness gate is closed by this local slice.

- **Call/init-code pricing (Q64) is locally supplied:** §3/§5/§7 own both
  VmConfig-first helpers, the two-Nat MessageCallGas result, six discharged
  ordinary laws and private public-law charge/error/affordability/read-set/init
  rounding and explicitly financed local-potential clients. Thirty-two complete
  literal controls and six complete charge witnesses, plus the dated external
  interpreted/native and twenty-five original comparisons scoped in §3, are local evidence. General
  source/default/host agreement, actual caller/config/target coherence, earlier
  CALL payments/state spill, preflight/child return/settlement, compiled/resource
  and whole G1/G2–G7/VM/guest gates remain open. The supplied scalar maximum and
  existing guards are reused; no global invariant or hidden default follows.

- **Jump-destination analysis is supplied locally:** §3/§5/§7 own the abstract immutable packed map, existing two operations and three discharged ordinary lookup equations, with all-code/all-Nat private reference refinement. Public-only clients, the unchanged 32 handwritten controls and the dated external 940-case comparisons scoped in §3/§4 are local evidence. Code/map provenance, a future cache's authenticity/coherence, actual JUMP/JUMPI operands/gas/error ordering, typed source/host generalization, compiled allocation/sharing/ownership, random campaigns and measured asymptotic/resource costs remain open. This closes no C1–C4, G1–G7, whole VM/guest/EEST or readiness gate.

- **Raw VM configuration data is supplied:** §3/§5/§7 own the exact four-Nat StateGasCosts, three-Nat VmLimits and complete three-record-field VmConfig, six discharged ordinary ext/eta laws and generic public-only constructor/law/selected-charge clients. No state amount observations, values/defaults/instances/factory, global WF or supported-policy claim is supplied. The separate state amount-provider choice, F8 specialization, actual Fork/consumer/frame/target consistency remain open; Q63 pricing is supplied separately.

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **Raw GasCosts data is supplied:** §3/§5/§7 own the exact class-plus-seven-BLS 144-field boundary, source-shaped types and two discharged ordinary ext/eta laws. Universal constructor/public-law and selected-cost charge clients supply the local data seam; no pinned values, defaults, instances, factory or supported-policy predicate is supplied.
- **B8 pricing and specialization remain partial:** MODEXP floor500/formula classification, module-derived maximum placement/checked-U64 range, separate StateGasCosts representation, BLS executable index/denominator support, EthFork literal/alias/derived-field factory and config/consumer coherence remain open. They block the corresponding claims, not the supplied raw record. No extra field, unsupported-config completion or Memory-pricing policy choice follows.
- **Bounded Stack is partially supplied:** §3/§7 own the private bounded carrier, six operations and eight ordinary laws. Swap all-input behavior, actual handler/frame ownership and compiled allocation/C1–C4 checks remain open; no whole VM or guest gate follows.
- **Scalar immediate decoders are supplied:** §3/§7 own the two existing UInt8 APIs and eight discharged ordinary laws. Complete 512-result guards, interpreted target/source frames and public-only clients establish the local slice. Actual handler/depth/gas/PC ordering, compiled costs, resource and guest gates remain open.
- **Padded buffer read is supplied:** §3/§7 own the standalone existing Bytes/U256 adapter and exactly three discharged ordinary laws. Complete-byte guards, public-only clients and strict frame controls are local evidence. Successful Python correspondence retains its explicit runtime/dependency/width/allocation premises; compiled costs, actual caller reachability and all Memory/R1/C1–C4/guest gates remain open.
- **G1 is partially discharged:** §3/§7 own the supplied complete meter, nominal exceptional-halt carrier, read-only check and two checked charges with ten all-raw-meter laws, plus commit/ordinary restore/entry restore with eight ordinary laws on their full local proof domains and refund/repay with seven ordinary all-raw-meter laws, plus four local transfer operations with eight ordinary laws (forfeit only on pending-spill-zero), and signed refund addition/scalar maximum with four unconditional ordinary laws. Caller premise reachability, remaining meter operations, actual settlement integration and whole-transaction conservation remain unimplemented/unproved. The Q61 `txStateGasUsed` observer and its single §7 equation are discharged; callers must establish the local baseline-to-grant proof. This closes no overall G1 or G2–G7 gate.
- **Cross-frame progress (G2) is unproved.** The bound "a child returns potential ≤ the potential granted" needs an induction over the runner and uses `L-SETTLE`, `L-INC` and the stipend accounting; its exact statement with 2-D gas is not yet written.
- **Transaction-level gas conservation** has no statement yet; `EthBlock` needs one for receipts and block accounting.
- **Top-level unsigned refund conversion remains a caller obligation.** Both `U256(gas_meter.refund_counter)` sites (`interpreter.py:285,318`) require `0 ≤ refundCounter < 2^256` and retain their source order (§3; Q66). The preparation-zero argument is recorded in EthVmRunner R-TOP-2; this guidance implements no actual caller proof and removes no checked cast. Normal-return lower/upper bounds remain unresolved: the sketched non-negativity argument does not itself prove the unsigned upper bound. The existing proof-or-`VmFault.u256Overflow .refundCounter` obligation (R-EXC-2/O13) stays at the applicable original point. Successful projection into Runner's Nat field must retain the range for later validated U256 reconstruction, without moving failure to settlement or adding a public converter.
- **Balance overflow in `move_ether`.** A recipient balance above `2^256 − 1` raises `OverflowError` in EELS (`state_tracker.py:663`, and `create_ether` at `:687`). The witness authenticates the state against a parent root the guest does not itself trust, so large balances are not excluded by the input format. It is argued reachable from the pinned source (O13); no fixture or probe witnesses it. The named constructor is owned by `EthState`'s `moveEther` and surfaces here as `VmFault.state`.
- **O13 enumeration still open.** The VM-internal Python faults are classified (CONTRACT O13, D14): BLOCKHASH's `IndexError` is fixture-witnessed, and the BLOBBASEFEE and balance overflows are argued reachable. The `VmFault` constructor list is frozen only once this module's failure-ledger entries close (DECISIONS B14).
- **`calculate_excess_blob_gas`** takes `Header | PreviousForkHeader` and uses `isinstance`; the Lean version takes three numbers, and `EthBlock` must reproduce the "fields absent → zeros" default [I: both header types at the pin carry the fields, so the default may be dead].
- **`calculate_blob_gas_price` on huge `excess_blob_gas`** runs `taylor_exponential` for a number of iterations roughly proportional to `excess_blob_gas / BLOB_BASE_FEE_UPDATE_FRACTION` (DISC-002); for adversarial parent headers this is a host-time problem (DISC-002), and `U256(price)` in BLOBBASEFEE is argued reachable as an overflow (O13, `instructions/environment.py:607`). Termination and cost belong to EthBase; the envelope question is open.
- **Local Memory (Q62) is supplied:** §3/§5/§7 own the private aligned carrier, six APIs and ten discharged ordinary laws, including complete write effects, immutable snapshots and actual empty-write identity. Public-only clients derive post-write read proofs from preserved size and the original local window proof. Actual caller alignment/window derivation, charge/allocation/return-buffer/static-check ordering, linear ownership, compiled C1–C4, R1, G1–G7 and guest gates remain open. No invalid-window completion, runtime error or global frame invariant follows; bufferRead remains independent.
- **Memory pricing (Q63) is locally supplied:** §3/§5/§7 own both VmConfig-first helpers, ten discharged ordinary laws, private public-only clients and forty-two full interpreted/native controls with twenty-four authenticated typed original comparisons. Clients derive actual Memory expansion/admitted-window/preservation facts through public laws; real handler payload/window derivation, frame/target config coherence, charge/allocation/check ordering, L-MEM-BOUND, compiled C1–C4, general source-host/resource and whole VM/guest gates remain open. Raw unaligned source controls remain source-only and unrun; no huge returned extent is allocated.
- **Meter well-formedness `Wf`** is not yet characterised. `state_gas_left ≤ state_gas_baseline` is **not** an invariant (a cross-frame refund can push the reservoir above the baseline), so the right invariant is still to be found; only the EELS asserts are known facts.
- **Envelope limits** for `Nat` gas (a `u64` fast path) are not specified; D1 and a future `Envelope` record decide.
