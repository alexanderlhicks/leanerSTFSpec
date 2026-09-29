# `EthVmCore`: EVM frame, environments, stack, memory, 2-D gas meter, jumpdest analysis

*Status: informal specification, draft. Date: 2026-09-29. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F1, F2, F3, F8, F9, F11, F12 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D1, D5, D11, D13, D14, D17, D22, D23, D24, D25, D27 · questions: B7/Q24, B8/Q1/Q26/Q43, B14/Q23, F11.*

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
- **R-LOG-1** `emitTransferLog` (`__init__.py:253–289`, EIP-7708) must be a no-op for amount 0, and otherwise append `Log(SYSTEM_ADDRESS, [TRANSFER_TOPIC, pad32 sender, pad32 recipient], be32 amount)` to the frame's logs. `SYSTEM_ADDRESS = 0xff…fe`. `TRANSFER_TOPIC = keccak256("Transfer(address,address,uint256)")` (`:40`) is a keccak-derived constant, so under D5 it is not a literal here: it is the `transferTopic` field of `HashConsts` (EthBase), queried once per block by `HashConsts.query` (EthHash) and read from `world.tx.block.consts`. The caller passes it to `emitTransferLog`. At `m := Id` its value is `0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef` [V: computed with the pinned EELS `keccak256`]; the check that `HashConsts.query` at `Id` equals this literal belongs to a module that can see `EthHash`.

### 2.3 Stack

- **R-STK-1** The stack holds at most 1024 words. `pop` on an empty stack must fail with `StackUnderflowError` (`stack.py:109–110`); `push` on a full stack with `StackOverflowError` (`:128–129`). Both are exceptional halts.
- **R-STK-2** `decode_single x` (`stack.py:25–53`, EIP-8024) must fail with `InvalidParameter` for `91 ≤ x ≤ 127` and otherwise return `(x + 145) mod 256`, which lies in `17…235`. `decode_pair x` (`:56–91`) must fail for `82 ≤ x ≤ 127`; otherwise with `k = x xor 143`, `(q, r) = divmod k 16`, return `(q+1, r+1)` if `q < r` else `(r+1, 29−q)`. The forbidden ranges contain `0x5B` (JUMPDEST) and `0x60–0x7F` (PUSH1–PUSH32), so jumpdest analysis need not skip these immediates [V: `runtime.py` does not].

### 2.4 Memory

- **R-MEM-1** Memory is a byte sequence whose length is always a multiple of 32 [I: every expansion adds `ceil32(end) − ceil32(size)`, `gas.py:801–811`]. `memory_write m start v` (`memory.py:20–36`) overwrites `[start, start+|v|)`; callers guarantee the window lies inside memory after expansion; an **empty** write at any `start`, even beyond the end, must be a no-op (Python slice assignment `m[s:s] = b""`). `memory_read_bytes` (`:39–60`) returns the window; an empty read at any start returns empty. `buffer_read buf start size` (`:63–83`) returns `buf[start, start+size)` right-padded with zeros to `size`, for any `start` (including `start ≥ |buf|` and `start ≥ 2^64`).
- **R-MEM-2** Expansion must be priced **before** it is performed: no handler may allocate memory before the corresponding `charge_gas` succeeds (every handler follows `calculate_gas_extend_memory` → `charge_gas` → `memory += zeros`). With `Nat` gas this bounds the allocation by the available gas.

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
| `tx_state_gas_used m R` (:570) | precondition `baseline ≤ R`; returns the `Int` `R − state_gas_left + spilled + committed` (may be negative) |
| `credit_state_gas_refund m a` (:606) | `x = min a spilled`; `gas_left += x`, `spilled −= x`, reservoir `+= a − x` (LIFO credit) |
| `repay_state_gas_spill` (:631) | `y = min reservoir spilled`; `gas_left += y`, reservoir `−= y`, `spilled −= y`; afterwards `reservoir = 0 ∨ spilled = 0` (a theorem, not a check) |
| `forfeit_remaining_gas` (:662) | precondition `spilled = 0`; `gas_left := 0` |
| `withhold_create_gas` (:678) | `g = max_message_call_gas gas_left`; `gas_left −= g`; returns `g` |
| `drain_state_gas_reservoir` (:701) | returns the reservoir and sets it to 0 (no 63/64 rule for state gas) |
| `restore_child_gas m g R` (:725) | `gas_left += g`, reservoir `+= R` (child never entered) |
| `calculate_memory_gas_cost s` (:749) | `w = ceil32(s)/32`; `3w + ⌊w²/512⌋`. The EELS `try/except ValueError` (:770–773) is dead code (`ExecutionGas` is a `NewType` of the unbounded `Uint`, so the call is the identity) [V] |
| `calculate_gas_extend_memory m ws` (:776) | fold over windows `(start, size)` in order, skipping `size = 0` **regardless of `start`**; with running `cur` (initially `\|m\|`), if `ceil32(start+size) > ceil32(cur)`, add the difference to `expand_by` and `C(after) − C(before)` to `cost`, then `cur := after` |
| `calculate_message_call_gas v g L mem extra stipend` (:816) | `stipend := 0` if `v = 0`; if `L < extra + mem` return `(g + extra, g + stipend)` (the caller then fails its charge); else `g' = min g (max_message_call_gas (L − mem − extra))`, return `(g' + extra, g' + stipend)` |
| `max_message_call_gas g` (:861) | `g − ⌊g/64⌋` (EIP-150) |
| `init_code_cost n` (:879) | `2 · ceil32(n)/32` (EIP-3860) |
| `calculate_excess_blob_gas` (:901) | from the parent's `(excess_blob_gas, blob_gas_used, base_fee_per_gas)` (zeros when absent): 0 if `excess + used < 14·2^17`; if `2^13 · base_fee > 2^17 · blob_price(excess)` return `excess + used · 7 / 21`; else `excess + used − 14·2^17` |
| `calculate_total_blob_gas` (:951) | `2^17 · \|blob_versioned_hashes\|` for blob transactions, else 0 |
| `calculate_blob_gas_price e` (:972) | `taylor_exponential(1, e, 11684671)` (`utils/numeric.py`, EthBase) |
| `calculate_data_fee` (:994) | total blob gas × blob gas price |
| `check_max_fee_per_blob_gas` (:1016) | no check without blobs; else fail iff `max_fee_per_blob_gas < price` |
| `check_block_gas_capacity` (:1053) | fail iff `min(2^24, tx_gas) > limit − block_gas_used`, or `tx_gas > limit − block_state_gas_used`, or `tx_blob_gas > 21·2^17 − blob_gas_used`, in that order |
| `allocate_evm_gas tx_gas intr` (:1120) | `evm = tx_gas − intr.execution`; `exec = min(2^24 − intr.execution, evm)`; reservoir `= evm − exec`. Precondition: intrinsic affordable and `intr.execution ≤ 2^24` (validated in `EthBlock`) |
| `settle_transaction_gas` (:1178) | `pre = tx_gas − gas_left − state_gas_left`; `refund = min(pre/5, refund_counter)`; `gas_used = max(pre − refund, floor)`; `state_used = max 0 state_gas_used`; `execution_gas_used = max(pre − state_used, floor)` (EIP-7778: pre-refund); `gas_left_out = tx_gas − gas_used` |

- **R-GAS-1** Every EELS `assert` above is a precondition of the Lean operation, discharged by callers (§7). The Lean operations must not contain fallible checks that EELS does not have.
- **R-GAS-2** Gas amounts are unbounded `Nat`; charging is checked; no wrapping, no saturating subtraction that hides a failed check.
- **R-GAS-3** `GasCosts` and `StateGasCosts` (`gas.py:48–259`) are fields of a gas-policy record, not literals inside handlers (ARCHITECTURE §8). The record also holds every precompile pricing dependency that EELS keeps outside `GasCosts` (DECISIONS B8, F9; §5). This module defines the record types; the Amsterdam values live in `EthFork`. Derived constants must be computed from their components as in EELS: `CALL_VALUE = ACCOUNT_WRITE + CALL_STIPEND = 11300`, `CREATE_ACCESS = 12000`, `REFUND_STORAGE_CLEAR = (10000 + 2100)·4800/5000 = 11616`, `STORAGE_SET = 64·1530 = 97920`, `NEW_ACCOUNT = 120·1530 = 183600`, `AUTH_BASE = 23·1530 = 35190`, `EXECUTION_PER_AUTH_BASE_COST = 101·16 + 3000 + 3000 + 2·100 = 7816`, `TX_ACCESS_LIST_ADDRESS = 2900`, `TX_ACCESS_LIST_STORAGE_KEY = 2000`, `MAX_BLOB_GAS_PER_BLOCK = 21·2^17`.

### 2.6 Exceptions

- **R-EXC-1** `ExceptionalHalt` (`exceptions.py:17`) has the subclasses `StackUnderflowError`, `StackOverflowError`, `OutOfGasError`, `InvalidOpcode(code)`, `InvalidJumpDestError`, `StackDepthLimitError`, `WriteInStaticContext`, `OutOfBoundsRead`, `InvalidParameter`, `InvalidContractPrefix`, `AddressCollision`, `KZGProofError`; precompiles also raise bare `ExceptionalHalt` (`precompiled_contracts/modexp.py:34, 38, 42`). `Revert` (`:24`) is **not** an exceptional halt. The Lean type must keep one constructor per class (for traces and receipts' diagnostics) although every exceptional halt has the same effect (O8): spill restored, remaining execution gas forfeited, output empty.
- **R-EXC-2** Non-EVM failures that EELS raises from inside the VM as ordinary Python exceptions must be kept **separate** from `ExceptionalHalt` in a `VmFault` type, because the guest maps them to a failure output rather than to a halted frame (`stateless.py:303` catches `Exception`): `witness` (missing trie/code data, O4, from `EthState`), `ancestorHashUnavailable` (BLOCKHASH beyond the witness headers, a Python `IndexError`, see EthVmInstructions), `u256Overflow` (Python `OverflowError` from `ethereum_types`: a negative top-level refund in `U256(refund_counter)` (`interpreter.py:318`; the sibling cast at `:285` is proved unreachable, because the refund counter is 0 there), or `U256(calculate_blob_gas_price(…))` in BLOBBASEFEE (`instructions/environment.py:607`)). A recipient balance exceeding 2^256−1 in `move_ether` is also an `OverflowError`; it is raised inside `EthState` and arrives as `state`. The `U256(...)` casts in NUMBER, GASLIMIT and BASEFEE cannot overflow, because the SSZ payload field widths (`uint64`, `uint64`, `uint256`) rule it out, so they have no constructor. These faults are CONTRACT **O13** members (D14): the existing invalid output, one named constructor each, never a catch-all. BLOCKHASH's `IndexError` (`instructions/block.py:58`) is witnessed by the fixture `validation_headers_missing_oldest_blockhash_ancestor`; the reachability of the others is argued in the failure ledger (maintained outside this repository). `InternalError` (O11) is a different type again (EthVmRunner).

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
| `forks/amsterdam/vm/stack.py::*` | 25–131 | `Stack.pop`, `Stack.push`, `decodeSingle`, `decodePair` | |
| `forks/amsterdam/vm/runtime.py::*` | 22 | `validJumpDestinations`, `JumpdestMap` | byte-level; no `Ops` import |
| `forks/amsterdam/vm/interpreter.py::STACK_DEPTH_LIMIT` | 84 | `abbrev STACK_DEPTH_LIMIT : Nat := 1024`; field `VmLimits.stackDepthLimit` | declared here because `FrameCtx` and the CALL/CREATE preflight need it and neither may import the runner. A literal, because the depth proofs and indexed types need a kernel-reducible value (F8); `EthFork` sets the field to it, with `vmLimits_depth := rfl` |
| `forks/amsterdam/vm/interpreter.py::MAX_CODE_SIZE` | 85 | field `VmLimits.maxCodeSize` (Amsterdam value `0x10000`, in `EthFork`) | EIP-7954; used by the runner's code deposit |
| `forks/amsterdam/vm/interpreter.py::MAX_INIT_CODE_SIZE` | 86 | field `VmLimits.maxInitCodeSize` (Amsterdam value `2 · 0x10000`, in `EthFork`) | CREATE/CREATE2 and `EthBlock` transaction validation |

**External semantics.** From `ethereum_types` 0.4.1 (`reference.toml`): `Uint` (unbounded, subtraction below zero raises `OverflowError`), `U256`/`U64`/`U8` (constructor, `+` and `from_signed` raise `OverflowError` out of range; `from_be_bytes` raises `ValueError` for more than 32 bytes; `wrapping_*` wrap), `Bytes`, `Bytes32`, `ulen`. Only the `OverflowError` cases listed in R-EXC-2 are behaviourally reachable from this module's callers; the Lean `Nat`/`U256` API (EthBase) must make each one explicit rather than wrap. `ceil32` and `taylor_exponential` come from `utils/numeric.py` (EthBase). `left_pad_zero_bytes` from `utils/byte.py`.

## 4. Tests

- **EEST fixture areas** (`STFSpec/informal/eest-fixture-index.txt`, `blockchain_tests/for_amsterdam/…`; the `_engine` copies carry no guest records, GAPS-CROSSCUTTING X5): gas meter and state gas: `amsterdam/eip8037_state_creation_gas_cost_increase` (268), `amsterdam/eip8038_state_access_gas_cost_increase` (88), `amsterdam/eip7778_block_gas_accounting_without_refunds` (9), `amsterdam/eip2780_reduce_intrinsic_tx_gas` (59), `amsterdam/eip7976_increase_calldata_floor_cost`, `osaka/eip7825_transaction_gas_limit_cap`; memory: `ported_static/stMemoryTest` (72), `stMemoryStressTest` (36), `stMemExpandingEIP150Calls`, `cancun/eip5656_mcopy`; call gas: `tangerine_whistle/eip150_operation_gas_costs`, `ported_static/stEIP150Specific`, `stEIP150singleCodeGasPrices`; stack limits: `ported_static/stStackTests`, `amsterdam/eip8024_dupn_swapn_exchange` (66); refunds: `ported_static/stRefundTest`, `istanbul/eip2200_net_gas_metering`; transfer logs: `amsterdam/eip7708_eth_transfer_logs` (38); blob gas: `cancun/eip4844_blobs`, `osaka/eip7918_blob_reserve_price`, `cancun/eip7516_blobgasfee`.
- **EELS unit tests:** none exercise `vm/` directly at e1a316a0 [V: `tests/json_loader/*` touches only tracing (`test_trace.py`)]. The EEST sources under `tests/amsterdam/eip8037_*` (`test_state_gas_reservoir.py`, `test_state_gas_cross_frame_refund.py`, `test_state_gas_ordering.py`) and `tests/amsterdam/eip8024_*` (`test_eip_vectors.py`) are the best specification of the meter and decoders.
- **`core` `#guard` cases** (a `#guard` evaluates only once every leaf it reaches is implemented, F16):
  - `decodeSingle`: all 256 inputs (219 valid, results exactly `17…235`, bijective on the valid range) [V: run against EELS]; `decodePair`: all 256 inputs (210 valid, `1 ≤ n ≤ 14`, `n < m ≤ 30 − n`, injective) [V: run].
  - Memory cost: `C 0 = 0`, `C 32 = 3`, `C (32·724) = 3·724 + 724²/512`; `extendMemory` on `[(2^256−1, 0)]` gives `(0, 0)`; `[(0,32),(0,64)]` equals `[(0,64)]`; a second window below the first adds nothing.
  - Meter: charge exactly `gas_left` (succeeds, leaves 0); charge `gas_left + 1` (fails, meter unchanged); state charge split across reservoir and `gas_left`; credit when `spilled < a` (remainder to reservoir); repay; restore after commit leaves committed spill charged; `restoreToEntry` refills both spills; negative `refund_counter` after one clear-reversal.
  - `maxMessageCallGas 64 = 63`, `63 = 63`, `0 = 0`; `calculateMessageCallGas` below `extra + mem`.
  - `settleTransactionGas`: refund capped at one fifth; floor binding both dimensions; negative `state_gas_used` clamped to 0.
  - Jumpdest: `0x5B` inside PUSH data excluded; PUSH32 truncated at end of code; `0x5B` after `0xE6` (DUPN) **included** (EELS gives `{1, 4}` for `E6 5B 60 5B 5B` [V: run]).
  - `(HashConsts.query (m := Id)).transferTopic = keccak256 "Transfer(address,address,uint256)" = 0xddf252ad…b3ef` (owned by EthHash §7, `HashConsts.query (m := Id) = HashConsts.literals`).
- **Property/differential:** random meter operation sequences against a direct `Nat` model of the six fields, checking Φ laws (§7); random window lists for `extendMemory` against the closed form; `validJumpDestinations` against a byte-by-byte reference over random code, including a 24 KiB and 64 KiB input for linear-time behaviour.

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

-- Memory (public; representation internal, D11)
structure Memory
def Memory.toBytes : Memory → List UInt8                 -- model
def Memory.size : Memory → Nat
def Memory.expand : Memory → Nat → Memory                -- append n zero bytes
def Memory.readBytes : Memory → Nat → Nat → Bytes         -- (start size); requires window inside or size = 0
def Memory.write : Memory → Nat → Bytes → Memory          -- empty write is the identity
def bufferRead : Bytes → U256 → U256 → Bytes              -- zero-padded, any start
structure ExtendMemory where cost : Nat; expandBy : Nat
def calculateGasExtendMemory : Memory → List (U256 × U256) → ExtendMemory
def calculateMemoryGasCost : Nat → Nat

-- Gas policy and meter (public)
structure GasCosts where …          -- one field per `GasCosts` constant (gas.py:72–259), then the
  -- precompile pricing dependencies EELS keeps elsewhere (B8, F9; values in EthFork):
  blsPairingBase blsPairingPerPair : Nat          -- 37700, 32600 (bls12_381_pairing.py:46)
  blsG1KDiscount blsG2KDiscount : Array Nat       -- 128 entries each (bls12_381/__init__.py:37, 168)
  blsG1MaxDiscount blsG2MaxDiscount blsMultiplier : Nat   -- 519, 524, 1000 (:299–301)
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
def txStateGasUsed (m : GasMeter) (R : Nat) : Int
def creditStateGasRefund : GasMeter → Nat → GasMeter
def repayStateGasSpill : GasMeter → GasMeter
def forfeitRemainingGas (m : GasMeter) (h : m.stateGasSpilled = 0) : GasMeter
def withholdCreateGas : GasMeter → Nat × GasMeter
def drainStateGasReservoir : GasMeter → Nat × GasMeter
def restoreChildGas : GasMeter → Nat → Nat → GasMeter
def addRefund : GasMeter → Int → GasMeter                                 -- `refund_counter += k`
structure MessageCallGas where cost subCall : Nat
def calculateMessageCallGas (value : U256) (gas gasLeft memoryCost extraGas : Nat) (stipend : Nat := costs.callStipend) : MessageCallGas
def maxMessageCallGas : Nat → Nat
def initCodeCost : Nat → Nat
-- transaction/block level (public; consumed by EthBlock)
def calculateExcessBlobGas (parentExcess parentUsed : U64) (parentBaseFee : Nat)
    : Except BlobGasArithmeticError U64  -- checked intermediates, in EELS order
def calculateTotalBlobGas (numBlobs : Nat) : Except BlobGasArithmeticError U64
def calculateBlobGasPrice : U64 → Nat
def calculateDataFee (excessBlobGas : U64) (numBlobs : Nat) : Nat
def checkMaxFeePerBlobGas (numBlobs : Nat) (maxFee : U256) (excess : U64) : Except BlobFeeError Unit
def checkBlockGasCapacity (env : BlockEnvironment) (c : BlockGasCounters) (txGas : Nat) (txBlobGas : U64) : Except CapacityError Unit
structure EvmGasAllocation where executionGas stateGasReservoir : Nat
def allocateEvmGas (txGas intrinsicExecution : Nat) : EvmGasAllocation
structure TransactionGasSettlement where gasUsed gasLeft executionGasUsed stateGasUsed : Nat
def settleTransactionGas (txGas calldataFloor gasLeft stateGasLeft : Nat) (refund : Nat) (stateGasUsed : Int) : TransactionGasSettlement

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
structure JumpdestMap                                     -- bitmap, internal representation
def validJumpDestinations : Bytes → JumpdestMap
def JumpdestMap.contains : JumpdestMap → Nat → Bool
```

`TxState`, `TxRevertible` and `StateError` come from `EthState`. Observations live only at `world.tx.obs`, and ancestor access only at `world.tx.block.oldestAncestorOffset`. A snapshot retains only `TxRevertible`. `Log` and `LogRope` are declared here (D27/D24). Precompile types are also declared here; the producer and runner import them. `PrecompileFn m` is monadic so that ECRECOVER's public-key hash goes through `KeccakQuery` (D5); only `EthPrecompiles` needs `[KeccakQuery m]`. `meter_law` is stated with `SatisfiesM` so that it holds for every `m`; at `m := Id` it is the plain equation, and that instance is the minimum required. It holds by construction for the normal form (EthPrecompiles §5), because the meter is fixed by `chargeGas` before the monadic body runs. `BlobGasArithmeticError`, `BlobFeeError` and `CapacityError` are local errors mapped by `EthBlock`; their complete constructor lists remain a §10 obligation. These are Lean-like signatures: declarations must be ordered before their uses in Lean.

Gas-policy-dependent helpers take `VmConfig` or the relevant cost record explicitly. Opcode handlers use `ctx.config`, and child contexts retain it. `BlockConfig` constructs the runner environment and this context from the same records. There are no free `costs` variables or hidden Amsterdam defaults in generic semantics. The current stack/depth proofs use the literal `STACK_DEPTH_LIMIT = 1024`; supporting a different limit requires changing those proofs and indexed types.

## 6. Data structures

| Type | Representation | Model and abstraction | Invariant | Persistence | Cost |
|---|---|---|---|---|---|
| `Stack` | `Array U256`, top at the end | `List U256`, top first; `α s = s.data.toList.reverse` | `size ≤ 1024` | linear-only (frame-owned; the suspended parent frame is never copied) | push/pop/peek/swap O(1) (amortised for push) |
| `Memory` | `ByteArray` (D11) | `List UInt8`; `α = ByteArray.toList` | `size % 32 = 0` | linear-only | expand O(n) amortised; read/write O(k); copy O(k) |
| `GasMeter` | record of `Nat`/`Int` | itself (public record) | `Wf m`: the EELS asserts that are invariants rather than preconditions; see §7 | value | O(1) per operation on `Nat`s of size < 2^64 in practice; bignum only for memory costs of huge windows |
| `LogRope` | strict immutable empty/leaf/concat tree | chronological `List Log` via `toList` | concat observes left before right; no mutable cache | immutable nodes, linear frame ownership | append O(1); flatten O(nodes + logs) via a work stack, including skew trees; discarded child logs do not enter the parent |
| `JumpdestMap` | `ByteArray` bitmap of `⌈\|code\|/8⌉` bytes | `Finset Nat` (= EELS `Set[Uint]`); `α b = {i \| bit i}` | only indices `< \|code\|` | read-only, shareable; a cache keyed by code hash is allowed outside semantic state (ARCHITECTURE §7) | build O(\|code\|); lookup O(1) |
| `AddrSet`, `SlotSet` (warm sets) | `Std.TreeSet` | finite set | ordered | **worst-case persistent**: the parent's version is retained across a child and reused if the child fails (ARCHITECTURE §5.0) | insert/member O(log n); merge on success O(1) by `L-WARM-MONO` |
| `accountsToDelete` | `Std.TreeSet Address` | finite set | — | persistent (retained parent) | union O(m log(n+m)) |
| `FrameCtx` | record; `code`, `callData` shared `ByteArray` | itself | `depth ≤ 1024` | read-only | — |

## 7. Contract and laws

**Stack** (model `List U256`, top first). [C] each with invariant preservation:
- `α (push s v) = v :: α s` when `size s < 1024`; `push s v = .error .stackOverflow` iff `size s = 1024`.
- `pop s = .ok (v, s')` iff `α s = v :: α s'`; `.error .stackUnderflow` iff `α s = []`.
- `peek? s i = (α s)[i]?`; `swap? s i j` swaps model positions `i, j` when both `< size`.
- `decodeSingle x = .ok n → 17 ≤ n ≤ 235`; injective on valid inputs; `decodePair x = .ok (n, m) → 1 ≤ n ≤ 14 ∧ n < m ∧ m ≤ 30 − n`, injective. [C]

**Memory** (model `List UInt8`). [C], used by [R] memory-opcode lemmas (exercise 1):
- `α (expand m k) = α m ++ replicate k 0`; preservation of 32-byte alignment requires `k % 32 = 0`. Window reads/writes require the in-bounds hypotheses stated in §5.
- read-after-write: `readBytes (write m s v) s |v| = v` when `s + |v| ≤ size m`; disjoint windows: `readBytes (write m s v) t k = readBytes m t k` when `[t,t+k)` ∩ `[s,s+|v|)` = ∅; `write m s [] = m` for **all** `s`; `size (write m s v) = size m` when in bounds.
- overlap (MCOPY): `write m d (readBytes m s k)` reads back as the snapshot of the source, i.e. copy is "read then write" (memmove semantics).
- `bufferRead b s k = (b.drop s).take k ++ replicate (k − …) 0`, length `k`.
- Expansion closed form: for windows `ws` with nonzero sizes, `(calculateGasExtendMemory m ws).expandBy = ceil32(max(size m, maxEnd ws)) − size m` and `cost = C(size m + expandBy) − C(size m)` [I: telescoping sum; prove].
- `L-MEM-BOUND` [T/S]: `chargeGas g (… + ext.cost) = .ok _ → ext.expandBy ≤ f(g)` for an explicit `f` (the quadratic inverse); this is what makes "no allocation before charge" a resource bound.

**Logs** [C]: `LogRope.toList (LogRope.append a b) = LogRope.toList a ++ LogRope.toList b`. Flatten maintains the emitted prefix and pending subtrees in chronological order; the total pending structural size decreases when a node is expanded. Each node and each leaf log is visited once. This proves order and the linear traversal claim without repeated prefix copying.

**Gas meter** [C] (each operation's field update is exactly the table in §2.5, stated as an equation lemma, `GasMeter.laws`). Φ laws (G1; source-checked, not yet proved, ARCHITECTURE §5.5 table):
- `chargeGas m a = .ok m' → m'.phi + a = m.phi`; `chargeGas m a = .error _ ↔ m.gasLeft < a`.
- `chargeStateGas m a = .ok m' → m'.phi = m.phi` and `m'.gasLeft ≤ m.gasLeft`; failure ↔ `m.stateGasLeft + m.gasLeft < a`.
- `(commitStateGas m h).phi = m.phi`; `(restoreStateGas m).phi = m.phi`; `(restoreStateGasToEntry m R ..).phi = m.phi`; `(creditStateGasRefund m a).phi = m.phi`; `(repayStateGasSpill m).phi = m.phi`; `(drainStateGasReservoir m).2.phi = m.phi`.
- `(forfeitRemainingGas m h).phi = m.stateGasCommittedSpill ≤ m.phi`.
- `(withholdCreateGas m) = (g, m') → m'.phi + g = m.phi ∧ g = m.gasLeft − m.gasLeft/64`.
- `(restoreChildGas m g R).phi = m.phi + g`.
- `repayStateGasSpill` post: `stateGasLeft = 0 ∨ stateGasSpilled = 0`.
- `calculateMessageCallGas v g L mem x = ⟨c, s⟩ → L ≥ mem + x → c ≤ L − mem ∧ s ≤ c − x + stipend(v)` (forwarded gas never exceeds what is charged, plus stipend): the `Ccallgas_lt_Ccall` analogue needed by G2.
- **`L-SETTLE`** [C]: after `restoreStateGas` then `forfeitRemainingGas` (halt) or `restoreStateGas` alone (revert), `ChildSettled child true` holds: `stateGasSpilled = 0 ∧ refundCounter = 0 ∧ stateGasLeft = stateGasBaseline`; every non-top frame has `stateGasCommittedSpill = 0` (only `createEvm` commits). These discharge `incorporateChild`'s preconditions.
- **`L-INC`** [C]: `(incorporateChild p c failed h).gasMeter.phi = p.gasMeter.phi + c.gasMeter.phi` (the repay step preserves Φ). Together with G2's "child returns potential ≤ potential granted" this gives the cross-frame bound.
- **`L-WARM-MONO`** [C]: if `p.accessedAddresses ⊆ c.accessedAddresses` then the union is `c.accessedAddresses` (same for slots). [F] the implementation may assign.
- Settlement [C]: `settleTransactionGas` preconditions `gasLeft + stateGasLeft ≤ txGas`, `calldataFloor ≤ txGas`, and `refund ≥ 0` (the caller converts `refundCounter : Int` with a proof or a `u256Overflow` fault, R-EXC-2); then `gasUsed ≤ txGas`, `executionGasUsed ≥ calldataFloor`.
- Transaction-level conservation [C, statement to be found]: an equation relating `txGas`, the returned `gasLeft + stateGasLeft`, `txStateGasUsed` and the gas charged; needed by `EthBlock` accounting proofs.

**Jumpdests** [C]: `(validJumpDestinations c).contains i ↔ i ∈ getValidJumpDestinations c` (the EELS set, defined as the model by structural recursion on remaining length); [C] cache consistency if a code-hash cache is added (Nipkow Ch. 18 invariant).

**Transfer log** [C]: `emitTransferLog f s r 0 = f`; otherwise `α f'.logs = α f.logs ++ [transferLog s r a]`.

### Informal correctness argument

**Claim.** Stack, memory, logs, jump destinations and gas operations refine their public observers and preserve the frame invariants required by stepping and settlement.

**Premises.** EthBase and EthState laws; well-formed gas meters; memory expansion aligned to words; exact Amsterdam limits/costs supplied consistently by VmConfig; explicitly checked casts and window bounds.

**Argument.** Reverse-array observation proves stack push/pop/peek equations by the final-element cases. Memory refinement splits each read/write into its in-range segment and zero extension, with the size-zero identity handled before offset conversion. Calculate expansion and charge its cost before allocation. LogRope induction gives flatten(append a b) = flatten a ++ flatten b, so rope shape is unobservable. Jump scanning induction advances by one plus the PUSH immediate length, marking only instruction bytes. Gas proofs split each operation's branch and account for all six meter fields. State-gas charges, commit, restores, refunds and repayment merely redistribute counted potential or affect the separate reservoir; execution charges decrease Φ. Child returns are explicit additions, so this local argument does not prove whole-call progress. VmWorld contains one TxState, avoiding independent observation or ancestor-cursor copies.

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

## 10. Gaps

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **Φ laws are source-checked only.** None of the §7 meter equations is a Lean theorem; G1 is "planned".
- **Cross-frame progress (G2) is unproved.** The bound "a child returns potential ≤ the potential granted" needs an induction over the runner and uses `L-SETTLE`, `L-INC` and the stipend accounting; its exact statement with 2-D gas is not yet written.
- **Transaction-level gas conservation** has no statement yet; `EthBlock` needs one for receipts and block accounting.
- **Negative top-level refund.** `U256(gas_meter.refund_counter)` raises `OverflowError` if the top frame's refund is negative. The preparation-failure cast (`interpreter.py:285`) is proved unreachable, because the refund counter is 0 there. The cast after execution (`:318`) is **unresolved**: a non-negativity invariant is sketched (every `−REFUND_STORAGE_CLEAR` reverses a surviving earlier `+` in the same transaction, and failed frames reset their refunds) [I] but unproved. Until it is proved, the spec must produce `VmFault.u256Overflow .refundCounter` there (an O13 candidate).
- **Balance overflow in `move_ether`.** A recipient balance above `2^256 − 1` raises `OverflowError` in EELS (`state_tracker.py:663`, and `create_ether` at `:687`). The witness authenticates the state against a parent root the guest does not itself trust, so large balances are not excluded by the input format. It is argued reachable from the pinned source (O13); no fixture or probe witnesses it. The named constructor is owned by `EthState`'s `moveEther` and surfaces here as `VmFault.state`.
- **O13 enumeration still open.** The VM-internal Python faults are classified (CONTRACT O13, D14): BLOCKHASH's `IndexError` is fixture-witnessed, and the BLOBBASEFEE and balance overflows are argued reachable. The `VmFault` constructor list is frozen only once this module's failure-ledger entries close (DECISIONS B14).
- **`calculate_excess_blob_gas`** takes `Header | PreviousForkHeader` and uses `isinstance`; the Lean version takes three numbers, and `EthBlock` must reproduce the "fields absent → zeros" default [I: both header types at the pin carry the fields, so the default may be dead].
- **`calculate_blob_gas_price` on huge `excess_blob_gas`** runs `taylor_exponential` for a number of iterations roughly proportional to `excess_blob_gas / BLOB_BASE_FEE_UPDATE_FRACTION` (DISC-002); for adversarial parent headers this is a host-time problem (DISC-002), and `U256(price)` in BLOBBASEFEE is argued reachable as an overflow (O13, `instructions/environment.py:607`). Termination and cost belong to EthBase; the envelope question is open.
- **Memory closed form** (telescoping of `calculate_gas_extend_memory`) and `L-MEM-BOUND` are unproved.
- **Meter well-formedness `Wf`** is not yet characterised. `state_gas_left ≤ state_gas_baseline` is **not** an invariant (a cross-frame refund can push the reservoir above the baseline), so the right invariant is still to be found; only the EELS asserts are known facts.
- **Envelope limits** for `Nat` gas (a `u64` fast path) are not specified; D1 and a future `Envelope` record decide.
