# `EthVmCore`: EVM frame, environments, stack, memory, 2-D gas meter, jumpdest analysis

*Status: informal specification, draft. Date: 2026-10-19. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F1, F2, F3, F8, F9, F11, F12, F20 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D1, D5, D11, D13, D14, D17, D22, D23, D24, D25, D27 · questions: B7/Q24, B8/Q1/Q26/Q43, B14/Q23, F11, Q61.*

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

## 4. Tests

- **Supplied bounded Stack controls:** Forty-one complete ordered observations cover empty pop/peek, zero/max/high-bit/duplicate words, every position of a mixed model, indices exactly at size and 2^4096, sizes 1023/1024, full push overflow and pop/replacement, and all deterministic sequence intermediates. Public-only callers consume all eight laws, establish success availability/exclusion of unrelated errors and both actual-Stack conditional inverses. The strict normal/`-O` parser checks full frames and rejects boolean/float integer aliases, malformed models/words/schema, incorrect ordering and whole-model changes with unchanged size/top. Original-helper comparison is only bounded typed pop/push; peek remains a labelled List-index adapter.

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
def txStateGasUsed (m : GasMeter) (T : Nat)
    (h : m.stateGasBaseline ≤ T) : Int
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
| `GasMeter` | record of `Nat`/`Int` | itself (public record) | no global invariant; supplied charge/refund/repay, withhold/drain/child restoration and ordinary restore admit every raw record; other operations use only their local premises (§7) | value | O(1) per operation on `Nat`s of size < 2^64 in practice; bignum only for memory costs of huge windows |
| `LogRope` | strict immutable empty/leaf/concat tree | chronological `List Log` via `toList` | concat observes left before right; no mutable cache | immutable nodes, linear frame ownership | append O(1); flatten O(nodes + logs) via a work stack, including skew trees; discarded child logs do not enter the parent |
| `JumpdestMap` | `ByteArray` bitmap of `⌈\|code\|/8⌉` bytes | `Finset Nat` (= EELS `Set[Uint]`); `α b = {i \| bit i}` | only indices `< \|code\|` | read-only, shareable; a cache keyed by code hash is allowed outside semantic state (ARCHITECTURE §7) | build O(\|code\|); lookup O(1) |
| `AddrSet`, `SlotSet` (warm sets) | `Std.TreeSet` | finite set | ordered | **worst-case persistent**: the parent's version is retained across a child and reused if the child fails (ARCHITECTURE §5.0) | insert/member O(log n); merge on success O(1) by `L-WARM-MONO` |
| `accountsToDelete` | `Std.TreeSet Address` | finite set | — | persistent (retained parent) | union O(m log(n+m)) |
| `FrameCtx` | record; `code`, `callData` shared `ByteArray` | itself | `depth ≤ 1024` | read-only | — |

## 7. Contract and laws

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
specify the all-input none/identity behavior. Both byte decoders remain unsupplied;
their bounds/injectivity obligations are unchanged: `decodeSingle x = .ok n →
17 ≤ n ≤ 235`, injective on valid inputs; `decodePair x = .ok (n,m) →
1 ≤ n ≤ 14 ∧ n < m ∧ m ≤ 30 − n`, injective. [C]

**Memory** (model `List UInt8`). [C], used by [R] memory-opcode lemmas (exercise 1):
- `α (expand m k) = α m ++ replicate k 0`; preservation of 32-byte alignment requires `k % 32 = 0`. Window reads/writes require the in-bounds hypotheses stated in §5.
- read-after-write: `readBytes (write m s v) s |v| = v` when `s + |v| ≤ size m`; disjoint windows: `readBytes (write m s v) t k = readBytes m t k` when `[t,t+k)` ∩ `[s,s+|v|)` = ∅; `write m s [] = m` for **all** `s`; `size (write m s v) = size m` when in bounds.
- overlap (MCOPY): `write m d (readBytes m s k)` reads back as the snapshot of the source, i.e. copy is "read then write" (memmove semantics).
- `bufferRead b s k = (b.drop s).take k ++ replicate (k − …) 0`, length `k`.
- Expansion closed form: for windows `ws` with nonzero sizes, `(calculateGasExtendMemory m ws).expandBy = ceil32(max(size m, maxEnd ws)) − size m` and `cost = C(size m + expandBy) − C(size m)` [I: telescoping sum; prove].
- `L-MEM-BOUND` [T/S]: `chargeGas g (… + ext.cost) = .ok _ → ext.expandBy ≤ f(g)` for an explicit `f` (the quadratic inverse); this is what makes "no allocation before charge" a resource bound.

**Logs** [C]: `LogRope.toList (LogRope.append a b) = LogRope.toList a ++ LogRope.toList b`. Flatten maintains the emitted prefix and pending subtrees in chronological order; the total pending structural size decreases when a node is expanded. Each node and each leaf log is visited once. This proves order and the linear traversal claim without repeated prefix copying.

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

**Transaction state-gas usage (Q61), prospective and not supplied.** The
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

This is a law type for a later implementation, not a supplied theorem. Cast before
subtraction: the result is signed and may be negative. All other raw fields are
unrestricted, including execution gas, refund sign and both spill pools; the
reservoir may exceed both baseline and grant. For example, `(E,R,B,q,S,C) =
(13,21,9,99,3,5)` with `T = 10` meets the premise and returns `-3`. Callers must
establish this local proof; no global `Wf`, non-negativity premise, clamp, runtime
error or bundled domain is added. Caller reachability and transaction conservation
remain separate obligations. The observer and this equation are unimplemented/unproved.

The charge, three rollback, two refund, four local transfer and signed-addition/scalar equations are supplied
above. The following list retains the remaining G1 and composition obligations:
- `calculateMessageCallGas v g L mem x = ⟨c, s⟩ → L ≥ mem + x → c ≤ L − mem ∧ s ≤ c − x + stipend(v)` (forwarded gas never exceeds what is charged, plus stipend): the `Ccallgas_lt_Ccall` analogue needed by G2.
- **`L-SETTLE`** [C]: after `restoreStateGas` then `forfeitRemainingGas` (halt) or `restoreStateGas` alone (revert), `ChildSettled child true` holds: `stateGasSpilled = 0 ∧ refundCounter = 0 ∧ stateGasLeft = stateGasBaseline`; every non-top frame has `stateGasCommittedSpill = 0` (only `createEvm` commits). These discharge `incorporateChild`'s preconditions.
- **`L-INC`** [C]: `(incorporateChild p c failed h).gasMeter.phi = p.gasMeter.phi + c.gasMeter.phi` (the repay step preserves Φ). Together with G2's "child returns potential ≤ potential granted" this gives the cross-frame bound.
- **`L-WARM-MONO`** [C]: if `p.accessedAddresses ⊆ c.accessedAddresses` then the union is `c.accessedAddresses` (same for slots). [F] the implementation may assign.
- Settlement [C]: `settleTransactionGas` preconditions `gasLeft + stateGasLeft ≤ txGas`, `calldataFloor ≤ txGas`, and `refund ≥ 0` (the caller converts `refundCounter : Int` with a proof or a `u256Overflow` fault, R-EXC-2); then `gasUsed ≤ txGas`, `executionGasUsed ≥ calldataFloor`.
- Transaction-level conservation [C, statement to be found]: an equation relating `txGas`, the returned `gasLeft + stateGasLeft`, `txStateGasUsed` and the gas charged; needed by `EthBlock` accounting proofs.

**Jumpdests** [C]: `(validJumpDestinations c).contains i ↔ i ∈ getValidJumpDestinations c` (the EELS set, defined as the model by structural recursion on remaining length); [C] cache consistency if a code-hash cache is added (Nipkow Ch. 18 invariant).

**Transfer log** [C]: `emitTransferLog f topic s r 0 = f`; otherwise, for `f' := emitTransferLog f topic s r a`, `α f'.logs = α f.logs ++ [Log(SYSTEM_ADDRESS, [topic, pad32 s, pad32 r], be32 a)]`.

### Informal correctness argument

**Claim.** Stack, memory, logs, jump destinations and gas operations refine their public observers and preserve the frame invariants required by stepping and settlement.

**Premises.** EthBase and EthState laws; local proof arguments for commit/entry restore and caller premises for the remaining meter operations (none for the supplied charge kernel, refund/repay or ordinary restore); memory expansion aligned to words; exact Amsterdam limits/costs supplied consistently by VmConfig; explicitly checked casts and window bounds.

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
- **Q61**: `txStateGasUsed` uses the local baseline-to-grant proof in §5/§7; DECISIONS owns the disposition. Caller premise reachability and implementation remain obligations.

## 10. Gaps

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **Bounded Stack is partially supplied:** §3/§7 own the private bounded carrier, six operations and eight ordinary laws. Swap all-input behavior, both decoders, actual handler/frame ownership and compiled allocation/C1–C4 checks remain open; no whole VM or guest gate follows.
- **G1 is partially discharged:** §3/§7 own the supplied complete meter, nominal exceptional-halt carrier, read-only check and two checked charges with ten all-raw-meter laws, plus commit/ordinary restore/entry restore with eight ordinary laws on their full local proof domains and refund/repay with seven ordinary all-raw-meter laws, plus four local transfer operations with eight ordinary laws (forfeit only on pending-spill-zero), and signed refund addition/scalar maximum with four unconditional ordinary laws. Caller premise reachability, remaining meter operations, settlement and transaction-conservation laws remain unimplemented/unproved. The Q61 `txStateGasUsed` observer and its single §7 equation remain unimplemented/unproved; callers must establish the local baseline-to-grant proof. This closes no overall G1 or G2–G7 gate.
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
