# `EthVmInstructions`: one handler per opcode, `StepResult`, child requests and resume operations

*Status: informal specification, draft; raw requests, indexed StepResult, Handler, opcode bytes, STOP and ADD/SUB/MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND/ADDMOD/MULMOD with their local laws supplied. Date: 2026-11-13. Pin: `tests-zkevm@v21.0.6` @59c1473d. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F1, F8, F10, F11, F20 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D1, D5, D13, D14, D17, D18, D26, D27 · questions: B7/Q24, B8/Q1, B14/Q23, F11.*

Paths in `file:line` references are relative to `src/ethereum/forks/amsterdam/vm/` unless stated otherwise; `I/` abbreviates `instructions/`. "[V]" marks a claim checked by reading the pinned source; "[I]" an inference. EELS `file:line` citations are at `59c1473d` except where marked and those listed in `STFSpec/informal/citation-remap-manual.txt`, which are still at `e1a316a0` (`tests-zkevm@v21.0.0`); verified observations are at `e1a316a0` unless marked as at `59c1473d` (GAPS-CROSSCUTTING X16).

## 1. Purpose

`EthVmInstructions` (root `STFSpec.Vm.Instructions`, layer L3) defines the semantics of every Amsterdam opcode as a non-recursive handler that maps a frame to a `StepResult`: a successor frame, a normal stop with output, a revert with output, an exceptional halt, or a **child request** (call or create) that the runner executes before calling a **named resume operation** on the suspended parent (D17). It also owns the opcode enumeration and its dispatch table (`I/__init__.py`), the single-step function `step`, and EIP-7702 delegation-designator parsing and call-target resolution. It must not import the runner or precompile implementations (`scripts/boundaries.toml`); CALL/CREATE semantics therefore stop at the request and resume at the outcome. The per-opcode lemmas stated here are the refinement interface for evm-asm's dispatch-loop proofs.

## 2. Requirements

### 2.1 General rules (apply to every handler)

- **R-GEN-1 Step order.** Each handler must perform its sub-steps in the EELS order: (1) static-context check, where EELS does it first; (2) pops (`StackUnderflowError`); (3) gas computation and `check_gas`/`charge_gas`; (4) state reads and writes; (5) memory expansion; (6) pushes; (7) `pc` update. The order matters beyond the exception name: **state reads are persistent observations** that survive a later exceptional halt or revert (ARCHITECTURE §6; they feed the BAL and the witness access record), so a read must happen exactly when EELS performs it, and not before a gas check that precedes it in EELS. EIP-8038's "STATE ACCESS after state-independent gas check" structure (`I/system.py:487–536`, `I/storage.py:85–116`) exists for this reason [V: comments].
- **R-GEN-2 Precedence among exceptional halts.** Where two halt conditions hold, the first in EELS order wins. All exceptional halts have the same guest-visible effect (O8), so precedence is observable only through traces and through which reads happened before the halt; both must match. Specific orders: most arithmetic/stack-consuming ops pop before charging (underflow beats OOG); DUP*/SWAP*/DUPN/SWAPN/EXCHANGE charge before the depth check (OOG beats underflow) (`I/stack.py:100–102, 132–134, 229–237`); push-producing ops charge before pushing (OOG beats overflow); CREATE/CREATE2/SSTORE/TSTORE/SELFDESTRUCT check the static flag **before** popping; CALL checks it after popping and only for non-zero value; LOG checks it after charging and expanding memory (`I/log.py:67–69`).
- **R-GEN-3 Memory.** Every memory-touching handler computes `calculate_gas_extend_memory` for its windows, charges `base + per-word + expansion` in one `charge_gas`, then expands, then reads/writes. Windows with size 0 never expand memory and never fail, whatever their offset. Offsets and sizes are full 256-bit values; conversion to `Nat` must be exact (never truncated to 64 bits before the gas check).
- **R-GEN-4 Words.** Arithmetic is modulo 2^256 through the `U256` API (EthBase, D1): signed operations use two's complement; `x / 0 = 0`, `x % 0 = 0`; ADDMOD/MULMOD compute over unbounded integers before reducing.
- **R-GEN-5 PC.** Handlers advance `pc` by 1, except PUSHn (`1 + n`, `I/stack.py:79`), DUPN/SWAPN/EXCHANGE (2, `:242, 278, 314`), JUMP/JUMPI (target or `pc+1`). Terminal handlers' `pc` updates are irrelevant. Immediate bytes beyond the end of code read as zero (`buffer_read`).
- **R-GEN-6 Invalid opcodes.** A byte that is not in `Ops` (103 of 256 values, including `0xFE`) causes `InvalidOpcode(byte)` before any charge (`interpreter.py:439–442`). Running off the end of code (`pc ≥ |code|`) is a normal stop with empty output (`interpreter.py:438`).
- **R-GEN-7 Non-EVM faults.** State-access failures (`WitnessError`, O4), BLOCKHASH beyond the available headers, and the BLOBBASEFEE `U256` conversion overflow propagate as `VmFault` (EthVmCore R-EXC-2), never as exceptional halts. The last two are CONTRACT O13 members. NUMBER, GASLIMIT and BASEFEE cannot overflow their `U256` cast: the SSZ payload fields are `uint64`, `uint64` and `uint256`.

### 2.2 Opcode table

Stack columns list operands top first. "mem" = memory-expansion cost of the listed windows; `w(n) = ceil32(n)/32`; warm/cold = 100/3000 for accounts and 100/2100 for slots, with the address/slot added to the frame's warm set. Costs are the `GasCosts` names of `gas.py:169–250`; state gas is `StateGasCosts`. "→ c" = continue.

**Stop, arithmetic, comparison, bitwise (all → c except STOP)**

| Hex | Name | EELS | Pops → pushes | Gas | Semantics / halts |
|---|---|---|---|---|---|
| 00 | STOP | `I/control_flow.py:22` | – | 0 | `.stop` output ∅ |
| 01 | ADD | `I/arithmetic.py:25` | a b → a+b | 3 | wrapping |
| 02 | MUL | `:79` | a b → a·b | 5 | wrapping |
| 03 | SUB | `:52` | a b → a−b | 3 | wrapping |
| 04 | DIV | `:106` | a b → a/b | 5 | b = 0 → 0 |
| 05 | SDIV | `:139` | a b → a÷b | 5 | signed, truncates toward 0; b = 0 → 0; (−2^255)÷(−1) = −2^255 (`U255_CEIL_VALUE`, `:136`) |
| 06 | MOD | `:172` | a b → a mod b | 5 | b = 0 → 0 |
| 07 | SMOD | `:202` | a b → sign(a)·(\|a\| mod \|b\|) | 5 | b = 0 → 0 |
| 08 | ADDMOD | `:232` | a b N → (a+b) mod N | 8 | unbounded sum; N = 0 → 0 |
| 09 | MULMOD | `:263` | a b N → (a·b) mod N | 8 | unbounded product; N = 0 → 0 |
| 0A | EXP | `:294` | a b → a^b mod 2^256 | 10 + 50·⌈bitlen(b)/8⌉ | |
| 0B | SIGNEXTEND | `:331` | k x → x' | 5 | k > 31 → x; else extend bit `8k+7` |
| 10–15 | LT GT SLT SGT EQ ISZERO | `I/comparison.py:21, 74, 48, 101, 127, 154` | a b → 0/1 (ISZERO: a → 0/1) | 3 | signed variants via two's complement |
| 16–19 | AND OR XOR NOT | `I/bitwise.py:21, 46, 71, 96` | a b → r (NOT: a → ~a) | 3 | |
| 1A | BYTE | `:120` | i w → byte | 3 | i ≥ 32 → 0; byte `i` counted from the most significant |
| 1B | SHL | `:156` | s v → v≪s | 3 | s ≥ 256 → 0 |
| 1C | SHR | `:186` | s v → v≫s | 3 | s ≥ 256 → 0 |
| 1D | SAR | `:216` | s v → v≫ₐs | 3 | s ≥ 256 → 0 or 2^256−1 by sign |
| 1E | CLZ | `:248` | x → 256 − bitlen(x) | 5 (LOW) | EIP-7939; CLZ 0 = 256 |

**KECCAK (KECCAK256), environment, block**

| Hex | Name | EELS | Pops → pushes | Gas | Semantics / halts |
|---|---|---|---|---|---|
| 20 | KECCAK | `I/keccak.py:26` | off sz → h | 30 + 6·w(sz) + mem(off,sz) | keccak256 of the window, as a `KeccakQuery` call (D5) |
| 30 | ADDRESS | `I/environment.py:35` | → target | 2 | |
| 31 | BALANCE | `:58` | a → bal | warm/cold | address masked to 160 bits (`to_address_masked`); warm-set add **before** the charge (`:72–76`); read after the charge; missing account → 0 |
| 32 | ORIGIN | `:89` | → origin | 2 | |
| 33 | CALLER | `:113` | → caller | 2 | |
| 34 | CALLVALUE | `:136` | → value | 2 | |
| 35 | CALLDATALOAD | `:159` | i → word | 3 | zero-padded read of 32 bytes at any i |
| 36 | CALLDATASIZE | `:185` | → \|cd\| | 2 | |
| 37 | CALLDATACOPY | `:208` | mo do sz → | 3 + 3·w(sz) + mem(mo,sz) | zero-padded source |
| 38 | CODESIZE | `:246` | → \|code\| | 2 | executing frame's code (init code in a create frame) |
| 39 | CODECOPY | `:269` | mo co sz → | 3 + 3·w(sz) + mem | zero-padded |
| 3A | GASPRICE | `:307` | → price | 2 | `effective_gas_price` |
| 3B | EXTCODESIZE | `:330` | a → n | warm/cold + 100 | EIP-8038 code-read surcharge; reads account and code after the charge; size of the **raw** code (23 for a delegation designator) |
| 3C | EXTCODECOPY | `:364` | a mo co sz → | warm/cold + 100 + 3·w(sz) + mem | warm-set add before charge; raw code, zero-padded |
| 3D | RETURNDATASIZE | `:411` | → \|rd\| | 2 | |
| 3E | RETURNDATACOPY | `:434` | mo ro sz → | 3 + 3·w(sz) + mem | after the charge, **`ro + sz > \|rd\|` → `OutOfBoundsRead`, even when `sz = 0`** (`:463`); then expand and copy |
| 3F | EXTCODEHASH | `:476` | a → h | warm/cold | account `== EMPTY_ACCOUNT` (absent or empty) → 0, else its `code_hash`; **no code read, no surcharge** |
| 40 | BLOCKHASH | `I/block.py:22` | n → h | 20 | 0 unless `n < number ≤ n + 256`; else `block_hashes[−(number − n)]` and `track_ancestor_access(number − n)` (a block-level observation, never reverted). If `number − n > \|block_hashes\|` EELS raises `IndexError` (`I/block.py:58`) → `VmFault.ancestorHashUnavailable` (O13) [V: `stateless.py:246` supplies only the witness headers; fixture `validation_headers_missing_oldest_blockhash_ancestor`] |
| 41 | COINBASE | `:71` | → coinbase | 2 | |
| 42 | TIMESTAMP | `:105` | → time | 2 | |
| 43 | NUMBER | `:139` | → number | 2 | `U256(number)` |
| 44 | PREVRANDAO | `:172` | → randao | 2 | |
| 45 | GASLIMIT | `:205` | → limit | 2 | |
| 46 | CHAINID | `:238` | → chain id | 2 | |
| 47 | SELFBALANCE | `I/environment.py:513` | → bal | 5 | read after charge |
| 48 | BASEFEE | `:539` | → base fee | 2 | `U256(base_fee_per_gas)`; cannot overflow (SSZ `uint256`) |
| 49 | BLOBHASH | `:562` | i → h | 3 | `i < \|hashes\|` → hash, else 0 |
| 4A | BLOBBASEFEE | `:589` | → price | 2 | `U256(calculate_blob_gas_price(excess_blob_gas))` (`:607`); overflow → `VmFault.u256Overflow .blobBaseFee` (O13, argued reachable) |
| 4B | SLOTNUM | `I/block.py:268` | → slot | 2 | EIP-7843: `block_env.slot_number` |

**Stack, memory, storage, control flow**

| Hex | Name | EELS | Pops → pushes | Gas | Semantics / halts |
|---|---|---|---|---|---|
| 50 | POP | `I/stack.py:26` | a → | 2 | pop before charge |
| 51 | MLOAD | `I/memory.py:89` | off → word | 3 + mem(off,32) | |
| 52 | MSTORE | `:26` | off v → | 3 + mem(off,32) | big-endian 32 bytes |
| 53 | MSTORE8 | `:57` | off v → | 3 + mem(off,1) | low byte |
| 54 | SLOAD | `I/storage.py:37` | k → v | warm/cold (slot) | warm-set add before the charge; read after |
| 55 | SSTORE | `:68` | k v → | see §2.4 | static first |
| 56 | JUMP | `I/control_flow.py:45` | d → | 8 | `d ∉ jumpdests` → `InvalidJumpDestError` (after charge) |
| 57 | JUMPI | `:70` | d c → | 10 | `c = 0` → `pc+1` (d not checked); else as JUMP |
| 58 | PC | `:101` | → pc | 2 | |
| 59 | MSIZE | `I/memory.py:119` | → \|mem\| | 2 | always a multiple of 32 |
| 5A | GAS | `I/control_flow.py:125` | → gas_left | 2 | value **after** this charge; execution gas only (not the reservoir) |
| 5B | JUMPDEST | `:149` | – | 1 | |
| 5C | TLOAD | `I/storage.py:164` | k → v | 100 | transient storage (EIP-1153) |
| 5D | TSTORE | `:189` | k v → | 100 | static first; revertible (part of the tx snapshot) |
| 5E | MCOPY | `I/memory.py:142` | dst src len → | 3 + 3·w(len) + mem([(src,len),(dst,len)]) | read-then-write (overlap-safe) |
| 5F | PUSH0 | `I/stack.py:49` | → 0 | 2 | |
| 60–7F | PUSH1…PUSH32 | `:49` (`push_n`) | → imm | 3 | `n` bytes after `pc`, zero-padded past end; `pc += 1+n` |
| 80–8F | DUP1…DUP16 | `:82` (`dup_n`) | → copy of i-th | 3 | charge, then `i > size` → underflow, then push (overflow) |
| 90–9F | SWAP1…SWAP16 | `:110` (`swap_n`) | swap top, (i+1)-th | 3 | charge, then `i ≥ size` → underflow |
| E6 | DUPN | `:213` | → copy of n-th | 3 | EIP-8024; charge; `n = decode_single(imm)` (`InvalidParameter` for imm 91…127); `n > size` → underflow; `pc += 2` |
| E7 | SWAPN | `:245` | swap 1st, (n+1)-th | 3 | as DUPN; `n + 1 > size` → underflow |
| E8 | EXCHANGE | `:281` | swap (n+1)-th, (m+1)-th | 3 | `(n,m) = decode_pair(imm)` (invalid 82…127); `max(n,m)+1 > size` → underflow |

**Logs and system**

| Hex | Name | EELS | Pops → pushes | Gas | Semantics / halts |
|---|---|---|---|---|---|
| A0–A4 | LOG0…LOG4 | `I/log.py:28` (`log_n`) | off sz t₁…tₙ → | 375 + 8·sz + 375·n + mem | charge, expand, **then** static → `WriteInStaticContext`; append `Log(target, topics, data)` |
| F0 | CREATE | `I/system.py:188` | e off sz → addr/0 | 12000 + mem + 2·w(sz); state gas via `generic_create` | §2.5 |
| F1 | CALL | `:465` | g a v io is oo os → 0/1 | §2.6 | §2.6 |
| F2 | CALLCODE | `:592` | g a v io is oo os → 0/1 | §2.6 | no static check |
| F3 | RETURN | `:307` | off sz → | mem | `.stop` with output = window |
| F4 | DELEGATECALL | `:781` | g a io is oo os → 0/1 | §2.6 | |
| F5 | CREATE2 | `:242` | e off sz salt → addr/0 | 12000 + 6·w(sz) + mem + 2·w(sz) | §2.5 |
| FA | STATICCALL | `:884` | g a io is oo os → 0/1 | §2.6 | |
| FD | REVERT | `:987` | off sz → | mem | `.revert` with output = window (gas not forfeited) |
| FF | SELFDESTRUCT | `:706` | b → | §2.7 | static first |

### 2.3 Dispatch

- **R-DSP-1** `Ops` (`I/__init__.py:32–220`) has exactly 153 constructors with the byte values listed; `op_implementation` (`:223–377`) maps each to its handler. The Lean dispatch must be a total `match` on `Ops` (not a map lookup), with `Ops.ofByte? : UInt8 → Option Ops` and the round-trip laws.
- **R-DSP-2** `step ctx f` must return `.stop f ∅` if `f.pc ≥ |ctx.code|`, `.halt f (invalidOpcode b)` if `Ops.ofByte? b = none`, and otherwise the handler's result. `step` never recurses and never changes `ctx`.

### 2.4 SSTORE (`I/storage.py:68–161`; EIP-2200, EIP-3529 refund values, EIP-8037 state gas, EIP-8038 access)

In order: (1) static → `WriteInStaticContext`; (2) pop key, new; (3) `cost := cold ? 2100 : 100`; (4) `check_gas(max(cost, 2301))`: the EIP-2200 sentry, **before any state read**; (5) warm the slot; (6) read `original` (`get_storage_original`) then `current`; (7) if `original = current ≠ new`: `cost += 10000` (`STORAGE_WRITE`); (8) if `current ≠ new`: `+11616` if `original ≠ 0 ∧ current ≠ 0 ∧ new = 0`; `−11616` if `original ≠ 0 ∧ current = 0`; `+10000` if `original = new` (each independently, on the `Int` refund counter); (9) state gas `97920` (`STORAGE_SET`) if `original = current = 0 ≠ new`; (10) if `current ≠ new ∧ original = new = 0`: `credit_state_gas_refund(97920)` **before** the charges; (11) `charge_gas(cost)`, then `charge_state_gas(state)`; (12) `set_storage`. A naive port that charges before step (10) can fail with OOG where EELS succeeds, because the credit can refill `gas_left` from the spill.

### 2.5 CREATE / CREATE2 and `generic_create` (`I/system.py:59–304`)

- **Handler part.** Static → halt; pop `endowment, offset, size` (CREATE2 also `salt`); charge as in the table; **then** `size > MAX_INIT_CODE_SIZE (131072)` → `OutOfGasError` (`:220, 284`); expand memory; address = `compute_contract_address(target, nonce(target))` (reads the account) or `compute_create2_contract_address(target, salt, init_code)`, both through `KeccakQuery` (EthCodec's `…Q` forms, D5).
- **Preflight** (`generic_create`, `:82–100`): read the init code; set `return_data := ∅`; if `balance(target) < endowment` or `nonce(target) = 2^64 − 1` or `depth + 1 > STACK_DEPTH_LIMIT`: push 0 and continue (nothing withheld; the opcode's own charge stays).
- **Destination access** (`:105–109`): warm the address; `newAccountCharged := ¬ is_account_alive(addr)`; if so `charge_state_gas(NEW_ACCOUNT = 183600)` (may halt with OOG).
- **Grant** (`:113`): `g := withhold_create_gas` (all but 1/64 of `gas_left`).
- **Collision** (`:118–121`): if `¬ account_deployable(addr)` (nonce ≠ 0 or code non-empty; storage is ignored): `increment_nonce(target)`, push 0, continue; `g` is **consumed** (not returned) and the reservoir is not drained.
- **Dispatch** (`:125–171`): `R := drain_state_gas_reservoir`; `increment_nonce(target)` (outside the child's snapshot: it survives a child failure); return `.create parent req` with child parameters `caller = target`, `current_target = addr`, `value = endowment`, empty call data, `code = init_code`, `code_address = none`, `should_transfer_value`, not static, precompiles enabled, meter `(g, R, baseline R)`, copies of the warm sets.
- **`resumeAfterCreate`** (`:177–185`, then `pc += 1`, `:239`/`:304`): `incorporate_child`; if the child failed: `credit_state_gas_refund(NEW_ACCOUNT)` when `newAccountCharged` (the amount comes from the config, which is why resume takes it, F10), `return_data := child.output` (revert data, or ∅ after a halt), push 0; else `return_data := ∅` and push the address. Successful creation never exposes the deployed code as return data (ARCHITECTURE §6).

### 2.6 CALL family and `generic_call` (`I/system.py:369–984`)

- **CALL** (`:465`): pop 7 (`to` masked); `static ∧ value ≠ 0` → halt; `mem` over the input then the output window; `access := cold(to) ? 3000 : 100`; `transfer := value ≠ 0 ? 11300 : 0`; `check_gas(access + transfer + mem)`; warm `to`; `calculate_delegation_cost(to)` (reads `to`'s account and code); if delegated: add its warm/cold cost, `check_gas` again, warm the delegate; read the code of `code_address`; `charge_gas(extra + mem)`; if `value ≠ 0 ∧ ¬alive(to)`: `charge_state_gas(NEW_ACCOUNT)` (`newAccountCharged`); **then** compute the forwarded gas from the *remaining* `gas_left` with `calculate_message_call_gas(value, gas, gas_left, 0, 0)` and charge it; drain the reservoir; expand memory; read the sender balance.
- **CALLCODE** (`:592`): `to := current_target`, cold/warm and delegation on the popped `code_address`; no static check (a self-transfer); `calculate_message_call_gas(value, gas, gas_left, mem, extra)` and `charge_gas(cost + mem)`; no account-creation charge; `insufficient_balance` checked.
- **DELEGATECALL** (`:781`): pop 6; no transfer cost; child keeps the parent's `caller` and `value`, `to = current_target`, `should_transfer_value = false`; no balance check.
- **STATICCALL** (`:884`): pop 6; child `value = 0`, `is_static = true`.
- **`generic_call`** preflight (`:381–393`): `return_data := ∅`; if `depth + 1 > STACK_DEPTH_LIMIT` or insufficient balance: `restore_child_gas(sub_call, R)` (the stipend included), credit `NEW_ACCOUNT` if charged, push 0, continue. Otherwise read the call data from memory and return `.call parent req` (child `is_static = is_staticcall ∨ ctx.isStatic`, `disable_precompiles = is_delegated`, copies of warm sets, meter `(sub_call, R, baseline R)`).
- **`resumeAfterCall`** (`:446–462`, then `pc += 1`): `incorporate_child`; `return_data := child.output` (for success, revert and halt alike: ∅ after a halt); credit `NEW_ACCOUNT` on failure if charged (amount from the config, F10); push 0 or `CALL_SUCCESS = 1`; write `child.output[0 : min(out_size, |output|)]` at `out_offset` (inside the already-expanded window).

### 2.7 SELFDESTRUCT (`I/system.py:706–778`; EIP-6780, EIP-8246)

Static → halt; pop `b` (masked); `cost := 5000 + (cold(b) ? 3000 : 0)`; `check_gas(cost)`; warm `b`; if `¬alive(b) ∧ balance(target) ≠ 0`: state gas `NEW_ACCOUNT` and execution `+9000`; `charge_gas` **before** `charge_state_gas`; move the whole balance to `b` (a no-op when `b = target`); if `b ≠ target`, use `emitTransferLog f ctx.systemAddress world.tx.block.consts.transferTopic target b balance` with the previously read originator balance (EIP-7708; helper is a no-op for 0); if `target ∈ created_accounts` add it to `accounts_to_delete`; `.stop` with output ∅. Deletion happens after the transaction via `clear_account_preserving_balance` (`fork.py:1088–1089`, EthBlock), so under EIP-8246 a self-destruct to itself of an account created in the same transaction **keeps** its balance [V: the called function's name and the EIP title; its body is EthState's].

### 2.8 EIP-7702 delegation (`eoa_delegation.py`)

- **R-DEL-1** `is_valid_delegation c ↔ |c| = 23 ∧ c[0:3] = 0xEF0100` (`:42–61`); `get_delegated_code_address` returns `c[3:23]` (`:64–81`).
- **R-DEL-2** `calculate_delegation_cost f a` (`:155–188`) reads `a`'s account and code and returns `(false, a, 0)` or `(true, d, warm(d) ? 100 : 3000)` **without** warming `d` (the caller warms after the second check).
- **R-DEL-3** `resolve_delegated_code_address` (`:84–109`, used by the runner's `create_evm`) reads the code, and for a designator charges warm/cold via `charge_gas_from_meter`, warms `d` and returns `(d, true)`.
- **R-DEL-4** Resolution is one level only: if `d`'s code is itself a designator, those 23 bytes execute as code and the first byte `0xEF` is an invalid opcode [I: follows from `get_code(code_address)` with no loop]. When `disable_precompiles` is set and `d` is a precompile address, **no code runs** and the call succeeds with empty output (runner, `interpreter.py:432–433`).

## 3. EELS source map

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `forks/amsterdam/vm/instructions/__init__.py::Ops` | 32 | `Ops`, `Ops.ofByte?`, `Ops.toByte` (supplied); `opImplementation`, `step` (unimplemented) | The enum/byte slice is detailed below; the `op_implementation` dict (`:223`) remains the future dispatch `match` |
| `forks/amsterdam/vm/instructions/arithmetic.py::*` | 28–374 | `add`, `sub`, `mul`, `div`, `sdiv`, `mod`, `smod`, `signextend` (supplied below); `addmod`, `mulmod`, `exp`, `U255_CEIL_VALUE` | Remaining arithmetic handlers unimplemented |
| `forks/amsterdam/vm/instructions/bitwise.py::*` | 24–277 | `bitwiseAnd` … `countLeadingZeros` | |
| `forks/amsterdam/vm/instructions/comparison.py::*` | 24–180 | `lessThan` … `isZero` | |
| `forks/amsterdam/vm/instructions/keccak.py::*` | 30 | `keccak` | through `KeccakQuery` (D5); `m := Id` gives `EthHash.keccak256` |
| `forks/amsterdam/vm/instructions/environment.py::*` | 35–610 | `address` … `blobBaseFee` | |
| `forks/amsterdam/vm/instructions/block.py::*` | 22–299 | `blockHash` … `slotNumber` | |
| `forks/amsterdam/vm/instructions/stack.py::*` | 29–317 | `pop`, `pushN`, `dupN`, `swapN`, `dupn`, `swapn`, `exchange` | the `partial` aliases `push0…push32`, `dup1…`, `swap1…` are dispatch instances |
| `forks/amsterdam/vm/instructions/memory.py::*` | 30–179 | `mstore`, `mstore8`, `mload`, `msize`, `mcopy` | |
| `forks/amsterdam/vm/instructions/storage.py::*` | 37–216 | `sload`, `sstore`, `tload`, `tstore` | |
| `forks/amsterdam/vm/instructions/control_flow.py::*` | 25–174 | `stop` (supplied, exact row below), `jump`, `jumpi`, `pc`, `gasLeft`, `jumpdest` | Remaining control-flow handlers unimplemented |
| `forks/amsterdam/vm/instructions/log.py::*` | 32 | `logN` | `log0…log4` aliases |
| `forks/amsterdam/vm/instructions/system.py::*` | 66–1023 | `genericCreate`, `create`, `create2`, `return_`, `GenericCall` (→ `CallRequest`), `genericCall`, `call`, `callcode`, `selfdestruct`, `delegatecall`, `staticcall`, `revert`, plus `resumeAfterCall`, `resumeAfterCreate` | the EELS functions are split at the dispatch point (§2.5–2.6) |
| `forks/amsterdam/vm/__init__.py::CALL_SUCCESS` | 39 | `CALL_SUCCESS : U256 := 1` | |
| `forks/amsterdam/vm/eoa_delegation.py::EOA_DELEGATION_MARKER` | 36 | `EOA_DELEGATION_MARKER` | `0xEF0100` |
| `forks/amsterdam/vm/eoa_delegation.py::EOA_DELEGATION_MARKER_LENGTH` | 37 | constant 3 | |
| `forks/amsterdam/vm/eoa_delegation.py::EOA_DELEGATED_CODE_LENGTH` | 38 | constant 23 | |
| `forks/amsterdam/vm/eoa_delegation.py::is_valid_delegation` | 42 | `isValidDelegation` | also used by `EthBlock` (EIP-3607 sender check) and the runner |
| `forks/amsterdam/vm/eoa_delegation.py::get_delegated_code_address` | 64 | `getDelegatedCodeAddress` | |
| `forks/amsterdam/vm/eoa_delegation.py::resolve_delegated_code_address` | 84 | `resolveDelegatedCodeAddress` | consumed by the runner's `createEvm` |
| `forks/amsterdam/vm/eoa_delegation.py::calculate_delegation_cost` | 155 | `calculateDelegationCost` | |

### Supplied arithmetic handlers

| EELS source at `59c1473d` | Lean declaration / exact type | Domain | Effects / ordered failures | Laws and tests | Status |
|---|---|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py:25–49` (`add`) | `STFSpec.Vm.Instructions.add {m : Type → Type} [Monad m] : Handler m`, in `STFSpec/Vm/Instructions/Arithmetic.lean`, exported by the Instructions facade | Every supplied context, complete raw Frame and complete `VmWorld m`; price is exactly `ctx.config.costs.opcodeAdd`, any Nat including zero or beyond word width; no LawfulMonad, hash, WF, code-byte or schedule-coherence premise | First pop x, second pop y, execution charge, wrap `U256.add x y`, push, PC+1. Empty underflow keeps f; singleton underflow keeps the first pop; shortage after both pops keeps both pops with unchanged complete meter and PC. Success changes only stack, PC and execution gas. Every outcome has literal underlying pure of a successful VmM result with the complete supplied world | `add_run_empty`, `add_run_singleton`, `add_run_oog`, `add_run_success`, `add_continue_phi`, `add_continue_progress` (§7); facade clients and native/interpreted/source controls (§4) | Handler and six ordinary local laws discharged; conditional source entry/selected-price relation; whole source-model/trace/reachability/dispatch/settlement and composed gates remain open |
| `src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py:52–76` (`sub`) | `STFSpec.Vm.Instructions.sub {m : Type → Type} [Monad m] : Handler m`, in the same leaf/facade | Same raw domain; selected price is independently `ctx.config.costs.opcodeSub` | Same order and complete failure-frame/world preservation; success pushes `U256.sub x y`, original top minus next word, modulo 2^256 | `sub_run_empty`, `sub_run_singleton`, `sub_run_oog`, `sub_run_success`, `sub_continue_phi`, `sub_continue_progress` (§7); same bounded controls | Handler and six ordinary local laws discharged; same explicit refinement limits |
| `src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py:79–103` (`mul`) | `STFSpec.Vm.Instructions.mul {m : Type → Type} [Monad m] : Handler m`, in the same leaf/facade | Same raw domain; selected price is independently `ctx.config.costs.opcodeMul` | Same order and complete failure-frame/world preservation; success pushes `U256.mul x y`, original top times next word, modulo 2^256 | `mul_run_empty`, `mul_run_singleton`, `mul_run_oog`, `mul_run_success`, `mul_continue_phi`, `mul_continue_progress` (§7); same bounded controls | Handler and six ordinary local laws discharged; same explicit refinement limits |
| `src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py:106–133` (`div`) | `STFSpec.Vm.Instructions.div {m : Type → Type} [Monad m] : Handler m`, in the same leaf/facade | Same raw domain; selected price is independently `ctx.config.costs.opcodeDiv` | Same order and complete failure-frame/world preservation; success pushes `U256.div x y`, original top divided by next word, or zero when the next word is zero. Charging precedes zero-divisor handling, so shortage still halts | `div_run_empty`, `div_run_singleton`, `div_run_oog`, `div_run_success`, `div_continue_phi`, `div_continue_progress` (§7); same bounded controls | Handler and six ordinary local laws discharged; same explicit refinement limits |
| `src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py:139–169` (`sdiv`) | `STFSpec.Vm.Instructions.sdiv {m : Type → Type} [Monad m] : Handler m`, in the same leaf/facade | Same raw domain; selected price is independently `ctx.config.costs.opcodeSdiv` | Same ordered pops and complete failure-frame/world preservation. Signed quotient truncates toward zero through `U256.sdiv x y`; zero divisor gives zero; signed min/−1 gives signed min. Special values still charge and can halt for shortage | `sdiv_run_empty`, `sdiv_run_singleton`, `sdiv_run_oog`, `sdiv_run_success`, `sdiv_continue_phi`, `sdiv_continue_progress` (§7); facade numeric-model clients and complete bounded controls (§4) | Handler and six ordinary local laws discharged; same explicit refinement limits |
| `src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py:172–199` (`mod`) | `STFSpec.Vm.Instructions.mod {m : Type → Type} [Monad m] : Handler m`, in the same leaf/facade | Same raw domain; selected price is independently `ctx.config.costs.opcodeMod` | Same ordered pops and complete failure-frame/world preservation. Unsigned remainder through `U256.mod x y`, including high-bit words; zero divisor gives zero. Special values still charge and can halt for shortage | `mod_run_empty`, `mod_run_singleton`, `mod_run_oog`, `mod_run_success`, `mod_continue_phi`, `mod_continue_progress` (§7); facade numeric-model clients and complete bounded controls (§4) | Handler and six ordinary local laws discharged; same explicit refinement limits |
| `src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py:202–229` (`smod`) | `STFSpec.Vm.Instructions.smod {m : Type → Type} [Monad m] : Handler m`, in the same leaf/facade | Same raw domain; selected price is independently `ctx.config.costs.opcodeSmod` | Same ordered pops and complete failure-frame/world preservation. Signed remainder through `U256.smod x y`, with the dividend sign; zero divisor gives zero. Special values still charge and can halt for shortage | `smod_run_empty`, `smod_run_singleton`, `smod_run_oog`, `smod_run_success`, `smod_continue_phi`, `smod_continue_progress` (§7); facade numeric-model clients and complete bounded controls (§4) | Handler and six ordinary local laws discharged; same explicit refinement limits |
| `src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py:232–260` (`addmod`) | `STFSpec.Vm.Instructions.addmod {m : Type → Type} [Monad m] : Handler m`, in the same leaf/facade | Every supplied context, complete raw Frame and complete `VmWorld m`; independent selected `ctx.config.costs.opcodeAddmod` admits every Nat, including zero and arbitrarily large prices, without LawfulMonad, hash, WF or schedule premises | Pop x, y, then z; charge; compute `U256.addmod x y z` using the unbounded sum before modulus z, or zero at z=0; push and PC+1. Empty/singleton/pair underflow retains exactly preceding pops and occurs before charge. OOG retains all three pops with complete unchanged meter and PC. Success changes only stack, PC and execution gas; every outcome retains the complete world under literal underlying pure | `addmod_run_empty`, `addmod_run_singleton`, `addmod_run_pair`, `addmod_run_oog`, `addmod_run_success`, `addmod_continue_phi`, `addmod_continue_progress` (§7); complete facade and public numeric-model clients, native/interpreted/parser/source controls (§4) | Handler and seven ordinary local laws discharged; selected source price 8 and explicit field relation; whole source-model/trace/reachability/dispatch/settlement and composed gates remain open |
| `src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py:263–291` (`mulmod`) | `STFSpec.Vm.Instructions.mulmod {m : Type → Type} [Monad m] : Handler m`, in the same leaf/facade | Every supplied context, complete raw Frame and complete `VmWorld m`; independent selected `ctx.config.costs.opcodeMulmod` admits every Nat, including zero and arbitrarily large prices, without LawfulMonad, hash, WF or schedule premises | Pop x, y, then z; charge; compute `U256.mulmod x y z` using the unbounded product before modulus z, or zero at z=0; push and PC+1. Empty/singleton/pair underflow retains exactly preceding pops and occurs before charge. OOG retains all three pops with complete unchanged meter and PC. Success changes only stack, PC and execution gas; every outcome retains the complete world under literal underlying pure | `mulmod_run_empty`, `mulmod_run_singleton`, `mulmod_run_pair`, `mulmod_run_oog`, `mulmod_run_success`, `mulmod_continue_phi`, `mulmod_continue_progress` (§7); complete facade and public numeric-model clients, native/interpreted/parser/source controls (§4) | Handler and seven ordinary local laws discharged; selected source price 8 and explicit field relation; whole source-model/trace/reachability/dispatch/settlement and composed gates remain open |
| `src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py:331–371` (`signextend`) | `STFSpec.Vm.Instructions.signextend {m : Type → Type} [Monad m] : Handler m`, in the same leaf/facade | Same raw domain; selected price is independently `ctx.config.costs.opcodeSignextend` | Pop unsigned byte index k, then value x, charge, compute `U256.signextend k x`, push, PC+1. Shortage retains both pops and the unchanged complete meter/PC. Guard k>31 follows charge and returns x without width arithmetic. At k≤31 retain low 8(k+1) bits and fill from bit 8k+7. Index 31 also preserves x. Both identity cases still charge and can halt for shortage | `signextend_run_empty`, `signextend_run_singleton`, `signextend_run_oog`, `signextend_run_success`, `signextend_continue_phi`, `signextend_continue_progress` (§7); facade numeric/identity clients and complete bounded controls (§4) | Handler and six ordinary local laws discharged; same explicit refinement limits |

The case laws retain actual public pop/push witnesses and complete residual stack
models, without a Stack constructor or model extensionality assumption. Two binary or three ternary
successful pops of the typed bounded stack leave room for the result; success
proves push availability rather than requiring it from a caller. No halt gas
forfeiture, rollback, output clearing, memory expansion or world action occurs
inside the private pure frame calculation. The resulting generic action equation
retains literal underlying `pure`, without a universal effect interpretation.
All six unchanged frame fields and five unchanged meter fields remain whole,
including returnData, raw LogRope shape, signed refund and both spills.

Source agreement supplies equality of the selected price to pinned 3 for ADD/SUB
and 5 for MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND, or 8 for ADDMOD/MULMOD
(`vm/gas.py:70–72,170–179`), exact Uint/Nat successor and gas
correspondence, nominal U256 word correspondence, top-first Lean/reversed Python stack relation, aligned
memory/byte and meter/log/set relations. It does not equate the raw complete Lean
configuration to the source schedule or equate sampled world metadata to source
state. The source direct body preserves running/output/error; a caught source
underflow or OOG maps to the local `.halt` result before interpreter settlement
(`interpreter.py:450–469`). The diagnostic charge trace is outside the supplied
Handler fields. Whole source-model, trace, reachable entry, actual dispatch and
runner settlement remain open. Neither runtime code-byte nor static-context guards
are added to these raw handlers.

SDIV and SMOD source observations `to_signed` occur immediately after each pop,
before charging (`I/arithmetic.py:151–155,214–218`, at `59c1473d`). They are pure,
total observations on supplied U256 words. Calling the total Base value helper
after successful charge preserves these effects, failures and results; this does
not assert identical textual evaluation order or host cost. Base's public
`toInt_sdiv`, `toInt_smod`, `ofInt?_sdiv` and `ofInt?_smod` own the exact signed
models and checked-construction success. `toNat_mod` owns the unsigned model.


ADDMOD and MULMOD use EthBase's existing `toNat_addmod` and `toNat_mulmod`
models. EELS observes each popped U256 as unbounded Uint before charging
(`I/arithmetic.py:244–246,275–277`); these total observations add no failure.
The unbounded sum/product is reduced only after the selected charge. A zero
modulus still charges and may halt for shortage. No wrapped ADD/MUL intermediate,
new word operation or caller push premise is introduced.

SIGNEXTEND's value model is owned by EthBase §3/§7. For k≤31 the source's
32-byte conversion, retained slice and optional 0xff prefix are defined and the
checked U256 reconstruction fits (`I/arithmetic.py:350–366`). The guarded branch
bounds the retained width to 256 bits. `toNat_signextend`,
`getLsbD_signextend` and the k>31/k=31 identity laws supply the public model,
without a new value algorithm or provider hypothesis.

### Supplied STOP handler

| EELS source at `59c1473d` | Lean declaration / exact type | Domain | Effects / ordered failures | Law and tests | Status |
|---|---|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/control_flow.py:22–42` (`stop`) | `STFSpec.Vm.Instructions.stop {m : Type → Type} [Monad m] : Handler m`, in `STFSpec/Vm/Instructions/Stop.lean`, exported by the Instructions facade | Every supplied context, complete raw Frame and complete `VmWorld m`; no hash, LawfulMonad, WF, code-byte, bounds, gas, stack or settlement premise | PC becomes `f.pc + 1`; all eight other whole frame fields, including returnData, and the whole world are retained; `.stop` has empty output. The complete result is literal underlying `pure (.ok (.stop updatedFrame Bytes.empty, w))`; no handler failure branch or state/hash action | Exactly `stop_run` (§7); private generic and Id public-law clients in `StopCallerProofs.lean`; native/interpreted complete frame observations and the bounded authenticated source comparison in §4 | Supplied handler and ordinary complete run law discharged; local source agreement uses the explicit source-entry relation below; whole source-model/reachability/dispatch/trace refinement remains open |

The source body writes `running := False` and then increments Uint PC by one.
It preserves arbitrary existing source output and error. Empty result output
therefore corresponds to a source entry with `output = b""` and `error = None`,
with source PC/Uint successor matching exact Nat successor, reversed source stack
matching the top-first public Stack model, aligned source memory matching the
complete Memory byte model, and all meter, log, deletion, return-data and warm-set
fields related through the public providers. Immutable context and source state
must also be related to their supplied Lean values for a whole source model;
that model and reachable-entry proof remain open. Direct body execution needs no
code-byte or running premise. Actual interpreter dispatch additionally requires
running execution, in-bounds PC, current byte `0x00` and the nonprecompile branch
(`interpreter.py:432–446`). These are source/dispatch premises, not Lean guards or
extra admission conditions. No claim about arbitrary underlying `Monad.pure`
effects follows from the literal transformer equation.

### Supplied opcode enumeration and byte conversions

| EELS source | Lean declaration / exact type | Domain | Effects / ordered failures | Laws and clients | Status |
|---|---|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/__init__.py:32–220` (`Ops`) | `STFSpec.Vm.Instructions.Ops` in `STFSpec/Vm/Instructions/Ops.lean`, exported by `STFSpec.Vm.Instructions` | Exactly 153 nullary constructors, one per source member | Pure finite vocabulary; no defaults or instances | Generated inductive infrastructure; private exhaustive constructor coverage in `OpsCallerProofs` | Supplied; source member/byte identities checked statically at the pin (out of tree: nothing for that comparison is committed, so it cannot be reproduced from this repository; the committed literals are its transcription) |
| Same source member assignments | `Ops.toByte : Ops → UInt8` | Every opcode, without a frame, gas, hash, monad or admission premise | Pure total literal match; no failure | `Ops.ofByte_toByte`; all 153 source-bound literal encoder pairs in private facade controls | Supplied; ordinary round trip discharged |
| Same source member assignments, and their complement in 0–255 | `Ops.ofByte? : UInt8 → Option Ops` | Every byte | Pure total literal match; `some` for the 153 assigned bytes, `none` for exactly 103 holes, including `0xFE`; no error conversion or charge | `Ops.toByte_ofByte`; all 256 literal decode equations, including every positive and every hole | Supplied; ordinary successful-decode round trip discharged |

Constructors follow lowercase EELS member spelling (`iszero`, `calldataload`,
`slotnum`, `dupn`, and so on); reserved `RETURN` becomes `return_`, following the
existing handler convention. Source `KECCAK` is the single member at `0x20`.
The two enum laws in §7 are its only authored public laws. Private facade clients also
derive encoder injectivity and exclusion of an absent byte through those laws,
without unfolding provider internals. Literal controls separately check source
identity: round trips alone would allow a consistent permutation of byte values.
The source comparison is a static finite enum assignment comparison, qualified
to typed-byte enum use; it executes no EELS runtime. It is out of tree: nothing for
it is committed, so it cannot be reproduced from this repository, and the committed
literal controls are its transcription. Dispatch, `step`, the remaining handlers
and all composed execution/error/resource obligations remain open.

### Supplied raw creation suspension carrier

| EELS split origin | Lean declaration | Domain | Effects / ordered failures | Laws and clients | Status |
|---|---|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/system.py:59–185` (`generic_create`, dispatch at `:133–171`, outcome at `:177–185`) | `STFSpec.Vm.Instructions.CreateRequest` in `STFSpec/Vm/Instructions/CreateRequest.lean`, exported by `STFSpec.Vm.Instructions` | Exactly seven independent fields in §5 order: two unrestricted `Nat` grants, nominal `U256` endowment, two nominal `Address` values, complete `Bytes` init code and `Bool` account-charge flag; no Monad/hash binder or admission premise | Pure raw construction/projection; no state access, hashing, grant computation, preflight, collision, child execution or failure | Generated record infrastructure only; private `CreateRequestCallerProofs` facade clients prove all-field constructor preservation, reconstruction, complete-field equality and every independent update. Public Base observers/laws retain every word/address and ordered byte; complete finite controls cover zero/huge independent grants, full-width values, equal/unequal addresses, empty/duplicate bytes and both booleans | Supplied raw carrier and private client proofs/controls; whole `generic_create` correspondence, producers and consumers unimplemented |

This is the Lean-side suspension interface specified in §5, not an implementation
of an EELS function. The source read identifies where the seven values arise and
where they are consumed. It supplies no source/admission bridge, gas-correctness
proof, child context, handler or resume implementation.

### Supplied raw call suspension carrier

| EELS split origin at `59c1473d` | Lean declaration | Domain | Effects / ordered failures | Laws and clients | Status |
|---|---|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/system.py:340–462` (`GenericCall`; `generic_call` dispatch `:395–439`, outcome `:443–462`) | `STFSpec.Vm.Instructions.CallRequest` in `STFSpec/Vm/Instructions/CallRequest.lean`, exported by `STFSpec.Vm.Instructions` | Exactly fourteen independent fields in §5 order: two unrestricted `Nat` grants, nominal `U256` value, three nominal `Address` values, four `Bool` flags, complete `Bytes` input/code and two nominal `U256` output-window words; no class/monad, WF, coherence or admission premise | Pure raw construction/projection; no preflight, state access, copying from memory, gas calculation, child execution or failure | Generated record infrastructure only; private `CallRequestCallerProofs` facade clients prove complete constructor preservation, reconstruction, all-field determination and all fourteen independent updates. Public Base observations/laws retain all nominal values and ordered bytes; complete asymmetric and negative controls below | Supplied raw carrier and private clients/controls; producers, consumers and whole `generic_call` correspondence unimplemented |

This is the Lean-side suspension carrier of §5. EELS has `GenericCall`, rather
than a Python `CallRequest` class. Source contexts identify grants at `:422–424`,
value/addresses/flags at `:409–418`, input bytes at `:396–400,412`, account-charge
use at `:390,449` and output windows at `:455–462`. The source combines staticness
at `:414`; this raw record merely retains the supplied `isStatic` field. No
producer/staticness policy or source execution/refinement follows from storage.
The carrier neither constrains nor interprets the independently supplied grants,
flags, addresses, byte arrays or output windows.

### Supplied typed results and handler signature

| Source context at `59c1473d` | Lean declaration / exact type | Domain | Effects / ordered failures | Laws and clients | Status |
|---|---|---|---|---|---|
| Project control abstraction of `src/ethereum/forks/amsterdam/vm/__init__.py:147–185`; execution control in `interpreter.py:438–465`; suspension splits in `I/system.py:133–185,395–462` | `STFSpec.Vm.Instructions.StepResult` in `STFSpec/Vm/Instructions/StepResult.lean`, exported by the Instructions facade | Exactly six constructors in §5 order under the original `ctx : FrameCtx`; complete Frame/Bytes/ExceptionalHalt/request payloads. Only call/create require the two existing strict literal depth and parent-stack proofs | Pure typed control carrier; no opcode, admission, state, gas, settlement or failure computation | Generated inductive infrastructure only; private `StepResultCallerProofs` checks exact signatures, complete payload retention/injectivity, all fifteen case distinctions, dependent elimination/reconstruction and both local proof boundaries | Supplied typed carrier; whole source-Evm/control refinement and remaining producers/consumers unimplemented |
| Project handler interface for the R-ENV-3 partition and D17 suspension split; no Python Handler alias | `STFSpec.Vm.Instructions.Handler` in `STFSpec/Vm/Instructions/Handler.lean`, exported by the Instructions facade | Exactly `(ctx : FrameCtx) → Frame → VmM m (StepResult ctx)` for arbitrary `m : Type → Type`, without a Monad or hash instance | Alias formation only; no execution or changed context returned | Private exact alias/application/run-type clients form the alias without class premises, retaining the original ctx index and Core's existing state/error transformer order | Supplied signature; STOP is detailed above; remaining handlers/step/dispatch are unimplemented |

These are the guided Lean control interfaces, not Python counterparts or opcode
implementations. Call/create retain independent complete supplied requests and
frames; their only local proofs are `ctx.depth < STACK_DEPTH_LIMIT` and
`parent.stack.size < STACK_DEPTH_LIMIT`. The literal Core limit is independent of
`ctx.config.limits.stackDepthLimit`. Construction establishes no preflight,
withholding, staticness, gas-progress, child settlement or F11 policy.

**External semantics.** `ethereum_types` `U256` operations used by handlers: `wrapping_add/sub/mul`, `//`, `%`, `to_signed`, `from_signed` (raises for out-of-range; unreachable from these handlers because all results are in range) [V], `from_be_bytes`, `to_be_bytes32`, `bit_length`, `~`, `&`, `|`, `^`, `>>`; `Uint(...)` conversions (exact, unbounded); `U8` for immediates; Python's `pow(b, e, 2^256)`; Python negative list indexing in BLOCKHASH (IndexError beyond length) and in DUPN/SWAPN/EXCHANGE (always in range after the checks). Each must be given by an `EthBase` `U256`/`Nat` law, not by Lean `BitVec` instances (D1).

## 4. Tests

**Supplied opcode controls.**
`STFSpec/Conformance/Vm/Instructions/OpsCallerProofs.lean` imports only the public
Instructions facade. Exact encoder/decoder signatures and both generic laws are
used without frame/context/hash/monad premises. Private clients derive injectivity
and missing-byte exclusion using only those laws. An exhaustive constructor match
checks all 153 literal encoder pairs; 256 ordinary kernel equations bind every
decoded byte to its literal expected constructor or `none` (153 positives and 103
holes). Expectations transcribe the pinned source assignments independently of the
implementation (the source comparison itself is out of tree, see §3); no enum
equality instance or native decision procedure is introduced. Warning-fatal
compilation and the compiled declaration audit cover the actual leaf, facade and
private clients. These are enum controls only; STOP controls are separate below.
The remaining handler and EEST tests remain unimplemented.

**Supplied raw carrier controls.**
`STFSpec/Conformance/Vm/Instructions/CreateRequestCallerProofs.lean` imports only
`STFSpec.Vm.Instructions`. Private generic clients cover the complete seven-field
constructor/projection tuple, reconstruction, equality from all fields and all
seven independent record updates with preservation of every other field. Public
Base word/address/byte observations and byte-construction laws avoid provider
storage unfolding. Four complete deterministic observations include independently
zero and greater-than-256-bit grants, maximum/full-width nominal values, distinct
and equal caller/destination, empty and ordered duplicate init bytes, and both
charging flags. These checks test raw data retention; the opcode/source tests
below remain unimplemented.

**Supplied raw call carrier controls.**
`STFSpec/Conformance/Vm/Instructions/CallRequestCallerProofs.lean` imports only the
public Instructions facade. Ordinary private clients check the exact ordered
constructor and projection tuple, arbitrary complete field retention,
reconstruction, whole-record determination and all fourteen independent updates
while retaining every sibling. Generic Bool parameters admit every flag
combination. Complete byte-list construction and nominal Base numeric laws use
public observers without unfolding provider storage. Four complete deterministic
observations cover zero and independently huge grants, full-width values and
windows, three unequal/equal addresses, empty/ordered duplicate and unequal
input/code bytes, and all-false/all-true/asymmetric flags. Negative complete
observations distinguish swapped destination/code addresses and a changed
flag/input/code/window tuple. Static transfer with nonzero value and output size
larger than code/input remain raw data. Warning-fatal compilation evaluates these
controls; the declaration audit covers leaf/facade/clients. These are storage
checks, with no Python oracle execution, opcode conformance or rollback claim.

**Supplied typed result/signature controls.**
`STFSpec/Conformance/Vm/Instructions/StepResultCallerProofs.lean` imports only the
public Instructions facade. Private clients check all six exact constructor types,
complete arbitrary Frame/Bytes/ExceptionalHalt/request retention and injectivity,
all fifteen distinct constructor pairs, dependent ctx-indexed elimination and
reconstruction, and extraction of both child bounds. Arbitrary type constructors
form and apply the exact Handler alias, including its complete run-result type,
without a Monad premise. Public Stack model/operation laws construct witnesses at
1024 and 1023; equality at the depth limit excludes child cases, and equality at
the stack limit excludes that suspended parent. Generic strict-bound construction
admits every smaller depth and stack, independently of arbitrary configured limits.
All four non-child constructors remain available at both limits with complete
payloads. No Stack/Memory/nominal storage is unfolded. Warning-fatal compilation
and declaration auditing cover the leaf types, facade and private clients; no
Python oracle, source execution, opcode, child/resume or admission proof is claimed.

**Executed arithmetic handler controls.**
`STFSpec/Conformance/Vm/Instructions/ArithmeticCallerProofs.lean` uses only the
public Instructions facade and provider laws. Generic clients consume all forty-two
complete case laws and retain complete result/world equations; concrete Id clients
consume the twenty accounting/progress laws. MUL/DIV success clients also derive
the complete natural-word stack model through `U256.toNat_mul`/`U256.toNat_div`.
SDIV/SMOD clients derive the guarded signed stack models through `U256.toInt_sdiv`/
`U256.toInt_smod`; MOD clients use `U256.toNat_mod`. SIGNEXTEND clients use `U256.toNat_signextend`
and the public k>31/k=31 identity laws. ADDMOD/MULMOD clients retain all
three actual pop witnesses and use `U256.toNat_addmod`/`U256.toNat_mulmod`
to derive the complete natural-word result model.
No private Stack/U256 representation or arbitrary-pure injectivity is used.

`scripts/ArithmeticNativeTests.lean` executes the public handlers on an input-only
TSV catalogue generated by `arithmetic_differential.py`. Both native and interpreted
outputs expose every frame field, control/error tag, potential and explicitly
sampled world sentinels; complete world retention follows from the ordinary laws.
The independent Python model checks all 843 ordered complete observations.
The 196 ADD/SUB/MUL/DIV cases remain an unchanged prefix; 68 cases each for
SDIV, MOD and SMOD follow. The 227 SIGNEXTEND input-only controls in
`arithmetic_signextend_inputs.json` extend that unchanged 400-case prefix. Cases
include empty/singleton/two-operand underflow/OOG ordering, both residual failure
stacks, selected raw prices 0/1/3/5/2^300+7, affordability c-1/c/c+1, independently
unequal other opcode and veryLow prices, full 1024-word stacks, max+1 and 0-1
wrap, both unequal SUB orders, high-bit operands, huge PC, static/depth-limit
contexts, nonempty aligned memory/logs/returnData/sets, signed refund and both
spills. A fixed seed supplies sixteen additional typed word/stack/gas cases per
ADD/SUB opcode; twenty additional cases use a separate fixed seed for each MUL/DIV
opcode. MUL controls include max/max and high-bit products reduced modulo 2^256.
DIV controls distinguish top/next order, zero dividend/divisor/both, exact and
nonexact quotients, dividend below divisor, equal/max operands, and shortage before
zero handling. The selected MUL/DIV field also differs from low and every other
arithmetic opcode field. The new cases include every sign combination, truncation versus floor, signed
min/−1 and min/±2, signed/unsigned high words, dividend-sign remainders, zero
divisors, special-value OOG before result construction, full-stack success/shortage
and a separate fixed seed. Each selected new field differs from low and all sibling
arithmetic prices. Normal and -O strict parser tests reject signed floor or
unsigned quotients, divisor-sign remainders, changed signed overflow, reversed
operands, unsigned MOD zero/order mistakes, selected-price confusion and wrong valid-shaped
products, reversed quotients, zero-divisor shortage bypass and selected-cost changes,
bool/float aliases, altered full fields, malformed framing and changed quantitative/control observations. Native
and interpreted executions use the same saved input bytes. CONTRIBUTING §6.3 and
the CI core job own the current required commands.

The SIGNEXTEND extension covers all 32 retained byte positions at the sign
threshold minus one, at it and above it, including set discarded high bytes.
Explicit zero/one/0x7f/0x80/0xff/0x100, index 30/31/32/2^255/max, operand-order,
identity-branch shortage and full-stack controls retain complete frame/world
observations. Twenty-four additional frozen word/stack/gas inputs vary the full
unsigned index and residual stack. Raw selected prices 0/1/5/2^300+7 differ from
low, veryLow and every sibling arithmetic price. The independent expected value
uses a low-word modulus and sign threshold, with the k>31 guard before width
construction. Normal and -O parser mutations reject wrong retained sign bits,
masking/shift substitutes, truncated or signed huge indices, reversed operands,
zero-to-ones fill, omitted identity charge, wrong selected prices and changed
complete fields, world samples, numeric types or framing.

The 216 ADDMOD/MULMOD input-only cases in `arithmetic_ternary_inputs.json`
append the unchanged 627-case catalogue. Their independently frozen complete
expectations cover all three pop underflows, OOG after all pops, zero-modulus
charging, raw selected prices 0/1/8/2^300+7 and affordability boundaries,
independent sibling/tier prices, unbounded-intermediate discriminators, full
1024-word success/shortage, huge PC and the same complete raw frame recipe.
Normal and -O parser controls retain every earlier negative case and reject
wrapped intermediates, either misplaced modulus, changed residual pop stacks,
zero-modulus charge bypass, wrong selected prices, changed complete fields/world
samples, bool/float aliases and malformed/omitted/reordered/duplicate new rows.

The source mode authenticates the unreplaced pin, original loaded source bytes,
installed dependency RECORDs/locked versions and raw locked numeric/RLP wheels,
using the frozen venv interpreter with -I -B under normal Python and -O as its
docstring specifies. It executes the original ADD/SUB/MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND/ADDMOD/MULMOD, pop/push, charge, signed observations/construction, get_sign, SIGNEXTEND byte conversions and numeric methods
on real Evm/GasMeter objects and a fail-on-access supplied PreState. The sixty
ADD/SUB cases with selected price 3, ninety-two MUL/DIV cases with selected
price 5 and 171 SDIV/MOD/SMOD cases with selected price 5 retain complete source
dataclass observations before and after, including failed-pop/charge partial
states. Each mode preserves those 323 direct calls as a prefix and executes 216 additional
SIGNEXTEND calls at source price 5, including complete source Evm observations.
Those 539 calls remain a prefix; 160 additional ADDMOD/MULMOD calls execute at
source price 8 in each mode. Original Uint multiplication/remainder/equality and
the original three-pop bodies are included in the authenticated function set.
The remaining 144 raw price cases are
mathematical Lean controls without source execution. Actual source exceptions
are caught for comparison without running interpreter settlement; source running/output/error remain
unchanged. This is direct handler-body evidence, not a state backend, trace-hook,
whole source-world relation, interpreter, EEST or guest execution claim.

**Executed STOP controls.**
`StopCallerProofs.lean` imports only the public Instructions facade. Private
clients apply `stop_run` under Monad alone and at Id, deriving complete result
and world retention through that law. `scripts/StopNativeTests.lean` executes
the public handler and emits every frame field through its public model, the
terminal tag and complete output, plus explicitly sampled world sentinels.
The generic law, rather than finite sentinel samples, proves complete world
retention. Four cases cover PC zero, `2^64` and beyond U256 width, empty/two/full
1024-word stacks, aligned nonzero memory, asymmetric six-field raw meters with
zero/huge execution gas, negative refund and both spills, duplicate complete
logs, distinct deletion/warm sets, returnData, static depth-limit contexts and
independent raw configuration/code/jumpdest values. Native and interpreted
outputs use the independent complete catalogue in `stop_differential.py`.
Strict parser regressions in `scripts/test_stop_output_parser.py` run under
normal Python and `-O`, including bool-as-integer and changed-field rejection.
The current commands are in CONTRIBUTING §6.3 and the CI core job.

The source mode in `stop_differential.py` authenticates the unreplaced EELS pin,
compiles original source bytes without cached code, validates loaded dependency
bytes against installed RECORDs and locked versions, and authenticates the raw
locked numeric/RLP wheels. It executes the actual Evm and original STOP directly,
with a fail-on-access supplied PreState, retaining complete before/after source
dataclass observations and the explicit numeric, stack-reversal, byte and set
relations to the four Lean frame cases. Three additional source-only entries
have nonempty output, an existing error, or both. They verify preservation of
those values and stay outside the normal-stop agreement domain in §3. Source
world/context retention is observed separately; this is not a complete source
model for the raw Lean world and its additional metadata. The driver docstring
gives the source invocation. It claims no interpreter dispatch, trace-hook,
reachability, arbitrary-provider execution, EEST or guest result.

**F8 inheritance/producer controls (unimplemented).** Check both child-context
systemAddress equations with a nonliteral parent address, independently varying
the F20 topic. SELFDESTRUCT cases compare complete logs for zero/nonzero balances
and equal/unequal beneficiaries, including all existing static/gas/state-fault
precedence and runner-owned revert/halt discard.

- **EEST fixture areas** (`blockchain_tests/for_amsterdam/…`, plus `for_bpo2toamsterdamattime15k` variants, which need bpo2 execution; the `_engine` copies cover the same areas with their own guest records, GAPS-CROSSCUTTING X5):
  - arithmetic/bitwise/comparison: `ported_static/vmArithmeticTest`, `vmBitwiseLogicOperation`, `stShift`, `constantinople/eip145_bitwise_shift`, `osaka/eip7939_count_leading_zeros`, `frontier/opcodes`;
  - stack: `ported_static/stStackTests`, `amsterdam/eip8024_dupn_swapn_exchange` (66; sources `test_dupn.py`, `test_swapn.py`, `test_exchange.py`, `test_endofcode_underflow.py`, `test_pc_advancement.py`, `test_eip_vectors.py`), `shanghai/eip3855_push0`, `ported_static/stEIP3855_push0`;
  - memory: `ported_static/stMemoryTest`, `stMemoryStressTest`, `cancun/eip5656_mcopy`, `ported_static/stEIP5656_MCOPY`;
  - storage: `ported_static/stSStoreTest`, `stRefundTest`, `istanbul/eip2200_net_gas_metering`, `amsterdam/eip8038_state_access_gas_cost_increase` (`test_sstore_*`, `test_sload_gas.py`), `amsterdam/eip8037_state_creation_gas_cost_increase` (`test_state_gas_sstore.py`, `test_state_gas_cross_frame_refund.py`), `cancun/eip1153_tstore`, `ported_static/stEIP1153_transientStorage`;
  - environment/block: `constantinople/eip1052_extcodehash`, `ported_static/stCodeCopyTest`, `stSelfBalance`, `istanbul/eip1344_chainid`, `cancun/eip7516_blobgasfee`, `cancun/eip4844_blobs` (BLOBHASH), `amsterdam/eip7843_slotnum`, `prague/eip2935_historical_block_hashes_from_state`, `amsterdam/eip8038_*` (`test_ext_code_opcodes_gas.py`);
  - logs and transfer logs: `ported_static/stLogTests`, `vmLogTest`, `amsterdam/eip7708_eth_transfer_logs`;
  - control flow: `ported_static/vmIOandFlowOperations`, `stBadOpcode`;
  - calls: `ported_static/stCallCodes`, `stCallCreateCallCodeTest`, `stCallDelegateCodesCallCodeHomestead`, `stCallDelegateCodesHomestead`, `stDelegatecallTestHomestead`, `stStaticCall` (246), `stStaticFlagEnabled`, `byzantium/eip214_staticcall`, `stNonZeroCallsTest`, `stZeroCallsTest`, `stZeroCallsRevert`, `stEIP150Specific`, `tangerine_whistle/eip150_operation_gas_costs`, `amsterdam/eip8037_*` (`test_state_gas_call.py`);
  - return data: `ported_static/stReturnDataTest`, `byzantium/eip211_return_data`, `stRevertTest`;
  - creates: `ported_static/stCreateTest`, `stCreate2`, `stInitCodeTest`, `stCodeSizeLimit`, `constantinople/eip1014_create2`, `frontier/create`, `cancun/create`, `shanghai/eip3860_initcode`, `frontier/eip2681_limit_account_nonce`, `amsterdam/eip7954_increase_max_contract_size`, `amsterdam/eip7997_deterministic_factory_contract`, `amsterdam/eip8037_*` (`test_state_gas_create.py`);
  - selfdestruct: `cancun/eip6780_selfdestruct`, `amsterdam/eip8246_selfdestruct_no_burn`, `amsterdam/eip8037_*` (`test_state_gas_selfdestruct.py`), `amsterdam/eip8038_*` (`test_selfdestruct_gas.py`);
  - delegation: `prague/eip7702_set_code_tx` (86), `amsterdam/eip8037_*` (`test_state_gas_delegation_pointer.py`);
  - broad: `ported_static/stRandom`, `stRandom2`, `stSystemOperationsTest`, `stSpecialTest`, `stBugs`, `stAttackTest`.
- **EELS unit tests:** none for `instructions/` at e1a316a0 [V].
- **`core` `#guard` cases** (per handler, via `step` on a synthetic frame; a `#guard` evaluates only once every leaf it reaches is implemented, F16): every arithmetic op at `0`, `1`, `2^255`, `2^256−1` (SDIV `−2^255 ÷ −1`, SMOD sign, SAR of negatives by 255/256, SIGNEXTEND k = 30, 31, 32, BYTE 31/32, EXP gas for exponents of 0/1/256/2^255, CLZ 0); `Ops.ofByte?` for all 256 bytes (153 some, 103 none; supplied by kernel `rfl` equations in `OpsCallerProofs`, §4); DUPN/SWAPN/EXCHANGE on every immediate including 91 and 127, the immediate past the end of code, and underflow by one; PUSH32 truncated at end of code; JUMPI with cond 0 to an invalid target; RETURNDATACOPY `(0, 1, 0)` with empty return data (halts); CALLDATALOAD at `2^256−1`; MCOPY overlapping both directions; LOG in a static frame (charges first); SSTORE all 27 `(original, current, new) ∈ {0, x, y}³` combinations with expected execution cost, refund delta and state gas, plus the gas-left = 2300 sentry; CALL with value to a dead account then failing child (state gas refilled); CREATE collision (grant consumed, nonce incremented); BLOCKHASH offsets 0, 1, 256, 257 and one beyond `|block_hashes|`.
- **Adversarial:** stack exactly 1024 then PUSH/DUP; 1023 then CALL chain; memory offset `2^64`, `2^256−1` with size 0 (no charge) and 1 (OOG); CALL gas argument `2^256−1` (capped by 63/64); static context for each state-changing op; RETURNDATACOPY bounds after revert, halt and successful create (empty).
- **Differential:** handler-by-handler against EELS on random frames (random stack, memory, meter, warm sets) using the EELS functions directly, including the order of state reads (recorded through an instrumented `TransactionState`).

## 5. Interface

The opcode API below is **supplied** through `STFSpec.Vm.Instructions`, with
exactly 153 constructors, the two total conversions and exactly the two ordinary
laws in §7. No deriving, instance, alias or public convenience declaration is
added. The remaining dispatch and handler operation signatures are targets.

The exact seven-field `CreateRequest` below is **supplied** through the public
`STFSpec.Vm.Instructions` facade. It has generated record infrastructure only:
no authored defaults, deriving/instances, public helper laws, semantic constructor
or invariant/proof field. Its two Nat grants, addresses, complete init bytes and
charging flag remain independent. The exact fourteen-field `CallRequest` below is
also **supplied** with only
generated record infrastructure. All fields remain complete and independent;
there is no class/monad binder, WF, depth/grant, account/code coherence or
admission premise. Neither carrier adds a default, instance or public helper
law. Raw storage selects no producer/staticness or F11 policy.

The exact six-constructor indexed `StepResult` and class-free `Handler` alias below
are also **supplied** through that facade, with only ordinary generated inductive
infrastructure and no authored default, instance or public helper-law family.
Call/create carry exactly the two displayed strict proofs against the existing
literal limit. The other four cases impose no such proofs. Handler returns only
mutable frame/control data at the original ctx index; its alias forms without a
Monad instance. STOP, ADD, SUB, MUL, DIV, SDIV, MOD, SMOD, SIGNEXTEND, ADDMOD and MULMOD and their local laws are supplied. Child context/frame
construction, remaining handlers, dispatch, step and resume remain unimplemented.

Core §3/§4/§5/§7 supplies nominal OverflowSite/VmFault values. R-GEN-7 still requires actual state-failure propagation, BLOCKHASH availability/ancestor tracking and BLOBBASEFEE checked conversion at their source points; no handler or reachability proof is supplied by the carriers.

```lean
-- Opcodes and dispatch (public)
inductive Ops | stop | add | … | selfdestruct              -- supplied, 153 source members
def Ops.toByte : Ops → UInt8
def Ops.ofByte? : UInt8 → Option Ops
-- Actual operations are generic in the oracle monad (D5), with `[Monad m]` and
-- `[KeccakQuery m]` where needed. Handler alias formation itself is class-free.
abbrev OpM (m : Type → Type) := ExceptT FrameExit (StateT Frame (VmM m))   -- internal: a throw keeps the frame and world
inductive FrameExit | stop (output : Bytes) | revert (output : Bytes) | halt (e : ExceptionalHalt)
                    | call (req : CallRequest) | create (req : CreateRequest)
abbrev Handler (m : Type → Type) := (ctx : FrameCtx) → Frame → VmM m (StepResult ctx)
def opImplementation : Ops → Handler m                    -- total match
def step : Handler m                                      -- R-DSP-2

-- Step results and child requests (public)
inductive StepResult (ctx : FrameCtx) where
  | continue (f : Frame)
  | stop (f : Frame) (output : Bytes)
  | revert (f : Frame) (output : Bytes)
  | halt (f : Frame) (e : ExceptionalHalt)
  | call (parent : Frame) (req : CallRequest) (h : ctx.depth < STACK_DEPTH_LIMIT)
      (hs : parent.stack.size < STACK_DEPTH_LIMIT)          -- the handler has just popped the arguments (F10)
  | create (parent : Frame) (req : CreateRequest) (h : ctx.depth < STACK_DEPTH_LIMIT)
      (hs : parent.stack.size < STACK_DEPTH_LIMIT)
structure CallRequest where
  gas stateGasReservoir : Nat; value : U256; caller to codeAddress : Address
  shouldTransferValue isStatic disablePrecompiles newAccountCharged : Bool
  callData code : Bytes; outOffset outSize : U256
structure CreateRequest where
  gas stateGasReservoir : Nat; endowment : U256; caller contractAddress : Address
  initCode : Bytes; newAccountCharged : Bool
structure ChildOutcome where
  frame : Frame; output : Bytes; error : Option FrameError
  settled : ChildSettled frame error.isSome                -- EthVmCore L-SETTLE; the runner's way of
                                                           -- producing it is open (F11, EthVmRunner §9)

-- Named resume operations (public, pure, total). They take the config for the NEW_ACCOUNT
-- credit on failure (F10); `hs` comes from the `StepResult` constructor.
def resumeAfterCall   (cfg : VmConfig) (parent : Frame) (req : CallRequest)   (c : ChildOutcome) (hs : parent.stack.size < STACK_DEPTH_LIMIT) : Frame
def resumeAfterCreate (cfg : VmConfig) (parent : Frame) (req : CreateRequest) (c : ChildOutcome) (hs : parent.stack.size < STACK_DEPTH_LIMIT) : Frame
def childCtxOfCall   (ctx : FrameCtx) (req : CallRequest)   (h : ctx.depth < STACK_DEPTH_LIMIT) : FrameCtx   -- depth + 1
def childCtxOfCreate (ctx : FrameCtx) (req : CreateRequest) (h : ctx.depth < STACK_DEPTH_LIMIT) : FrameCtx
def childFrame (parent : Frame) (gas reservoir : Nat) : Frame   -- empty stack/memory/logs, copied warm sets

-- Supplied executable handlers:
def stop {m : Type → Type} [Monad m] : Handler m
def add {m : Type → Type} [Monad m] : Handler m
def sub {m : Type → Type} [Monad m] : Handler m
def mul {m : Type → Type} [Monad m] : Handler m
def div {m : Type → Type} [Monad m] : Handler m
def sdiv {m : Type → Type} [Monad m] : Handler m
def mod {m : Type → Type} [Monad m] : Handler m
def smod {m : Type → Type} [Monad m] : Handler m
def addmod {m : Type → Type} [Monad m] : Handler m
def mulmod {m : Type → Type} [Monad m] : Handler m
def signextend {m : Type → Type} [Monad m] : Handler m

-- One handler per opcode (public): stop, add, mul, sub, div, sdiv, mod, smod, addmod, mulmod, exp,
-- signextend, lessThan, greaterThan, signedLessThan, signedGreaterThan, equal, isZero,
-- bitwiseAnd, bitwiseOr, bitwiseXor, bitwiseNot, getByte, bitwiseShl, bitwiseShr, bitwiseSar,
-- countLeadingZeros, keccak, address, balance, origin, caller, callvalue, calldataload,
-- calldatasize, calldatacopy, codesize, codecopy, gasprice, extcodesize, extcodecopy,
-- returndatasize, returndatacopy, extcodehash, blockHash, coinbase, timestamp, number,
-- prevRandao, gasLimit, chainId, selfBalance, baseFee, blobHash, blobBaseFee, slotNumber,
-- pop, mload, mstore, mstore8, sload, sstore, jump, jumpi, pc, msize, gasLeft, jumpdest,
-- tload, tstore, mcopy, pushN (n : Fin 33), dupN (n : Fin 16), swapN (n : Fin 16),
-- dupn, swapn, exchange, logN (n : Fin 5), create, call, callcode, return_, delegatecall,
-- create2, staticcall, revert, selfdestruct : Handler m
def genericCreate … ; def genericCall …                    -- internal, return FrameExit

-- EIP-7702 (public)
def EOA_DELEGATION_MARKER : Bytes; def EOA_DELEGATION_MARKER_LENGTH : Nat; def EOA_DELEGATED_CODE_LENGTH : Nat
def isValidDelegation : Bytes → Bool
def getDelegatedCodeAddress : Bytes → Option Address
def calculateDelegationCost (f : Frame) (a : Address) : VmM m (Bool × Address × Nat)
def resolveDelegatedCodeAddress (costs : GasCosts) (g : GasMeter) (warm : AddrSet) (a : Address) : VmM m (Except ExceptionalHalt (Address × Bool × GasMeter × AddrSet))
def CALL_SUCCESS : U256

-- Relational view (public, for consumers)
inductive Step : (ctx : FrameCtx) → Frame → VmWorld Id → StepResult ctx → VmWorld Id → Prop   -- at m := Id
theorem step_iff : step ctx f w = .ok (r, w') ↔ Step ctx f w r w'
theorem Step.deterministic : Step ctx f w r₁ w₁ → Step ctx f w r₂ w₂ → r₁ = r₂ ∧ w₁ = w₂
```

**State API consumed from `EthState`** (names as in `state_tracker.py`, each `Except WitnessError`): `getAccount`, `getCode` (with the address, for code-access recording at v21.0.0; keyed by hash only at v21.0.6, EthState §10), `getStorage`, `getStorageOriginal`, `getTransientStorage`, `setStorage`, `setTransientStorage`, `isAccountAlive`, `accountDeployable`, `incrementNonce`, `moveEther` (may raise the balance-overflow fault), `createdAccounts`, `trackAncestorAccess` (on `world.tx.block.oldestAncestorOffset`). From EthCodec: `computeContractAddressQ`, `computeCreate2ContractAddressQ` (the `KeccakQuery` forms, D5). From EthBase: `Address.ofU256Masked` (`to_address_masked`).

## 6. Data structures

| Type | Representation | Model / abstraction | Invariant | Persistence | Cost |
|---|---|---|---|---|---|
| `Ops` (supplied) | inductive, 153 constructors; direct literal matches | byte value via `toByte` | both round trips in §7 discharged; 103 unassigned bytes decode to `none` | value | target `ofByte?` O(1) (a 256-entry table or a nibble match beside the literal reference, D25); the current literal 153-arm match compiles to a comparison chain (DEBT-OPS-DECODE); no table allocation or performance measurement claimed |
| `StepResult ctx` (supplied) | inductive | — | `.call/.create` carry `ctx.depth < STACK_DEPTH_LIMIT` and `parent.stack.size < STACK_DEPTH_LIMIT` | value | — |
| `CreateRequest` (supplied) | raw seven-field record; init code uses Base `Bytes` | complete independent fields | none added by the raw carrier; future producers establish §2.5 grants/effects | value | fixed-field record construction/projection; init bytes retained through the Base provider |
| `CallRequest` (supplied) | raw fourteen-field record; `callData`, `code` use Base `Bytes` | complete independent fields | none added by the raw carrier; future producers establish §2.6 grants/effects and input copying | value | fixed-field construction/projection; complete bytes retained through the Base provider |
| `ChildOutcome` | record | — | `ChildSettled` | value | — |
| handlers | functions in `VmM m` (pure at `m := Id`) | — | preserve `Frame` invariants (stack ≤ 1024, memory size % 32 = 0) | — | O(1) for word ops; O(k) for copies/hashes of k bytes, k bounded by gas |

The suspended parent frame (in `.call/.create`) is linear: the runner holds the only reference while the child runs, so memory writes in `resumeAfterCall` are in place (ARCHITECTURE §7: diagnostics must not retain frames).

## 7. Contract and laws

**Supplied opcode laws.** The ordinary byte round trips, the first unconditional and
the second conditioned only on a successful decode, are:

```lean
theorem Ops.ofByte_toByte (o : Ops) : Ops.ofByte? (Ops.toByte o) = some o
theorem Ops.toByte_ofByte (b : UInt8) (o : Ops) (h : Ops.ofByte? b = some o) :
  Ops.toByte o = b
```

Constructor cases prove the first; decoder cases and UInt8 numeric injectivity
prove the second. The latter has only its displayed successful-decode equality,
with no additional well-formedness, execution or oracle hypothesis. Both are
discharged for the supplied enum. This does not implement `opImplementation`,
`step`, invalid-opcode halting or any opcode effect.

**Supplied raw creation request.** Its public contract is exactly the seven fields
in §5, with ordinary generated constructor/projection/reconstruction reduction.
Private complete facade clients establish all-field preservation and independent
updates on arbitrary records without adding public ext/eta/equation laws or
admission. The 63/64 requirement belongs to future producers (§2.5), not a raw
record proof field. No preflight, state/gas correctness, source refinement,
child-context/staticness, settlement or resume law follows from construction.

**Supplied raw call request.** Its public contract is exactly the fourteen fields
in §5, with ordinary generated constructor/projection/reconstruction reduction.
Private complete facade clients establish all-field retention, determination and
independent updates on arbitrary records. No public helper law or extra admission
is introduced. The complete `Bytes` and nominal words are retained without
truncation, zero padding, window clamping, flag combination or code/address
coherence checks. Grant/staticness/source correctness and child/resume effects
belong to future producers and consumers (§2.6); construction proves none of them.

**Supplied typed results and Handler.** Their public contracts are exactly the
six constructors and class-free alias in §5. Private complete facade clients
establish payload retention/injectivity, six-case distinction, dependent
elimination/reconstruction, exact alias/run types and the two strict child proof
boundaries using public provider laws. No authored public helper-law family is
added. The fixed ctx index prevents a handler result from returning a changed
context. Actual operation effects, preservation/progress, source refinement,
child execution, settlement/resume and F11 remain separate obligations.

**Supplied STOP law.** For every `{m : Type → Type} [Monad m]`, context,
complete frame and world, `stop_run` states
`((stop ctx f).run w).run = pure (.ok (.stop { f with pc := f.pc + 1 } Bytes.empty, w))`.
This is one ordinary complete transformer equation, with no LawfulMonad,
KeccakQuery, source-entry or global coherence hypothesis. All other whole fields
are preserved, including returnData, which differs from terminal output.
At Id the underlying pure is the literal successful result/world pair. For an
arbitrary supplied Monad, the law adds no interpretation of pure, no generic
effect observer and no assertion that pure emits no effects or returns a value.
Source agreement uses §3's source/entry premises; reachable entry, trace and
step-level refinement remain open. STOP closes no continuing-iteration gas or
fuel gate.

**Supplied ADD/SUB/MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND local laws.** The following forty-eight ordinary laws are
**discharged** at exactly these types. The thirty-two case laws retain literal underlying
pure under Monad alone and admit every raw selected price; no source/admission,
LawfulMonad or hash premise appears. Residual abstract stacks are witnessed by the
actual public operations, and the success laws prove push availability.

```lean
theorem add_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((add ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w))

theorem add_run_singleton {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      ((add ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w))

theorem add_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeAdd) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ ((add ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w))

theorem add_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : ctx.config.costs.opcodeAdd ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ s₂.push (U256.add x y) = .ok out ∧
      out.toList = U256.add x y :: xs ∧
      ((add ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeAdd } }, w))

theorem add_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((add ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeAdd = f.gasMeter.phi

theorem add_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((add ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeAdd) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi

theorem sub_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((sub ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w))

theorem sub_run_singleton {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      ((sub ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w))

theorem sub_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeSub) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ ((sub ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w))

theorem sub_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : ctx.config.costs.opcodeSub ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ s₂.push (U256.sub x y) = .ok out ∧
      out.toList = U256.sub x y :: xs ∧
      ((sub ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSub } }, w))

theorem sub_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((sub ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeSub = f.gasMeter.phi

theorem sub_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((sub ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeSub) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi

theorem mul_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((mul ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w))

theorem mul_run_singleton {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      ((mul ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w))

theorem mul_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeMul) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ ((mul ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w))

theorem mul_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : ctx.config.costs.opcodeMul ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ s₂.push (U256.mul x y) = .ok out ∧
      out.toList = U256.mul x y :: xs ∧
      ((mul ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeMul } }, w))

theorem mul_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((mul ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeMul = f.gasMeter.phi

theorem mul_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((mul ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeMul) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi

theorem div_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((div ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w))

theorem div_run_singleton {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      ((div ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w))

theorem div_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeDiv) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ ((div ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w))

theorem div_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : ctx.config.costs.opcodeDiv ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ s₂.push (U256.div x y) = .ok out ∧
      out.toList = U256.div x y :: xs ∧
      ((div ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeDiv } }, w))

theorem div_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((div ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeDiv = f.gasMeter.phi

theorem div_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((div ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeDiv) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi

theorem sdiv_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((sdiv ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w))

theorem sdiv_run_singleton {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      ((sdiv ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w))

theorem sdiv_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeSdiv) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ ((sdiv ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w))

theorem sdiv_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : ctx.config.costs.opcodeSdiv ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ s₂.push (U256.sdiv x y) = .ok out ∧
      out.toList = U256.sdiv x y :: xs ∧
      ((sdiv ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSdiv } }, w))

theorem sdiv_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((sdiv ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeSdiv = f.gasMeter.phi

theorem sdiv_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((sdiv ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeSdiv) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi

theorem mod_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((mod ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w))

theorem mod_run_singleton {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      ((mod ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w))

theorem mod_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeMod) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ ((mod ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w))

theorem mod_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : ctx.config.costs.opcodeMod ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ s₂.push (U256.mod x y) = .ok out ∧
      out.toList = U256.mod x y :: xs ∧
      ((mod ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeMod } }, w))

theorem mod_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((mod ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeMod = f.gasMeter.phi

theorem mod_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((mod ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeMod) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi

theorem smod_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((smod ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w))

theorem smod_run_singleton {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      ((smod ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w))

theorem smod_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeSmod) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ ((smod ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w))

theorem smod_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : ctx.config.costs.opcodeSmod ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ s₂.push (U256.smod x y) = .ok out ∧
      out.toList = U256.smod x y :: xs ∧
      ((smod ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSmod } }, w))

theorem smod_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((smod ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeSmod = f.gasMeter.phi

theorem smod_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((smod ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeSmod) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi

theorem signextend_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((signextend ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w))

theorem signextend_run_singleton {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      ((signextend ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w))

theorem signextend_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeSignextend) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ ((signextend ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w))

theorem signextend_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : ctx.config.costs.opcodeSignextend ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ s₂.push (U256.signextend x y) = .ok out ∧
      out.toList = U256.signextend x y :: xs ∧
      ((signextend ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSignextend } }, w))

theorem signextend_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((signextend ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeSignextend = f.gasMeter.phi

theorem signextend_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((signextend ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeSignextend) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi
```

The sixteen accounting/progress laws observe actual Id continuations. They never invert an equation
under arbitrary Monad.pure. Exact potential loss equals the selected raw price;
strict progress requires only that price to be at least one. Zero selected price
therefore permits continuation with unchanged potential. Pinned-source prices 3 for ADD/SUB and 5 for MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND are
separate selected-cost specializations, without a global raw schedule predicate.

**Supplied ADDMOD/MULMOD local laws.** These fourteen ordinary laws are
**discharged**. Ten complete case equations retain literal underlying pure under
Monad alone on every raw selected price. Three actual pop witnesses and the
residual model determine successful and OOG frames; the pair law supplies the
third-pop underflow case. Push availability follows from the existing Stack bound.
The four Id laws observe actual continuations and require only the displayed
selected-price positivity for strict progress.

```lean
theorem addmod_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((addmod ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w))

theorem addmod_run_singleton {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      ((addmod ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w))

theorem addmod_run_pair {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256)
    (h : f.stack.toList = [x, y]) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = [] ∧ ((addmod ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .stackUnderflow, w))

theorem addmod_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y z : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: z :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeAddmod) :
    ∃ s₁ s₂ s₃ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.pop = .ok (z, s₃) ∧ s₃.toList = xs ∧ ((addmod ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₃ } .outOfGas, w))

theorem addmod_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y z : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: z :: xs)
    (hc : ctx.config.costs.opcodeAddmod ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ s₃ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.pop = .ok (z, s₃) ∧ s₃.toList = xs ∧ s₃.push (U256.addmod x y z) = .ok out ∧
      out.toList = U256.addmod x y z :: xs ∧
      ((addmod ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeAddmod } }, w))

theorem addmod_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((addmod ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeAddmod = f.gasMeter.phi

theorem addmod_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((addmod ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeAddmod) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi

theorem mulmod_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((mulmod ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w))

theorem mulmod_run_singleton {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      ((mulmod ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w))

theorem mulmod_run_pair {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256)
    (h : f.stack.toList = [x, y]) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = [] ∧ ((mulmod ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .stackUnderflow, w))

theorem mulmod_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y z : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: z :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeMulmod) :
    ∃ s₁ s₂ s₃ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.pop = .ok (z, s₃) ∧ s₃.toList = xs ∧ ((mulmod ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₃ } .outOfGas, w))

theorem mulmod_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y z : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: z :: xs)
    (hc : ctx.config.costs.opcodeMulmod ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ s₃ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.pop = .ok (z, s₃) ∧ s₃.toList = xs ∧ s₃.push (U256.mulmod x y z) = .ok out ∧
      out.toList = U256.mulmod x y z :: xs ∧
      ((mulmod ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeMulmod } }, w))

theorem mulmod_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((mulmod ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeMulmod = f.gasMeter.phi

theorem mulmod_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((mulmod ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeMulmod) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi
```

**Remaining per-opcode semantic lemmas** [R] (for evm-asm and pancaketh) use the
public Core/State contracts and never unfold their representations. ADD/SUB/MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND/ADDMOD/MULMOD use
the supplied handler laws above, replacing the former literal-3 `step_add` sketch.
Actual `step`, its code-byte premises, `step_iff` and determinism remain unimplemented.

Memory ops: `step_mstore` states `α mem' = α (write (expand mem e) off (be32 v))` with `e = expandBy`, and gas `3 + cost`; storage ops state the read/write through `getStorage`/`setStorage` laws and the exact SSTORE cost/refund/state-gas table of §2.4 as a function `sstoreCharges original current new cold`. CALL/CREATE lemmas state the request fields and the parent frame at suspension (the exact meter after withholding), and separately the resume equations. The lemma set must also give **exception precedence** (R-GEN-2) as in powdr's `StepDeterminism.lean`.

**Child context policy** [C] (F8; local pure helper supplied by EthVmCore §3/§7): for every parent context, request and existing depth proof, `(childCtxOfCall ctx req h).systemAddress = ctx.systemAddress` and `(childCtxOfCreate ctx req h).systemAddress = ctx.systemAddress`. Both retain `ctx.config` as already required. Requests, Handler, step and child-constructor parameter lists are unchanged; no request field or runner dependency carries the address. SELFDESTRUCT uses this inherited context address and the stored F20 topic after the existing ordered gas charges and balance move, before deletion registration. Its source agreement separately instantiates the pinned address/topic; local Step, gas-progress and inheritance laws require no new global address/source predicate.

**Frame invariants** [C]: every handler preserves `stack.size ≤ 1024`, `memory.size % 32 = 0`, `ctx` unchanged (by typing), `f.accessedAddresses ⊆ f'.accessedAddresses` (warm sets only grow within a frame), and `Wf gasMeter`.

**Gas progress** [T] (feeds EthVmRunner G2): the supplied ADD/SUB/MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND/ADDMOD/MULMOD laws above require local selected-price positivity for strict progress on raw configurations. The following whole-iteration target uses a related positive pinned schedule; it is not an unconditional theorem on raw zero-price inputs. For every handler, if the result is `.continue f'` then `f'.gasMeter.phi + 1 ≤ f.gasMeter.phi` (every non-terminal opcode has execution cost ≥ 1 [V: minimum costs are JUMPDEST 1, `BASE` 2; the only zero-cost handlers, STOP/RETURN/REVERT, are terminal]; state-gas charges, credits and repays leave Φ unchanged). For `.call parent req`: `parent.gasMeter.phi + req.gas + 100 ≤ f.gasMeter.phi`, where `req.gas` already includes the stipend: the charge is `access + transfer + delegation + mem + g'` and `req.gas = g' + stipend`, with `access ≥ 100` and `transfer − stipend = 11300 − 2300` when a stipend is paid [I]. The preflight-failure path (`.continue`) satisfies the same bound through `restore_child_gas`. For `.create`: `parent.gasMeter.phi + req.gas + 12000 ≤ f.gasMeter.phi`; the collision path (`.continue`) loses `12000 + g` [I]. For the resume operations: `(resumeAfterCall cfg p r c hs).gasMeter.phi = p.gasMeter.phi + c.frame.gasMeter.phi` (EthVmCore `L-INC`; the NEW_ACCOUNT credit preserves Φ).

**Resume laws** [C]: return-data rules of ARCHITECTURE §6 (`CALL`: child output in all three outcomes; `CREATE`: ∅ on success, child output on failure); stack effect (one push); memory: only the window `[outOffset, outOffset + min(outSize, |output|))` changes; logs/deletions/warm sets merged iff success; `pc` advanced by 1.

**Delegation** [C]: `isValidDelegation (EOA_DELEGATION_MARKER ++ a) = true` for every 20-byte `a`; `getDelegatedCodeAddress` inverts it.

**Relational view** [R]: `step_iff` and `Step.deterministic`; a small-step relation `Steps` for straight-line code with additive gas (`GasSteps`-style) for consumers.

### Informal correctness argument

**Claim.** Each opcode's one executable handler refines the pinned instruction, including the order of guards, charges, observations, faults and child requests.

**Premises.** EthVmCore/State contracts; canonical opcode decoding; valid frame/config invariants; source correspondence for each claimed handler; explicit distinction between FrameError and global VmFault.

**Argument.** For an opcode, symbolically execute the Python checks and the handler in the same order. Relate popped operands through Stack.toList, memory through its window observer and state through overlay lookups. At each guard, prove that both sides select the same failing branch, including observations made before that failure. Successful primitives preserve the relation and yield the same next PC, stack, output and meter. CALL/CREATE stop at a request containing the already withheld gas, child context and resume data. Child execution is supplied by the runner; resume then uses the child settlement contract to update return data, memory, stack, logs and gas. This factorisation covers the source operation without adding a second opcode implementation. The executable step/relation equivalence follows by cases on StepResult; fidelity to EELS is a separate per-handler obligation.

**Open obligations.** Expand every source-map group into exact guard/effect equations, finish resume preconditions and cross-call gas inequalities, and audit implicit Python failures. Proofs must compare selected observations and error priority, not only successful whole-state results.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthVmCore`, `EthHash`, `EthCodec`
- **Used by:** `EthVmRunner` (calls `step`, `childCtxOf*`, `childFrame`, the resume operations and `resolveDelegatedCodeAddress`); `EthBlock` (uses `isValidDelegation`).
- **Seams:** provides `Handler`, `step`, `StepResult`, requests and resume operations; consumes EthVmCore's frame, meter and memory contracts, EthState's lookup/overlay laws (through `VmM m`), `KeccakQuery` (KECCAK; CREATE and CREATE2 addresses through EthCodec's `…Q` forms), RLP (CREATE address). Relies on: the frame it receives satisfies the EthVmCore invariants; the runner passes back a `ChildOutcome` built from a frame with `ChildSettled`. The supplied `.call/.create` types guarantee only `depth < STACK_DEPTH_LIMIT` and room in the parent stack for the result (`hs`). Future handler contracts additionally require balance and nonce preflight and the parent meter already withholding the grant.

## 9. Open decisions

- **D1**: handlers use only `U256` observer laws; exercise 4.
- **D5** (broad scope, monad-parametric; B10): **every** keccak goes through `KeccakQuery`, including the KECCAK opcode and CREATE/CREATE2 address derivation, so handlers live in `VmM m`. Execution instantiates `m := Id`, where the instance is concrete `keccak256`. A narrower scope needs the agreement prototype's justification.
- **D14** (accepted): halts are frame exits (O8); BLOCKHASH's missing ancestor and the BLOBBASEFEE overflow are `VmFault`s in CONTRACT O13 (R-GEN-7).
- **D26** (accepted): secp256k1 recovery stays in the runner; handlers do not import it.
- **D27** (accepted): `Log` is `EthVmCore`'s; LOG0–LOG4 and the EIP-7708 transfer log reuse it.
- **D13**: the parent frame in `.call/.create` is a value; both a recursive runner and a continuation stack can consume it.
- **D17**: accepted; this module is its opcode side. Replacement exercises 1 and 3 test that memory/gas changes stay within handlers' contracts.
- **D18**: an unoptimised handler (for example MCOPY via intermediate copy) is correct and complete; performance debt only.
- NEW-VM-1: resolved by D14, CONTRACT O13 and DECISIONS B14 (Q23) (EthVmCore R-EXC-2).
- NEW-VM-2: resolved by DECISIONS B7 (Q24): halts are values.
- **F11** (open): how the runner produces the `ChildSettled` proof in `ChildOutcome` (EthVmRunner §9).

## 10. Gaps

- **Opcode bytes supplied; dispatch open:** §3 owns the exact 153-member enum, total conversions, two discharged ordinary laws and complete literal byte controls. `opImplementation`, `step`, invalid-opcode halting and all handlers/laws except the supplied STOP/ADD/SUB/MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND/ADDMOD/MULMOD slices remain unimplemented. The enum fixes no future `swapN` argument interpretation, CALL staticness or F11 policy; source-runtime, composed resource, fuel and guest obligations remain open.

- **Raw request carriers supplied; execution open:** §3 owns the exact `CreateRequest` and `CallRequest` types and private complete facade controls. `genericCreate`, CREATE/CREATE2 preflight, ordered state/gas effects, grant computation, collision and source/admission bridge, CALL-family/`genericCall` producers and their source/admission bridge, child context/frame, `ChildOutcome` and resume remain unimplemented. The raw carriers add no admission/staticness policy and resolve neither F11 nor fuel, host-resource, guest or EEST obligations.

- **Typed results/signature supplied; execution open:** §3/§5/§7 own the exact six-constructor indexed `StepResult`, class-free `Handler` alias and private complete facade clients. Only the two strict local child bounds are carried. The STOP/ADD/SUB/MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND/ADDMOD/MULMOD effects and their complete local laws are supplied separately above. Remaining opcode effects, dispatch/step/Step relation, whole source-Evm/control refinement, child execution/settlement/resume, gas/staticness/admission and F11 remain open; these types close no fuel, resource, guest or readiness gate.

- **Core settlement assertion boundary:** EthVmCore §3/§5/§7 supplies the raw
  ChildSettled predicate and constructive Decidable instance only. Actual non-top
  committed-spill-zero initialization/preservation, call/create settlement and
  snapshots, returned proof production, incorporation and child/resume remain open.
  This logical decision procedure chooses neither F11 production option and
  supplies no runtime check, settled executor or generic Q83 effect bridge.

- **F8 address inheritance and SELFDESTRUCT:** both child-context field equations and actual SELFDESTRUCT emission remain unimplemented. Require complete logs under independently varied nonliteral address/topic, nested CALL/CREATE inheritance, zero balance, unequal/equal beneficiary and existing gas/static/state-fault ordering. Preserve revert/halt log discard through the runner; no new guard or raw-context admission is selected.

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **STOP/ADD/SUB/MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND/ADDMOD/MULMOD supplied; remaining per-opcode laws open.** §3/§7 own `stop_run` and the sixty-two ADD/SUB/MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND/ADDMOD/MULMOD local laws, including raw selected-cost accounting and conditional Id progress. Their local source-entry/price boundaries and bounded direct-source tests are explicit; complete source-model, reachable-entry and trace refinement remain open. Remaining per-opcode/precedence lemmas, `step_iff` and determinism are specifications only; private raw-carrier and typed-result/signature clients prove no execution semantics.
- **Gas progress for the CALL family** is [I]: the inequality "execution charge of the calling opcode ≥ stipend + 1" must be proved for all four call opcodes, both preflight-failure paths, and the EIP-150 branch where `gas_left < extra + mem` (which fails the charge, so it is a halt, not a continue).
- **BLOCKHASH in the stateless setting**: if the witness carries fewer than `number − n` headers, EELS raises `IndexError` (`I/block.py:58`), which reaches the inner catch-all (`stateless.py:294`). This is witnessed by the fixture `validation_headers_missing_oldest_blockhash_ancestor` and classified as O13 with `VmFault.ancestorHashUnavailable`. The named carrier is supplied by Core; actual handler/check/propagation implementation and its source refinement remain open, as does constructor freezing (DECISIONS B14).
- **BLOBBASEFEE `U256` overflow** (`I/environment.py:607`) is argued reachable on an unanchored parent header (O13), but not witnessed. It also costs `taylor_exponential` time proportional to its result (DISC-002). NUMBER, GASLIMIT and BASEFEE cannot overflow (R-GEN-7).
- **Read-order fidelity** (R-GEN-1) is required for BAL and witness observations but has no dedicated test harness; EEST `eip7928_block_level_access_lists` (211 fixtures) is the only indirect check.
- **`to_address_masked`** is owned by `EthBase`, and **`compute_contract_address`, `compute_create2_contract_address`** by `EthCodec` (A1, A2) (`utils/address.py`); this spec assumes their behaviour (low 20 bytes; `keccak(rlp([sender, nonce]))[12:]`; `keccak(0xff ‖ sender ‖ salt ‖ keccak(init))[12:]`) [I: not re-read].
- **`account_deployable` ignores storage** [V], so a CREATE to an address with only storage succeeds after `destroy_storage` in `process_create`; relies on EthState's `destroy_storage` semantics.
- **EIP-8246 detail**: the balance-preserving clear is in `fork.py`/`state_tracker.py` (not read here in full); the SELFDESTRUCT handler spec depends on it only through `accounts_to_delete`.
- **Static LOG precedence** (charge and expand before the static check) is observable only in traces; traces are diagnostics (§7 of ARCHITECTURE), so the Lean trace schema must decide whether it records it.
- **`Ops` enum line numbers**: the constant block spans `I/__init__.py:32–220`; the `partial` aliases (push1…) are not inventory items and are covered by `pushN`/`dupN`/`swapN`/`logN`.
- **Precompile-addressed code under delegation** (R-DEL-4) is inferred from the runner branch; no dedicated fixture located.
