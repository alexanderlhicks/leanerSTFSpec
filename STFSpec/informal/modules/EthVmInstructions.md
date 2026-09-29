# `EthVmInstructions`: one handler per opcode, `StepResult`, child requests and resume operations

*Status: informal specification, draft. Date: 2026-09-29. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F1, F8, F10, F11 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D1, D5, D13, D14, D17, D18, D26, D27 · questions: B7/Q24, B8/Q1, B14/Q23, F11.*

Paths in `file:line` references are relative to `src/ethereum/forks/amsterdam/vm/` unless stated otherwise; `I/` abbreviates `instructions/`. "[V]" marks a claim checked by reading the pinned source; "[I]" an inference.

## 1. Purpose

`EthVmInstructions` (root `STFSpec.Vm.Instructions`, layer L3) defines the semantics of every Amsterdam opcode as a non-recursive handler that maps a frame to a `StepResult`: a successor frame, a normal stop with output, a revert with output, an exceptional halt, or a **child request** (call or create) that the runner executes before calling a **named resume operation** on the suspended parent (D17). It also owns the opcode enumeration and its dispatch table (`I/__init__.py`), the single-step function `step`, and EIP-7702 delegation-designator parsing and call-target resolution. It must not import the runner or precompile implementations (`scripts/boundaries.toml`); CALL/CREATE semantics therefore stop at the request and resume at the outcome. The per-opcode lemmas stated here are the refinement interface for evm-asm's dispatch-loop proofs.

## 2. Requirements

### 2.1 General rules (apply to every handler)

- **R-GEN-1 Step order.** Each handler must perform its sub-steps in the EELS order: (1) static-context check, where EELS does it first; (2) pops (`StackUnderflowError`); (3) gas computation and `check_gas`/`charge_gas`; (4) state reads and writes; (5) memory expansion; (6) pushes; (7) `pc` update. The order matters beyond the exception name: **state reads are persistent observations** that survive a later exceptional halt or revert (ARCHITECTURE §6; they feed the BAL and the witness access record), so a read must happen exactly when EELS performs it, and not before a gas check that precedes it in EELS. EIP-8038's "STATE ACCESS after state-independent gas check" structure (`I/system.py:494–543`, `I/storage.py:85–116`) exists for this reason [V: comments].
- **R-GEN-2 Precedence among exceptional halts.** Where two halt conditions hold, the first in EELS order wins. All exceptional halts have the same guest-visible effect (O8), so precedence is observable only through traces and through which reads happened before the halt; both must match. Specific orders: most arithmetic/stack-consuming ops pop before charging (underflow beats OOG); DUP*/SWAP*/DUPN/SWAPN/EXCHANGE charge before the depth check (OOG beats underflow) (`I/stack.py:103–105, 135–137, 232–240`); push-producing ops charge before pushing (OOG beats overflow); CREATE/CREATE2/SSTORE/TSTORE/SELFDESTRUCT check the static flag **before** popping; CALL checks it after popping and only for non-zero value; LOG checks it after charging and expanding memory (`I/log.py:71–73`).
- **R-GEN-3 Memory.** Every memory-touching handler computes `calculate_gas_extend_memory` for its windows, charges `base + per-word + expansion` in one `charge_gas`, then expands, then reads/writes. Windows with size 0 never expand memory and never fail, whatever their offset. Offsets and sizes are full 256-bit values; conversion to `Nat` must be exact (never truncated to 64 bits before the gas check).
- **R-GEN-4 Words.** Arithmetic is modulo 2^256 through the `U256` API (EthBase, D1): signed operations use two's complement; `x / 0 = 0`, `x % 0 = 0`; ADDMOD/MULMOD compute over unbounded integers before reducing.
- **R-GEN-5 PC.** Handlers advance `pc` by 1, except PUSHn (`1 + n`, `I/stack.py:82`), DUPN/SWAPN/EXCHANGE (2, `:245, 281, 317`), JUMP/JUMPI (target or `pc+1`). Terminal handlers' `pc` updates are irrelevant. Immediate bytes beyond the end of code read as zero (`buffer_read`).
- **R-GEN-6 Invalid opcodes.** A byte that is not in `Ops` (103 of 256 values, including `0xFE`) causes `InvalidOpcode(byte)` before any charge (`interpreter.py:445–448`). Running off the end of code (`pc ≥ |code|`) is a normal stop with empty output (`interpreter.py:444`).
- **R-GEN-7 Non-EVM faults.** State-access failures (`WitnessError`, O4), BLOCKHASH beyond the available headers, and the BLOBBASEFEE `U256` conversion overflow propagate as `VmFault` (EthVmCore R-EXC-2), never as exceptional halts. The last two are CONTRACT O13 members. NUMBER, GASLIMIT and BASEFEE cannot overflow their `U256` cast: the SSZ payload fields are `uint64`, `uint64` and `uint256`.

### 2.2 Opcode table

Stack columns list operands top first. "mem" = memory-expansion cost of the listed windows; `w(n) = ceil32(n)/32`; warm/cold = 100/3000 for accounts and 100/2100 for slots, with the address/slot added to the frame's warm set. Costs are the `GasCosts` names of `gas.py:178–259`; state gas is `StateGasCosts`. "→ c" = continue.

**Stop, arithmetic, comparison, bitwise (all → c except STOP)**

| Hex | Name | EELS | Pops → pushes | Gas | Semantics / halts |
|---|---|---|---|---|---|
| 00 | STOP | `I/control_flow.py:25` | – | 0 | `.stop` output ∅ |
| 01 | ADD | `I/arithmetic.py:28` | a b → a+b | 3 | wrapping |
| 02 | MUL | `:82` | a b → a·b | 5 | wrapping |
| 03 | SUB | `:55` | a b → a−b | 3 | wrapping |
| 04 | DIV | `:109` | a b → a/b | 5 | b = 0 → 0 |
| 05 | SDIV | `:142` | a b → a÷b | 5 | signed, truncates toward 0; b = 0 → 0; (−2^255)÷(−1) = −2^255 (`U255_CEIL_VALUE`, `:139`) |
| 06 | MOD | `:175` | a b → a mod b | 5 | b = 0 → 0 |
| 07 | SMOD | `:205` | a b → sign(a)·(\|a\| mod \|b\|) | 5 | b = 0 → 0 |
| 08 | ADDMOD | `:235` | a b N → (a+b) mod N | 8 | unbounded sum; N = 0 → 0 |
| 09 | MULMOD | `:266` | a b N → (a·b) mod N | 8 | unbounded product; N = 0 → 0 |
| 0A | EXP | `:297` | a b → a^b mod 2^256 | 10 + 50·⌈bitlen(b)/8⌉ | |
| 0B | SIGNEXTEND | `:334` | k x → x' | 5 | k > 31 → x; else extend bit `8k+7` |
| 10–15 | LT GT SLT SGT EQ ISZERO | `I/comparison.py:24, 77, 51, 104, 130, 157` | a b → 0/1 (ISZERO: a → 0/1) | 3 | signed variants via two's complement |
| 16–19 | AND OR XOR NOT | `I/bitwise.py:24, 49, 74, 99` | a b → r (NOT: a → ~a) | 3 | |
| 1A | BYTE | `:123` | i w → byte | 3 | i ≥ 32 → 0; byte `i` counted from the most significant |
| 1B | SHL | `:159` | s v → v≪s | 3 | s ≥ 256 → 0 |
| 1C | SHR | `:189` | s v → v≫s | 3 | s ≥ 256 → 0 |
| 1D | SAR | `:219` | s v → v≫ₐs | 3 | s ≥ 256 → 0 or 2^256−1 by sign |
| 1E | CLZ | `:251` | x → 256 − bitlen(x) | 5 (LOW) | EIP-7939; CLZ 0 = 256 |

**KECCAK256, environment, block**

| Hex | Name | EELS | Pops → pushes | Gas | Semantics / halts |
|---|---|---|---|---|---|
| 20 | KECCAK256 | `I/keccak.py:30` | off sz → h | 30 + 6·w(sz) + mem(off,sz) | keccak256 of the window, as a `KeccakQuery` call (D5) |
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
| 40 | BLOCKHASH | `I/block.py:22` | n → h | 20 | 0 unless `n < number ≤ n + 256`; else `block_hashes[−(number − n)]` and `track_ancestor_access(number − n)` (a block-level observation, never reverted). If `number − n > \|block_hashes\|` EELS raises `IndexError` (`I/block.py:58`) → `VmFault.ancestorHashUnavailable` (O13) [V: `stateless.py:254` supplies only the witness headers; fixture `validation_headers_missing_oldest_blockhash_ancestor`] |
| 41 | COINBASE | `:72` | → coinbase | 2 | |
| 42 | TIMESTAMP | `:106` | → time | 2 | |
| 43 | NUMBER | `:140` | → number | 2 | `U256(number)` |
| 44 | PREVRANDAO | `:173` | → randao | 2 | |
| 45 | GASLIMIT | `:206` | → limit | 2 | |
| 46 | CHAINID | `:239` | → chain id | 2 | |
| 47 | SELFBALANCE | `I/environment.py:513` | → bal | 5 | read after charge |
| 48 | BASEFEE | `:539` | → base fee | 2 | `U256(base_fee_per_gas)`; cannot overflow (SSZ `uint256`) |
| 49 | BLOBHASH | `:562` | i → h | 3 | `i < \|hashes\|` → hash, else 0 |
| 4A | BLOBBASEFEE | `:589` | → price | 2 | `U256(calculate_blob_gas_price(excess_blob_gas))` (`:607`); overflow → `VmFault.u256Overflow .blobBaseFee` (O13, argued reachable) |
| 4B | SLOTNUM | `I/block.py:269` | → slot | 2 | EIP-7843: `block_env.slot_number` |

**Stack, memory, storage, control flow**

| Hex | Name | EELS | Pops → pushes | Gas | Semantics / halts |
|---|---|---|---|---|---|
| 50 | POP | `I/stack.py:29` | a → | 2 | pop before charge |
| 51 | MLOAD | `I/memory.py:93` | off → word | 3 + mem(off,32) | |
| 52 | MSTORE | `:30` | off v → | 3 + mem(off,32) | big-endian 32 bytes |
| 53 | MSTORE8 | `:61` | off v → | 3 + mem(off,1) | low byte |
| 54 | SLOAD | `I/storage.py:37` | k → v | warm/cold (slot) | warm-set add before the charge; read after |
| 55 | SSTORE | `:68` | k v → | see §2.4 | static first |
| 56 | JUMP | `I/control_flow.py:48` | d → | 8 | `d ∉ jumpdests` → `InvalidJumpDestError` (after charge) |
| 57 | JUMPI | `:73` | d c → | 10 | `c = 0` → `pc+1` (d not checked); else as JUMP |
| 58 | PC | `:104` | → pc | 2 | |
| 59 | MSIZE | `I/memory.py:123` | → \|mem\| | 2 | always a multiple of 32 |
| 5A | GAS | `I/control_flow.py:128` | → gas_left | 2 | value **after** this charge; execution gas only (not the reservoir) |
| 5B | JUMPDEST | `:152` | – | 1 | |
| 5C | TLOAD | `I/storage.py:164` | k → v | 100 | transient storage (EIP-1153) |
| 5D | TSTORE | `:189` | k v → | 100 | static first; revertible (part of the tx snapshot) |
| 5E | MCOPY | `I/memory.py:146` | dst src len → | 3 + 3·w(len) + mem([(src,len),(dst,len)]) | read-then-write (overlap-safe) |
| 5F | PUSH0 | `I/stack.py:52` | → 0 | 2 | |
| 60–7F | PUSH1…PUSH32 | `:52` (`push_n`) | → imm | 3 | `n` bytes after `pc`, zero-padded past end; `pc += 1+n` |
| 80–8F | DUP1…DUP16 | `:85` (`dup_n`) | → copy of i-th | 3 | charge, then `i > size` → underflow, then push (overflow) |
| 90–9F | SWAP1…SWAP16 | `:113` (`swap_n`) | swap top, (i+1)-th | 3 | charge, then `i ≥ size` → underflow |
| E6 | DUPN | `:216` | → copy of n-th | 3 | EIP-8024; charge; `n = decode_single(imm)` (`InvalidParameter` for imm 91…127); `n > size` → underflow; `pc += 2` |
| E7 | SWAPN | `:248` | swap 1st, (n+1)-th | 3 | as DUPN; `n + 1 > size` → underflow |
| E8 | EXCHANGE | `:284` | swap (n+1)-th, (m+1)-th | 3 | `(n,m) = decode_pair(imm)` (invalid 82…127); `max(n,m)+1 > size` → underflow |

**Logs and system**

| Hex | Name | EELS | Pops → pushes | Gas | Semantics / halts |
|---|---|---|---|---|---|
| A0–A4 | LOG0…LOG4 | `I/log.py:32` (`log_n`) | off sz t₁…tₙ → | 375 + 8·sz + 375·n + mem | charge, expand, **then** static → `WriteInStaticContext`; append `Log(target, topics, data)` |
| F0 | CREATE | `I/system.py:195` | e off sz → addr/0 | 12000 + mem + 2·w(sz); state gas via `generic_create` | §2.5 |
| F1 | CALL | `:472` | g a v io is oo os → 0/1 | §2.6 | §2.6 |
| F2 | CALLCODE | `:599` | g a v io is oo os → 0/1 | §2.6 | no static check |
| F3 | RETURN | `:314` | off sz → | mem | `.stop` with output = window |
| F4 | DELEGATECALL | `:788` | g a io is oo os → 0/1 | §2.6 | |
| F5 | CREATE2 | `:249` | e off sz salt → addr/0 | 12000 + 6·w(sz) + mem + 2·w(sz) | §2.5 |
| FA | STATICCALL | `:891` | g a io is oo os → 0/1 | §2.6 | |
| FD | REVERT | `:994` | off sz → | mem | `.revert` with output = window (gas not forfeited) |
| FF | SELFDESTRUCT | `:713` | b → | §2.7 | static first |

### 2.3 Dispatch

- **R-DSP-1** `Ops` (`I/__init__.py:32–220`) has exactly 153 constructors with the byte values listed; `op_implementation` (`:223–377`) maps each to its handler. The Lean dispatch must be a total `match` on `Ops` (not a map lookup), with `Ops.ofByte? : UInt8 → Option Ops` and the round-trip laws.
- **R-DSP-2** `step ctx f` must return `.stop f ∅` if `f.pc ≥ |ctx.code|`, `.halt f (invalidOpcode b)` if `Ops.ofByte? b = none`, and otherwise the handler's result. `step` never recurses and never changes `ctx`.

### 2.4 SSTORE (`I/storage.py:68–161`; EIP-2200, EIP-3529 refund values, EIP-8037 state gas, EIP-8038 access)

In order: (1) static → `WriteInStaticContext`; (2) pop key, new; (3) `cost := cold ? 2100 : 100`; (4) `check_gas(max(cost, 2301))`: the EIP-2200 sentry, **before any state read**; (5) warm the slot; (6) read `original` (`get_storage_original`) then `current`; (7) if `original = current ≠ new`: `cost += 10000` (`STORAGE_WRITE`); (8) if `current ≠ new`: `+11616` if `original ≠ 0 ∧ current ≠ 0 ∧ new = 0`; `−11616` if `original ≠ 0 ∧ current = 0`; `+10000` if `original = new` (each independently, on the `Int` refund counter); (9) state gas `97920` (`STORAGE_SET`) if `original = current = 0 ≠ new`; (10) if `current ≠ new ∧ original = new = 0`: `credit_state_gas_refund(97920)` **before** the charges; (11) `charge_gas(cost)`, then `charge_state_gas(state)`; (12) `set_storage`. A naive port that charges before step (10) can fail with OOG where EELS succeeds, because the credit can refill `gas_left` from the spill.

### 2.5 CREATE / CREATE2 and `generic_create` (`I/system.py:66–311`)

- **Handler part.** Static → halt; pop `endowment, offset, size` (CREATE2 also `salt`); charge as in the table; **then** `size > MAX_INIT_CODE_SIZE (131072)` → `OutOfGasError` (`:227, 291`); expand memory; address = `compute_contract_address(target, nonce(target))` (reads the account) or `compute_create2_contract_address(target, salt, init_code)`, both through `KeccakQuery` (EthCodec's `…Q` forms, D5).
- **Preflight** (`generic_create`, `:89–107`): read the init code; set `return_data := ∅`; if `balance(target) < endowment` or `nonce(target) = 2^64 − 1` or `depth + 1 > STACK_DEPTH_LIMIT`: push 0 and continue (nothing withheld; the opcode's own charge stays).
- **Destination access** (`:112–116`): warm the address; `newAccountCharged := ¬ is_account_alive(addr)`; if so `charge_state_gas(NEW_ACCOUNT = 183600)` (may halt with OOG).
- **Grant** (`:120`): `g := withhold_create_gas` (all but 1/64 of `gas_left`).
- **Collision** (`:125–128`): if `¬ account_deployable(addr)` (nonce ≠ 0 or code non-empty; storage is ignored): `increment_nonce(target)`, push 0, continue; `g` is **consumed** (not returned) and the reservoir is not drained.
- **Dispatch** (`:132–178`): `R := drain_state_gas_reservoir`; `increment_nonce(target)` (outside the child's snapshot: it survives a child failure); return `.create parent req` with child parameters `caller = target`, `current_target = addr`, `value = endowment`, empty call data, `code = init_code`, `code_address = none`, `should_transfer_value`, not static, precompiles enabled, meter `(g, R, baseline R)`, copies of the warm sets.
- **`resumeAfterCreate`** (`:184–192`, then `pc += 1`, `:246`/`:311`): `incorporate_child`; if the child failed: `credit_state_gas_refund(NEW_ACCOUNT)` when `newAccountCharged` (the amount comes from the config, which is why resume takes it, F10), `return_data := child.output` (revert data, or ∅ after a halt), push 0; else `return_data := ∅` and push the address. Successful creation never exposes the deployed code as return data (ARCHITECTURE §6).

### 2.6 CALL family and `generic_call` (`I/system.py:376–991`)

- **CALL** (`:472`): pop 7 (`to` masked); `static ∧ value ≠ 0` → halt; `mem` over the input then the output window; `access := cold(to) ? 3000 : 100`; `transfer := value ≠ 0 ? 11300 : 0`; `check_gas(access + transfer + mem)`; warm `to`; `calculate_delegation_cost(to)` (reads `to`'s account and code); if delegated: add its warm/cold cost, `check_gas` again, warm the delegate; read the code of `code_address`; `charge_gas(extra + mem)`; if `value ≠ 0 ∧ ¬alive(to)`: `charge_state_gas(NEW_ACCOUNT)` (`newAccountCharged`); **then** compute the forwarded gas from the *remaining* `gas_left` with `calculate_message_call_gas(value, gas, gas_left, 0, 0)` and charge it; drain the reservoir; expand memory; read the sender balance.
- **CALLCODE** (`:599`): `to := current_target`, cold/warm and delegation on the popped `code_address`; no static check (a self-transfer); `calculate_message_call_gas(value, gas, gas_left, mem, extra)` and `charge_gas(cost + mem)`; no account-creation charge; `insufficient_balance` checked.
- **DELEGATECALL** (`:788`): pop 6; no transfer cost; child keeps the parent's `caller` and `value`, `to = current_target`, `should_transfer_value = false`; no balance check.
- **STATICCALL** (`:891`): pop 6; child `value = 0`, `is_static = true`.
- **`generic_call`** preflight (`:388–400`): `return_data := ∅`; if `depth + 1 > STACK_DEPTH_LIMIT` or insufficient balance: `restore_child_gas(sub_call, R)` (the stipend included), credit `NEW_ACCOUNT` if charged, push 0, continue. Otherwise read the call data from memory and return `.call parent req` (child `is_static = is_staticcall ∨ ctx.isStatic`, `disable_precompiles = is_delegated`, copies of warm sets, meter `(sub_call, R, baseline R)`).
- **`resumeAfterCall`** (`:453–469`, then `pc += 1`): `incorporate_child`; `return_data := child.output` (for success, revert and halt alike: ∅ after a halt); credit `NEW_ACCOUNT` on failure if charged (amount from the config, F10); push 0 or `CALL_SUCCESS = 1`; write `child.output[0 : min(out_size, |output|)]` at `out_offset` (inside the already-expanded window).

### 2.7 SELFDESTRUCT (`I/system.py:713–785`; EIP-6780, EIP-8246)

Static → halt; pop `b` (masked); `cost := 5000 + (cold(b) ? 3000 : 0)`; `check_gas(cost)`; warm `b`; if `¬alive(b) ∧ balance(target) ≠ 0`: state gas `NEW_ACCOUNT` and execution `+9000`; `charge_gas` **before** `charge_state_gas`; move the whole balance to `b` (a no-op when `b = target`); if `b ≠ target`, `emit_transfer_log` (EIP-7708; nothing for 0); if `target ∈ created_accounts` add it to `accounts_to_delete`; `.stop` with output ∅. Deletion happens after the transaction via `clear_account_preserving_balance` (`fork.py:1134–1135`, EthBlock), so under EIP-8246 a self-destruct to itself of an account created in the same transaction **keeps** its balance [V: the called function's name and the EIP title; its body is EthState's].

### 2.8 EIP-7702 delegation (`eoa_delegation.py`)

- **R-DEL-1** `is_valid_delegation c ↔ |c| = 23 ∧ c[0:3] = 0xEF0100` (`:42–61`); `get_delegated_code_address` returns `c[3:23]` (`:64–81`).
- **R-DEL-2** `calculate_delegation_cost f a` (`:159–196`) reads `a`'s account and code and returns `(false, a, 0)` or `(true, d, warm(d) ? 100 : 3000)` **without** warming `d` (the caller warms after the second check).
- **R-DEL-3** `resolve_delegated_code_address` (`:84–113`, used by the runner's `create_evm`) reads the code, and for a designator charges warm/cold via `charge_gas_from_meter`, warms `d` and returns `(d, true)`.
- **R-DEL-4** Resolution is one level only: if `d`'s code is itself a designator, those 23 bytes execute as code and the first byte `0xEF` is an invalid opcode [I: follows from `get_code(code_address)` with no loop]. When `disable_precompiles` is set and `d` is a precompile address, **no code runs** and the call succeeds with empty output (runner, `interpreter.py:438–439`).

## 3. EELS source map

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `forks/amsterdam/vm/instructions/__init__.py::Ops` | 32 | `inductive Ops`, `Ops.ofByte?`, `Ops.toByte`, `opImplementation`, `step` | the `op_implementation` dict (`:223`) is a module constant not listed in the inventory; specified here as the dispatch `match` |
| `forks/amsterdam/vm/instructions/arithmetic.py::*` | 28–374 | `add` … `signextend`, `U255_CEIL_VALUE` | |
| `forks/amsterdam/vm/instructions/bitwise.py::*` | 24–277 | `bitwiseAnd` … `countLeadingZeros` | |
| `forks/amsterdam/vm/instructions/comparison.py::*` | 24–180 | `lessThan` … `isZero` | |
| `forks/amsterdam/vm/instructions/keccak.py::*` | 30 | `keccak` | through `KeccakQuery` (D5); `m := Id` gives `EthHash.keccak256` |
| `forks/amsterdam/vm/instructions/environment.py::*` | 35–610 | `address` … `blobBaseFee` | |
| `forks/amsterdam/vm/instructions/block.py::*` | 22–299 | `blockHash` … `slotNumber` | |
| `forks/amsterdam/vm/instructions/stack.py::*` | 29–317 | `pop`, `pushN`, `dupN`, `swapN`, `dupn`, `swapn`, `exchange` | the `partial` aliases `push0…push32`, `dup1…`, `swap1…` are dispatch instances |
| `forks/amsterdam/vm/instructions/memory.py::*` | 30–179 | `mstore`, `mstore8`, `mload`, `msize`, `mcopy` | |
| `forks/amsterdam/vm/instructions/storage.py::*` | 37–216 | `sload`, `sstore`, `tload`, `tstore` | |
| `forks/amsterdam/vm/instructions/control_flow.py::*` | 25–174 | `stop`, `jump`, `jumpi`, `pc`, `gasLeft`, `jumpdest` | |
| `forks/amsterdam/vm/instructions/log.py::*` | 32 | `logN` | `log0…log4` aliases |
| `forks/amsterdam/vm/instructions/system.py::*` | 66–1023 | `genericCreate`, `create`, `create2`, `return_`, `GenericCall` (→ `CallRequest`), `genericCall`, `call`, `callcode`, `selfdestruct`, `delegatecall`, `staticcall`, `revert`, plus `resumeAfterCall`, `resumeAfterCreate` | the EELS functions are split at the dispatch point (§2.5–2.6) |
| `forks/amsterdam/vm/__init__.py::CALL_SUCCESS` | 44 | `CALL_SUCCESS : U256 := 1` | |
| `forks/amsterdam/vm/eoa_delegation.py::EOA_DELEGATION_MARKER` | 36 | `EOA_DELEGATION_MARKER` | `0xEF0100` |
| `forks/amsterdam/vm/eoa_delegation.py::EOA_DELEGATION_MARKER_LENGTH` | 37 | constant 3 | |
| `forks/amsterdam/vm/eoa_delegation.py::EOA_DELEGATED_CODE_LENGTH` | 38 | constant 23 | |
| `forks/amsterdam/vm/eoa_delegation.py::is_valid_delegation` | 42 | `isValidDelegation` | also used by `EthBlock` (EIP-3607 sender check) and the runner |
| `forks/amsterdam/vm/eoa_delegation.py::get_delegated_code_address` | 64 | `getDelegatedCodeAddress` | |
| `forks/amsterdam/vm/eoa_delegation.py::resolve_delegated_code_address` | 84 | `resolveDelegatedCodeAddress` | consumed by the runner's `createEvm` |
| `forks/amsterdam/vm/eoa_delegation.py::calculate_delegation_cost` | 159 | `calculateDelegationCost` | |

**External semantics.** `ethereum_types` `U256` operations used by handlers: `wrapping_add/sub/mul`, `//`, `%`, `to_signed`, `from_signed` (raises for out-of-range; unreachable from these handlers because all results are in range) [V], `from_be_bytes`, `to_be_bytes32`, `bit_length`, `~`, `&`, `|`, `^`, `>>`; `Uint(...)` conversions (exact, unbounded); `U8` for immediates; Python's `pow(b, e, 2^256)`; Python negative list indexing in BLOCKHASH (IndexError beyond length) and in DUPN/SWAPN/EXCHANGE (always in range after the checks). Each must be given by an `EthBase` `U256`/`Nat` law, not by Lean `BitVec` instances (D1).

## 4. Tests

- **EEST fixture areas** (`blockchain_tests/for_amsterdam/…`, plus `for_bpo2toamsterdamattime15k` variants, which need bpo2 execution; the `_engine` copies carry no guest records, GAPS-CROSSCUTTING X5):
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
- **`core` `#guard` cases** (per handler, via `step` on a synthetic frame; a `#guard` evaluates only once every leaf it reaches is implemented, F16): every arithmetic op at `0`, `1`, `2^255`, `2^256−1` (SDIV `−2^255 ÷ −1`, SMOD sign, SAR of negatives by 255/256, SIGNEXTEND k = 30, 31, 32, BYTE 31/32, EXP gas for exponents of 0/1/256/2^255, CLZ 0); `Ops.ofByte?` for all 256 bytes (153 some, 103 none); DUPN/SWAPN/EXCHANGE on every immediate including 91 and 127, the immediate past the end of code, and underflow by one; PUSH32 truncated at end of code; JUMPI with cond 0 to an invalid target; RETURNDATACOPY `(0, 1, 0)` with empty return data (halts); CALLDATALOAD at `2^256−1`; MCOPY overlapping both directions; LOG in a static frame (charges first); SSTORE all 27 `(original, current, new) ∈ {0, x, y}³` combinations with expected execution cost, refund delta and state gas, plus the gas-left = 2300 sentry; CALL with value to a dead account then failing child (state gas refilled); CREATE collision (grant consumed, nonce incremented); BLOCKHASH offsets 0, 1, 256, 257 and one beyond `|block_hashes|`.
- **Adversarial:** stack exactly 1024 then PUSH/DUP; 1023 then CALL chain; memory offset `2^64`, `2^256−1` with size 0 (no charge) and 1 (OOG); CALL gas argument `2^256−1` (capped by 63/64); static context for each state-changing op; RETURNDATACOPY bounds after revert, halt and successful create (empty).
- **Differential:** handler-by-handler against EELS on random frames (random stack, memory, meter, warm sets) using the EELS functions directly, including the order of state reads (recorded through an instrumented `TransactionState`).

## 5. Interface

```lean
-- Opcodes and dispatch (public)
inductive Ops | stop | add | … | selfdestruct              -- 153 constructors, EELS names
def Ops.toByte : Ops → UInt8
def Ops.ofByte? : UInt8 → Option Ops
-- Generic in the oracle monad (D5): `{m} [Monad m]` throughout, plus `[KeccakQuery m]` on the
-- handlers that hash (KECCAK256, CREATE, CREATE2) and hence on `opImplementation` and `step`.
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

-- One handler per opcode (public): add, mul, sub, div, sdiv, mod, smod, addmod, mulmod, exp,
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

**State API consumed from `EthState`** (names as in `state_tracker.py`, each `Except WitnessError`): `getAccount`, `getCode` (with the address, for code-access recording), `getStorage`, `getStorageOriginal`, `getTransientStorage`, `setStorage`, `setTransientStorage`, `isAccountAlive`, `accountDeployable`, `incrementNonce`, `moveEther` (may raise the balance-overflow fault), `createdAccounts`, `trackAncestorAccess` (on `world.tx.block.oldestAncestorOffset`). From EthCodec: `computeContractAddressQ`, `computeCreate2ContractAddressQ` (the `KeccakQuery` forms, D5). From EthBase: `Address.ofU256Masked` (`to_address_masked`).

## 6. Data structures

| Type | Representation | Model / abstraction | Invariant | Persistence | Cost |
|---|---|---|---|---|---|
| `Ops` | inductive, 153 constructors | byte value via `toByte` | `ofByte? (toByte o) = some o`; `ofByte? b = some o → toByte o = b` | value | `ofByte?` O(1) (a 256-entry table or `match`) |
| `StepResult ctx` | inductive | — | `.call/.create` carry `ctx.depth < STACK_DEPTH_LIMIT` and `parent.stack.size < STACK_DEPTH_LIMIT` | value | — |
| `CallRequest`, `CreateRequest` | records; `callData`, `code`, `initCode` share `ByteArray`s | — | `gas` computed by the 63/64 rule from the parent's `gas_left` at the grant | value | O(1) plus the input copy O(\|in\|) already paid by gas |
| `ChildOutcome` | record | — | `ChildSettled` | value | — |
| handlers | functions in `VmM m` (pure at `m := Id`) | — | preserve `Frame` invariants (stack ≤ 1024, memory size % 32 = 0) | — | O(1) for word ops; O(k) for copies/hashes of k bytes, k bounded by gas |

The suspended parent frame (in `.call/.create`) is linear: the runner holds the only reference while the child runs, so memory writes in `resumeAfterCall` are in place (ARCHITECTURE §7: diagnostics must not retain frames).

## 7. Contract and laws

**Per-opcode semantic lemmas** [R] (for evm-asm and pancaketh), one per handler, stated only with EthVmCore's stack/memory/meter laws and EthState's lookup laws, never by unfolding representations. Template (ADD):

```lean
theorem step_add (h₁ : ctx.code[f.pc]? = some 0x01) (h₂ : f.stack.toList = a :: b :: s)
    (h₃ : 3 ≤ f.gasMeter.gasLeft) :
  step ctx f w = .ok (.continue { f with pc := f.pc + 1, stack := ⟪(a + b) :: s⟫,
                                          gasMeter := f.gasMeter.charged 3 }, w)
theorem step_add_underflow (h₁ : …) (h₂ : f.stack.size < 2) : ∃ f', step ctx f w = .ok (.halt f' .stackUnderflow, w)
theorem step_add_oog (h₁ : …) (h₂ : f.stack.toList = a :: b :: s) (h₃ : f.gasMeter.gasLeft < 3) : ∃ f', step ctx f w = .ok (.halt f' .outOfGas, w)
```

Memory ops: `step_mstore` states `α mem' = α (write (expand mem e) off (be32 v))` with `e = expandBy`, and gas `3 + cost`; storage ops state the read/write through `getStorage`/`setStorage` laws and the exact SSTORE cost/refund/state-gas table of §2.4 as a function `sstoreCharges original current new cold`. CALL/CREATE lemmas state the request fields and the parent frame at suspension (the exact meter after withholding), and separately the resume equations. The lemma set must also give **exception precedence** (R-GEN-2) as in powdr's `StepDeterminism.lean`.

**Frame invariants** [C]: every handler preserves `stack.size ≤ 1024`, `memory.size % 32 = 0`, `ctx` unchanged (by typing), `f.accessedAddresses ⊆ f'.accessedAddresses` (warm sets only grow within a frame), and `Wf gasMeter`.

**Gas progress** [T] (feeds EthVmRunner G2): for every handler, if the result is `.continue f'` then `f'.gasMeter.phi + 1 ≤ f.gasMeter.phi` (every non-terminal opcode has execution cost ≥ 1 [V: minimum costs are JUMPDEST 1, `BASE` 2; the only zero-cost handlers, STOP/RETURN/REVERT, are terminal]; state-gas charges, credits and repays leave Φ unchanged). For `.call parent req`: `parent.gasMeter.phi + req.gas + 100 ≤ f.gasMeter.phi`, where `req.gas` already includes the stipend: the charge is `access + transfer + delegation + mem + g'` and `req.gas = g' + stipend`, with `access ≥ 100` and `transfer − stipend = 11300 − 2300` when a stipend is paid [I]. The preflight-failure path (`.continue`) satisfies the same bound through `restore_child_gas`. For `.create`: `parent.gasMeter.phi + req.gas + 12000 ≤ f.gasMeter.phi`; the collision path (`.continue`) loses `12000 + g` [I]. For the resume operations: `(resumeAfterCall cfg p r c hs).gasMeter.phi = p.gasMeter.phi + c.frame.gasMeter.phi` (EthVmCore `L-INC`; the NEW_ACCOUNT credit preserves Φ).

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
- **Seams:** provides `Handler`, `step`, `StepResult`, requests and resume operations; consumes EthVmCore's frame, meter and memory contracts, EthState's lookup/overlay laws (through `VmM m`), `KeccakQuery` (KECCAK256; CREATE and CREATE2 addresses through EthCodec's `…Q` forms), RLP (CREATE address). Relies on: the frame it receives satisfies the EthVmCore invariants; the runner passes back a `ChildOutcome` built from a frame with `ChildSettled`. Guarantees: `.call/.create` only when `depth < STACK_DEPTH_LIMIT` and the parent stack has room for the result (`hs`), balance and nonce preflight passed, and the parent's meter already withholds the grant.

## 9. Open decisions

- **D1**: handlers use only `U256` observer laws; exercise 4.
- **D5** (broad scope, monad-parametric; B10): **every** keccak goes through `KeccakQuery`, including the KECCAK256 opcode and CREATE/CREATE2 address derivation, so handlers live in `VmM m`. Execution instantiates `m := Id`, where the instance is concrete `keccak256`. A narrower scope needs the agreement prototype's justification.
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

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **No lemma is written.** The per-opcode lemmas, precedence lemmas, `step_iff` and determinism are specifications only.
- **Gas progress for the CALL family** is [I]: the inequality "execution charge of the calling opcode ≥ stipend + 1" must be proved for all four call opcodes, both preflight-failure paths, and the EIP-150 branch where `gas_left < extra + mem` (which fails the charge, so it is a halt, not a continue).
- **BLOCKHASH in the stateless setting**: if the witness carries fewer than `number − n` headers, EELS raises `IndexError` (`I/block.py:58`), which reaches the inner catch-all (`stateless.py:303`). This is witnessed by the fixture `validation_headers_missing_oldest_blockhash_ancestor` and classified as O13 with `VmFault.ancestorHashUnavailable`. No gap remains beyond freezing the constructor list (DECISIONS B14).
- **BLOBBASEFEE `U256` overflow** (`I/environment.py:607`) is argued reachable on an unanchored parent header (O13), but not witnessed. It also costs `taylor_exponential` time proportional to its result (DISC-002). NUMBER, GASLIMIT and BASEFEE cannot overflow (R-GEN-7).
- **Read-order fidelity** (R-GEN-1) is required for BAL and witness observations but has no dedicated test harness; EEST `eip7928_block_level_access_lists` (202 fixtures) is the only indirect check.
- **`to_address_masked`** is owned by `EthBase`, and **`compute_contract_address`, `compute_create2_contract_address`** by `EthCodec` (A1, A2) (`utils/address.py`); this spec assumes their behaviour (low 20 bytes; `keccak(rlp([sender, nonce]))[12:]`; `keccak(0xff ‖ sender ‖ salt ‖ keccak(init))[12:]`) [I: not re-read].
- **`account_deployable` ignores storage** [V], so a CREATE to an address with only storage succeeds after `destroy_storage` in `process_create`; relies on EthState's `destroy_storage` semantics.
- **EIP-8246 detail**: the balance-preserving clear is in `fork.py`/`state_tracker.py` (not read here in full); the SELFDESTRUCT handler spec depends on it only through `accounts_to_delete`.
- **Static LOG precedence** (charge and expand before the static check) is observable only in traces; traces are diagnostics (§7 of ARCHITECTURE), so the Lean trace schema must decide whether it records it.
- **`Ops` enum line numbers**: the constant block spans `I/__init__.py:32–220`; the `partial` aliases (push1…) are not inventory items and are covered by `pushN`/`dupN`/`swapN`/`logN`.
- **Precompile-addressed code under delegation** (R-DEL-4) is inferred from the runner branch; no dedicated fixture located.
