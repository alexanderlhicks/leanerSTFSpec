# `EthVmInstructions`: one handler per opcode, `StepResult`, child requests and resume operations

*Status: informal specification, draft. Section 3 records the supplied carriers, opcode conversions, handlers and local laws. Date: 2026-11-24. Pin: `tests-zkevm@v21.0.6` @59c1473d. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F1, F8, F10, F11, F20 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D1, D5, D13, D14, D17, D18, D26, D27 · questions: B7/Q24, B8/Q1, B14/Q23, Q91, Q92, Q93, Q94, Q95, F11.*

Paths in `file:line` references are relative to `src/ethereum/forks/amsterdam/vm/` unless stated otherwise; `I/` abbreviates `instructions/`. "[V]" marks a claim checked by reading the pinned source; "[I]" an inference. EELS `file:line` citations are at `59c1473d` except where marked and those listed in `STFSpec/informal/citation-remap-manual.txt`, which are still at `e1a316a0` (`tests-zkevm@v21.0.0`); verified observations are at `e1a316a0` unless marked as at `59c1473d` (GAPS-CROSSCUTTING X16).

## 1. Purpose

`EthVmInstructions` (root `STFSpec.Vm.Instructions`, layer L3) defines the semantics of every Amsterdam opcode as a non-recursive handler that maps a frame to a `StepResult`: a successor frame, a normal stop with output, a revert with output, an exceptional halt, or a **child request** (call or create) that the runner executes before calling a **named resume operation** on the suspended parent (D17). It also owns the opcode enumeration and its dispatch table (`I/__init__.py`), the single-step function `step`, and EIP-7702 delegation-designator parsing and call-target resolution. It must not import the runner or precompile implementations (`scripts/boundaries.toml`); CALL/CREATE semantics therefore stop at the request and resume at the outcome. The per-opcode lemmas stated here are the refinement interface for evm-asm's dispatch-loop proofs.

## 2. Requirements

### 2.1 General rules (apply to every handler)

- **R-GEN-1 Step order.** Each handler must perform its sub-steps in the EELS order: (1) static-context check, where EELS does it first; (2) pops (`StackUnderflowError`); (3) gas computation and `check_gas`/`charge_gas`; (4) state reads and writes; (5) memory expansion; (6) pushes; (7) `pc` update. The order matters beyond the exception name: **state reads are persistent observations** that survive a later exceptional halt or revert (ARCHITECTURE §6; they feed the BAL and the witness access record), so a read must happen exactly when EELS performs it, and not before a gas check that precedes it in EELS. EIP-8038's "STATE ACCESS after state-independent gas check" structure (`I/system.py:487–536`, `I/storage.py:85–116`) exists for this reason [V: comments].
- **R-GEN-2 Precedence among exceptional halts.** Where two halt conditions hold, the first in EELS order wins. All exceptional halts have the same guest-visible effect (O8), so precedence is observable only through traces and through which reads happened before the halt; both must match. Specific orders: most arithmetic/stack-consuming ops pop before charging (underflow beats OOG); DUP*/SWAP*/DUPN/SWAPN/EXCHANGE charge before the depth check (OOG beats underflow) (`I/stack.py:100–102, 132–134, 229–237`); push-producing ops charge before pushing (OOG beats overflow); CREATE/CREATE2/SSTORE/TSTORE/SELFDESTRUCT check the static flag **before** popping; CALL checks it after popping and only for non-zero value; LOG checks it after charging and expanding memory (`I/log.py:67–69`).
- **R-GEN-3 Memory.** Every memory-touching handler computes `calculate_gas_extend_memory` for its windows, charges `base + per-word + expansion` in one `charge_gas`, then expands, then reads/writes. A window with size 0 adds no expansion and is admitted at every offset. The selected charge still requires affordability. RETURN and REVERT follow Q92. Offsets and sizes are full 256-bit values; conversion to `Nat` must be exact (never truncated to 64 bits before the gas check).
- **R-GEN-4 Words.** Arithmetic is modulo 2^256 through the `U256` API (EthBase, D1): signed operations use two's complement; `x / 0 = 0`, `x % 0 = 0`; ADDMOD/MULMOD compute over unbounded integers before reducing.
- **R-GEN-5 PC.** Handlers advance `pc` by 1, except PUSHn (`1 + n`, `I/stack.py:79`), DUPN/SWAPN/EXCHANGE (2, `:242, 278, 314` at `59c1473d`), JUMP/JUMPI (target or `pc+1`). Terminal handlers' `pc` updates are irrelevant. Stack-immediate reads follow Q91 below.
- **R-GEN-6 Invalid opcodes.** A byte that is not in `Ops` (103 of 256 values, including `0xFE`) causes `InvalidOpcode(byte)` before any charge (`interpreter.py:439–442`). Running off the end of code (`pc ≥ |code|`) is a normal stop with empty output (`interpreter.py:438`).
- **R-GEN-7 Non-EVM faults.** The VM routes `StateError` from State actions
  through `VmFault.state` (EthVmCore R-EXC-2). EthState R29 owns the failure
  classification, including O4 for wrapped witness errors. BLOCKHASH beyond
  the available headers and the BLOBBASEFEE `U256` conversion overflow also
  propagate as `VmFault` and fall under O13. These faults are distinct from
  exceptional halts. The guest's NUMBER and GASLIMIT values fit U256 by their
  SSZ widths. Q93 specifies raw GASPRICE and BASEFEE conversion below.
  EthVmCore R-EXC-2 gives the caller bounds and guest classification.

**Stack-immediate reads (Q91).** Charge the selected execution price before
reading the code. If the charge fails, halt with the entry frame and
`.outOfGas`. After payment, read the padded window at the exact Nat offset
`f.pc + 1` in `ctx.code`. Missing bytes contribute zero. This read rule also
defines raw calls whose start exceeds the U256 range.

PUSH0 uses the empty window and pushes zero. PUSH1–PUSH32 read their
declared widths and push the big-endian word. DUPN and SWAPN pass one padded
byte to Core's `decodeSingle`. EXCHANGE passes one padded byte to
`decodePair`. Decode before checking stack depth or pushing. Advance the PC
only after the stack operation succeeds. EELS `I/stack.py:49–79,213–314`
at `59c1473d`.

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
| 16–19 | AND OR XOR NOT | `I/bitwise.py:21, 46, 71, 96` | a b → r (NOT: a → ~a) | 3 | Top first. NOT complements all 256 bits. |
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
| 35 | CALLDATALOAD | `:159` | i → word | 3 | Pop and charge, then push a big-endian word from the 32-byte zero-padded call-data window. |
| 36 | CALLDATASIZE | `:185` | → \|cd\| | 2 | Push the call-data size word after its own charge (Q94). |
| 37 | CALLDATACOPY | `:208` | mo do sz → | 3 + 3·w(sz) + mem(mo,sz) | Charge the destination window, then copy zero-padded frame call data. |
| 38 | CODESIZE | `:246` | → \|code\| | 2 | Push the executing code size word after its own charge (Q94). A create frame uses its init code. |
| 39 | CODECOPY | `:269` | mo co sz → | 3 + 3·w(sz) + mem(mo,sz) | Charge the destination window, then copy zero-padded executing code. |
| 3A | GASPRICE | `:307` | → price | 2 | Check and push `effective_gas_price` after its own charge (Q93 below). |
| 3B | EXTCODESIZE | `:330` | a → n | warm/cold + 100 | EIP-8038 code-read surcharge; reads account and code after the charge; size of the **raw** code (23 for a delegation designator) |
| 3C | EXTCODECOPY | `:364` | a mo co sz → | warm/cold + 100 + 3·w(sz) + mem | warm-set add before charge; raw code, zero-padded |
| 3D | RETURNDATASIZE | `:411` | → \|rd\| | 2 | Push the current return-data size word after its own charge (Q94). |
| 3E | RETURNDATACOPY | `:434` | mo ro sz → | 3 + 3·w(sz) + mem | after the charge, **`ro + sz > \|rd\|` → `OutOfBoundsRead`, even when `sz = 0`** (`:463`); then expand and copy |
| 3F | EXTCODEHASH | `:476` | a → h | warm/cold | account `== EMPTY_ACCOUNT` (absent or empty) → 0, else its `code_hash`; **no code read, no surcharge** |
| 40 | BLOCKHASH | `I/block.py:22` | n → h | 20 | 0 unless `n < number ≤ n + 256`; else `block_hashes[−(number − n)]` and `track_ancestor_access(number − n)` (a block-level observation, never reverted). If `number − n > \|block_hashes\|` EELS raises `IndexError` (`I/block.py:58`) → `VmFault.ancestorHashUnavailable` (O13) [V: `stateless.py:246` supplies only the witness headers. CONTRACT O13 records the pinned witness fixture.] |
| 41 | COINBASE | `:71` | → coinbase | 2 | |
| 42 | TIMESTAMP | `:105` | → time | 2 | |
| 43 | NUMBER | `:139` | → number | 2 | `U256(number)` |
| 44 | PREVRANDAO | `:172` | → randao | 2 | |
| 45 | GASLIMIT | `:205` | → limit | 2 | |
| 46 | CHAINID | `:238` | → chain id | 2 | |
| 47 | SELFBALANCE | `I/environment.py:513` | → bal | 5 | read after charge |
| 48 | BASEFEE | `:539` | → base fee | 2 | Check and push `base_fee_per_gas` after its own charge (Q93 below). |
| 49 | BLOBHASH | `:562` | i → h | 3 | `i < \|hashes\|` → hash, else 0 |
| 4A | BLOBBASEFEE | `:589` | → price | 2 | `U256(calculate_blob_gas_price(excess_blob_gas))` (`:607`); overflow → `VmFault.u256Overflow .blobBaseFee` (O13, argued reachable) |
| 4B | SLOTNUM | `I/block.py:268` | → slot | 2 | EIP-7843: `block_env.slot_number` |

**Raw byte-size words (Q94).** Each handler charges its selected
execution tariff before converting the selected byte count. CALLDATASIZE
uses `ctx.config.costs.opcodeCallDataSize` and `ctx.callData.size`.
CODESIZE uses `ctx.config.costs.opcodeCodeSize` and `ctx.code.size`.
RETURNDATASIZE uses `ctx.config.costs.opcodeReturnDataSize` and the
current `frame.returnData.size`. A charge denial halts with out-of-gas
and the complete entry frame. After payment, convert the full Nat size
with `U256.ofNat`, then attempt the push. A full stack halts with the
complete charged frame. Success pushes the word and increments the
Nat PC by one. Every result retains the supplied world. At mathematical
size `2^256`, a paid frame with room pushes zero. EELS
`I/environment.py:185–205,246–266,411–431` at `59c1473d`.

**Raw GASPRICE and BASEFEE (Q93).** GASPRICE uses
`ctx.txEnv.effectiveGasPrice` and `ctx.config.costs.opcodeGasPrice`.
BASEFEE uses `ctx.blockEnv.baseFeePerGas` and
`ctx.config.costs.opcodeBaseFee`. Each handler uses only its selected
tariff and fee. Charge the selected tariff before testing
`fee < 2^256` (`I/environment.py:307–327,539–559` at the pin).
A denied charge yields `.halt` for out-of-gas with the original frame.
An out-of-range paid fee yields `VmFault.u256Overflow` with the selected
site even on a full stack. In EELS the charge is already applied when
the conversion raises. EthVmCore R-EXC-2 defines the Lean fault boundary.
With a fitting fee, a failed push halts with the paid frame. A successful
push increments the Nat PC by one and changes only the stack, PC and
execution gas. Every frame result retains the original world.

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
| 58 | PC | `:101` | → pc | 2 | After payment check the entry PC and push its word (Q95). |
| 59 | MSIZE | `I/memory.py:119` | → \|mem\| | 2 | always a multiple of 32 |
| 5A | GAS | `I/control_flow.py:125` | → gas_left | 2 | After payment check the paid execution balance and push its word (Q95). |
| 5B | JUMPDEST | `:149` | – | 1 | |
| 5C | TLOAD | `I/storage.py:164` | k → v | 100 | transient storage (EIP-1153) |
| 5D | TSTORE | `:189` | k v → | 100 | static first; revertible (part of the tx snapshot) |
| 5E | MCOPY | `I/memory.py:142` | dst src len → | 3 + 3·w(len) + mem([(src,len),(dst,len)]) | read-then-write (overlap-safe) |
| 5F | PUSH0 | `I/stack.py:49` | → 0 | 2 | |
| 60–7F | PUSH1…PUSH32 | `:49` (`push_n`) | → imm | 3 | `n` bytes after `pc`, zero-padded past end; `pc += 1+n` |
| 80–8F | DUP1…DUP16 | `:82` (`dup_n`) | → copy of i-th | 3 | charge, then `i > size` → underflow, then push (overflow) |
| 90–9F | SWAP1…SWAP16 | `:110` (`swap_n`) | swap top, (i+1)-th | 3 | charge, then `i ≥ size` → underflow |
| E6 | DUPN | `:213` | → copy of n-th | 3 | EIP-8024; charge; `n = decode_single(imm)` (`InvalidParameter` for imm 91…127); `n > size` → underflow; `pc += 2` |
| E7 | SWAPN | `:245` | swap 1st, (n+1)-th | 3 | Charge, read the padded byte and decode as for DUPN. Underflow if `n + 1 > size`. Success advances the PC by two. |
| E8 | EXCHANGE | `:281` | swap (n+1)-th, (m+1)-th | 3 | Charge and read the padded byte. `decode_pair(imm)` rejects 82…127. Underflow if `max(n,m) + 1 > size`. Success advances the PC by two. |

**Logs and system**

| Hex | Name | EELS | Pops → pushes | Gas | Semantics / halts |
|---|---|---|---|---|---|
| A0–A4 | LOG0…LOG4 | `I/log.py:28` (`log_n`) | off sz t₁…tₙ → | 375 + 8·sz + 375·n + mem | charge, expand, **then** static → `WriteInStaticContext`; append `Log(target, topics, data)` |
| F0 | CREATE | `I/system.py:188` | e off sz → addr/0 | 12000 + mem + 2·w(sz); state gas via `generic_create` | §2.5 |
| F1 | CALL | `:465` | g a v io is oo os → 0/1 | §2.6 | §2.6 |
| F2 | CALLCODE | `:592` | g a v io is oo os → 0/1 | §2.6 | no static check |
| F3 | RETURN | `:307` | off sz → | §2.9 | `.stop` with the window as output |
| F4 | DELEGATECALL | `:781` | g a io is oo os → 0/1 | §2.6 | |
| F5 | CREATE2 | `:242` | e off sz salt → addr/0 | 12000 + 6·w(sz) + mem + 2·w(sz) | §2.5 |
| FA | STATICCALL | `:884` | g a io is oo os → 0/1 | §2.6 | |
| FD | REVERT | `:987` | off sz → | §2.9 | `.revert` with the window as output |
| FF | SELFDESTRUCT | `:706` | b → | §2.7 | static first |

**Raw PC and GAS (Q95).** PC pays `ctx.config.costs.opcodePc`, then
selects the entry `f.pc`. GAS pays `ctx.config.costs.opcodeGas`, then
selects the paid meter's execution `gasLeft`. A denied charge returns
the complete entry frame and world for every raw operand. Payment
precedes `U256.ofNat?`, and the cast precedes the push. An oversized value
returns `.error (.u256Overflow site)` with `.pc` or `.gasLeft`.
EthVmCore R-EXC-2 owns the site and the source's paid prefix. After a
fitting cast, full-stack halt returns the complete paid frame and world.
Success pushes the word, increments the Nat PC by one and preserves
the rest of the paid frame and the supplied world. EELS
`I/control_flow.py:101–122,125–146` at `59c1473d`.

### 2.3 Dispatch

- **R-DSP-1** `Ops` (`I/__init__.py:32–220`) has exactly 153 constructors with the byte values listed; `op_implementation` (`:223–377`) maps each to its handler. The Lean dispatch must be a total `match` on `Ops` (not a map lookup), with `Ops.ofByte? : UInt8 → Option Ops` and the round-trip laws.
- **R-DSP-2** `step ctx f` must return `.stop f ∅` if `f.pc ≥ |ctx.code|`, `.halt f (invalidOpcode b)` if `Ops.ofByte? b = none`, and otherwise the handler's result. `step` never recurses and never changes `ctx`.

### 2.4 SSTORE (`I/storage.py:68–161`; EIP-2200, EIP-3529 refund values, EIP-8037 state gas, EIP-8038 access)

In order: (1) static → `WriteInStaticContext`; (2) pop key, new; (3) `cost := cold ? 2100 : 100`; (4) `check_gas(max(cost, 2301))`: the EIP-2200 sentry, **before any state read**; (5) warm the slot; (6) read `original` (`get_storage_original`) then `current`; (7) if `original = current ≠ new`: `cost += 10000` (`STORAGE_WRITE`); (8) if `current ≠ new`: `+11616` if `original ≠ 0 ∧ current ≠ 0 ∧ new = 0`; `−11616` if `original ≠ 0 ∧ current = 0`; `+10000` if `original = new` (each independently, on the `Int` refund counter); (9) state gas `97920` (`STORAGE_SET`) if `original = current = 0 ≠ new`; (10) if `current ≠ new ∧ original = new = 0`: `credit_state_gas_refund(97920)` **before** the charges; (11) `charge_gas(cost)`, then `charge_state_gas(state)`; (12) `set_storage`.

In the zero restoration case in step (10), `current ≠ 0` and
`original = new = 0`. The step (7) write surcharge and step (9)
state charge are zero. The earlier sentry already checked the
entire warm or cold access charge. Preserve the source order by
crediting the refund, charging execution gas, charging state gas
and then writing the slot.

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
- **R-DEL-3** `resolve_delegated_code_address` (`:84–109`, used by the runner's `create_evm`) reads the target's account and then its code by the returned hash. Ordinary code returns `(a, false)` with the entry gas and warmth. For a designator, select the warm or cold price by membership of `d`, charge execution gas, and insert `d` if it was cold. Return `(d, true)` after payment.
- **R-DEL-4** Resolution is one level only: if `d`'s code is itself a designator, those 23 bytes execute as code and the first byte `0xEF` is an invalid opcode [I: follows from `get_code(code_address)` with no loop]. When `disable_precompiles` is set and `d` is a precompile address, **no code runs** and the call succeeds with empty output (runner, `interpreter.py:432–433`).

### 2.9 RETURN and REVERT (Q92)

Pop the U256 offset, then pop the U256 length from the first residual
stack. First underflow retains the entry frame. Second underflow
retains the first residual stack. Once both pops succeed, calculate
`e = calculateGasExtendMemory ctx.config f.memory [(off, len)]`.
Charge `ctx.config.costs.zero + e.cost` for RETURN and `e.cost`
for REVERT. In each handler, apply the execution affordability guard
before changing memory. Denial leaves both pops in effect and retains
the entry execution and state gas, memory and other frame fields.
EELS `src/ethereum/forks/amsterdam/vm/instructions/system.py:307–337,987–1016`
and `src/ethereum/forks/amsterdam/vm/gas.py:379–410` at the pin.

The Q63 helper reads the ZERO seed before considering any window.
RETURN requests that helper and separately reads ZERO at the charge
site. REVERT uses the seeded helper cost. If `Δ` is the growth
delta and `z = ctx.config.costs.zero`, the raw charges are
`2*z + Δ` and `z + Δ`. The seed and the memory-word coefficient
are independently supplied natural numbers. At the pinned Amsterdam
prices, ZERO is zero and both charges equal `Δ`.
EELS `src/ethereum/forks/amsterdam/vm/gas.py:761–798` at the pin.

On payment, debit just execution gas, keep the second residual stack,
and expand memory by `e.expandBy` zero bytes. Read the admitted
window at the exact Nat values of the U256 offset and length. Return
`.stop` for RETURN and `.revert` for REVERT, with that byte sequence
as the terminal output. Keep `pc`, `returnData` and all other frame
fields. The output carries a snapshot of the expanded memory window
and belongs to the terminal result. A zero-length window admits an
empty read at every offset, adds no growth and pays its selected raw
charge. The Runner owns exceptional-halt and revert settlement.
EELS `src/ethereum/forks/amsterdam/vm/interpreter.py:450–465` at the pin.

## 3. EELS source map

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `forks/amsterdam/vm/instructions/__init__.py::Ops` | 32 | `Ops`, `Ops.ofByte?`, `Ops.toByte` (supplied); `opImplementation`, `step` (unimplemented) | The enum/byte slice is detailed below; the `op_implementation` dict (`:223`) remains the future dispatch `match` |
| `forks/amsterdam/vm/instructions/arithmetic.py::*` | 28–374 | `add`, `sub`, `mul`, `div`, `sdiv`, `mod`, `smod`, `signextend`, `addmod`, `mulmod`, `exp` (supplied below), `U255_CEIL_VALUE` | Standalone handlers and local laws |
| `forks/amsterdam/vm/instructions/bitwise.py::*` | 21–274 | `bitwiseAnd` … `countLeadingZeros` (supplied below) | Standalone handlers and local laws |
| `forks/amsterdam/vm/instructions/comparison.py::*` | 21–177 | `lessThan`, `greaterThan`, `signedLessThan`, `signedGreaterThan`, `equal`, `isZero` (supplied below) | Standalone handlers and local laws |
| `forks/amsterdam/vm/instructions/keccak.py::keccak` | 26–62 | `keccak` (supplied below) | Pop offset and size, pay, expand, query once, push all digest bytes and advance PC. |
| `forks/amsterdam/vm/instructions/environment.py::*` | 35–610 | `address` … `blobBaseFee` | The bounded frame and transaction queries, BALANCE, CALLDATALOAD, CALLDATACOPY, CODECOPY, EXTCODEHASH, EXTCODECOPY, SELFBALANCE, GASPRICE, BASEFEE, the three byte-size words and BLOBHASH have standalone handlers below. |
| `forks/amsterdam/vm/instructions/block.py::*` | 22–298 | `blockHash` … `slotNumber` | BLOCKHASH and the bounded block queries have standalone handlers below. |
| `forks/amsterdam/vm/instructions/stack.py::*` | 26–314 | `pop`, `pushN`, `dupN`, `swapN`, `dupn`, `swapn`, `exchange` | The `partial` aliases `push0…push32`, `dup1…`, `swap1…` are dispatch instances. Q91 specifies the immediate reads in §2 and the source boundary in §7. POP, PUSH, fixed DUP, DUPN, fixed SWAP, SWAPN and EXCHANGE are supplied below. |
| `forks/amsterdam/vm/instructions/memory.py::mstore` | 26–54 | `mstore` (supplied) | Two pops, paid 32-byte big-endian write, PC + 1 |
| `forks/amsterdam/vm/instructions/memory.py::mstore8` | 57–86 | `mstore8` (supplied) | Two pops, paid low-byte write, PC + 1 |
| `forks/amsterdam/vm/instructions/memory.py::mload` | 89–116 | `mload` (supplied) | Offset pop, paid 32-byte big-endian read and push, PC + 1 |
| `forks/amsterdam/vm/instructions/memory.py::msize` | 119 | `msize` | Unimplemented |
| `forks/amsterdam/vm/instructions/memory.py::mcopy` | 142 | `mcopy` | Standalone two-window snapshot copy with local action and accounting laws (§§3–5 and §7). |
| `forks/amsterdam/vm/instructions/storage.py::*` | 37–216 | `sload` (supplied below), `sstore`, `tload` (supplied below), `tstore` (supplied below) | |
| `forks/amsterdam/vm/instructions/control_flow.py::*` | 22–171 | `stop`, `jump`, `jumpi`, `pc`, `gasLeft`, `jumpdest` | The supplied standalone handlers and local contracts are recorded below. |
| `forks/amsterdam/vm/instructions/log.py::*` | 32 | `logN` | The standalone handler and local laws cover all five aliases (§§3–5 and §7). |
| `forks/amsterdam/vm/instructions/system.py::*` | 66–1023 | `genericCreate`, `create`, `create2`, `return_`, `GenericCall` (→ `CallRequest`), `genericCall`, `call`, `callcode`, `selfdestruct`, `delegatecall`, `staticcall`, `revert`, plus `resumeAfterCall`, `resumeAfterCreate` | the EELS functions are split at the dispatch point (§2.5–2.6) |
| `forks/amsterdam/vm/__init__.py::CALL_SUCCESS` | 39 | `CALL_SUCCESS : U256 := 1` | |
| `forks/amsterdam/vm/eoa_delegation.py::EOA_DELEGATION_MARKER` | 36 | `EOA_DELEGATION_MARKER` (supplied) | The complete byte sequence `0xEF0100`. |
| `forks/amsterdam/vm/eoa_delegation.py::EOA_DELEGATION_MARKER_LENGTH` | 37 | constant 3 | |
| `forks/amsterdam/vm/eoa_delegation.py::EOA_DELEGATED_CODE_LENGTH` | 38 | constant 23 | |
| `forks/amsterdam/vm/eoa_delegation.py::is_valid_delegation` | 42–61 | `isValidDelegation` (supplied) | Exact length and prefix test. EthBlock's EIP-3607 sender check and the runner are prospective consumers. |
| `forks/amsterdam/vm/eoa_delegation.py::get_delegated_code_address` | 64–81 | `getDelegatedCodeAddress` (supplied) | Exact address suffix on the valid branch. |
| `forks/amsterdam/vm/eoa_delegation.py::resolve_delegated_code_address` | 84–109 | `resolveDelegatedCodeAddress` (supplied below) | The runner's `createEvm` still needs to consume the address, flag, meter and warmth. |
| `forks/amsterdam/vm/eoa_delegation.py::calculate_delegation_cost` | 155 | `calculateDelegationCost` | |

### Supplied KECCAK handler

| EELS source at `59c1473d` | Lean declaration | Domain and ordered effects | Laws and tests |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/keccak.py:26–62` | `STFSpec.Vm.Instructions.keccak` in `STFSpec/Vm/Instructions/Keccak.lean`, exported by the Instructions facade | Every supplied context, frame and world. Pop offset and byte count. Charge base plus rounded-word price and the singleton memory quote. Payment expands memory, reads the exact window, queries `KeccakQuery` once, pushes its complete big-endian answer and advances PC. The static flag has no effect. | Ordered run, byte and local Id accounting laws (§7), and recorded-oracle and concrete source controls (§4). |
### Supplied EXTCODECOPY handler

| EELS source at `59c1473d` | Lean declaration | Domain and ordered effects | Laws and tests |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/environment.py:364–405` | `STFSpec.Vm.Instructions.extcodecopy` in `STFSpec/Vm/Instructions/ExtCodeCopy.lean`, exported by the Instructions facade | Every raw frame, context and world. Mask the address word, retain the reached pop prefix, quote the destination and insert cold warmth before payment. Payment expands memory, reads the defaulted account and then its raw code, writes the padded source slice and advances PC. The static flag has no effect. | Private ordered run, observation, byte and Id accounting laws (§7), and complete facade controls (§4). |
### Supplied EIP-7702 designator functions

| EELS source at `59c1473d` | Lean declaration | Domain and result | Laws and tests |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/eoa_delegation.py:36–61` | `STFSpec.Vm.Instructions.EOA_DELEGATION_MARKER` and `isValidDelegation` in `STFSpec/Vm/Instructions/DelegationDesignator.lean`, exported by the Instructions facade | The marker contains the three bytes `ef 01 00`. On every `Bytes`, recognition is true exactly at length 23 with that complete prefix. | Ordinary `isValidDelegation_iff` (§7) and exact byte controls (§4). |
| `src/ethereum/forks/amsterdam/vm/eoa_delegation.py:64–81` | `STFSpec.Vm.Instructions.getDelegatedCodeAddress` in the same module and facade | Every `Bytes`. Invalid input yields `none`. Valid input supplies the complete 20-byte suffix as an address. | Ordinary `getDelegatedCodeAddress_eq_some_iff` (§7) and complete address controls (§4). |

### Supplied delegation resolver

| EELS source at `59c1473d` | Lean declaration | Effects and ordered failures | Laws and tests |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/eoa_delegation.py:84–109` | `STFSpec.Vm.Instructions.resolveDelegatedCodeAddress` in `STFSpec/Vm/Instructions/DelegationResolution.lean`, exported by the Instructions facade | Lift the account and code reads in order. A State failure returns an outer fault. Ordinary code preserves the address, meter and warmth. A designator selects the price by its destination and charges execution gas. Denial returns an inner halt with the reached world. Payment returns the delegate, paid meter and updated warmth. | Whole generic action and five Id laws (§7). Recording providers, raw tariffs and direct-source cases (§4). |

### Supplied SLOAD handler

| EELS source at `59c1473d` | Lean declaration | Effects and ordered failures | Laws and tests |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/storage.py:37–65` | `STFSpec.Vm.Instructions.sload` in `STFSpec/Vm/Instructions/Sload.lean`, exported by the Instructions facade | Pop the slot word and convert it to exactly 32 big-endian bytes. Look up warmth for the current target and key in the entry slot set. Insert a cold slot before charging the selected execution price. After payment, lift the current storage read (EthState R11), push its result and advance PC. Underflow retains the frame and world. Denied payment retains the pop and slot warmth, with the original PC, meter and world. | Private action, framing and charge laws (§7); standalone controls (§4). |

### Supplied BLOBHASH handler

| EELS source at `59c1473d` | Lean declaration | Effects and ordered failures | Laws and tests |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/environment.py:562–586` | `STFSpec.Vm.Instructions.blobHash` in `STFSpec/Vm/Instructions/BlobHash.lean`, exported by the Instructions facade | Pop the full U256 index before charging the dedicated execution price. After payment, index the supplied ordered versioned hash array with the full Nat value. Push the complete big-endian hash word or zero outside the array, then advance PC. Underflow retains the entry frame and world. Denied payment retains the pop and the rest of the entry frame and world. | Private array, byte, frame and accounting laws (§7) and standalone controls (§4). |

### Supplied BLOCKHASH handler

| EELS source at `59c1473d` | Lean declaration | Effects and ordered failures | Laws and tests |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/block.py:22–68` | `STFSpec.Vm.Instructions.blockHash` in `STFSpec/Vm/Instructions/BlockHash.lean`, exported by the Instructions facade | Pop the full requested word and charge `ctx.config.costs.opcodeBlockHash`. Use exact Nat arithmetic for the current number and age. Out-of-range requests push zero. A missing in-range ancestor gives `VmFault.ancestorHashUnavailable` at the array access. An in-range hit records R27 before pushing the full hash word. Successful cases advance PC by one. | Private exact run, action and gas laws (§7) and bounded facade controls (§4). |

### Supplied CALLDATALOAD handler

| EELS source at `59c1473d` | Lean declaration | Effects and ordered failures | Laws and tests |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/environment.py:159–183` | `STFSpec.Vm.Instructions.calldataload` in `STFSpec/Vm/Instructions/CallDataLoad.lean`, exported by the Instructions facade | Pop the full offset and charge `ctx.config.costs.opcodeCallDataLoad`. Underflow precedes payment. Denial retains the pop and skips the read. On payment, use Core `bufferRead` on `ctx.callData`, push the complete big-endian word and advance PC by one. | Private ordered run, padded-word and gas laws (§7) and bounded facade controls (§4). |

### Supplied standalone byte-size handlers (Q94)

| EELS source at `59c1473d` | Lean declaration | Contract |
|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/environment.py:185–205` | `calldatasize` | Push the call-data size word. |
| `src/ethereum/forks/amsterdam/vm/instructions/environment.py:246–266` | `codesize` | Push the executing code size word. |
| `src/ethereum/forks/amsterdam/vm/instructions/environment.py:411–431` | `returndatasize` | Push the current return-data size word. |

The three operations require a `Monad` instance and use the class-free
`Handler` alias. The Instructions facade exports them from
`STFSpec/Vm/Instructions/SizeWords.lean`. Section 2 specifies the charge and
push order, §5 gives the signatures, §7 the private laws and §4 the controls.
The executable capacity check retains the paid full frame. An ordinary
equality relates it to the direct `Stack.push` match on every word.

### Supplied standalone PC and GAS handlers (Q95)

| EELS source at `59c1473d` | Lean declaration | Contract |
|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/control_flow.py:101–122` | `pc` | Check and push the entry PC after payment. |
| `src/ethereum/forks/amsterdam/vm/instructions/control_flow.py:125–146` | `gasLeft` | Check and push the paid execution balance. |

The Instructions facade exports both handlers from
`STFSpec/Vm/Instructions/PcGasWords.lean`. The interfaces, four result
paths and controls appear in §§2/4/5/7.

### Supplied TLOAD handler

| EELS source at `59c1473d` | Lean declaration | Effects and ordered failures | Laws and tests |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/storage.py:164–186` | `STFSpec.Vm.Instructions.tload` in `STFSpec/Vm/Instructions/Tload.lean`, exported by the Instructions facade | Pop one word and convert the whole key to 32 big-endian bytes. Charge `ctx.config.costs.opcodeTload`, then read transient storage at `ctx.currentTarget` through `liftState`. Push the result and advance PC. Stack underflow precedes charging. An unaffordable charge retains the pop and precedes the read. | Private local branch, framing and charge laws (§7) and complete bounded controls (§4). |

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
| `src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py:294–328` (`exp`) | `STFSpec.Vm.Instructions.exp {m : Type → Type} [Monad m] : Handler m`, in the same leaf/facade | Every supplied context, complete raw Frame and complete `VmWorld m`; independent `opcodeExpBase` and `opcodeExpPerByte` admit every Nat, including zero and prices above word width; no LawfulMonad, hash, WF, code-byte or schedule premise | Pop base, pop unsigned exponent, charge base plus per-byte price times `(U256.bitLength exponent + 7) / 8`, compute `U256.exp base exponent`, push and PC+1. Both underflow cases retain preceding pops before selecting gas. OOG retains both pops with complete unchanged meter and PC. Success changes only stack, PC and execution gas, including when exponent is zero. All outcomes retain the complete world under literal underlying pure | `exp_run_empty`, `exp_run_singleton`, `exp_run_oog`, `exp_run_success`, `exp_continue_phi`, `exp_continue_progress` (§7); complete facade, symbolic numeric-model and actual-input accounting clients; native/interpreted/parser/source controls (§4) | Handler and six ordinary local laws discharged; source prices 10/50 and explicit field relation; whole source-model/trace/reachability/dispatch/settlement and composed gates remain open |
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

Source agreement uses the pinned prices 3 for ADD/SUB, 5 for
MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND and 8 for ADDMOD/MULMOD
(`vm/gas.py:70–72,170–179`). For EXP, it uses the base price 10 and per-byte
price 50 (`vm/gas.py:243–244`). It also supplies exact Uint/Nat successor and
gas correspondence, nominal U256 word correspondence, a top-first
Lean/reversed Python stack relation, and aligned memory/byte and meter/log/set
relations. It does not equate the raw complete Lean
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

EXP observes each popped word as unbounded Uint, takes the second operand's
bit length and rounds up to bytes (`I/arithmetic.py:306–320`, at `59c1473d`).
EthBase's public `bitLength_def` and `bitLength_le` establish the exact count and
its at-most-32-byte bound. Both price multiplication and addition use Nat,
without U256 wrapping. Charging precedes modular power even for exponent zero;
`0^0 = 1`. The executable square-and-multiply `U256.exp` is used directly, and
`toNat_exp` supplies the symbolic modular-power model. Its linear reference and
full natural powers are never executed on large exponents.

SIGNEXTEND's value model is owned by EthBase §3/§7. For k≤31 the source's
32-byte conversion, retained slice and optional 0xff prefix are defined and the
checked U256 reconstruction fits (`I/arithmetic.py:350–366`). The guarded branch
bounds the retained width to 256 bits. `toNat_signextend`,
`getLsbD_signextend` and the k>31/k=31 identity laws supply the public model,
without a new value algorithm or provider hypothesis.

### Supplied binary comparison handlers

All five declarations are in `STFSpec/Vm/Instructions/Comparison.lean` and are
exported by the Instructions facade. Each accepts every supplied context, bounded
frame and `VmWorld m`. Each reads its own raw Nat price from `ctx.config.costs`.

| EELS source at `59c1473d` | Lean declaration / exact type | Raw price | Result on first and second words `x`, `y` | Laws and deterministic controls |
|---|---|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/comparison.py:21–45` (`less_than`) | `STFSpec.Vm.Instructions.lessThan {m : Type → Type} [Monad m] : Handler m` | `opcodeLt` | `U256.lt x y` is one when `x.toNat < y.toNat` and zero otherwise. | Six discharged local laws (§7). Control for `1 < 2^255` with zero gas and zero price (§4). |
| `src/ethereum/forks/amsterdam/vm/instructions/comparison.py:74–98` (`greater_than`) | `STFSpec.Vm.Instructions.greaterThan {m : Type → Type} [Monad m] : Handler m` | `opcodeGt` | `U256.gt x y` is one when `y.toNat < x.toNat` and zero otherwise. | Six discharged local laws (§7). Control for `2^256 − 1 > 1` at the exact price (§4). |
| `src/ethereum/forks/amsterdam/vm/instructions/comparison.py:48–71` (`signed_less_than`) | `STFSpec.Vm.Instructions.signedLessThan {m : Type → Type} [Monad m] : Handler m` | `opcodeSlt` | `U256.slt x y` is one when `x.toInt < y.toInt` and zero otherwise. | Six discharged local laws (§7). Control for signed minimum below −1 (§4). |
| `src/ethereum/forks/amsterdam/vm/instructions/comparison.py:101–124` (`signed_greater_than`) | `STFSpec.Vm.Instructions.signedGreaterThan {m : Type → Type} [Monad m] : Handler m` | `opcodeSgt` | `U256.sgt x y` is one when `y.toInt < x.toInt` and zero otherwise. | Six discharged local laws (§7). Control for signed maximum above signed minimum at a price above word width (§4). |
| `src/ethereum/forks/amsterdam/vm/instructions/comparison.py:127–151` (`equal`) | `STFSpec.Vm.Instructions.equal {m : Type → Type} [Monad m] : Handler m` | `opcodeEq` | `U256.eq x y` is one when `x.toNat = y.toNat` and zero otherwise. | Six discharged local laws (§7). Control for equal maximum words and unequal words differing at the sign bit (§4). |

The ordered failures apply to each row. An empty stack retains the entry frame.
A singleton stack retains its first pop. Both underflows precede the charge.
On gas denial the two pops survive and the entry meter and PC are retained.
Success pushes the result, charges execution gas and increments the unbounded
PC. Two pops from a bounded stack leave room for the result, including at entry
depth 1024. Every local run equation retains the complete supplied world under
literal underlying `pure`.

Local source agreement uses typed source words, reverses the source stack list
for `Stack.toList` and selects the Amsterdam price 3 for each operation. See EELS
`src/ethereum/forks/amsterdam/vm/stack.py:94–131` and
`src/ethereum/forks/amsterdam/vm/gas.py:68–70,180–184,379–410` at `59c1473d`.
The source charge emits its gas trace event before checking affordability.

EELS converts each signed operand immediately after its pop. The first conversion
precedes the second pop, and the second conversion precedes the charge. The
locked `ethereum-types` 0.4.1 `ethereum_types/numeric.py:675–686` conversion is
total for typed words and agrees with the two's-complement model of
`U256.toInt_eq_toNat_cond`. The Lean worker evaluates the pure Base result after
an affordable charge. Moving these conversions preserves local frame effects and
failure precedence. Trace correspondence and the source entry relation remain
open.

The file-private reference body follows the source-shaped pop, charge and
push sequence. The executable body checks the stack size before each pop and
uses the public Stack laws to rule out error arms after those checks and the
final push. An ordinary equality relates the two bodies on every frame,
price and word operation. It supplies the shared proof of the per-opcode
laws in §7.

The checked native LT calls reuse stack storage after exclusive entry. A
caller retaining a nonempty frame requires one copy at the first pop. The
later updates reuse the intermediate stack storage. Section 4 gives the
tested entry depths and paths. Ownership across interpreter steps remains
open.

For all five rows, `process_call` first consumes the source exceptional halt,
settles the meter and restores the transaction snapshot (CONTRACT O8). The
creation route also uses this consumer. The corresponding Lean runner handoff
remains open (EthVmRunner §2.4). EELS
`src/ethereum/forks/amsterdam/vm/interpreter.py:360,438–469` at `59c1473d`.

### Supplied ISZERO handler

| EELS source at `59c1473d` | Lean declaration | Domain | Effects and ordered failures | Laws and tests | Status |
|---|---|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/comparison.py:154–177` (`is_zero`) | `STFSpec.Vm.Instructions.isZero {m : Type → Type} [Monad m] : Handler m` in `STFSpec/Vm/Instructions/Comparison.lean`, exported by the Instructions facade | Every supplied context, frame and `VmWorld m`. The selected price is the raw Nat field `ctx.config.costs.opcodeIsZero`. | Pop one word, charge, push the word zero test and advance the PC. Empty underflow retains the entire frame. Gas denial retains the pop. Success changes stack, execution gas and PC. The three run equations retain the complete supplied world under literal underlying `pure`. | Five ordinary laws (§7), facade clients and eight complete frame controls (§4). | Local handler and laws supplied. The private stack worker agrees with the source-shaped reference definition (§7). Dispatch, reachable-entry and trace refinement remain open. |

Source agreement specializes the selected price to `GasCosts.OPCODE_ISZERO`
(3) and relates the source stack in reverse to `Stack.toList`. Core owns the
stack and meter laws. EthBase owns the full-word numeric result
`U256.toNat_iszero`. EELS `src/ethereum/forks/amsterdam/vm/gas.py:68–71,180–185`
and `src/ethereum/forks/amsterdam/vm/stack.py:94–131` are at `59c1473d`.

A pop from any nonempty bounded stack leaves space for the push, including from
depth 1024. An unaffordable charge retains all six meter fields and the PC.
Success advances the unbounded PC by one and leaves every other frame field
intact. Every raw context is admitted, including static contexts and PCs beyond
the end of the code. Source agreement at the handler entry also needs the source
field relations. Trace events, the source control fields and the interpreter's
exceptional settlement remain separate obligations.

`process_call` is the first gated source consumer. It catches the exceptional
halt, settles the meter and restores the transaction snapshot (CONTRACT O8).
The corresponding Lean runner handoff remains open (EthVmRunner §2.4).
EELS `src/ethereum/forks/amsterdam/vm/interpreter.py:450–469` at `59c1473d`.

### Supplied standalone bitwise handlers

The nine handlers are in `STFSpec/Vm/Instructions/Bitwise.lean` and are
exported by the Instructions facade. Each accepts every supplied context,
bounded frame and `VmWorld m` under Monad alone. The price in Lean is the
selected raw Nat field of `ctx.config.costs`.

| EELS source at `59c1473d` | Lean declaration / exact type | Raw price | Result | Laws and deterministic controls |
|---|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/bitwise.py:21–43` (`bitwise_and`) | `STFSpec.Vm.Instructions.bitwiseAnd {m : Type → Type} [Monad m] : Handler m` | `opcodeAnd` | `U256.and x y` | Six discharged local laws (§7). Zero-price success with overlapping bits (§4). |
| `src/ethereum/forks/amsterdam/vm/instructions/bitwise.py:46–68` (`bitwise_or`) | `STFSpec.Vm.Instructions.bitwiseOr {m : Type → Type} [Monad m] : Handler m` | `opcodeOr` | `U256.or x y` | Six discharged local laws (§7). Exact-price success and denial one unit below it (§4). |
| `src/ethereum/forks/amsterdam/vm/instructions/bitwise.py:71–93` (`bitwise_xor`) | `STFSpec.Vm.Instructions.bitwiseXor {m : Type → Type} [Monad m] : Handler m` | `opcodeXor` | `U256.xor x y` | Six discharged local laws (§7). Exact-price success and denial one unit below it (§4). |
| `src/ethereum/forks/amsterdam/vm/instructions/bitwise.py:96–117` (`bitwise_not`) | `STFSpec.Vm.Instructions.bitwiseNot {m : Type → Type} [Monad m] : Handler m` | `opcodeNot` | `U256.not x` | Five discharged local laws (§7). Complement of the maximum word at a price above word width, with a paired denial (§4). |
| `src/ethereum/forks/amsterdam/vm/instructions/bitwise.py:120–153` (`get_byte`) | `STFSpec.Vm.Instructions.getByte {m : Type → Type} [Monad m] : Handler m` | `opcodeByte` | `U256.byte x y` | Six discharged local laws (§7). Indices 0, 31, 32 and the maximum word, with exact-price success and one-unit-short denial (§4). |
| `src/ethereum/forks/amsterdam/vm/instructions/bitwise.py:156–183` (`bitwise_shl`) | `STFSpec.Vm.Instructions.bitwiseShl {m : Type → Type} [Monad m] : Handler m` | `opcodeShl` | `U256.shl x y` | Six discharged local laws (§7). Shift amounts 255 and 256, with exact-price success and one-unit-short denial (§4). |
| `src/ethereum/forks/amsterdam/vm/instructions/bitwise.py:186–213` (`bitwise_shr`) | `STFSpec.Vm.Instructions.bitwiseShr {m : Type → Type} [Monad m] : Handler m` | `opcodeShr` | `U256.shr x y` | Six discharged local laws (§7). Shift amounts 255 and 256, with exact-price success and one-unit-short denial (§4). |
| `src/ethereum/forks/amsterdam/vm/instructions/bitwise.py:216–245` (`bitwise_sar`) | `STFSpec.Vm.Instructions.bitwiseSar {m : Type → Type} [Monad m] : Handler m` | `opcodeSar` | `U256.sar x y` | Six discharged local laws (§7). Shift amounts 255 and 256 and both signs at the maximum amount, with exact-price success and one-unit-short denial (§4). |
| `src/ethereum/forks/amsterdam/vm/instructions/bitwise.py:248–274` (`count_leading_zeros`) | `STFSpec.Vm.Instructions.countLeadingZeros {m : Type → Type} [Monad m] : Handler m` | `opcodeClz` | `U256.clz x` | Five discharged local laws (§7). The zero and maximum words, with exact-price success and one-unit-short denial (§4). |

The binary handlers pop `x` then `y`. For BYTE and the shifts, `x` is
the index or shift amount. NOT and CLZ pop `x`. First-pop underflow
retains the entry frame. Second-pop underflow in a binary handler retains the
first pop. Both underflows precede the charge. Gas denial keeps the completed
pops, PC and complete meter. A successful charge permits the push because at
least one pop from a bounded stack leaves space, including at depth 1024.
Success changes the stack, execution gas and unbounded PC. The complete run
equations retain the supplied world under literal underlying `pure`.

Source agreement at handler entry relates typed U256 values and reverses the
source stack for `Stack.toList`. The pinned selectors are 5 for CLZ and 3 for
the other eight instructions. The source charge emits the gas trace event before
the affordability test. EthBase owns the word models `U256.toBitVec_and`,
`U256.toBitVec_or`, `U256.toBitVec_xor`, `U256.toBitVec_not`, `U256.toNat_byte`,
`U256.toBitVec_shl`, `U256.toBitVec_shr`, `U256.toBitVec_sar` and
`U256.toNat_clz`. EELS `src/ethereum/forks/amsterdam/vm/stack.py:94–131`,
`src/ethereum/forks/amsterdam/vm/gas.py:70–71,186–194,379–410` at `59c1473d` and
locked `ethereum-types` 0.4.1 `ethereum_types/numeric.py:256–309,670–673`.

SHL converts both operands to `Uint` before the source charge. SAR converts the
amount to `int` and the value to a signed integer before the charge, including
on gas denial. Those conversions are total on the typed operands. The local
result laws describe the complete frame effects. Correspondence for these
conversion timings and the gas event belongs to the source trace obligation.
Locked `ethereum-types` 0.4.1 `ethereum_types/numeric.py:44–48,321–322,539–540,675–686`.

Two private reference bodies follow the unary and binary source sequences.
The executable bodies test stack depth before each pop. The Core Stack laws
rule out errors after those depth checks and after the final push. An ordinary
equality for each body establishes the same result for every frame, raw price
and word operation. Section 4 gives the native entry controls.

For all nine rows, `process_call` first consumes the source exceptional halt,
settles the meter and restores the transaction snapshot (CONTRACT O8).
The creation route also uses this consumer. The corresponding Lean handoff
remains open (EthVmRunner §2.4). EELS
`src/ethereum/forks/amsterdam/vm/interpreter.py:360,438–469` at `59c1473d`.

### Supplied standalone POP handler

| EELS source at `59c1473d` | Lean declaration / exact type | Domain | Effects and ordered failures | Laws and tests |
|---|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/stack.py:26–46` (`pop`) | `STFSpec.Vm.Instructions.pop {m : Type → Type} [Monad m] : Handler m`, defined in `STFSpec/Vm/Instructions/Pop.lean` and exported by the Instructions facade | Every supplied context, bounded frame and `VmWorld m`. The price is the raw Nat `ctx.config.costs.opcodePop`. | Empty stack halts with the whole entry frame before charging. Gas denial retains the actual residual stack, PC and whole meter. Success retains the residual stack, reduces execution gas by the selected price and advances the PC by one. Every result retains the supplied world. | Five discharged local laws (§7). Complete frame controls for both failures and exact, surplus, zero and greater-than-word-width prices (§4). |

Source agreement at handler entry reverses the typed EELS word stack
for `Stack.toList`. The pinned price is 2. The source gas trace event
precedes the affordability test. EELS
`src/ethereum/forks/amsterdam/vm/stack.py:94–112` and
`src/ethereum/forks/amsterdam/vm/gas.py:69,201,379–410` at `59c1473d`.

The private reference body pops before charging. The executable checks
the stack size before taking ownership of its storage. Core's Stack laws
give an ordinary equality of these bodies on every raw frame and price.
The source `process_call` consumes exceptional halts under O8. The Lean
settlement handoff remains open (EthVmRunner §2.4). EELS
`src/ethereum/forks/amsterdam/vm/interpreter.py:438–469` at `59c1473d`.

### Supplied standalone JUMP and JUMPI handlers

The Instructions facade exports both handlers from
`STFSpec/Vm/Instructions/ControlFlow.lean`. Each has the signature
`{m : Type → Type} [Monad m] : Handler m`, accepts every supplied
frame, context and world, and retains the supplied world.

| EELS source at `59c1473d` | Lean declaration | Effects and ordered failures | Laws and tests |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/control_flow.py:45–68` (`jump`) | `STFSpec.Vm.Instructions.jump` | Pop the destination, charge `ctx.config.costs.opcodeJump`, then check `ctx.jumpdests` at the destination's Nat value. A valid destination becomes the PC. Underflow retains the entry frame. Gas denial retains the pop. An invalid destination retains the pop, debit and entry PC. | Three run laws and two Id laws (§7), complete frame controls (§4). |
| `src/ethereum/forks/amsterdam/vm/instructions/control_flow.py:70–98` (`jumpi`) | `STFSpec.Vm.Instructions.jumpi` | Pop the destination then the condition. Underflow on the second pop retains the first pop. Charge `ctx.config.costs.opcodeJumpi`. Gas denial retains both pops. A paid zero condition advances the entry PC by one and skips membership. A paid nonzero condition checks the supplied map as in JUMP. | Five run laws and two Id laws (§7), complete frame controls (§4). |

The selected execution prices are raw Nat values. The pinned prices are
8 and 10, respectively. Ordinary equalities relate both executable
handlers to their private source-shaped references using the Core
stack and charge laws. Frame assembly must establish that the
immutable destination map corresponds to the executing code.
The source trace and the exceptional settlement handoff remain open
(EthVmRunner §2.4, CONTRACT O8).
EELS `src/ethereum/forks/amsterdam/vm/gas.py:195–196,379–410`,
`src/ethereum/forks/amsterdam/vm/stack.py:94–112` and
`src/ethereum/forks/amsterdam/vm/interpreter.py:438–469` at `59c1473d`.

### Supplied standalone JUMPDEST handler

| EELS source at `59c1473d` | Lean declaration and type | Domain | Effects and ordered failures | Laws and tests |
|---|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/control_flow.py:149–171` (`jumpdest`) | `STFSpec.Vm.Instructions.jumpdest {m : Type → Type} [Monad m] : Handler m`, defined in `STFSpec/Vm/Instructions/ControlFlow.lean` and exported by the Instructions facade | Every supplied frame, context and world. The price is the raw Nat `ctx.config.costs.opcodeJumpDest`. | Gas denial retains the entry frame. Payment advances the Nat PC by one and changes only execution gas. Both results retain the stack and supplied world. | Four local laws (§7), complete frame and native identity controls (§4). |

The pinned price is 1. The source leaf charges and advances the PC
without using the destination map. The source gas trace event precedes
the affordability test. The source `process_call` consumes exceptional
halts under O8. See EthVmRunner §2.4 for the Lean settlement handoff.
EELS `src/ethereum/forks/amsterdam/vm/gas.py:197,379–410` and
`src/ethereum/forks/amsterdam/vm/interpreter.py:438–469` at `59c1473d`.

### Supplied standalone PUSH handler

| EELS source at `59c1473d` | Lean declaration / exact type | Domain | Effects and ordered failures | Laws and tests |
|---|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/stack.py:49–79` (`push_n`) | `STFSpec.Vm.Instructions.pushN (n : Fin 33) {m : Type → Type} [Monad m] : Handler m`, in `STFSpec/Vm/Instructions/Push.lean` and exported by the Instructions facade | Every supplied frame, context and world with width `n`. Use the raw Nat price from `opcodePush0` at width zero and `opcodePush` at every other width. | Gas denial retains the entry frame. A full stack after payment retains the debit and the rest of the entry frame. Success pushes the exact padded immediate and adds `1 + n.val` to PC. Each outcome retains the supplied world. | Five ordinary run and accounting laws (§7). Facade guards, raw offset and pinned-source frame comparisons, and native ownership controls (§4). |

The private reference decodes the padded Nat window through
`U256.ofBeBytes?`. The width bound proves that the window fits and gives
the exact unsigned value using `Uint.ofBeBytes`. The executable checks
capacity after payment and uses that exact value on the nonfull path.
An ordinary private equality covers both branches for every raw PC.
Section 7 states the remaining source correspondence.

The pinned prices are 2 for PUSH0 and 3 for PUSH1–PUSH32. EELS
`gas.py:69–70,223–224` at `59c1473d`.

### Supplied standalone DUP and DUPN handlers

The Instructions facade exports both handlers from
`STFSpec/Vm/Instructions/Dup.lean`. Both use the class-free `Handler`
alias, require a `Monad` instance and return the supplied world under literal `pure`.

| EELS source at `59c1473d` | Lean declaration and type | Domain | Effects and ordered failures | Laws and tests |
|---|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/stack.py:82–107` (`dup_n`) | `STFSpec.Vm.Instructions.dupN (ordinal : Fin 16) {m : Type → Type} [Monad m] : Handler m` | Every supplied context, frame and world. The ordinal is zero-based from the top of the stack. | Charge `opcodeDup`. Denial retains the entry frame. Check depth before capacity. Either paid failure retains the debit, entry stack and PC. Success copies the selected word onto the stack and advances the PC by one. | Six run and accounting laws (§7) and complete facade controls (§4). |
| `src/ethereum/forks/amsterdam/vm/instructions/stack.py:213–242` (`dupn`) | `STFSpec.Vm.Instructions.dupn {m : Type → Type} [Monad m] : Handler m` | Every supplied context, frame and world. Paid source agreement uses the fitting Q91 start (§7). | Charge `opcodeDupn`. Denial retains the entry frame. After payment, read the padded byte at `pc + 1` and call `decodeSingle`. Invalid decode precedes the depth and capacity checks. A successful decode supplies the one-based depth. Success copies the selected word and advances the PC by two. Paid failures retain the debit, entry stack and PC. | Seven run and accounting laws (§7) and complete facade controls (§4). |

The two raw price fields are independent. Both pinned prices are 3.
Both handlers share a private worker for the depth check and copy.
An ordinary equality relates it to the direct Stack peek and push
on every raw frame. The paid DUPN read uses the exact Nat offset,
including values beyond the word range. EELS
`src/ethereum/forks/amsterdam/vm/gas.py:70,225–227`,
`src/ethereum/forks/amsterdam/vm/memory.py:63–83` and
`src/ethereum/forks/amsterdam/vm/stack.py:25–53,115–131` at `59c1473d`.

### Supplied standalone bounded context-word handlers

Each declaration below has the signature `{m : Type → Type} [Monad m] : Handler m`.
The Instructions facade exports them from `STFSpec/Vm/Instructions/ContextWords.lean`.
All accept any supplied frame, context and world. Each opcode charges its
own raw Nat price from `ctx.config.costs`. Denial retains the entry frame.
A full stack after payment retains the debit, entry stack and entry PC.
Success pushes the selected word and advances the Nat PC by one. Every
result retains the supplied world under literal `pure`.

| EELS source at `59c1473d` | Lean declaration | Selected price field | Selected word |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/environment.py:35–55` (`ADDRESS`) | `STFSpec.Vm.Instructions.address` | `opcodeAddress` | `ctx.currentTarget.toU256` |
| `src/ethereum/forks/amsterdam/vm/instructions/environment.py:89–110` (`ORIGIN`) | `STFSpec.Vm.Instructions.origin` | `opcodeOrigin` | `ctx.txEnv.origin.toU256` |
| `src/ethereum/forks/amsterdam/vm/instructions/environment.py:113–133` (`CALLER`) | `STFSpec.Vm.Instructions.caller` | `opcodeCaller` | `ctx.caller.toU256` |
| `src/ethereum/forks/amsterdam/vm/instructions/environment.py:136–156` (`CALLVALUE`) | `STFSpec.Vm.Instructions.callvalue` | `opcodeCallValue` | `ctx.value` |
| `src/ethereum/forks/amsterdam/vm/instructions/block.py:71–102` (`COINBASE`) | `STFSpec.Vm.Instructions.coinbase` | `opcodeCoinbase` | `ctx.blockEnv.coinbase.toU256` |
| `src/ethereum/forks/amsterdam/vm/instructions/block.py:105–136` (`TIMESTAMP`) | `STFSpec.Vm.Instructions.timestamp` | `opcodeTimestamp` | `ctx.blockEnv.time` |
| `src/ethereum/forks/amsterdam/vm/instructions/block.py:172–202` (`PREVRANDAO`) | `STFSpec.Vm.Instructions.prevRandao` | `opcodePrevRandao` | `U256.ofBeBytes32 ctx.blockEnv.prevRandao` |
| `src/ethereum/forks/amsterdam/vm/instructions/block.py:238–265` (`CHAINID`) | `STFSpec.Vm.Instructions.chainId` | `opcodeChainId` | `U256.ofNat ctx.blockEnv.chainId.toNat` |
| `src/ethereum/forks/amsterdam/vm/instructions/block.py:268–298` (`SLOTNUM`) | `STFSpec.Vm.Instructions.slotNumber` | `opcodeSlotNum` | `U256.ofNat ctx.blockEnv.slotNumber.toNat` |

The selected conversions are exact at the current field types. The four
addresses widen their unsigned value, and the two U64 fields widen to
U256. PREVRANDAO decodes all 32 bytes in big-endian order. CALLVALUE and
TIMESTAMP use the existing U256 values. The pinned price is 2 for each
opcode. A private ordinary equality relates the shared executable worker
to the direct charge, read and push reference. Section 7 gives the five
local laws for each handler, and §4 records the complete frame controls.
EELS `src/ethereum/forks/amsterdam/vm/gas.py:69,200,205–208,212,215,217,221,379–410`
and `src/ethereum/forks/amsterdam/vm/stack.py:115–131` at `59c1473d`.

### Supplied standalone SWAPN and EXCHANGE handlers

The Instructions facade exports both handlers from
`STFSpec/Vm/Instructions/DynamicSwap.lean`. Each retains the complete
supplied world under literal `pure`.

| EELS source at `59c1473d` | Lean declaration and type | Domain | Effects and ordered failures | Laws and tests |
|---|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/stack.py:245–278` (`swapn`) | `STFSpec.Vm.Instructions.swapn {m : Type → Type} [Monad m] : Handler m` | Every supplied context, frame and world. Paid source agreement uses the fitting Q91 start (§7). | Charge `opcodeSwapn`. Denial retains the entry frame. Read the padded byte at `pc + 1`, then call `decodeSingle`. Invalid decode precedes the depth check. Success swaps top-relative indices `0` and `n` and adds two to the PC. Paid failures retain the debit, entry stack and PC. | Six ordinary run and accounting laws (§7) and complete facade controls (§4). |
| `src/ethereum/forks/amsterdam/vm/instructions/stack.py:281–314` (`exchange`) | `STFSpec.Vm.Instructions.exchange {m : Type → Type} [Monad m] : Handler m` | Every supplied context, frame and world. Paid source agreement uses the fitting Q91 start (§7). | Charge `opcodeExchange`. Denial retains the entry frame. Read the padded byte at `pc + 1`, then call `decodePair`. Invalid decode precedes the depth check. Success swaps the decoded top-relative indices and adds two to the PC. Paid failures retain the debit, entry stack and PC. | Six ordinary run and accounting laws (§7) and complete facade controls (§4). |

The raw prices are independent. Both pinned prices are 3. The read uses
the exact Nat offset on every raw frame. A private ordinary equality
relates each executable worker to the direct Core swap model.
EELS `gas.py:70,228–229`, `memory.py:63–83` and
`stack.py:25–91` at `59c1473d`.

### Supplied standalone GASPRICE and BASEFEE handlers

| Source | Lean declaration | Entry domain | Ordered effects | Checks and status |
|---|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/environment.py:307–327` (`gasprice` at the pin) | `STFSpec.Vm.Instructions.gasprice {m : Type → Type} [Monad m] : Handler m` | Every supplied context, frame and world. The raw fee and tariff are Nat. | Charge `opcodeGasPrice`, check `effectiveGasPrice` for U256, and push the checked value. Paid conversion failure gives `VmFault.u256Overflow .gasPrice`. | Private ordered action and accounting laws (§7) and complete facade controls (§4). |
| `src/ethereum/forks/amsterdam/vm/instructions/environment.py:539–559` (`base_fee` at the pin) | `STFSpec.Vm.Instructions.baseFee {m : Type → Type} [Monad m] : Handler m` | Every supplied context, frame and world. The raw fee and tariff are Nat. | Charge `opcodeBaseFee`, check `baseFeePerGas` for U256, and push the checked value. Paid conversion failure gives `VmFault.u256Overflow .baseFee`. | Private ordered action and accounting laws (§7) and complete facade controls (§4). |

Both entries use the private worker in `STFSpec/Vm/Instructions/FeeWords.lean`
through the Instructions facade. After successful conversion it checks
capacity so a nonfull frame can transfer ownership of its stack. An ordinary
equality relates that push to the direct Core Stack push on every frame.

### Supplied standalone fixed SWAP handlers

| EELS source at `59c1473d` | Lean declaration and type | Domain | Effects and ordered failures | Laws and tests |
|---|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/stack.py:110–141,195–210` (`swap_n`, `swap1`–`swap16`) | `STFSpec.Vm.Instructions.swapN (n : Fin 16) {m : Type → Type} [Monad m] : Handler m` | Every supplied context, frame and world. The ordinal `n` corresponds to opcode `0x90 + n.val` and top-relative depth `n.val + 1`. | Charge `opcodeSwap`. Denial retains the entry frame. After payment, missing depth halts with the paid frame. Success exchanges both original cells through Core `Stack.swap?` and advances the Nat PC by one. All outcomes retain the supplied world. | Three complete run laws and two local Id laws (§7). All 16 source bindings, complete frame controls and native ownership checks (§4). |

The pinned price is 3 (`vm/gas.py:70,226`). The private executable checks
depth after payment, then gives an exclusive stack to `Stack.swap?` when the
caller supplies one. An ordinary equality relates the worker to a direct
`Stack.swap?` match for every raw frame. Immediate SWAPN and EXCHANGE use
their separate Q91 read and decode.

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
| `src/ethereum/forks/amsterdam/vm/instructions/__init__.py:32–220` (`Ops`) | `STFSpec.Vm.Instructions.Ops` in `STFSpec/Vm/Instructions/Ops.lean`, exported by `STFSpec.Vm.Instructions` | Exactly 153 nullary constructors, one per source member | Pure finite vocabulary; no defaults or instances | Generated inductive infrastructure; private exhaustive constructor coverage in `OpsCallerProofs` | Supplied. Complete source member and byte checks in §4 |
| Same source member assignments | `Ops.toByte : Ops → UInt8` | Every opcode, without a frame, gas, hash, monad or admission premise | Pure total literal match; no failure | `Ops.ofByte_toByte`; all 153 source-bound literal encoder pairs in private facade controls | Supplied; ordinary round trip discharged |
| Same source member assignments, and their complement in 0–255 | `Ops.ofByte? : UInt8 → Option Ops` | Every byte | Pure total lookup. Returns `some` for the 153 assigned bytes and `none` for the 103 holes, including `0xFE`. No error conversion or charge | `Ops.toByte_ofByte` and all 256 literal decode equations | Supplied. A private theorem proves equality with the literal reference definition (§7) |

Constructors follow lowercase EELS member spelling (`iszero`, `calldataload`,
`slotnum`, `dupn`, and so on); reserved `RETURN` becomes `return_`, following the
existing handler convention. Source `KECCAK` is the single member at `0x20`.
The two enum laws in §7 are its only authored public laws. The source checks in §4
bind each constructor to its assigned byte, since both round trips would also hold
for a consistent permutation. Dispatch, `step`, the remaining handlers and all
composed execution, error and resource obligations remain open.

### Supplied raw creation suspension carrier

| EELS split origin | Lean declaration | Domain | Effects / ordered failures | Laws and clients | Status |
|---|---|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/system.py:59–185` (`generic_create`, dispatch at `:133–171`, outcome at `:177–185`) | `STFSpec.Vm.Instructions.CreateRequest` in `STFSpec/Vm/Instructions/CreateRequest.lean`, exported by `STFSpec.Vm.Instructions` | Exactly seven independent fields in §5 order: two unrestricted `Nat` grants, nominal `U256` endowment, two nominal `Address` values, complete `Bytes` init code and `Bool` account-charge flag; no Monad/hash binder or admission premise | Pure raw construction/projection; no state access, hashing, grant computation, preflight, collision, child execution or failure | Generated record infrastructure only; private `CreateRequestCallerProofs` facade clients prove all-field constructor preservation, reconstruction, complete-field equality and every independent update. Public Base observers/laws retain every word/address and ordered byte; complete finite controls cover zero/huge independent grants, full-width values, equal/unequal addresses, empty/duplicate bytes and both booleans | Supplied raw carrier and private client proofs/controls; whole `generic_create` correspondence, producers and consumers unimplemented |

This is the Lean-side suspension interface specified in §5, not an implementation
of an EELS function. The source read identifies where the seven values arise and
where they are consumed. It supplies no source/admission bridge, gas-correctness
proof, handler or resume implementation. The immutable CREATE consumer is supplied below.

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
| Project handler interface for the R-ENV-3 partition and D17 suspension split; no Python Handler alias | `STFSpec.Vm.Instructions.Handler` in `STFSpec/Vm/Instructions/Handler.lean`, exported by the Instructions facade | Exactly `(ctx : FrameCtx) → Frame → VmM m (StepResult ctx)` for arbitrary `m : Type → Type`, without a Monad or hash instance | Alias formation only; no execution or changed context returned | Private exact alias/application/run-type clients form the alias without class premises, retaining the original ctx index and Core's existing state/error transformer order | Supplied signature. The handler rows above identify the supplied operations. `step` and dispatch remain open |

These are the guided Lean control interfaces, not Python counterparts or opcode
implementations. Call/create retain independent complete supplied requests and
frames; their only local proofs are `ctx.depth < STACK_DEPTH_LIMIT` and
`parent.stack.size < STACK_DEPTH_LIMIT`. The literal Core limit is independent of
`ctx.config.limits.stackDepthLimit`. Construction establishes no preflight,
withholding, staticness, gas-progress, child settlement or F11 policy.

### Supplied immutable CREATE context

| EELS at `59c1473d` | Lean declaration | Domain and result | Laws and status |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/system.py:133–150` (`generic_create` context at dispatch) | `childCtxOfCreate` in `STFSpec/Vm/Instructions/CreateChildContext.lean`, exported by the Instructions facade | Any parent and request with `ctx.depth < STACK_DEPTH_LIMIT`. Uses the request's caller, contract address, endowment and init code. The child has empty calldata, no code address, value transfer enabled, static mode false and precompiles enabled. Core builds the jump map from the init code. The child inherits both environments, config and system address. | Supplied complete `childCtxOfCreate_eq` and two F8 policy projections in §7. Section 4 covers the result at bounded source and raw inputs. Dispatch and request production remain open. |

### Supplied mutable child frame initialization

| EELS source at `59c1473d` [V] | Lean declaration | Domain and result | Tests and status |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/system.py:151–165`, within `generic_create`, with defaults at `src/ethereum/forks/amsterdam/vm/gas.py:295–311` | `STFSpec.Vm.Instructions.childFrame` in `STFSpec/Vm/Instructions/ChildFrame.lean`, exported by the Instructions facade | Supply `create_message_gas` as the execution grant and `create_message_state_gas_reservoir` as the reservoir. The constructor initializes the nine mutable fields as specified in §7. | Mutable initialization supplied. Private complete facade equation and controls in §4. |
| `src/ethereum/forks/amsterdam/vm/instructions/system.py:420–434`, within `generic_call`, with the same meter defaults | Same `childFrame` | Supply `params.gas` as the execution grant and `params.state_gas_reservoir` as the reservoir. The same initialization applies to every raw frame and pair of grants. | Mutable initialization supplied. Same private facade equation and controls in §4. |

EELS initializes these fields inline at both child entry sites. The rows cover
those assignments and the three meter defaults. Context and outcome are separate
from the mutable frame. The surrounding operations still need source refinement
for grant computation, dispatch, execution and resume.

### Supplied settled child outcome carrier

| EELS ownership context at `59c1473d` | Lean declaration | Domain | Effects / ordered failures | Laws and clients | Status |
|---|---|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/__init__.py:221,226–228` incorporation assertions; `src/ethereum/forks/amsterdam/vm/interpreter.py:449–465` child error handling | `STFSpec.Vm.Instructions.ChildOutcome` in `STFSpec/Vm/Instructions/ChildOutcome.lean`, exported by `STFSpec.Vm.Instructions` | Exactly `frame : Frame`, `output : Bytes`, `error : Option FrameError` and supplied `settled : ChildSettled frame error.isSome`; complete payloads with only the existing Core predicate | Pure construction/projection with an already supplied local proof; no runtime check, settlement effect or error | Generated record infrastructure only; private `ChildOutcomeCallerProofs` facade clients check complete construction/projections, dependent reconstruction/elimination, determination and proof-aware replacements, both predicate branches, complete error/output payloads and negative elaboration controls (§4) | Supplied carrier and private controls. EthVmRunner §3 owns the proof-taking result adapter. Actual producer reachability, rollback, source-Evm refinement, incorporation, runner settlement/proof production and resume remain open. |

This is the Lean-side return carrier of §5, not a Python class or an implementation
of child handling. Core owns the transparent `ChildSettled` predicate and its
constructive decidability. The stored proof chooses neither F11 production route.
Success requires only zero committed spill; failure also resets pending spill,
signed refund and reservoir to baseline. Output, execution gas, successful refund
and every unrelated frame field have no additional condition. Halt and revert
share `error.isSome = true` while retaining their distinct complete payloads.

**External semantics.** `ethereum_types` `U256` operations used by handlers: `wrapping_add/sub/mul`, `//`, `%`, `to_signed`, `from_signed` (raises for out-of-range; unreachable from these handlers because all results are in range) [V], `from_be_bytes`, `to_be_bytes32`, `bit_length`, `~`, `&`, `|`, `^`, `>>`; `Uint(...)` conversions (exact, unbounded); `U8` for immediates; Python's `pow(b, e, 2^256)`; Python negative list indexing in BLOCKHASH (IndexError beyond length) and in DUPN/SWAPN/EXCHANGE (always in range after the checks). Each must be given by an `EthBase` `U256`/`Nat` law, not by Lean `BitVec` instances (D1).

### Supplied TSTORE handler

| EELS source at `59c1473d` | Lean declaration | Effects and ordered failures | Laws and tests |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/storage.py:189–216` | `STFSpec.Vm.Instructions.tstore` in `STFSpec/Vm/Instructions/Tstore.lean`, exported by Instructions | Static context halts before either pop. Pop the full slot key and then the value. Charge the configured execution price before the State write at the current target. Advance PC by one on success. | Private complete action equations and equality with the ordinary reference in §7. Deterministic full-stack, meter, frame and transient-map controls in §4. |

### Supplied RETURN and REVERT handlers

| Source at the pin | Lean declaration and domain | Ordered outcomes | Validation |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/system.py:307–337` | `return_ {m : Type → Type} [Monad m] : Handler m` in `STFSpec/Vm/Instructions/ReturnRevert.lean` | Pop the offset and length. Q92 charges the explicit ZERO plus the seeded extension cost. On payment, expand, read the admitted exact window and return `.stop`. | Four ordinary local laws in §7 and complete controls in §4. |
| `src/ethereum/forks/amsterdam/vm/instructions/system.py:987–1016` | `revert {m : Type → Type} [Monad m] : Handler m` in `STFSpec/Vm/Instructions/ReturnRevert.lean` | Pop the offset and length. Q92 charges the seeded extension cost. On payment, expand, read the admitted exact window and return `.revert`. | Four ordinary local laws in §7 and complete controls in §4. |

Both operations are supplied through the Instructions facade. The laws
give complete residual frames and the same supplied world for all four
branches. The selected raw charges observe independently supplied ZERO
and memory-word prices. See §2.9 for their source order and §7 for the
local Memory admission. The private executable pop worker consumes the
nonempty stack with a size witness. An ordinary equality identifies
it with the pop reference on every frame, including empty ones (D25).

### Supplied CALLDATACOPY and CODECOPY handlers

| EELS source at `59c1473d` | Lean declaration | Effects and ordered failures | Laws and tests |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/instructions/environment.py:208–243` | `calldatacopy {m : Type → Type} [Monad m] : Handler m` | Pop destination, source and length in order. Then charge the call-data copy base, copy words and destination expansion before writing the padded bytes from `ctx.callData`. | Complete local laws (§7) and byte-level facade controls (§4). |
| `src/ethereum/forks/amsterdam/vm/instructions/environment.py:269–304` | `codecopy {m : Type → Type} [Monad m] : Handler m` | Use the code copy base and `ctx.code` with the same operand, charge and memory order. | Complete local laws (§7) and byte-level facade controls (§4). |

The Instructions facade exports both entries from
`STFSpec/Vm/Instructions/LocalCopy.lean`. The provider quote prices only
the destination window. The two bases, per-word price, memory-word price
and raw ZERO seed are the existing `VmConfig` fields. On a paid run the
Memory laws supply expansion alignment and the local write proof.
`bufferRead` takes the full U256 source offset and length. EELS
`vm/gas.py:761–798` and `vm/memory.py:20–36,63–83`.

### Supplied MCOPY handler

| EELS source at `59c1473d` | Lean declaration | Complete local effect |
|---|---|---|
| `vm/instructions/memory.py:142–175`, `vm/memory.py:20–60` | `mcopy` in `LocalCopy.lean` | Pop destination, source and length. Quote source before destination and charge before expanding. Read the entire source slice from that expansion and write its snapshot to the destination. |

### Supplied LOG0 through LOG4 handlers

| EELS source at `59c1473d` | Lean declaration | Complete local effect |
|---|---|---|
| `vm/instructions/log.py:28–86` | `logN (n : Fin 5)` in `LogOpcode.lean` | Pop the window and exactly `n` topics. Charge the full configured cost. Expand before checking static mode. A successful call appends the whole log in pop order and advances PC. |

## 4. Tests

**RETURN and REVERT controls (Q92).**

- `ReturnRevertControls.lean` checks each opcode through the Instructions
  facade. Compare the complete frame and supplied world at first
  underflow, second underflow and denial after both pops. Use asymmetric
  offset and length, nonempty residual stack, distinct nonzero meter
  fields and existing `returnData`. Repeat a failing case with too
  little gas to establish which guard runs first.
- At the pinned ZERO 0, exercise zero length at maximum offset, a
  nonempty in-bounds window, and a window crossing a word boundary.
  Check payment exactly at the required gas, excess gas for a paid
  result, and one unit below a positive charge. Check the appended
  zeros, byte order, full execution debit, nominal terminal constructor,
  unchanged PC and independent `returnData`. Compare direct handlers
  against the authenticated pinned source in normal and optimized
  Python. The source's outer halt or revert settlement has its own
  Runner comparison.
- Exercise raw ZERO 7 with the pinned memory-word price. A zero-length
  window at maximum offset requires 14 gas for RETURN and 7 for REVERT.
  With one word of initial memory, offset 30 and length 4 require 17
  and 10 gas. Test exact payment and denial one unit below each
  threshold. Vary ZERO and the memory-word coefficient independently
  in raw Lean controls. Isolated counterfactual source closures provide
  evidence for the arithmetic at nonzero ZERO. The pinned comparison
  continues to use the original Amsterdam constants. The retained-memory
  guard writes a later value and checks the original bytes and output snapshot.

Both interpreted and compiled facade runs match 32 original pinned leaf
cases per Python mode, 80 baseline and isolated nonzero-ZERO cases,
and 12 independent raw mathematical cases. Three further original
Runner cases record post-handler settlement. The native client checks
40 exclusive and retained entry cases, including full stacks. It checks
pointer identity separately from the complete frame and output values.
The observed call order is one or two pops on underflow, both pops then
pricing and charge on denial, and expansion then reading after payment.
The observed exclusive stack reuses its backing through successful pops.
Retained frames keep the original stack and bytes. Growth reuses the
spare exclusive memory backing in the capacity case and copies the
retained backing. The output bytes remain a snapshot after a later write.
These are finite ownership observations.

**Supplied opcode controls.**
`STFSpec/Conformance/Vm/Instructions/OpsCallerProofs.lean` imports only the public
Instructions facade. Private clients derive injectivity and exclusion of unassigned
bytes from the two public laws. An exhaustive constructor match checks all 153
literal encoder pairs. At default Lean settings, 256 `rfl` equations check every
decoder result against the pinned source assignments. Warning-fatal compilation,
the declaration audit and kernel replay cover the leaf, facade and clients.

An out-of-tree comparison imports the pinned EELS `Ops` enum under Python in normal
mode and with `-O`. It checks all 256 native Lean results against the source enum,
including member names, assigned bytes and holes. The committed literal controls
record the same assignments. The standalone handlers have the controls below.
EEST guest execution remains open.

**Supplied raw carrier controls.**
`STFSpec/Conformance/Vm/Instructions/CreateRequestCallerProofs.lean` imports only
`STFSpec.Vm.Instructions`. Private generic clients cover the complete seven-field
constructor/projection tuple, reconstruction, equality from all fields and all
seven independent record updates with preservation of every other field. Public
Base word/address/byte observations and byte-construction laws avoid provider
storage unfolding. Four complete deterministic observations include independently
zero and greater-than-256-bit grants, maximum/full-width nominal values, distinct
and equal caller/destination, empty and ordered duplicate init bytes, and both
charging flags. These checks cover raw data retention. CREATE and CREATE2
opcode and source conformance tests remain unimplemented.

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
public Instructions facade and provider laws. Generic clients consume all forty-six
complete case laws and retain complete result/world equations; concrete Id clients
consume the twenty-two accounting/progress laws. MUL/DIV success clients also derive
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
The independent Python model checks all 1257 ordered complete observations, preserving the accepted 843-case prefix.
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

The 414 frozen EXP inputs in `arithmetic_exp_inputs.json` append that 843-case
prefix. Independent expected words use builtin modular `pow`; byte count uses
integer bit length. Controls cover zero/one/255/256/257/2^255/max exponents,
below/equal/above all 31 internal byte boundaries, c−1/c and independent raw-price
c−1/c/c+1 boundaries, zero/one/high/full-width bases, `0^0`, zero/one/parity,
wrap and operand order, base-independent charge pairs, ten full-stack cases and
24 fixed-seed raw cases. Both context flags, huge PC, complete nontrivial frame,
signed refund and both spills remain observed. The new cases comprise 27
underflows, 143 OOG results and 244 continuations.

EXP uses a separate ten-cell TSV branch with both raw price fields; the old
nine-cell input path and output keys stay unchanged. EXP observations expose
`expBase` and `expPerByte`, including underflow without an exponent; no derived
`cost` field is supplied. Native and interpreted decoder regressions reject
missing/extra cells, malformed/negative numbers, unknown opcodes, invalid flags,
over-width words and stacks longer than 1024. Normal/-O parser controls reject
reversed power operands, proper-shaped wrong results, base-dependent or rounded-
down byte counts, zero-needs-one-byte counts, signed/truncated exponents, swapped
or sibling/tier prices, wrapped gas arithmetic, omitted zero-exponent charges,
wrong partial stacks/meter/PC, changed complete fields/world samples/phi, raw-field
type/value/omission/addition errors and malformed/duplicate/omitted/reordered rows.
The strict 3,000,000-byte parser bound is unchanged.

The source mode authenticates the unreplaced pin, original loaded source bytes,
installed dependency RECORDs/locked versions and raw locked numeric/RLP wheels,
using the frozen EELS Python 3.13.5 interpreter with `-I -B` in normal and optimized
modes as the driver docstring specifies. It executes the original ADD/SUB/MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND/ADDMOD/MULMOD/EXP, pop/push, charge, signed observations/construction, get_sign, SIGNEXTEND byte conversions and numeric methods
on real Evm/GasMeter objects and a fail-on-access supplied PreState. The sixty
ADD/SUB cases with selected price 3, ninety-two MUL/DIV cases with selected
price 5 and 171 SDIV/MOD/SMOD cases with selected price 5 retain complete source
dataclass observations before and after, including failed-pop/charge partial
states. Each mode preserves those 323 direct calls as a prefix and executes 216 additional
SIGNEXTEND calls at source price 5, including complete source Evm observations.
Those 539 calls remain a prefix; 160 additional ADDMOD/MULMOD calls execute at
source price 8 in each mode. Original Uint multiplication/remainder/equality and
the original three-pop bodies are included in the authenticated function set.
Those 699 original calls remain in the same order, followed by 265 EXP calls
selected only by raw price pair 10/50, including underflow and OOG. Both modes
therefore execute 964 direct calls; the remaining 293 raw-price cases are
mathematical Lean controls without source execution. EXP authentication retains
the original function and Uint bit-length/floor-division/modular-power/conversion
methods, actual `ExecutionGas`, pop/push/charge/GasCosts bindings, raw prices,
`U256.MAX_VALUE` and modulus construction. Builtin pow is authenticated separately
by its original binding and identity; it has no Python code object. Actual source exceptions
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

**Supplied binary comparison controls.**
`STFSpec/Conformance/Vm/Instructions/ComparisonCallerProofs.lean` applies all
thirty public local laws through the Instructions facade. The success clients
use the Base word laws to obtain the signed and unsigned numeric result models.

`STFSpec/Conformance/Vm/Instructions/ComparisonGuards.lean` checks all nine
frame fields, the result tag and sampled world values in 25 direct calls.
All five handlers encounter empty and singleton underflow at zero available gas.
The five independent raw prices are 0, 1, 7, 2^300 + 3 and 13, with common
tier 19. Each exact budget continues, and each positive price denies one unit
less after both pops. The controls also exercise true and false results,
signed boundaries, full-word equality, a PC above word width and stack depth
1024. The run laws in §7 give complete world retention.

A private comparison calls the Lean facade and checks the complete mutable
frames and result tags against 80 authenticated direct source observations in
each saved Python mode at price 3. The cases include both static flags, both
underflow positions, gas denial, signed edges, full stacks and PC increments
across the 64-bit and 256-bit boundaries. The source observations also record
the signed conversion and gas helper order separately. Dedicated pinned EEST
members in `ported_static/vmBitwiseLogicOperation` cover all five opcodes.

Private native controls compare the complete frame and result of the original
and revised LT routes. They observe entry ownership, the copies during stack
updates and the returned stack pointer at runtime depths 0, 1, 2, 8, 256 and
1024. Each depth uses both exclusive and retained entry and execution budgets
of 2 and 3. They also check the complete frame retained by the caller.
The general handler differential, composed `step` and guest fixture execution
remain open.

**Supplied ISZERO controls.**
`STFSpec/Conformance/Vm/Instructions/ComparisonCallerProofs.lean` uses the
public facade to derive the complete ordered run equations, the numeric
result model, whole-world retention on success, exact accounting at zero
price and progress at positive price.

`STFSpec/Conformance/Vm/Instructions/ComparisonGuards.lean` checks all nine
frame fields, the exact result tag and sampled world values in eight direct
handler cases. The cases cover underflow at zero and positive prices,
shortage after one pop, success at the exact price, zero-price success with a
maximum word and a PC above word width, a price above word width with and
without sufficient gas, and replacement on a full stack. The cases use
static contexts, nontrivial memory, ordered duplicate logs, independent sets
and all six meter fields. The run laws in §7 give complete world retention.

A private comparison uses 18 direct calls to the pinned original EELS handler
and to the Lean facade at price 3. It checks the complete mutable frame before
and after each call, including the exact result categories. The source records
also check the original helper order and agree in normal and optimized Python.

Private native controls check all nine fields of the result frame and every
frame retained by the caller. They cover exclusive and retained entry at
stack depths 0, 1, 8, 256 and 1024, with execution budgets of 2 and 3. The
nonempty exclusive cases reuse the stack through the pop and, after payment,
the push. The nonempty retained cases copy at the pop and reuse that copy for
the push when the charge succeeds. The general handler differential, composed
`step` and guest fixture execution remain open.

**Supplied standalone bitwise controls.**
`STFSpec/Conformance/Vm/Instructions/BitwiseCallerProofs.lean` uses the facade
to apply all 52 laws and the Base numeric and bit-vector result models.
`STFSpec/Conformance/Vm/Instructions/BitwiseGuards.lean` checks every frame
field, the result tag and sampled world values. With zero execution gas, AND,
OR, XOR and NOT halt on empty stacks. The three binary handlers halt with an
empty residual stack on singleton inputs. Seven price controls use independent
AND, OR, XOR and NOT prices of 0, 1, 7 and 2^300 + 3 and a separate tier price
of 19. With the required operands, execution continues at zero price with zero
gas and at each positive price with the exact budget. Each positive price denies
one unit less after the required pops.

The same guards exercise empty stacks for BYTE, SHL, SHR, SAR and CLZ and
singleton stacks for the four binary handlers. The new controls set the five
selected prices to 11, 13, 17, 29 and 2^300 + 5, with separate tier prices of
19 and 23. They check exact payment and one-unit-short denial for each handler.
The success cases cover BYTE at indices 0, 31, 32 and the maximum word.
They also cover shifts at 255 and 256, SAR with both signs at the maximum
amount, and CLZ at zero and the maximum word.

A private comparison invokes the public handlers in interpreted and native Lean.
For AND/OR/XOR/NOT, both modes agree on all nine mutable frame fields and
the result category with 53 authenticated direct EELS calls in normal and
optimized Python. These cases cover both static flags, both underflow
positions, denial, high and
alternating bits, all-zero and all-one words, full stacks and PC increments
across the 64-bit and 256-bit boundaries. The source observations also record
the actual pop order, charge and gas trace event. The pinned archive has 46
published guest input/output pairs for these opcodes under
`ported_static/vmBitwiseLogicOperation`.

For BYTE, SHL, SHR, SAR and CLZ, 87 authenticated direct EELS calls cover
59 successes, ten first-pop underflows, eight second-pop underflows and ten
denied charges. The cases include full stacks, the word boundaries above and
both static flags. Both Lean modes agree with each Python mode on the nine
mutable fields before and after each call and on the result category. Twenty-five
additional facade controls vary just the selected raw price. They use zero
price, exact and one-unit-short budgets, and repeat both payment outcomes at
2^300 + 5. The authenticated Amsterdam archive members in
`vmBitwiseLogicOperation` for BYTE, `eip145_bitwise_shift` for the shifts and
`eip7939_count_leading_zeros` for CLZ contain 24, six and 1,192 guest
input/output pairs, respectively.

Private native controls use the actual public entries with an exclusive or
retained frame at stack depths 0, 1, 2, 8, 256 and 1024. They use independent
positive raw prices with exact and one-unit-short budgets. The 240 cases for
BYTE, SHL, SHR, SAR and CLZ also cover zero and surplus budgets. The native
checks compare every result frame field and every field of a retained input
frame. The probe checks the identity of the supplied world and observes the
backing array at entry, at each stack mutation and at return. On the tested
paths the exclusive array is reused. If the handler pops from a retained frame,
the first pop copies the array and later mutations reuse that copy.
Interpreter-level ownership, the general handler differential and guest
fixture execution remain open.

**Supplied MLOAD, MSTORE and MSTORE8 controls.**
`STFSpec/Conformance/Vm/Instructions/MemoryWordControls.lean` checks all
seventeen ordinary laws through the Instructions facade. Its twenty complete
guards cover both static flags, independent raw base prices, the raw Q63 ZERO
seed, exact and one-short gas, full-depth MLOAD and an exact Nat PC above a
word. Direct EELS comparisons use twenty-six complete frames in each pinned
Python mode and the interpreted and compiled Lean handlers. These cases cover
the reached underflows, in-bounds and growing windows, low-byte writes,
full-depth loads and huge-offset denial before allocation. The comparison uses
the pinned prices and a complete related source frame. Its fault observation
is the immediate VM exception, before the runner settles the frame.

Forty-six native controls check all three handlers with exclusive and retained
frames. They compare whole frames and the supplied world identity, including at
full depth, and observe the actual arguments to both store pops and to the
load's pop and push. Each nonempty exclusive pop reuses its backing.
The first nonempty retained pop copies it. Subsequent pops reuse that copy,
as does the load push when its backing has capacity. The retained values
stay intact. Exclusive in-bounds stores reuse the memory backing, and writes
from retained frames copy it. In-bounds loads and denied charges keep the
memory backing in both cases. Exclusive growth reuses sufficient capacity
and otherwise expands to the required extent.

**Supplied KECCAK controls.**
`STFSpec/Conformance/Vm/Instructions/KeccakControls.lean` compares complete
frame fields and sampled world values through the facade. Its recording oracle
checks exact paid preimages, absence of queries on both underflow prefixes and
denial, and use of the supplied answer with leading zeros. The Id guards include
a full stack and independent raw prices. Bounded direct-source comparisons
cover complete frames in both pinned Python modes and interpreted and compiled
Lean, including the 31/32/33-byte tariff boundary, the 135/136/137-byte Keccak
rate boundary and denial before a window beyond the word range can allocate.
Paired native ownership controls compare exclusive and retained frames,
including growth within spare capacity, growth past capacity and unchanged
memory for zero extension.
**Supplied EXTCODECOPY controls.**
`STFSpec/Conformance/Vm/Instructions/ExtCodeCopyControls.lean` checks
all frame fields and exact account and code callback observations through
the facade. The guards cover each pop prefix, cold and warm denial, both
missing-witness errors, a full stack, bytes at wide offsets and paid
memory growth. Direct-source controls in both pinned Python modes compare
complete frames and their transaction observations with interpreted and
compiled Lean. They include reserved empty code, transaction and block hits,
raw delegation bytes and the 31/32/33-byte copy price changes. The native
ownership controls compare exclusive and retained frames, actual growth
within existing capacity, newly allocated growth and paid provider failures.
**Supplied EIP-7702 designator controls.**
`STFSpec/Conformance/Vm/Instructions/DelegationDesignatorControls.lean`
uses both ordinary laws through the public facade. The guards cover the exact
marker, wrong bytes at each prefix position, short and long inputs, and
complete address bytes including leading zeros and a marker inside the
suffix. Direct-source comparisons in both pinned Python modes exercise
every possible byte at each marker position, the nearby lengths and every
suffix position. Interpreted and optimized native runs compare the complete
recognition and address results. Native access controls check the bounded
prefix reads and show that rejected inputs, including long packed sequences,
reach neither suffix copy nor address decoding.

**Supplied delegation resolver controls.**
`STFSpec/Conformance/Vm/Instructions/DelegationResolutionControls.lean`
exercises both State faults, exact account and code keys, transaction and
block precedence, and the reserved hash ahead of both code overlays. The
controls check cold and warm payment boundaries, zero-price insertion,
ordinary code at nonzero `ZERO`, and unchanged execution results outside
the selected field updates. A delegate whose code also contains a designator
checks that resolution stops after the first destination. The pinned direct
cases compare both Python modes with interpreted and native Lean. Recording
providers preserve the exact reached effects at the outer error boundary.

**Supplied EXTCODEHASH controls.**
`STFSpec/Conformance/Vm/Instructions/ExtCodeHashControls.lean` checks
the account test with the block's supplied empty-code hash. The guards
cover absence, exact emptiness, an empty-code hash on funded and nonzero
nonce accounts, and a code-only account with a high-byte hash and
unavailable code. They exercise the selected warm and cold prices,
the full-depth stack, and the nominal account-provider error. The
effectful provider records account reads and detects any attempted
code fetch. Pinned normal and optimized source calls are paired with the
interpreted and compiled facade, including both denial paths and full
frame, transaction and code-read observations.

**Supplied BALANCE controls.**
`STFSpec/Conformance/Vm/Instructions/BalanceControls.lean` exercises the public
entry through twelve guards. The cases cover unrelated raw tariffs, including
a zero warm tariff, the high-bit address mask, both warmth-dependent denials,
static input, full depth, a present zero, a tombstone and an absent account.
The underlying State effect records the complete masked query on payment and
records no query on either denied path. The guards also check both the complete
nested provider error and the underlying Monad failure.

The seven complete original BALANCE cases agree in both pinned Python modes
and the interpreted and compiled facade. They retain all mutable frame fields
and the source-related State tracker fields, including actual account-write
insertion order. The pinned trace observes pop and mask before charging, cold
insertion by charge time, and a read and push on payment.
EELS `vm/instructions/environment.py:58–86` and `state_tracker.py:174–225`.
The native controls exercise full-depth exclusive and retained frames, local
provider faults and both forms of denial. Exclusive pop and paid push reuse
their backing. A retained frame copies at the pop and preserves the saved value.

**Supplied SELFBALANCE controls.**
`STFSpec/Conformance/Vm/Instructions/SelfBalanceControls.lean` uses the public
handler in eleven complete guards. They cover denial at full depth, paid
overflow and provider fault at full depth, both account overlays and an absent
or maximal balance. Raw price choices include zero and nine, with independent
warm and cold prices. The backing effect records the target once on provider
fall-through and distinguishes the reached failure phases.

The interpreted and compiled facades agree with seven pinned-price and three
isolated price cases in both pinned Python modes. The source phase recorder
checks the entry and result frame, both access sets, State observations and
the order of payment, read and push. The isolated comparisons temporarily
substitute tariffs zero and nine in the running observation. The pinned
tariff is five. EELS `vm/instructions/environment.py:513–538` and
`state_tracker.py:174–225`. Ten native controls test actual exclusive
and retained stack owners. The successful exclusive append reuses backing
with spare capacity. A retained caller keeps its saved frame through the new
push. Denial and overflow preserve the entry stack backing.

**Supplied mutable child frame controls.**
`STFSpec/Conformance/Vm/Instructions/ChildFrameCallerProofs.lean` imports the
Instructions facade. A private equation reconstructs the result with all nine
frame fields and all six meter fields for arbitrary parent and grants. A
separate private proof checks `ChildSettled (childFrame parent gas reservoir) false`
at entry. Public observers check that a populated parent with nonempty stack,
written memory, logs, return data and three separately populated sets yields the
prescribed empty fields and inherits both warm sets. Meter controls exercise
zero grants and two unequal grants above 2^256, including each large grant paired
with zero. The pinned source comparison is a reading of the inline assignments
in §3.

**Standalone SLOAD controls.**
`STFSpec/Conformance/Vm/Instructions/SloadControls.lean` exercises the public
handler in a static frame. The cases distinguish address and slot warmth,
check the leading-zero slot bytes and cover a full entry stack. A recording
provider distinguishes denied reads from a paid lookup and retains the
complete witness fault on failure. The cases cover a transaction slot
holding zero over a clear, a transaction clear over a block slot, a
maximum block slot over a block clear, and a block clear over the provider.
Independent raw prices include zero on either warmth branch. The source
comparison uses the pinned selected price and compares the related frame
and State fields at the call boundary.

**Standalone BLOBHASH controls.**
`STFSpec/Conformance/Vm/Instructions/BlobHashControls.lean` checks the
first and last hash, duplicate entries, a stored zero hash, an empty
array, indices at the array size and beyond the host word width, and
the maximum U256 index. The cases cover underflow, denied payment,
unchanged world fields, full depth and raw prices including zero.
The bounded comparison uses original pinned Python in both modes and
the exact interpreted and compiled facade. Compiled controls record
the actual exclusive and retained stack paths, including denied payment.

**Standalone BLOCKHASH controls.**
`STFSpec/Conformance/Vm/Instructions/BlockHashControls.lean` checks complete
frame projections and the ancestor cursor for underflow, gas denial, current
and future requests, ages 1, 256 and 257, missing history, and a full stack.
A stored zero hash still records the successful ancestor access. Raw inputs cross the U256 boundary and vary the tariff independently. The
controls use actual R24 snapshot and restore with a changed transient field.
The saved field is restored and the block cursor survives.

The direct comparison pairs the actual interpreted and compiled facade with
sixteen authenticated pinned observations in normal and optimized Python.
It compares complete local frame projections and shared tracker fields.
For the missing case Lean returns the exact fault offset. The pinned Python
control checks the pop and charge before `IndexError`, with no R27 call.
Linked native controls run the real stack pop and push with exclusive and
retained frames. They exercise the actual R27 call before the successful hash
push and check that out-of-range, underflow, denied and missing cases skip it.
The named O13 fixture establishes the existing guest outcome at the pin.
The controls here cover the standalone handler.

**Standalone CALLDATALOAD controls.**
`STFSpec/Conformance/Vm/Instructions/CallDataLoadControls.lean` checks the
complete mutable frame projection and shared world fields. Cases cover
underflow, gas denial, full stacks, exact and partial windows, empty
input, very large offsets and independent configured prices.

The original review compared fourteen paired cases across the interpreted
and compiled facade and both authenticated Python modes at the pin. The
orchestrator used a separate eleven-case matrix. The exact current-parent
review expanded the fourteen-case review matrix to eighteen. The native
observer sees the linked pop and charge before the padded read and push,
including the full set of 32 bytes and the exact offset. It checks the
exclusive and retained paths through the real Stack operations. The
retained entry stack stays intact, and its copied tail is reused on push.

**Executed TLOAD controls.**
`scripts/TloadNativeTests.lean` runs the public handler on the input-only
`tload_inputs.json` catalogue. Native and interpreted streams compare all nine
frame fields, the six meter fields, block and transaction data, Lean write-order
indexes and constants, four provider samples and the absence of provider calls.
The cases cover empty and full stacks, exact and insufficient gas, a zero key,
absence and an explicit zero over persistent writes. They include competing
truncated and reversed keys, distinct full target addresses, static and regular
contexts, and raw prices of zero and more than 256 bits. Return data, logs,
memory, deletion and warm sets carry independent values.

`tload_differential.py` runs the pinned TLOAD function on real Evm, GasMeter
and State tracker carriers in isolated normal and optimized Python. It binds
the loaded EELS source to the pinned Git objects and checks installed package
versions and RECORD hashes. Eight cases at the pinned price of 100 compare all
frame fields and the shared world fields against both Lean streams. The source
worker checks preservation of its remaining context and control fields, and
records the gas event and the original transient read's address and key. Three
Lean-only cases cover a zero configured price and both sides of a charge above
word width. CONTRIBUTING §6.3 gives the commands.

A separate native `Id` probe builds a 1,024-word stack using a runtime-supplied
length and passes the frame once to TLOAD. In the pinned Lean build, both pop
and push receive an exclusive array and reuse it in this case. Stack growth,
caller sharing and composed allocation remain cost obligations under
EthVmCore §6 and REVIEW §7.

**Supplied standalone POP controls.**
`STFSpec/Conformance/Vm/Instructions/PopControls.lean` uses the facade to
apply all five local laws. Eight guards compare the result tag, projected
values of all frame fields and sampled world values. They cover empty
stacks with zero and affordable gas, denial after one pop, exact and
surplus gas, zero price and a price beyond 256 bits. The paid and denied
full-stack cases retain the 1,023 residual words.

The private source comparison calls the pinned EELS handler on 32 typed
frames in each Python mode. Interpreted and native calls to the public Lean
handler agree with EELS on the result category and the projected values of all
nine mutable frame fields before and after the call. The source records one
pop attempt and zero pushes in every case. Eight empty-stack cases halt before
the charge. The gas trace event follows the successful pop in the twelve gas
denials and the twelve successful calls. The cases cover depths 0, 1, 2 and
1,024 and PC boundaries at 64 and 256 bits.

A private native probe calls the public handler with exclusive and retained
input frames at depths 0, 1, 2, 8, 256 and 1,024. It checks the projected
values of all returned and retained frame fields and the supplied world
identity in 48 cases.
The cases use a zero price and zero balance, or a price beyond 256 bits with
a short, exact or surplus balance. Each nonempty case performs one pop and
returns its resulting array. An exclusive stack reuses its input array. A
retained stack copies once at the pop. Interpreter ownership and guest
fixture execution remain open.

**Supplied standalone JUMP and JUMPI controls.**
`STFSpec/Conformance/Vm/Instructions/JumpControls.lean` exercises
the public facade and applies all twelve local laws. Thirteen guards
compare complete frame observations and sampled world values. They
cover first-pop and second-pop underflow, shortage after the required
pops, paid zero and nonzero conditions, a valid target and a JUMPDEST
byte inside PUSH1 data. Independent raw prices, a PC above the
256-bit range and a full operand stack exercise the raw handler domain.

Twenty complete branch frame pairs match pinned EELS in normal and
optimized Python against both the interpreted and native facade.
The native ownership probe compares 48 complete cases against the
reference and checks world identity. Retained entry frames keep their
values. All twenty exclusive facade cases that pop operands reuse
their stack backing.

**Supplied standalone JUMPDEST controls.**
`STFSpec/Conformance/Vm/Instructions/JumpdestControls.lean` calls the
facade and applies all four local laws. Six guards compare complete
frame observations and sampled world values, with empty and full
stacks and PCs near and above the word range. The cases include zero,
short, exact and surplus balances and independent raw prices.

Six complete directly observed pinned source frames in each Python
mode match the interpreted and native facade projections. The native
ownership probe checks all returned and retained frame fields, the
original stack backing and the supplied world identity in 16 cases.
The controls exercise execution shortage and successful payment.

**Supplied settled child outcome controls.**
`STFSpec/Conformance/Vm/Instructions/ChildOutcomeCallerProofs.lean` imports only
the public Instructions facade. Private ordinary clients check the exact ordered
constructor, every projection including the supplied proof, complete-field
determination, dependent elimination and reconstruction. Replacing the frame or
error supplies only the corresponding local settled proof; replacing output
retains the existing proof. Arbitrary provider values remain whole: no private
Stack, Memory or nominal storage is unfolded, and no fork default is imported.

All-frame witnesses cover success with negative/positive refund, pending spill,
unequal reservoir/baseline and zero/huge execution gas, plus failed halt and
revert with arbitrary gas/baseline and complete supplied output. Generic opcode
and String reasons remain intact; halt/revert stay distinct. Complete ordered
byte controls include duplicate/nonempty output in all three error branches.
Each settlement clause has a negative meter control, and constructive decisions
check both flags. Three negative elaboration controls require the missing proof,
refuse a success proof for failure and refuse a proof about another frame; their
diagnostics test local proof dependency, not runtime rejection or reachability.
These controls supply no producer, Python oracle, rollback or execution claim.

**CREATE child context controls.** `CreateChildContextControls.lean` tests the
public constructor at depths zero and 1023 and with a static parent. The controls
use distinct parent and request addresses, nonliteral policy, empty and nonempty
init code, and a parent jump map that differs from the child's. Private facade clients check
whole configuration and environment inheritance and independence from request
grants and the account-charge flag. The bounded source comparison observes
the pinned `generic_create` dispatch in normal and optimized Python and compares
the complete child parameters and jump positions with interpreted and native Lean.

**Remaining F8 inheritance/producer controls.** Check the CALL child-context
systemAddress equation with a nonliteral parent address. Vary that address and
the F20 topic independently for SELFDESTRUCT. Compare complete logs for zero/nonzero balances
and equal/unequal beneficiaries, including all existing static/gas/state-fault
precedence and runner-owned revert/halt discard.

**Standalone TSTORE controls.** `TstoreChecks.lean` checks static precedence,
both pop failures, a failed charge after both pops, exact and surplus gas,
and insertion, overwrite and zero erasure. Full-width keys and words and
entries that share either component restrict the effect to the selected
pair. The controls keep the rest of the frame, the five other meter fields,
observation and order sentinels, and zero provider calls. The three
non-pinned price cases exercise zero and both sides of a configured
charge of seven. Ten pinned-price controls cover the direct EELS opcode
and tracker comparison in isolated normal and optimized Python. These
tests compare the returned status, ordered stack, gas, PC and transient
map and observe source pop, charge and write order.

A native probe supplies the stack depth at runtime. Under exclusive
entry, the compiled handler reused the array in both pops at depths 2,
3, 513 and 1,024. Composed caller sharing and allocation remain open
under REVIEW §7. The fixture areas below cover this opcode family.

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

**Supplied LOG controls.** `LogOpcodeControls.lean` compares complete
frame results and sampled world observations. It checks all five counts,
every short stack prefix, denial before a required expansion, and paid
static failure after that expansion. Success preserves old log order and
appends the current target, the ordered complete topic words, and the
selected bytes. An additional case reads an empty window at the largest
U256 offset with zero prices. A paid full-stack case retains every
unconsumed word.

The implementer's matrix compares 55 complete before and after frames in
interpreted and compiled Lean against each pinned Python mode. Native traces check the successful
pops, the complete topic conversion values, the single quote and charge,
expansion and the full read. They observe the supplied world identity in
every result. With exclusive entry, the compiled pops reuse the stack array.
A retained frame requires one copy on the first pop. Later pops reuse that
array. For LOG0 and LOG4, paid static and ordinary calls grow exclusive
64-byte memory to 96 bytes in the original backing with capacity 126.
Retained frames keep their original stack and memory while the paid
result uses a new backing. Growth from 32 to 64 bytes with capacity
62 allocates a larger backing. Empty-stack and gas-denied controls retain
the original memory and perform no expansion or read.

**Supplied PUSH controls.** `STFSpec/Conformance/Vm/Instructions/PushControls.lean`
uses the facade to apply the five public laws. Its ten guards compare the
result tag, projected values of all frame fields and sampled world values.
They cover PUSH0, truncated PUSH2, full-width PUSH32, both selected prices,
a zero price, and exact, surplus and short budgets. At `pc = 2^256` with
code `[0x60, 0xab]`, a paid PUSH1 reads zero. A modular offset would read
`0xab`. The pinned direct source raises `OverflowError` for that input.
The full-stack guards distinguish denial from stack overflow after payment.

The interpreted and native private facade probes compare the projected
values of all nine frame fields before and after the call. They match the
pinned reference on 24 gas denials and twelve paid cases with fitting read
starts, including PUSH32 whose window end exceeds the U256 range. Twelve
paid cases with unfitting starts match an independent model of the Q91 Nat
extension. The source records agree in normal and optimized Python.

The private native ownership probe checks 120 complete projected result
frames, the original retained frames and the supplied world identity.
Zero, short, exact and surplus budgets are tested at widths 0, 1 and 32 and
depths 0, 1, 3, 1,023 and 1,024. Nonfull paid calls perform one push. The
exclusive stack reuses its array when it has spare capacity. The retained
stack copies on a successful push.

**Supplied fixed DUP and DUPN controls.**
`STFSpec/Conformance/Vm/Instructions/DupControls.lean` checks
all thirteen local laws through the facade. Fourteen guards compare
all frame fields and sampled world values. They cover independent
prices, denial, invalid paid decoding, exact depth and underflow by
one, full stack, a missing immediate and a PC above the U256 range.

The facade matches 96 fixed DUP and 475 paid DUPN frame pairs from
the pinned EELS in both Python modes. The paid table covers all 256
bytes. Eleven additional source pairs cover targeted failure and
padding cases. One paid case beyond the U256 start bound exercises
the raw Nat extension.

The compiled facade and reference match in 90 complete ownership
cases. They retain the supplied world and preserve saved frames.
The exclusive facade reuses the backing in 14 cases with spare
capacity and grows it in six cases. The retained facade copies the
backing when it pushes.

**Supplied bounded context-word controls.**
`STFSpec/Conformance/Vm/Instructions/ContextWordControls.lean` uses the
public facade and all 45 ordinary laws. The 29 guards compare every
frame field and sampled world values. They distinguish all nine raw
prices and selected fields. The cases include a leading-zero address,
maximum call value, high-bit randomness, wide PCs and zero-price
continuation. Shortage on a full stack exercises charge precedence.

Both isolated pinned Python modes match the interpreted facade on
48 complete frame and transaction context pairs and 60 complete block
context pairs. The compiled ownership probe matches 180 complete
reference and facade pairs. All 360 calls retain world identity.
Exclusive facade calls reuse the backing in 27 spare-capacity cases
and grow it in 27 cases. The 54 retained successful cases copy the
backing and preserve the saved frame.

**Supplemental frame and block context controls.**
`STFSpec/Conformance/Vm/Instructions/FrameContextWordControls.lean`
runs sixteen guards for ADDRESS, ORIGIN, CALLER and CALLVALUE.
It varies tariffs and staticness and checks the complete frame for
denial, paid overflow and success, including wide prices and full-width
values. `STFSpec/Conformance/Vm/Instructions/BlockContextWordControls.lean`
runs twenty guards for the five block-context handlers. It also checks
U64 widening and the big-endian randomness round trip.

The block-context implementer's separate comparison covers 95 direct
cases per pinned Python mode, and the orchestrator's comparison covers
35 cases. Both compared interpreted and compiled Lean. These counts
describe the original block-context evaluations.

**Supplied SWAPN and EXCHANGE controls.**
`STFSpec/Conformance/Vm/Instructions/DynamicSwapControls.lean` checks the
twelve local laws through the facade. Twenty guards compare every frame
field and sample the world. They cover distinct prices, gas shortage
before an invalid immediate, invalid decoding on empty and full stacks,
the exact minimum depth, underflow by one, success at capacity, a missing
immediate, zero price and gas or PC beyond the word range.

The facade matches 475 paid SWAPN and 466 paid EXCHANGE source frames in
both pinned Python modes. Each table covers all 256 immediate bytes.
Additional controls exercise both payment outcomes outside the fitting
read range and compare the paid raw Nat extension with an independent
stack model. The compiled controls check complete result frames and
world identity, exclusive backing reuse and retained stack preservation.
**Supplied local-copy controls.**
`STFSpec/Conformance/Vm/Instructions/LocalCopyControls.lean` covers the
three pop prefixes, denial before allocation, memory growth, existing
memory, padding and the empty-window identity at a huge offset. It checks
the complete residual frames, including a full entry stack, and exercises
independent, zero and wide raw prices. The implementer's matrix compares 34 complete
frames in interpreted and compiled Lean against each pinned Python mode.
Linked observations check the
actual pops, destination quote, charge, expansion, padded read and write.
Exclusive and retained inputs have matching values, and retained frames
preserve their original memory.

**Supplied MCOPY controls.** `MemoryCopyControls.lean` checks all three
underflow prefixes and compares every frame field and sampled world
observations. It covers both overlap directions, identical windows,
either window requiring expansion, and source bytes from the new zero
region. Maximum offsets succeed at zero length and leave memory intact.
Positive oversized windows exercise denial. The controls also cover a
full stack, wide prices, and a one-unit boundary between exact payment
and denial.

The implementer's matrix compares 24 complete frames in interpreted and
compiled Lean against each pinned Python mode. Compiled tests observe the two-window quote
in order, its full charge, one expansion, complete snapshot bytes and
the exact destination write. The same tests check retained and exclusive
frames for within-memory overlap, growth, zero length and denial.
The covered write reuses its exclusive memory buffer in the paired
ownership control. A retained entry keeps its original bytes. Zero-length
writes preserve the original buffer in both ownership cases.

**Supplied GASPRICE and BASEFEE controls.**
`STFSpec/Conformance/Vm/Instructions/FeeWordControls.lean` runs eleven
paired guards through the public handlers. These compare the nine frame
fields and sampled world values on success and halt, and the exact nominal
site for a conversion fault. Controls include distinct raw tariffs and fee
fields, stack depths 1,023 and 1,024, the largest and first excluded fee,
a wide PC, zero prices and a price above 2^256.

The private interpreted and native facade probes match twenty direct cases
from both pinned Python modes. For six conversion faults they compare the
complete paid prefix on the Python side and the nominal site on the Lean side.
Sixteen compiled ownership profiles cover both handlers with exclusive and
retained frames. Successful pushes reuse an exclusive stack array with spare
capacity and copy a retained array. Full-stack halt, conversion fault and
gas denial perform no push in the compiled worker.

**Supplied byte-size controls (Q94).**
`STFSpec/Conformance/Vm/Instructions/SizeWordControls.lean` covers
distinct byte fields and tariffs, the complete denied and paid full
frames, and the pushed word, charged meter and Nat PC on success.
The return-data controls vary the current buffer under a single context.
The implementer's 27 complete direct cases match in both facade modes
and both pinned Python modes, including empty and 65,539-byte selected
fields. The orchestrator's separate replay compares 21 cases in the same
four modes.
The native controls check charge before conversion, and conversion before
the push on success, with exclusive and retained stacks. The symbolic law
at size `2^256` uses the Base word model.

**PC and GAS controls (Q95).** `PcGasWordControls.lean` checks denial,
paid cast failure, a fitting paid full stack and a fitting success with
independent prices and meter fields. The controls include the last fitting
value and the first excluded value on both spare and full stacks. GAS
observes the paid balance, even when the entry balance lies outside U256.
PC can advance past the word bound after pushing the last fitting value.

The implementer's 26 direct cases match in both facade modes and both
pinned Python modes. The orchestrator's separate replay compares 20 cases
in the same four modes. It checks the complete paid Python prefix
separately from each Lean nominal fault. Compiled traces check the exact
operand passed to conversion after payment, the two nominal sites, and
retention of memory and world when a frame is returned. Eight exclusive
and retained frame pairs cover denial, paid conversion fault, fitting
full stack and success for each opcode.

**Supplied fixed SWAP controls.**
`STFSpec/Conformance/Vm/Instructions/SwapControls.lean` uses the public
laws and compares all frame fields with sampled world values. It covers
the whole fixed index range, denial before depth, a full stack, PC above
the word range and zero and wide prices.

The implementer's 128 complete observations across all sixteen bindings
match in both facade modes and both pinned Python modes. The
orchestrator's separate replay compares 70 complete frame pairs in the
same four modes. The native controls
check the exact charge before each successful exchange, the two selected
indexes and the original world. Each of six exclusive successful runs
reuses its stack backing. Each of six matching retained runs copies the
backing and leaves the saved frame intact.

## 5. Interface

The standalone KECCAK handler is supplied through the Instructions facade.

```lean
def keccak {m : Type → Type} [Monad m] [KeccakQuery m] : Handler m
```
The standalone EXTCODECOPY handler is supplied through the Instructions facade.

```lean
def extcodecopy {m : Type → Type} [Monad m] : Handler m
```

The opcode enumeration and byte conversions below are **supplied** through
`STFSpec.Vm.Instructions`, with exactly 153 constructors, two total conversions
and the two ordinary laws in §7. No deriving, instance, alias or public
convenience declaration is added. Opcode dispatch and `step` are targets.

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
Monad instance. Section 3 records the supplied standalone handlers and their
local laws. The mutable child frame and immutable CREATE context constructors are
supplied separately. The CALL child context, remaining handlers, dispatch, step and resume remain open.

The exact four-field `ChildOutcome` is also supplied, retaining its complete frame,
output, optional error and supplied Core `ChildSettled frame error.isSome` proof.
Construction adds no producer, runtime guard or F11 proof-production choice.

Core §3/§4/§5/§7 supplies nominal OverflowSite/VmFault values.
BLOCKHASH uses the ancestor fault at the missing array access and the State R27
action on a hit. The remaining R-GEN-7 obligations include checked conversion
for BLOBBASEFEE and propagation through dispatch and the guest. The Q93 raw
fee handlers are supplied below.

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

-- Supplied mutable child frame initialization:
def childFrame (parent : Frame) (gas reservoir : Nat) : Frame

-- Selected supplied handler signatures. Section 3 lists all supplied handlers.
def stop {m : Type → Type} [Monad m] : Handler m
def pushN (n : Fin 33) {m : Type → Type} [Monad m] : Handler m
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
def lessThan {m : Type → Type} [Monad m] : Handler m
def greaterThan {m : Type → Type} [Monad m] : Handler m
def signedLessThan {m : Type → Type} [Monad m] : Handler m
def signedGreaterThan {m : Type → Type} [Monad m] : Handler m
def equal {m : Type → Type} [Monad m] : Handler m
def isZero {m : Type → Type} [Monad m] : Handler m
def bitwiseAnd {m : Type → Type} [Monad m] : Handler m
def bitwiseOr {m : Type → Type} [Monad m] : Handler m
def bitwiseXor {m : Type → Type} [Monad m] : Handler m
def bitwiseNot {m : Type → Type} [Monad m] : Handler m
def getByte {m : Type → Type} [Monad m] : Handler m
def bitwiseShl {m : Type → Type} [Monad m] : Handler m
def bitwiseShr {m : Type → Type} [Monad m] : Handler m
def bitwiseSar {m : Type → Type} [Monad m] : Handler m
def countLeadingZeros {m : Type → Type} [Monad m] : Handler m
def pop {m : Type → Type} [Monad m] : Handler m
def jump {m : Type → Type} [Monad m] : Handler m
def jumpi {m : Type → Type} [Monad m] : Handler m
def jumpdest {m : Type → Type} [Monad m] : Handler m
def dupN (ordinal : Fin 16) {m : Type → Type} [Monad m] : Handler m
def swapN (n : Fin 16) {m : Type → Type} [Monad m] : Handler m
def dupn {m : Type → Type} [Monad m] : Handler m
def mload {m : Type → Type} [Monad m] : Handler m
def mstore {m : Type → Type} [Monad m] : Handler m
def mstore8 {m : Type → Type} [Monad m] : Handler m
def address {m : Type → Type} [Monad m] : Handler m
def origin {m : Type → Type} [Monad m] : Handler m
def caller {m : Type → Type} [Monad m] : Handler m
def callvalue {m : Type → Type} [Monad m] : Handler m
def coinbase {m : Type → Type} [Monad m] : Handler m
def timestamp {m : Type → Type} [Monad m] : Handler m
def prevRandao {m : Type → Type} [Monad m] : Handler m
def chainId {m : Type → Type} [Monad m] : Handler m
def slotNumber {m : Type → Type} [Monad m] : Handler m
def swapn {m : Type → Type} [Monad m] : Handler m
def exchange {m : Type → Type} [Monad m] : Handler m
def balance {m : Type → Type} [Monad m] : Handler m
def selfBalance {m : Type → Type} [Monad m] : Handler m
def sload {m : Type → Type} [Monad m] : Handler m
def extcodehash {m : Type → Type} [Monad m] : Handler m
def blobHash {m : Type → Type} [Monad m] : Handler m
def blockHash {m : Type → Type} [Monad m] : Handler m
def calldataload {m : Type → Type} [Monad m] : Handler m
def calldatacopy {m : Type → Type} [Monad m] : Handler m
def codecopy {m : Type → Type} [Monad m] : Handler m
def mcopy {m : Type → Type} [Monad m] : Handler m
def tload {m : Type → Type} [Monad m] : Handler m
def tstore {m : Type → Type} [Monad m] : Handler m
def logN {m : Type → Type} [Monad m] (n : Fin 5) : Handler m

-- Supplied Q92 handlers
def return_ {m : Type → Type} [Monad m] : Handler m
def revert {m : Type → Type} [Monad m] : Handler m

-- Supplied standalone fee handlers (Q93).
def gasprice {m : Type → Type} [Monad m] : Handler m
def baseFee {m : Type → Type} [Monad m] : Handler m

-- Supplied standalone PC and GAS handlers (Q95).
def pc {m : Type → Type} [Monad m] : Handler m
def gasLeft {m : Type → Type} [Monad m] : Handler m

-- Supplied standalone byte-size handlers (Q94).
def calldatasize {m : Type → Type} [Monad m] : Handler m
def codesize {m : Type → Type} [Monad m] : Handler m
def returndatasize {m : Type → Type} [Monad m] : Handler m

-- Remaining handlers (public): extcodesize, returndatacopy, number, gasLimit,
-- blobBaseFee, sstore, msize, create, call, callcode, delegatecall, create2, staticcall,
-- selfdestruct : Handler m
def genericCreate … ; def genericCall …                    -- internal, return FrameExit

-- Supplied EIP-7702 designator and resolution interface
def EOA_DELEGATION_MARKER : Bytes
def isValidDelegation : Bytes → Bool
def getDelegatedCodeAddress : Bytes → Option Address
def resolveDelegatedCodeAddress (costs : GasCosts) (g : GasMeter) (warm : AddrSet) (a : Address) : VmM m (Except ExceptionalHalt (Address × Bool × GasMeter × AddrSet))

-- Prospective EIP-7702 declarations
def EOA_DELEGATION_MARKER_LENGTH : Nat
def EOA_DELEGATED_CODE_LENGTH : Nat
def calculateDelegationCost (f : Frame) (a : Address) : VmM m (Bool × Address × Nat)
def CALL_SUCCESS : U256

-- Relational view (public, for consumers)
inductive Step : (ctx : FrameCtx) → Frame → VmWorld Id → StepResult ctx → VmWorld Id → Prop   -- at m := Id
theorem step_iff : step ctx f w = .ok (r, w') ↔ Step ctx f w r w'
theorem Step.deterministic : Step ctx f w r₁ w₁ → Step ctx f w r₂ w₂ → r₁ = r₂ ∧ w₁ = w₂
```

**State API consumed from `EthState`.** Use `liftState` (EthVmCore §5) to run
`StateM m` actions on `world.tx`. It wraps the complete `StateError` in
`VmFault.state` on failure. The action list is `getAccount`, hash-only `getCode`,
`getStorage`, `getStorageOriginal`, `getTransientStorage` (supplied under EthState §5/§7), `setStorage`,
`setTransientStorage`, `isAccountAlive`, `accountDeployable`, `incrementNonce`,
`moveEther` (which can return `StateError.balanceOverflow`) and
`trackAncestorAccess`. EthState R27 gives its cursor update and
`StateM m Unit` signature.
Read `createdAccounts` from `world.tx.obs`.

EthCodec supplies `computeContractAddressQ` and `computeCreate2ContractAddressQ`
(the `KeccakQuery` forms, D5). EthBase supplies `Address.ofU256Masked`
(`to_address_masked`).

TSTORE uses `setTransientStorage` through the supplied `liftState`.
The State action has type `StateM m Unit` and owns the update under
EthState R23. Its transient pair key uses the full slot word.

## 6. Data structures

| Type | Representation | Model / abstraction | Invariant | Persistence | Cost |
|---|---|---|---|---|---|
| `Ops` (supplied) | 153 constructors, literal encoder and private 16 by 16 decoder table | literal reference definition (§7) | 103 unassigned bytes decode to `none` | immutable table shared across calls | One initialization builds 16 rows with 256 total entries. Each decode is O(1) with two indexed reads (DEBT-OPS-DECODE). |
| `StepResult ctx` (supplied) | inductive | — | `.call/.create` carry `ctx.depth < STACK_DEPTH_LIMIT` and `parent.stack.size < STACK_DEPTH_LIMIT` | value | — |
| `CreateRequest` (supplied) | raw seven-field record; init code uses Base `Bytes` | complete independent fields | none added by the raw carrier; future producers establish §2.5 grants/effects | value | fixed-field record construction/projection; init bytes retained through the Base provider |
| `CallRequest` (supplied) | raw fourteen-field record; `callData`, `code` use Base `Bytes` | complete independent fields | none added by the raw carrier; future producers establish §2.6 grants/effects and input copying | value | fixed-field construction/projection; complete bytes retained through the Base provider |
| `ChildOutcome` (supplied) | four-field record; complete Frame/Bytes/Option FrameError and local proof | complete payload fields | only `ChildSettled frame error.isSome`; no output or execution-gas condition | value | fixed-field construction/projection; no execution/resource claim |
| handlers | functions in `VmM m` (pure at `m := Id`) | — | preserve `Frame` invariants (stack ≤ 1024, memory size % 32 = 0) | — | O(1) for word ops; O(k) for copies/hashes of k bytes, k bounded by gas |

The suspended parent frame (in `.call/.create`) is linear: the runner holds the only reference while the child runs, so memory writes in `resumeAfterCall` are in place (ARCHITECTURE §7: diagnostics must not retain frames).

## 7. Contract and laws

**Supplied TSTORE contract.** The handler uses `Monad m` alone. A static
halt retains the original frame and world. The first underflow retains
the original frame, and the second retains the successful key pop.
An unaffordable charge retains the two pops and the original meter and
PC. All four exceptional cases return the original world through one
underlying `pure`.

After both successful pops and an affordable charge, the complete
action is the lifted R23 write followed by the continuation with the
popped stack, charged meter and advanced PC. The proof uses the public
Stack and gas laws and leaves the State update in the public action.
R23 owns zero erasure and preservation of other transaction fields.
Checking emptiness before each pop lets the ordinary Stack laws
discharge the impossible post-guard errors. A private equality
relates the compiled handler to the source-shaped reference for every
`Monad` instance.


**Supplied opcode laws.** The ordinary byte round trips, the first unconditional and
the second conditioned only on a successful decode, are:

```lean
theorem Ops.ofByte_toByte (o : Ops) : Ops.ofByte? (Ops.toByte o) = some o
theorem Ops.toByte_ofByte (b : UInt8) (o : Ops) (h : Ops.ofByte? b = some o) :
  Ops.toByte o = b
```

The private table applies the literal reference definition to every byte. Dividing
by 16 gives the row and taking the remainder gives the column. Both indices are
below 16. Recombining them recovers the input byte, so a private ordinary theorem
equates both decoders for every `UInt8`. After rewriting with that equality,
constructor cases prove the first law. Cases on the literal decoder and UInt8
numeric injectivity prove the second.

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

**Supplied mutable child frame initialization.** For every parent and both
`Nat` grants, `childFrame` sets the program counter to zero and starts with
empty stack, memory, logs, deletion set and return data. It retains the parent's
warm address and storage-key sets as persistent values. The meter uses `gas`
for execution gas and `reservoir` for both remaining and baseline state gas.
The signed refund, pending spill and committed spill are zero. The constructor
is pure and total. The private entry proof uses the zero committed spill.
Execution must preserve that clause through handlers, precompiles and nested
resume before the runner can use it at settlement (F11).

**Supplied settled child outcome.** Its public contract is exactly the four
fields in §5. Ordinary generated reduction retains the complete data and supplied
local proof. Private facade clients use only Core's existing predicate and
constructive decidability. Frame/error replacements require the corresponding
local proof; output replacement requires none. No authored public law, producer,
runtime guard, stronger output/gas/refund condition or F11 route is introduced.
EthVmRunner §3 owns the proof-taking result adapter. Actual reachability,
settlement, rollback, incorporation, source-Evm refinement and resume remain
open.

**Supplied typed results and Handler.** Their public contracts are exactly the
six constructors and class-free alias in §5. Private complete facade clients
establish payload retention/injectivity, six-case distinction, dependent
elimination/reconstruction, exact alias/run types and the two strict child proof
boundaries using public provider laws. No authored public helper-law family is
added. The fixed ctx index prevents a handler result from returning a changed
context. Actual operation effects, preservation/progress, source refinement,
child execution, settlement/resume and F11 remain separate obligations.

**Supplied SLOAD contract.** The handler uses `Monad m` alone. It selects the
supplied `warmAccess` or `coldStorageAccess` from slot membership before any
insertion. Both prices admit every Nat. The private action equations give
literal underlying `pure` for stack underflow and for denied payment after
either warmth branch. Both skip the lifted State action. Denial keeps
the residual stack and adds a cold slot with the rest of the frame and
world intact.

On payment, the private action equation runs one actual
`liftState (getStorage ctx.currentTarget key)`. At Id a fault keeps the
supplied State error under `VmFault.state`. A successful State action
supplies the returned complete world and the word pushed into the space
proved by the pop. Success advances the original Nat PC by one and
updates only the stack, execution gas and slot warmth. The resulting
meter potential plus the selected price equals the entry potential,
so it decreases strictly when that price is positive. The actual Core
pop consumes the nonempty stack and the paid push consumes its residual;
a private ordinary equality relates the pop path to its readable reference.
R11 owns the current-storage lookup and observations. Dispatch and
composed resource and fuel claims remain open.

**Supplied BLOBHASH contract.** The handler takes `Monad m` alone. Its
underflow, denial and success laws return the complete frame and world
under literal underlying `pure`. Underflow precedes charging. Denial
uses the post-pop frame and skips the push. After payment an actual
push fits the space made by the pop, and success changes the stack,
execution gas and PC. The whole transaction context, including array
order and duplicate occurrences, is retained.

The in-range law returns all 32 bytes at the selected Nat index. The
out-of-range law gives zero for every index at least the array size.
For a continuing Id run with its actual pop witness, the meter
potential plus the selected raw price equals the entry potential.
Strict progress uses positivity of that price. The ordinary pop and
push equations connect the ownership paths to their public Stack
operations. Source agreement uses the supplied versioned hashes and
pinned price 3. Dispatch and composed source, resource and fuel gates
remain open.

**Supplied BLOCKHASH contract.** The handler uses `Monad m` alone.
Underflow returns the whole input frame and world before charging. An
unaffordable charge returns the frame with the actual pop and keeps the
whole original meter and world. After a successful charge, compare the
full requested word with the exact Nat block number. A request for the
current block, a future block or an age greater than 256 pushes zero and
retains the entire world. At ages 1 through 256, insufficient history
returns `ancestorHashUnavailable` with the exact age. A hit selects
`blockHashes[blockHashes.size - age]` and runs the actual lifted State
R27 action before pushing the full big-endian word. R27 owns the cursor
update and R24 preserves it across transaction restore.

Private ordinary equations justify the reference pop, actual push and
branch ordering. Each continuing frame has the actual pushed stack, Nat
PC plus one, the charged meter and the original remaining fields. At Id,
a continuing run pays exactly the configured price in `phi`. A positive
price also gives strict local progress. Raw zero prices are admitted.

**Supplied CALLDATALOAD contract.** The handler uses `Monad m` alone.
Underflow returns the original frame and world. Denial returns the actual
post-pop stack with the original meter, PC and other frame fields. Payment
uses the exact configured price. The read begins at the full requested
U256 offset in `FrameCtx.callData`. Core's `bufferRead` uses Nat endpoint
arithmetic and returns the available bytes followed by enough zeros to
make 32 bytes. The big-endian value fits U256 and agrees with the
successful checked decoder. Push the word into the room left by the pop.
Only the stack, execution gas and Nat PC change in a continuing frame.
Every result retains the original world.

Private ordinary laws cover the actual pop and push, padded word and
complete results. A continuing Id run spends exactly the configured price
in `phi`. Strict local progress requires a positive price.

**Supplied TLOAD contract.** The handler uses `Monad m` alone and charges the
raw Nat price from the supplied context. Underflow returns the original frame
and world. OOG returns the frame with the pop applied and the original meter, PC
and world. These private equations retain literal underlying `pure`. At Id,
an affordable charge and successful pop give a successful push of exactly the
transient word, defaulting to zero. Public Stack laws establish space after the
pop, and the State action law through `liftState` retains the supplied world.
Success changes the stack, PC and `gasLeft`. The resulting meter potential plus
the selected cost equals the original potential. Both static and regular
contexts follow the same path, and both warm sets are retained. Source
comparisons use the pinned price and the field relations in §4.

The executable handler checks `Stack.size` before consuming the stack. The
Stack laws rule out pop failure on the nonempty branch and push failure
after a successful pop. These proofs let the compiler omit the branches
that would keep previous stack arrays alive across pop and push. A private
ordinary equality connects the executable handler to the source-shaped
reference for every `Monad` instance.

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

**Supplied EXP local laws.** These six ordinary laws are **discharged**.
The four complete equations quantify only Monad and preserve literal underlying
pure of the complete successful result/world. Raw zero and arbitrarily large
prices remain admitted. The two actual-Id laws require the displayed stack model
so their exponent is the real second pop; progress adds only positivity of that
actual complete charge. Zero charge permits continuation with unchanged phi.
A zero base price and per-byte price one give strict progress at exponent one,
while exponent zero has no byte charge. No public price helper, selector or
global positive-price predicate is added.

Private `ArithmeticCallerProofs` consumers apply every complete equation with
actual pop/push witnesses under Monad alone, derive the unsigned stack model via
`U256.toNat_exp`, and consume ordinary zero/one value laws. Actual-Id consumers
use both accounting laws, zero cost and base-zero/per-byte-positive examples,
derive hstack from actual public pop equations, and exclude empty/singleton
continuation. No Stack/U256 representation or arbitrary-pure injectivity enters
these clients. The private local worker computes price after both pops and uses
public Stack/meter laws to prove failure order and push availability.

```lean
theorem exp_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((exp ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w))

theorem exp_run_singleton {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (base : U256)
    (h : f.stack.toList = [base]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (base, s₁) ∧ s₁.toList = [] ∧
      ((exp ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w))

theorem exp_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (base exponent : U256) (xs : List U256)
    (h : f.stack.toList = base :: exponent :: xs) (hc : f.gasMeter.gasLeft < (ctx.config.costs.opcodeExpBase + ctx.config.costs.opcodeExpPerByte *
      ((U256.bitLength exponent + 7) / 8))) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (base, s₁) ∧ s₁.pop = .ok (exponent, s₂) ∧
      s₂.toList = xs ∧ ((exp ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w))

theorem exp_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (base exponent : U256) (xs : List U256)
    (h : f.stack.toList = base :: exponent :: xs) (hc : (ctx.config.costs.opcodeExpBase + ctx.config.costs.opcodeExpPerByte *
      ((U256.bitLength exponent + 7) / 8)) ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (base, s₁) ∧ s₁.pop = .ok (exponent, s₂) ∧
      s₂.toList = xs ∧ s₂.push (U256.exp base exponent) = .ok out ∧
      out.toList = U256.exp base exponent :: xs ∧
      ((exp ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - (ctx.config.costs.opcodeExpBase + ctx.config.costs.opcodeExpPerByte *
      ((U256.bitLength exponent + 7) / 8)) } }, w))

theorem exp_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (base exponent : U256) (xs : List U256)
    (hstack : f.stack.toList = base :: exponent :: xs)
    (hrun : ((exp ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + (ctx.config.costs.opcodeExpBase + ctx.config.costs.opcodeExpPerByte *
      ((U256.bitLength exponent + 7) / 8)) = f.gasMeter.phi

theorem exp_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (base exponent : U256) (xs : List U256)
    (hstack : f.stack.toList = base :: exponent :: xs)
    (hrun : ((exp ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ (ctx.config.costs.opcodeExpBase + ctx.config.costs.opcodeExpPerByte *
      ((U256.bitLength exponent + 7) / 8))) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi
```

**Supplied binary comparison local laws.** The thirty local laws below are
discharged. The four run equations per handler need only the displayed stack
and gas premises and a Monad instance. The equations give the complete frame
and world, including actual pop and push witnesses for the ordered cases.
The accounting laws consume actual continuing Id runs. A zero selected price
leaves Φ unchanged. Only strict progress requires a positive price.

```lean
theorem lessThan_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((lessThan ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w))

theorem lessThan_run_singleton {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      ((lessThan ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w))

theorem lessThan_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeLt) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ ((lessThan ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w))

theorem lessThan_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : ctx.config.costs.opcodeLt ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ s₂.push (U256.lt x y) = .ok out ∧
      out.toList = U256.lt x y :: xs ∧
      ((lessThan ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeLt } }, w))

theorem lessThan_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((lessThan ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeLt = f.gasMeter.phi

theorem lessThan_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((lessThan ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeLt) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi

theorem greaterThan_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((greaterThan ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w))

theorem greaterThan_run_singleton {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      ((greaterThan ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w))

theorem greaterThan_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeGt) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ ((greaterThan ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w))

theorem greaterThan_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : ctx.config.costs.opcodeGt ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ s₂.push (U256.gt x y) = .ok out ∧
      out.toList = U256.gt x y :: xs ∧
      ((greaterThan ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeGt } }, w))

theorem greaterThan_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((greaterThan ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeGt = f.gasMeter.phi

theorem greaterThan_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((greaterThan ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeGt) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi

theorem signedLessThan_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((signedLessThan ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w))

theorem signedLessThan_run_singleton {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      ((signedLessThan ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w))

theorem signedLessThan_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeSlt) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ ((signedLessThan ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w))

theorem signedLessThan_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : ctx.config.costs.opcodeSlt ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ s₂.push (U256.slt x y) = .ok out ∧
      out.toList = U256.slt x y :: xs ∧
      ((signedLessThan ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSlt } }, w))

theorem signedLessThan_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((signedLessThan ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeSlt = f.gasMeter.phi

theorem signedLessThan_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((signedLessThan ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeSlt) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi

theorem signedGreaterThan_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((signedGreaterThan ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w))

theorem signedGreaterThan_run_singleton {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      ((signedGreaterThan ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w))

theorem signedGreaterThan_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeSgt) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ ((signedGreaterThan ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w))

theorem signedGreaterThan_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : ctx.config.costs.opcodeSgt ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ s₂.push (U256.sgt x y) = .ok out ∧
      out.toList = U256.sgt x y :: xs ∧
      ((signedGreaterThan ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSgt } }, w))

theorem signedGreaterThan_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((signedGreaterThan ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeSgt = f.gasMeter.phi

theorem signedGreaterThan_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((signedGreaterThan ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeSgt) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi

theorem equal_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((equal ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w))

theorem equal_run_singleton {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      ((equal ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w))

theorem equal_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeEq) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ ((equal ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w))

theorem equal_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : ctx.config.costs.opcodeEq ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ s₂.push (U256.eq x y) = .ok out ∧
      out.toList = U256.eq x y :: xs ∧
      ((equal ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeEq } }, w))

theorem equal_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((equal ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeEq = f.gasMeter.phi

theorem equal_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((equal ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeEq) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi
```

**Supplied ISZERO local laws.** The three run equations need only the displayed
stack and gas premises and the supplied Monad instance. The accounting and
progress laws consume an actual continuing Id run. A zero price leaves Φ
unchanged. The positive-price premise appears only in the progress law.

The executable worker checks stack size before popping. For a nonempty bounded
stack, a pop succeeds and leaves room for the push. The private equality with
the source-shaped reference definition uses these facts and the original
charge order. The run and accounting proofs use that equality on the complete
step result.

```lean
theorem isZero_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((isZero ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w))

theorem isZero_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256) (xs : List U256)
    (h : f.stack.toList = x :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeIsZero) :
    ∃ stack : Stack, f.stack.pop = .ok (x, stack) ∧ stack.toList = xs ∧
      ((isZero ctx f).run w).run =
        pure (Except.ok (.halt { f with stack } .outOfGas, w))

theorem isZero_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256) (xs : List U256)
    (h : f.stack.toList = x :: xs)
    (hc : ctx.config.costs.opcodeIsZero ≤ f.gasMeter.gasLeft) :
    ∃ stack out : Stack, f.stack.pop = .ok (x, stack) ∧ stack.toList = xs ∧
      stack.push (U256.iszero x) = .ok out ∧ out.toList = U256.iszero x :: xs ∧
      ((isZero ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeIsZero } }, w))

theorem isZero_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((isZero ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeIsZero = f.gasMeter.phi

theorem isZero_continue_progress (ctx : FrameCtx) (f f' : Frame)
    (w w' : VmWorld Id) (h : ((isZero ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeIsZero) :
    f'.gasMeter.phi + 1 ≤ f.gasMeter.phi
```

**Supplied standalone bitwise laws.** The table instantiates the law forms
below with the handler, raw price field and Base word operation in each §3 row.
The run equations quantify over every `FrameCtx`, bounded `Frame` and
`VmWorld m` for the supplied `Monad m`. The continuing equations quantify
over actual Id runs with both input and output frames and worlds.

| Handler | Ordered run laws | Continuing Id laws |
|---|---|---|
| `bitwiseAnd` | `bitwiseAnd_run_empty`, `bitwiseAnd_run_singleton`, `bitwiseAnd_run_oog`, `bitwiseAnd_run_success` | `bitwiseAnd_continue_phi`, `bitwiseAnd_continue_progress` |
| `bitwiseOr` | `bitwiseOr_run_empty`, `bitwiseOr_run_singleton`, `bitwiseOr_run_oog`, `bitwiseOr_run_success` | `bitwiseOr_continue_phi`, `bitwiseOr_continue_progress` |
| `bitwiseXor` | `bitwiseXor_run_empty`, `bitwiseXor_run_singleton`, `bitwiseXor_run_oog`, `bitwiseXor_run_success` | `bitwiseXor_continue_phi`, `bitwiseXor_continue_progress` |
| `bitwiseNot` | `bitwiseNot_run_empty`, `bitwiseNot_run_oog`, `bitwiseNot_run_success` | `bitwiseNot_continue_phi`, `bitwiseNot_continue_progress` |
| `getByte` | `getByte_run_empty`, `getByte_run_singleton`, `getByte_run_oog`, `getByte_run_success` | `getByte_continue_phi`, `getByte_continue_progress` |
| `bitwiseShl` | `bitwiseShl_run_empty`, `bitwiseShl_run_singleton`, `bitwiseShl_run_oog`, `bitwiseShl_run_success` | `bitwiseShl_continue_phi`, `bitwiseShl_continue_progress` |
| `bitwiseShr` | `bitwiseShr_run_empty`, `bitwiseShr_run_singleton`, `bitwiseShr_run_oog`, `bitwiseShr_run_success` | `bitwiseShr_continue_phi`, `bitwiseShr_continue_progress` |
| `bitwiseSar` | `bitwiseSar_run_empty`, `bitwiseSar_run_singleton`, `bitwiseSar_run_oog`, `bitwiseSar_run_success` | `bitwiseSar_continue_phi`, `bitwiseSar_continue_progress` |
| `countLeadingZeros` | `countLeadingZeros_run_empty`, `countLeadingZeros_run_oog`, `countLeadingZeros_run_success` | `countLeadingZeros_continue_phi`, `countLeadingZeros_continue_progress` |

Let `run := ((handler ctx f).run w).run` and let `price` be the field
selected from `ctx.config.costs`. In the binary cases, `word x y` is the
corresponding Base operation. Unary `word x` is `U256.not x` or `U256.clz x`.

- **Empty.** If `f.stack.toList = []`, then
  `run = pure (Except.ok (.halt f .stackUnderflow, w))`.
- **Singleton (binary).** If `f.stack.toList = [x]`, there exists `s₁` with
  `f.stack.pop = .ok (x, s₁)`, `s₁.toList = []` and
  `run = pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w))`.
- **Gas denial (binary).** If `f.stack.toList = x :: y :: xs` and
  `f.gasMeter.gasLeft < price`, there exist `s₁` and `s₂` with
  `f.stack.pop = .ok (x, s₁)`, `s₁.pop = .ok (y, s₂)`, `s₂.toList = xs`
  and `run = pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w))`.
- **Gas denial (unary).** If `f.stack.toList = x :: xs` and
  `f.gasMeter.gasLeft < price`, there exists `s` with
  `f.stack.pop = .ok (x, s)`, `s.toList = xs` and
  `run = pure (Except.ok (.halt { f with stack := s } .outOfGas, w))`.
- **Success (binary).** If `f.stack.toList = x :: y :: xs` and
  `price ≤ f.gasMeter.gasLeft`, there exist `s₁`, `s₂` and `out` with
  `f.stack.pop = .ok (x, s₁)`, `s₁.pop = .ok (y, s₂)`, `s₂.toList = xs`,
  `s₂.push (word x y) = .ok out` and `out.toList = word x y :: xs`.
  The run equals `pure (Except.ok (.continue updatedFrame, w))` with the
  update displayed below.
- **Success (unary).** If `f.stack.toList = x :: xs` and
  `price ≤ f.gasMeter.gasLeft`, there exist `s` and `out` with
  `f.stack.pop = .ok (x, s)`, `s.toList = xs`, `s.push (word x) = .ok out`
  and `out.toList = word x :: xs`. The same complete run equation applies.
- **Accounting.** If the Id run equals `.ok (.continue f', w')`, then
  `f'.gasMeter.phi + price = f.gasMeter.phi`.
- **Progress.** For the same Id run, if `1 ≤ price`, then
  `f'.gasMeter.phi + 1 ≤ f.gasMeter.phi`.

```lean
updatedFrame := { f with
  pc := f.pc + 1
  stack := out
  gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - price } }
```

**Supplied POP local laws.** The generic run equations use the public
`Stack.toList` and actual pop witness. They retain the whole supplied world
under literal `pure` for the supplied Monad. The Id accounting equation uses
the selected raw price. Strict progress requires a positive price.

```lean
theorem pop_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (empty : f.stack.toList = []) :
    ((pop ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w))

theorem pop_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256) (xs : List U256)
    (entry : f.stack.toList = x :: xs)
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodePop) :
    ∃ stack : Stack, f.stack.pop = .ok (x, stack) ∧ stack.toList = xs ∧
      ((pop ctx f).run w).run =
        pure (Except.ok (.halt { f with stack } .outOfGas, w))

theorem pop_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256) (xs : List U256)
    (entry : f.stack.toList = x :: xs)
    (enough : ctx.config.costs.opcodePop ≤ f.gasMeter.gasLeft) :
    ∃ stack : Stack, f.stack.pop = .ok (x, stack) ∧ stack.toList = xs ∧
      ((pop ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodePop } }, w))

theorem pop_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((pop ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodePop = f.gasMeter.phi

theorem pop_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((pop ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodePop) :
    f'.gasMeter.phi + 1 ≤ f.gasMeter.phi
```

**Supplied JUMP and JUMPI local laws.** The run equations expose each
completed pop and retain the world under literal `pure`. The paid
membership branches use the supplied map. The local Id laws give exact
potential loss and require a positive price for strict progress.

```lean
theorem jump_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (empty : f.stack.toList = []) :
    ((jump ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w))

theorem jumpi_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (empty : f.stack.toList = []) :
    ((jumpi ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w))

theorem jumpi_run_missing_condition {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (destination : U256) (residual : Stack)
    (popped : f.stack.pop = .ok (destination, residual)) (empty : residual.toList = []) :
    ((jumpi ctx f).run w).run =
      pure (Except.ok (.halt { f with stack := residual } .stackUnderflow, w))

theorem jump_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (destination : U256) (residual : Stack)
    (popped : f.stack.pop = .ok (destination, residual))
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeJump) :
    ((jump ctx f).run w).run =
      pure (Except.ok (.halt { f with stack := residual } .outOfGas, w))

theorem jumpi_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (destination condition : U256)
    (first residual : Stack)
    (popped : f.stack.pop = .ok (destination, first)) (tested : first.pop = .ok (condition, residual))
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeJumpi) :
    ((jumpi ctx f).run w).run =
      pure (Except.ok (.halt { f with stack := residual } .outOfGas, w))

theorem jump_run_paid {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (destination : U256) (residual : Stack)
    (popped : f.stack.pop = .ok (destination, residual))
    (enough : ctx.config.costs.opcodeJump ≤ f.gasMeter.gasLeft) :
    let after : Frame := { f with
      stack := residual
      gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeJump } }
    ((jump ctx f).run w).run = pure (Except.ok
      ((if ctx.jumpdests.contains destination.toNat then .continue { after with pc := destination.toNat }
        else .halt after .invalidJumpDest), w))

theorem jumpi_run_paid_zero {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (destination condition : U256)
    (first residual : Stack)
    (popped : f.stack.pop = .ok (destination, first)) (tested : first.pop = .ok (condition, residual))
    (enough : ctx.config.costs.opcodeJumpi ≤ f.gasMeter.gasLeft)
    (zero : condition.toNat = 0) :
    let after : Frame := { f with
      stack := residual
      gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeJumpi } }
    ((jumpi ctx f).run w).run =
      pure (Except.ok (.continue { after with pc := f.pc + 1 }, w))

theorem jumpi_run_paid_nonzero {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (destination condition : U256)
    (first residual : Stack)
    (popped : f.stack.pop = .ok (destination, first)) (tested : first.pop = .ok (condition, residual))
    (enough : ctx.config.costs.opcodeJumpi ≤ f.gasMeter.gasLeft)
    (nonzero : condition.toNat ≠ 0) :
    let after : Frame := { f with
      stack := residual
      gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeJumpi } }
    ((jumpi ctx f).run w).run = pure (Except.ok
      ((if ctx.jumpdests.contains destination.toNat then .continue { after with pc := destination.toNat }
        else .halt after .invalidJumpDest), w))

theorem jump_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((jump ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeJump = f.gasMeter.phi

theorem jumpi_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((jumpi ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeJumpi = f.gasMeter.phi

theorem jump_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((jump ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeJump) :
    f'.gasMeter.phi + 1 ≤ f.gasMeter.phi

theorem jumpi_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((jumpi ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeJumpi) :
    f'.gasMeter.phi + 1 ≤ f.gasMeter.phi
```

**Supplied JUMPDEST local laws.** The two run equations retain the
supplied world under literal `pure`. Continuing Id runs lose the exact
selected price in meter potential and make strict progress at positive
prices.

```lean
theorem jumpdest_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeJumpDest) :
    ((jumpdest ctx f).run w).run = pure (Except.ok (.halt f .outOfGas, w))

theorem jumpdest_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeJumpDest ≤ f.gasMeter.gasLeft) :
    ((jumpdest ctx f).run w).run = pure (Except.ok
      (.continue { f with
        pc := f.pc + 1
        gasMeter := { f.gasMeter with
          gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeJumpDest } }, w))

theorem jumpdest_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((jumpdest ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeJumpDest = f.gasMeter.phi

theorem jumpdest_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((jumpdest ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeJumpDest) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi
```

**Supplied bounded context-word laws.** The nine declarations in §3
have the same five local law forms. In the following equations, `h`
is the named handler, `price` its selected Nat field of
`ctx.config.costs`, and `word` its selected U256 expression from §3.
The first three laws use `{m : Type → Type} [Monad m]`, `ctx : FrameCtx`,
`f : Frame` and `w : VmWorld m`.

```lean
-- h_run_oog
f.gasMeter.gasLeft < price →
  ((h ctx f).run w).run = pure (Except.ok (.halt f .outOfGas, w))

-- h_run_overflow
price ≤ f.gasMeter.gasLeft → f.stack.size = 1024 →
  ((h ctx f).run w).run = pure (Except.ok (.halt { f with
    gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - price } }
    .stackOverflow, w))

-- h_run_success
price ≤ f.gasMeter.gasLeft → f.stack.size < 1024 →
  ∃ stack : Stack, f.stack.push word = .ok stack ∧ stack.toList = word :: f.stack.toList ∧
    ((h ctx f).run w).run = pure (Except.ok (.continue { f with
      pc := f.pc + 1
      stack
      gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - price } }, w))
```

For `w w' : VmWorld Id` and `f f' : Frame`, both local accounting laws
assume `((h ctx f).run w).run = .ok (.continue f', w')`.
`h_continue_phi` concludes `f'.gasMeter.phi + price = f.gasMeter.phi`.
`h_continue_progress` also assumes `1 ≤ price` and concludes
`f'.gasMeter.phi + 1 ≤ f.gasMeter.phi`.

**Supplied BALANCE laws.** `balance_run_underflow` retains the complete entry
frame and world. After the actual pop, use the low 160 bits of the word
(EthBase `Address.ofU256Masked`). Entry warmth selects `warmAccess` or
`coldAccountAccess`. The two raw prices are independent, with respective
pinned values 100 and 3,000 (EELS `vm/gas.py:76–77`). Insert the address only
on the cold path, before charging. The two denial equations retain the
residual stack, selected warm set, complete entry meter and world, and the
original PC.

`balance_run_paid` requires the actual pop and proof that the selected
tariff fits. Its literal Monad-only action runs `liftState (getAccount address)`.
On success the entire returned transaction passes through, and the push is
admitted by the actual pop. The result advances the exact Nat PC, changes
only execution gas in the meter, and keeps the other frame fields. The private
size-witnessed pop worker has the full source-shaped pop result on every frame.

`balance_run_state_fault` and `balance_run_provider_fault` retain the exact
nominal error at Id. The provider form requires both overlay misses and the
actual provider error. Only a successful absent lookup defaults the balance
to zero (EthState R29/R30). `balance_run_success` gives the complete paid frame
and world for the observed successful account read and gives exact potential
debit by the selected price. `balance_run_observations` identifies the actual
continuation's State observations and retained fields. `balance_run_model`
identifies its top stack word under the existing `MathState.WF` and
`ModelsLookups` hypotheses. Neither hypothesis enters the executable handler.

**Supplied SELFBALANCE laws.** Charge `ctx.config.costs.opcodeSelfBalance`
against the entry meter. A denied action returns the entry frame and world
through the supplied Monad's pure. Payment runs the actual
`liftState (getAccount ctx.currentTarget)`. Its exact Id result preserves
the State provider's nominal fault (EthState R29/R30), or supplies the
complete resulting transaction and pushes the returned balance.

On overflow the paid meter and the read transaction pass with the entry
stack and PC in the halt result. On success the actual push supplies the
new top word and exact stack tail, and the Nat PC increases by one.
Both outcomes retain the other frame fields, including the two access sets.
The read retains the block, revertible fields and unrelated observations.
An actual Id continuation debits the selected tariff from gas potential.
The private size-witnessed push worker equals the source-shaped push
with both outcomes.

**Supplied EXTCODEHASH laws.** The handler shares BALANCE's actual pop,
low-160-bit mask, entry warmth, charge and admitted push. The private
underflow and denial equations give the complete frame and world for
each branch. The paid Monad equation runs one actual defaulted account
read. It uses the supplied constants from the input world for the
complete account comparison. Equality to the empty account gives zero.
For any other account the word has the account hash's exact 32 big-endian
bytes. No code query or surcharge follows the read.

The private Id fault law propagates the exact State error. The Id success
law supplies the exact pushed word, residual stack, PC and selected-price
potential debit, and passes through the full returned transaction. The
observation equation retains the block and revertible records and the
unrelated observation sets, including code reads. It adds precisely
the masked account read. Source agreement instantiates the supplied
F20 constants to the pin.

**Remaining per-opcode semantic lemmas** [R] (for evm-asm and pancaketh) use the
public Core/State contracts and never unfold their representations. ADD/SUB/MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND/ADDMOD/MULMOD/EXP use
the supplied handler laws above, replacing the former literal-3 `step_add` sketch.
LT/GT/SLT/SGT/EQ/ISZERO, AND/OR/XOR/NOT/BYTE/SHL/SHR/SAR/CLZ, POP, JUMP, JUMPI, JUMPDEST, PUSH, fixed DUP, DUPN and fixed SWAP use their supplied local laws. Actual `step`, its code-byte premises, `step_iff` and determinism remain unimplemented.

**Supplied fixed-width memory laws.** For the offset returned by the first
actual pop, take `e = calculateGasExtendMemory ctx.config f.memory [(off, width)]`.
This is the source's seeded estimate (EELS `vm/gas.py:761–798`, Q63).
The charge is the selected base plus `e.cost`, with
`opcodeMloadBase`, `opcodeMstoreBase` and `opcodeMstore8Base` read independently.
The widths are 32, 32 and 1 respectively. With the pinned schedule the three
bases are 3 and ZERO is 0. On raw configurations the estimate includes the
configured ZERO seed once.

The `_run_` equations require only `Monad m`, the actual pop results and the
reached charge comparison. An initially missing offset halts with the entry
frame. A missing store value halts with the first pop's residual stack.
Denial halts with the residual stack after all required pops, the entry memory,
meter and PC. Payment gives the exact execution-gas debit and advances the
exact Nat PC by one. Each equation retains the complete supplied world and
untouched frame fields. The handlers take the same branches in static frames.

The private pop worker checks nonemptiness before passing the owned stack to
the actual pop. Its ordinary equality gives the whole source-shaped pop result
for every frame, including empty input. The paid worker consumes the residual
frame and passes its stack and memory to the selected update.

The three `_run_success` laws witness the complete new memory. First extend
the entry byte list by `e.expandBy` zeros. MLOAD retains that expanded list,
reads exactly 32 bytes from the offset and witnesses both the exact big-endian
word and the successful push on the popped tail. The actual pop creates the
room needed for that push. MSTORE replaces the width-32 slice with all 32
big-endian bytes. MSTORE8 replaces the single byte with
`UInt8.ofNat word.toNat`. Q62 and Q63 justify the aligned extension, the
admitted window and the read and write equations through the public providers.
The three `_continue_phi` laws give `phi(after) + price = phi(before)`
on actual Id continuations with the offset-pop witness. The three
`_continue_progress` laws require `1 ≤ price` on the same paths.

**Supplied KECCAK laws.** The two actual pops determine the offset, size
and residual stack. A failed pop returns the frame with precisely that
residual stack. When both pops succeed, let `e` be
`calculateGasExtendMemory ctx.config f.memory [(offset, size)]`.
The selected charge is `opcodeKeccak256Base + opcodeKeccak256PerWord *
(ceil32 size.toNat / 32) + e.cost`. The Core quote includes the raw ZERO
seed once. Denial retains the residual stack and original memory, meter
and PC. Each failure returns the supplied world in the underlying `pure`.

Payment gives the exact execution debit and extends memory by `e.expandBy`
zeros. The local Core coverage equations admit the complete read at the
exact Nat offset and width, including an empty read at any offset. The
paid law is the literal underlying bind of one query on that complete
byte window. Its continuation pushes the answer on the residual stack,
increments the exact Nat PC by one and returns the supplied world. The
private push proof uses the room made by the pops, and the fixed-width
byte law recovers all 32 digest bytes from the pushed word. The owned stack
and memory paths each have a private ordinary equality to
the corresponding frame-projection form.

In Id the existing EthHash instance supplies concrete `keccak256`. Every
continuation satisfies `phi(after) + price = phi(before)`, and a positive
selected charge gives the local strict decrease. Other monads supply their
own query action. The equations use the two handler class premises from §5.
Source correspondence uses related entry fields, the pinned prices and
the concrete answer. See §10 for composed obligations.
**Supplied EXTCODECOPY laws.** Pop the address word, destination start,
source start and byte count in that order. Mask the popped address word. Each underflow equation
keeps the residual stack and all other fields and returns the given world.
Once all pops succeed, quote the singleton destination window. Use the
entry warmth to choose the warm or cold account tariff and insert a cold
address before charging. The charge adds one warm code-read tariff, the
selected copy-per-word tariff times the rounded byte count, and the Core
quote with its configured ZERO seed. Denial retains the residual stack
and resulting warmth, with the entry PC, memory, meter and world.

Payment expands memory by the quoted amount. The private paid worker
receives the expanded frame before entering State. Its ordinary equality
gives the source-shaped frame projection, and the separate compiled call
keeps expansion before both reads in Id, including on either fault.
The generic action lifts
`getAccount` at the masked address and `getCode` at the returned hash
on the actual resulting transaction. At Id, either reached State error
becomes the same wrapped `VmFault.state` as `liftState`, and the
successful result carries the transaction after both reads. The observer
law adds the account read and adds the code-read membership on the
nonreserved code-provider branch. The provider's raw bytes feed the
immutable padded read, even for a delegation marker. That read supplies
exactly the requested width. Its size and the Q63 coverage law prove the
Q62 destination window, with empty writes admitted at every offset.
Success writes those bytes into the expanded memory, retains the resulting
warmth and residual stack, and increments the exact Nat PC. The Id
continuation spends exactly the selected price in meter potential and
makes strict local progress when that price is positive.

Storage laws use the `getStorage` and `setStorage` observations and the exact
SSTORE cost, refund and state-gas table of §2.4 as a function
`sstoreCharges original current new cold`. CALL and CREATE laws give the
request fields and exact parent meter after withholding, with separate resume
equations. The remaining local laws must give exception precedence (R-GEN-2)
as in powdr's `StepDeterminism.lean`.

**CREATE context** [C]. For every parent `ctx`, raw request `req` and
`h : ctx.depth < STACK_DEPTH_LIMIT`, `childCtxOfCreate_eq` gives the entire
child constructor from §3, at depth `ctx.depth + 1`. The depth proof comes
from `h`. The request's grants and account-charge flag are consumed by other
operations. `childCtxOfCreate_config` and `childCtxOfCreate_systemAddress` are
the two supplied whole-field inheritance equations under F8.

**Remaining child context policy** [C] (F8). For every parent context, call
request and existing depth proof, `(childCtxOfCall ctx req h).systemAddress = ctx.systemAddress`
and the child's config equals `ctx.config`. Requests, Handler, step and
child-constructor parameter lists are unchanged. SELFDESTRUCT uses the inherited
context address and the stored F20 topic after the ordered gas charges and balance
move, before deletion registration. Its source agreement separately instantiates
the pinned address and topic. Local Step, gas-progress and inheritance laws
require no new global address/source predicate.

**Supplied local copy laws.** The first, second and third underflow
equations retain the exact preceding pop prefixes. The quote is
`calculateGasExtendMemory ctx.config f.memory [(destination, length)]`.
The charge adds the selected base and
`opcodeCopyPerWord * (ceil32 length.toNat / 32)` to the full quote cost.
A denial retains all three pops and the original memory and meter.
A paid continuation writes the exact padded source into the expanded
memory, returns the same residual stack, advances the Nat PC and
subtracts exactly the selected charge from execution gas. The byte-list
model retains every byte outside the written window. All five equations
retain the whole supplied world. When the requested length is zero, the
quote contributes the original ZERO seed, the per-word term vanishes and
the memory value is identical at every destination and source offset.
The Id laws give the exact loss in potential and strict progress when
the total charge is positive.

**Frame invariants** [C]: every handler preserves `stack.size ≤ 1024`, `memory.size % 32 = 0`, `ctx` unchanged (by typing), `f.accessedAddresses ⊆ f'.accessedAddresses` (warm sets only grow within a frame), and `Wf gasMeter`.

### Supplied RETURN and REVERT local laws (Q92)

For the signatures below, let `e` denote
`calculateGasExtendMemory ctx.config f.memory [(off, len)]`,
`returnPrice` denote `ctx.config.costs.zero + e.cost`, and
`revertPrice` denote `e.cost`. Let `expanded` denote
`f.memory.expand e.expandBy hExpand` and `output` denote
`expanded.readBytes off.toNat len.toNat hRead`. These are local
expressions determined by the arguments. The signatures introduce
no extra declarations for them.

MP7 supplies `hExpand : e.expandBy % 32 = 0`. By M2 and M4 the
expanded size is `f.memory.size + e.expandBy`. MP8 for the sole
listed window then supplies
`hRead : len.toNat = 0 ∨ off.toNat + len.toNat ≤ expanded.size`.
Q62 supplies the empty and nonempty read behaviour. The caller
supplies neither memory proof. The local laws quantify any existing
`FrameCtx`, `Frame` and `VmWorld m` under `Monad m` alone and
return the literal underlying `pure`.

```lean
theorem return_run_first_underflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (first : f.stack.pop = .error .stackUnderflow) :
    ((return_ ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w))
theorem return_run_second_underflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (off : U256) (s₁ : Stack)
    (first : f.stack.pop = .ok (off, s₁)) (second : s₁.pop = .error .stackUnderflow) :
    ((return_ ctx f).run w).run =
      pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w))
theorem return_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (off len : U256) (s₁ s₂ : Stack)
    (first : f.stack.pop = .ok (off, s₁)) (second : s₁.pop = .ok (len, s₂))
    (short : f.gasMeter.gasLeft < returnPrice) :
    ((return_ ctx f).run w).run =
      pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w))
theorem return_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (off len : U256) (s₁ s₂ : Stack)
    (first : f.stack.pop = .ok (off, s₁)) (second : s₁.pop = .ok (len, s₂))
    (enough : returnPrice ≤ f.gasMeter.gasLeft) :
    ((return_ ctx f).run w).run =
      pure (Except.ok (.stop { f with
        stack := s₂
        memory := expanded
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - returnPrice } } output, w))

theorem revert_run_first_underflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (first : f.stack.pop = .error .stackUnderflow) :
    ((revert ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w))
theorem revert_run_second_underflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (off : U256) (s₁ : Stack)
    (first : f.stack.pop = .ok (off, s₁)) (second : s₁.pop = .error .stackUnderflow) :
    ((revert ctx f).run w).run =
      pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w))
theorem revert_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (off len : U256) (s₁ s₂ : Stack)
    (first : f.stack.pop = .ok (off, s₁)) (second : s₁.pop = .ok (len, s₂))
    (short : f.gasMeter.gasLeft < revertPrice) :
    ((revert ctx f).run w).run =
      pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w))
theorem revert_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (off len : U256) (s₁ s₂ : Stack)
    (first : f.stack.pop = .ok (off, s₁)) (second : s₁.pop = .ok (len, s₂))
    (enough : revertPrice ≤ f.gasMeter.gasLeft) :
    ((revert ctx f).run w).run =
      pure (Except.ok (.revert { f with
        stack := s₂
        memory := expanded
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - revertPrice } } output, w))
```

The paid laws describe the terminal handler result before the Runner
settles it. The existing `Handler` and indexed `StepResult` carry
these results, including the same immutable context. F8 owns the
context's fields and F11 owns child settlement proof production.
The implementations and ordered local proofs are supplied. Section 4
records the bounded frame comparisons and raw condition controls.

**Gas progress** [T] (feeds EthVmRunner G2). The local strict progress laws require a positive actual charge on raw configurations. The whole-iteration target uses a related positive pinned schedule. For every handler, if the result is `.continue f'` then `f'.gasMeter.phi + 1 ≤ f.gasMeter.phi` (every non-terminal opcode has execution cost ≥ 1 [V: minimum costs are JUMPDEST 1, `BASE` 2; the only zero-cost handlers, STOP/RETURN/REVERT, are terminal]; state-gas charges, credits and repays leave Φ unchanged). For `.call parent req`: `parent.gasMeter.phi + req.gas + 100 ≤ f.gasMeter.phi`, where `req.gas` already includes the stipend: the charge is `access + transfer + delegation + mem + g'` and `req.gas = g' + stipend`, with `access ≥ 100` and `transfer − stipend = 11300 − 2300` when a stipend is paid [I]. The preflight-failure path (`.continue`) satisfies the same bound through `restore_child_gas`. For `.create`: `parent.gasMeter.phi + req.gas + 12000 ≤ f.gasMeter.phi`; the collision path (`.continue`) loses `12000 + g` [I]. For the resume operations: `(resumeAfterCall cfg p r c hs).gasMeter.phi = p.gasMeter.phi + c.frame.gasMeter.phi` (EthVmCore `L-INC`; the NEW_ACCOUNT credit preserves Φ).


**Supplied PUSH laws.** The three run equations describe the complete
results under literal underlying `pure`. The success equation exposes the
actual `Stack.push` result and its list model. The Id laws account for the
selected price and give strict progress at a positive price.

```lean
theorem pushN_run_oog (n : Fin 33) {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) :
    let price := if n.val = 0 then ctx.config.costs.opcodePush0 else ctx.config.costs.opcodePush
    f.gasMeter.gasLeft < price →
      ((pushN n ctx f).run w).run = pure (Except.ok (.halt f .outOfGas, w))

theorem pushN_run_overflow (n : Fin 33) {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (full : f.stack.size = 1024) :
    let price := if n.val = 0 then ctx.config.costs.opcodePush0 else ctx.config.costs.opcodePush
    price ≤ f.gasMeter.gasLeft →
      ((pushN n ctx f).run w).run = pure (Except.ok
        (.halt { f with gasMeter := { f.gasMeter with
          gasLeft := f.gasMeter.gasLeft - price } } .stackOverflow, w))

theorem pushN_run_success (n : Fin 33) {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (space : f.stack.size < 1024) :
    let price := if n.val = 0 then ctx.config.costs.opcodePush0 else ctx.config.costs.opcodePush
    let word := U256.ofNat (Uint.ofBeBytes (ctx.code.extractPadded (f.pc + 1) n.val))
    price ≤ f.gasMeter.gasLeft →
      ∃ stack : Stack, f.stack.push word = .ok stack ∧ stack.toList = word :: f.stack.toList ∧
        ((pushN n ctx f).run w).run = pure (Except.ok
          (.continue { f with
            pc := f.pc + 1 + n.val
            stack
            gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - price } }, w))

theorem pushN_continue_phi (n : Fin 33) (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((pushN n ctx f).run w).run = .ok (.continue f', w')) :
    let price := if n.val = 0 then ctx.config.costs.opcodePush0 else ctx.config.costs.opcodePush
    f'.gasMeter.phi + price = f.gasMeter.phi

theorem pushN_continue_progress
    (n : Fin 33) (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((pushN n ctx f).run w).run = .ok (.continue f', w')) :
    let price := if n.val = 0 then ctx.config.costs.opcodePush0 else ctx.config.costs.opcodePush
    1 ≤ price → f'.gasMeter.phi + 1 ≤ f.gasMeter.phi
```

**Supplied fixed SWAP laws.** All three run laws preserve the complete
`VmWorld m` under underlying `pure`. `swapN_run_oog` retains the full
entry frame for a short execution grant. With enough gas,
`swapN_run_underflow` retains the full paid frame when the stack size is
at most `n.val + 1`. `swapN_run_success` gives the actual successful
`Stack.swap? 0 (n.val + 1)` witness, both original words and the full
top-relative list after replacing those two cells, with unchanged size.
Its result has exactly the Core execution debit, the exchanged stack
and PC incremented by one. The local `swapN_continue_phi` equation gives
the exact configured cost for each continuing Id run.
`swapN_continue_progress` needs only positivity of that cost.
Source agreement specializes the tariff and identifies input and result
frame fields. Dispatch and halt settlement remain open.

**Supplied fixed DUP and DUPN laws.** Each outcome retains the supplied
world. A successful duplication exposes the actual peek and push,
the exact stack model and the complete continuing frame. The Id laws
account for the selected price and give strict progress at positive prices.

```lean
theorem dupN_run_oog (ordinal : Fin 16) {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeDup) :
    ((dupN ordinal ctx f).run w).run = pure (Except.ok (.halt f .outOfGas, w))

theorem dupN_run_underflow (ordinal : Fin 16) {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeDup ≤ f.gasMeter.gasLeft)
    (short : f.stack.size ≤ ordinal.val) :
    ((dupN ordinal ctx f).run w).run =
      pure (Except.ok (.halt { f with
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeDup } }
        .stackUnderflow, w))

theorem dupN_run_overflow (ordinal : Fin 16) {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeDup ≤ f.gasMeter.gasLeft) (full : f.stack.size = 1024) :
    ((dupN ordinal ctx f).run w).run =
      pure (Except.ok (.halt { f with
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeDup } }
        .stackOverflow, w))

theorem dupN_run_success (ordinal : Fin 16) {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeDup ≤ f.gasMeter.gasLeft)
    (fits : ordinal.val < f.stack.size) (space : f.stack.size < 1024) :
    ∃ (word : U256) (stack : Stack),
      f.stack.peek? ordinal.val = some word ∧ f.stack.push word = .ok stack ∧
      stack.toList = word :: f.stack.toList ∧
      ((dupN ordinal ctx f).run w).run =
        pure (Except.ok (.continue { f with
          gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeDup }
          pc := f.pc + 1, stack }, w))

theorem dupN_continue_phi (ordinal : Fin 16) (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (ran : ((dupN ordinal ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeDup = f.gasMeter.phi

theorem dupN_continue_progress (ordinal : Fin 16)
    (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (ran : ((dupN ordinal ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeDup) :
    f'.gasMeter.phi + 1 ≤ f.gasMeter.phi

theorem dupn_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeDupn) :
    ((dupn ctx f).run w).run = pure (Except.ok (.halt f .outOfGas, w))

theorem dupn_run_invalid {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeDupn ≤ f.gasMeter.gasLeft)
    (decoded : decodeSingle ((ctx.code[f.pc + 1]?).getD 0) = .error .invalidParameter) :
    ((dupn ctx f).run w).run =
      pure (Except.ok (.halt { f with
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeDupn } }
        .invalidParameter, w))

theorem dupn_run_underflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (depth : Nat)
    (enough : ctx.config.costs.opcodeDupn ≤ f.gasMeter.gasLeft)
    (decoded : decodeSingle ((ctx.code[f.pc + 1]?).getD 0) = .ok depth)
    (short : f.stack.size < depth) :
    ((dupn ctx f).run w).run =
      pure (Except.ok (.halt { f with
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeDupn } }
        .stackUnderflow, w))

theorem dupn_run_overflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (depth : Nat)
    (enough : ctx.config.costs.opcodeDupn ≤ f.gasMeter.gasLeft)
    (decoded : decodeSingle ((ctx.code[f.pc + 1]?).getD 0) = .ok depth)
    (full : f.stack.size = 1024) :
    ((dupn ctx f).run w).run =
      pure (Except.ok (.halt { f with
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeDupn } }
        .stackOverflow, w))

theorem dupn_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (depth : Nat)
    (enough : ctx.config.costs.opcodeDupn ≤ f.gasMeter.gasLeft)
    (decoded : decodeSingle ((ctx.code[f.pc + 1]?).getD 0) = .ok depth)
    (fits : depth ≤ f.stack.size) (space : f.stack.size < 1024) :
    ∃ (word : U256) (stack : Stack),
      f.stack.peek? (depth - 1) = some word ∧ f.stack.push word = .ok stack ∧
      stack.toList = word :: f.stack.toList ∧
      ((dupn ctx f).run w).run =
        pure (Except.ok (.continue { f with
          gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeDupn }
          pc := f.pc + 2, stack }, w))

theorem dupn_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (ran : ((dupn ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeDupn = f.gasMeter.phi

theorem dupn_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (ran : ((dupn ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeDupn) :
    f'.gasMeter.phi + 1 ≤ f.gasMeter.phi
```

**Supplied SWAPN and EXCHANGE laws.** Both success laws expose the
actual Core swap, the two entry words, the complete top-first stack
model and the paid successor. An in-range swap succeeds at any
capacity. Core's `decodePair_bounds` puts the two decoded indices in
strict order, so the right index determines EXCHANGE's minimum depth.
The Id laws account for each selected price and give strict progress
at positive prices.

```lean
theorem swapn_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeSwapn) :
    ((swapn ctx f).run w).run = pure (Except.ok (.halt f .outOfGas, w))

theorem swapn_run_invalid {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeSwapn ≤ f.gasMeter.gasLeft)
    (decoded : decodeSingle ((ctx.code[f.pc + 1]?).getD 0) = .error .invalidParameter) :
    ((swapn ctx f).run w).run =
      pure (Except.ok (.halt { f with
        gasMeter := { f.gasMeter with
          gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSwapn } }
        .invalidParameter, w))

theorem swapn_run_underflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (depth : Nat)
    (enough : ctx.config.costs.opcodeSwapn ≤ f.gasMeter.gasLeft)
    (decoded : decodeSingle ((ctx.code[f.pc + 1]?).getD 0) = .ok depth)
    (short : f.stack.size ≤ depth) :
    ((swapn ctx f).run w).run =
      pure (Except.ok (.halt { f with
        gasMeter := { f.gasMeter with
          gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSwapn } }
        .stackUnderflow, w))

theorem swapn_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (depth : Nat)
    (enough : ctx.config.costs.opcodeSwapn ≤ f.gasMeter.gasLeft)
    (decoded : decodeSingle ((ctx.code[f.pc + 1]?).getD 0) = .ok depth)
    (within : depth < f.stack.size) :
    ∃ (stack : Stack) (a b : U256), f.stack.swap? 0 depth = some stack ∧
      f.stack.toList[0]? = some a ∧ f.stack.toList[depth]? = some b ∧
      stack.toList = (f.stack.toList.set 0 b).set depth a ∧
      ((swapn ctx f).run w).run =
        pure (Except.ok (.continue { f with
          gasMeter := { f.gasMeter with
          gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSwapn }
          pc := f.pc + 2, stack }, w))

theorem swapn_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (ran : ((swapn ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeSwapn = f.gasMeter.phi

theorem swapn_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (ran : ((swapn ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeSwapn) :
    f'.gasMeter.phi + 1 ≤ f.gasMeter.phi

theorem exchange_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeExchange) :
    ((exchange ctx f).run w).run = pure (Except.ok (.halt f .outOfGas, w))

theorem exchange_run_invalid {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeExchange ≤ f.gasMeter.gasLeft)
    (decoded : decodePair ((ctx.code[f.pc + 1]?).getD 0) = .error .invalidParameter) :
    ((exchange ctx f).run w).run =
      pure (Except.ok (.halt { f with
        gasMeter := { f.gasMeter with
          gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeExchange } }
        .invalidParameter, w))

theorem exchange_run_underflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (i j : Nat)
    (enough : ctx.config.costs.opcodeExchange ≤ f.gasMeter.gasLeft)
    (decoded : decodePair ((ctx.code[f.pc + 1]?).getD 0) = .ok (i, j))
    (short : f.stack.size ≤ j) :
    ((exchange ctx f).run w).run =
      pure (Except.ok (.halt { f with
        gasMeter := { f.gasMeter with
          gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeExchange } }
        .stackUnderflow, w))

theorem exchange_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (i j : Nat)
    (enough : ctx.config.costs.opcodeExchange ≤ f.gasMeter.gasLeft)
    (decoded : decodePair ((ctx.code[f.pc + 1]?).getD 0) = .ok (i, j))
    (within : j < f.stack.size) :
    ∃ (stack : Stack) (a b : U256), f.stack.swap? i j = some stack ∧
      f.stack.toList[i]? = some a ∧ f.stack.toList[j]? = some b ∧
      stack.toList = (f.stack.toList.set i b).set j a ∧
      ((exchange ctx f).run w).run =
        pure (Except.ok (.continue { f with
          gasMeter := { f.gasMeter with
          gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeExchange }
          pc := f.pc + 2, stack }, w))

theorem exchange_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (ran : ((exchange ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeExchange = f.gasMeter.phi

theorem exchange_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (ran : ((exchange ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeExchange) :
    f'.gasMeter.phi + 1 ≤ f.gasMeter.phi
```

**Stack-immediate source agreement (Q91)** [C], planned. Prove the two
charge cases for related source and Lean frames. In the denied case, the
source raises the gas exception before evaluating the offset cast, so the
case applies at every related PC. After payment, including for PUSH0, the
source constructs `U256(evm.pc + Uint(1))`. Relate the paid branches under
the local premise `f.pc + 1 < 2^256`. EELS adds the read width in `Uint`, so
the fitting-start premise suffices for the padded window. For the one-byte
operations, carry the read equality into the existing Core decoder laws.
EELS `I/stack.py:49–79,213–314`, `memory.py:63–83` at `59c1473d` and
locked `ethereum-types` 0.4.1 `ethereum_types/numeric.py:44–48,605–612`.

At source dispatch the running fetch guard gives `pc < |code|`. With
related code whose length is less than `2^256`, this gives
`pc + 1 ≤ |code| < 2^256`. EthVmRunner R-LOOP-1 owns the obligation to
supply these local facts. The raw frame and handler accept arbitrary Nat PCs.
EELS `interpreter.py:438–445` at `59c1473d`.

**GASPRICE and BASEFEE local laws (Q93)** [C], supplied. The private
run equations cover denial, paid unsigned conversion fault, paid full
stack with a fitting fee, and success after payment with a fitting fee
and available stack space. Denial returns the complete entry frame and
world. Paid conversion failure carries the exact selected nominal site.
A fitting full-stack halt preserves every frame field except execution gas.
Success retains the world and returns the paid meter, the exact top-first
stack with the new U256 word at its head, and the Nat PC incremented by one.
The private Id accounting equation says that successor potential plus the
selected price equals entry potential. A positive selected price then gives
strict decrease. The caller and dispatch obligations remain in §10.

**Byte-size local laws (Q94)** [C], supplied. The private run equations
preserve the world and give the complete entry frame on denial and the
complete paid frame on a full stack for every raw byte size. On success
the returned frame has the exact debit, `U256.ofNat size` pushed onto the
original stack and the Nat PC incremented by one. The whole-size law
uses only `size < 2^256` for that field, and the symbolic equation gives
zero at `2^256`. The Id continuation spends exactly the selected price
in potential, and a positive price gives strict progress. At the pin,
successful `len` on the authenticated 64-bit CPython runtime returns at most `2^63 - 1`, so source bytes
satisfy the premise. A symbolic Python length proxy with a larger
advertised length can raise inside `len` before the U256 constructor.
That proxy lies outside the source byte-field type. Practical host
resource behavior belongs to CONTRACT O12.

**PC and GAS local laws (Q95)** [C], supplied by private ordinary laws in
`PcGasWords.lean`. Denial gives the complete
entry frame and world regardless of the selected word's range. Payment with
a value outside U256 gives the exact nominal site and carries no paid frame
or world. With a fitting word, a paid full stack retains the complete paid
frame and world. Success returns that meter and world, the exact pushed
value and Nat PC increment. The private stack worker equals its
source-shaped reference. The successful Id continuation spends exactly
the selected price from meter potential, so a positive price gives strict
decrease. The fitting GAS premise is on the paid execution balance. The
source relation and caller bounds remain open.

**Resume laws** [C]: return-data rules of ARCHITECTURE §6 (`CALL`: child output in all three outcomes; `CREATE`: ∅ on success, child output on failure); stack effect (one push); memory: only the window `[outOffset, outOffset + min(outSize, |output|))` changes; logs/deletions/warm sets merged iff success; `pc` advanced by 1.

**Delegation designator** [C]. The two supplied ordinary laws cover
every input byte sequence and complete returned address.

```lean
theorem isValidDelegation_iff (code : Bytes) :
    isValidDelegation code = true ↔
      code.toList.length = 23 ∧ code.toList.take 3 = [0xef, 0x01, 0x00]
theorem getDelegatedCodeAddress_eq_some_iff (code : Bytes) (address : Address) :
    getDelegatedCodeAddress code = some address ↔
      code.toList.length = 23 ∧ code.toList.take 3 = [0xef, 0x01, 0x00] ∧
        code.toList.drop 3 = address.toBytes.toList
```

The packed recognizer tests length before reading the three fixed prefix
positions. The Base byte-index observation gives the matching list prefix.
Its suffix theorem uses the Base extraction length, list and address
decoding laws. These laws admit each marker followed by a 20-byte address
and recover all bytes of that address. The code length and marker length
are local implementation values.

**Delegation resolution** [C]. `resolveDelegatedCodeAddress_run` gives the
complete ordered action under Monad alone. It lifts `getAccount a`, then lifts
`getCode` at the returned hash in the updated world. It applies the designator
extractor to that byte array and calls `chargeGas` on a designator. The price
comes from `warmAccess` or `coldAccountAccess` according to membership of the
delegate in the input set.

The five local Id laws identify the reached account fault, reached code fault,
ordinary return, selected-price denial and paid resolution. Both State faults
are outer `VmFault.state` values. Gas denial is an inner `.outOfGas` with the
world from both reads. Ordinary code gives the original address, false, and
the entire entry meter and warm set. Paid resolution changes only the meter's
execution gas, decreases its `phi` by exactly the selected price, and returns
the delegate and true. The warm branch retains the set and the cold branch
inserts the delegate after payment. The surrounding runner still owns the
use of the result and source-context agreement.

**Relational view** [R]: `step_iff` and `Step.deterministic`; a small-step relation `Steps` for straight-line code with additive gas (`GasSteps`-style) for consumers.

**MCOPY local laws** [C], supplied privately in `LocalCopy.lean`. Each
underflow law retains the completed pop prefix without charging. On a
complete prefix, the memory quote lists source then destination. The
charge is the configured base plus the per-word price times the rounded
copy word count, plus the entire quote including its ZERO seed. Denial
retains the popped frame and the supplied world.

Payment expands memory once. The whole memory model is the expanded
prefix before the destination, the complete source slice from the same
expansion, then the expanded suffix after the destination window. This
preserves the snapshot interpretation for overlaps and identical windows.
At zero length both windows are erased from the pricing calculation,
even at maximum offsets. The charge retains the base and seed and the
memory remains identical. Success retains the residual stack and paid
meter and advances Nat PC once. The Id potential law accounts for the
complete charge, and a positive charge gives strict decrease.

**LOG local laws** [C], supplied privately in `LogOpcode.lean`. The stack
model identifies the offset, width and exact topic prefix in that order.
Each returned topic retains all 32 big-endian bytes. The checked stack
worker equals the reference pop, including the original empty residual.
A short stack halts with that residual and retains the other entry fields
and the world. With a complete prefix, the charge is the configured base,
data price times the full byte count, topic price times the count, plus
the singleton window quote from EthVmCore §7. The quote carries its
`ZERO` seed even for an empty window.

Denial retains the popped frame and world. The paid worker consumes the
frame's memory and applies the quoted zero expansion before the static
check. Its private ordinary equality gives the complete result of the
source-shaped reference. A static failure retains the
expanded memory, paid meter, popped stack and original logs and PC.
Success reads the admitted slice of that expanded memory, appends exactly
one log for `ctx.currentTarget`, and advances PC by one. The existing
coverage proof accepts an empty read at every offset. The complete Id
potential equation accounts for the selected charge, and any positive
charge gives strict decrease.

### Informal correctness argument

**Claim.** Each opcode's one executable handler refines the pinned instruction, including the order of guards, charges, observations, faults and child requests.

**Premises.** EthVmCore/State contracts; canonical opcode decoding; valid frame/config invariants; source correspondence for each claimed handler; explicit distinction between FrameError and global VmFault.

**Argument.** For an opcode, symbolically execute the Python checks and the handler in the same order. Relate popped operands through Stack.toList, memory through its window observer and state through overlay lookups. At each guard, prove that both sides select the same failing branch, including observations made before that failure. Successful primitives preserve the relation and yield the same next PC, stack, output and meter. CALL/CREATE stop at a request containing the already withheld gas, child context and resume data. Child execution is supplied by the runner; resume then uses the child settlement contract to update return data, memory, stack, logs and gas. This factorisation covers the source operation without adding a second opcode implementation. The executable step/relation equivalence follows by cases on StepResult; fidelity to EELS is a separate per-handler obligation.

**Open obligations.** Expand every source-map group into exact guard/effect equations, finish resume preconditions and cross-call gas inequalities, and audit implicit Python failures. Proofs must compare selected observations and error priority, not only successful whole-state results.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthVmCore`, `EthHash`, `EthCodec`
- **Used by:** `EthVmRunner` (calls `step`, `childCtxOf*`, `childFrame`, the resume operations and `resolveDelegatedCodeAddress`); `EthBlock` (uses `isValidDelegation`).
- **Seams:** supplies `Handler`, `StepResult`, the request carriers, `childFrame`, `childCtxOfCreate` and `resolveDelegatedCodeAddress`. The `step` and resume interfaces are targets. Consumes EthVmCore's frame, meter and memory contracts, EthState's lookup/overlay laws (through `VmM m`), `KeccakQuery` (KECCAK; CREATE and CREATE2 addresses through EthCodec's `…Q` forms), RLP (CREATE address). Relies on: the frame it receives satisfies the EthVmCore invariants; the runner passes back a `ChildOutcome` built from a frame with `ChildSettled`. The supplied `.call/.create` types guarantee only `depth < STACK_DEPTH_LIMIT` and room in the parent stack for the result (`hs`). Future handler contracts additionally require balance and nonce preflight and the parent meter already withholding the grant.

## 9. Open decisions

- **D1**: handlers use only `U256` observer laws; exercise 4.
- **D5** (broad scope, monad-parametric; B10): **every** keccak goes through `KeccakQuery`, including the KECCAK opcode and CREATE/CREATE2 address derivation, so handlers live in `VmM m`. Execution instantiates `m := Id`, where the instance is concrete `keccak256`. A narrower scope needs the agreement prototype's justification.
- **D14** (accepted): halts are frame exits (O8); BLOCKHASH's missing ancestor and the BLOBBASEFEE overflow are `VmFault`s in CONTRACT O13 (R-GEN-7).
- **D26** (accepted): secp256k1 recovery stays in the runner; handlers do not import it.
- **D27** (accepted): `Log` is `EthVmCore`'s; LOG0–LOG4 and the EIP-7708 transfer log reuse it.
- **D13**: the parent frame in `.call/.create` is a value; both a recursive runner and a continuation stack can consume it.
- **D17**: accepted; this module is its opcode side. Replacement exercises 1 and 3 test that memory/gas changes stay within handlers' contracts.
- **D18**: an unoptimised handler (for example MCOPY via intermediate copy) is correct and complete; performance debt only.
- **Q93** gives the raw GASPRICE and BASEFEE paths in §2 and the supplied
  interface in §5.
- NEW-VM-1: resolved by D14, CONTRACT O13 and DECISIONS B14 (Q23) (EthVmCore R-EXC-2).
- NEW-VM-2: resolved by DECISIONS B7 (Q24): halts are values.
- **Q91** covers stack-immediate reads and their source correspondence (§§2 and 7).
- **Q92** owns the selected raw RETURN and REVERT charge rule (§§2.9/7).
- **Q94** settles the raw byte-size word rule (§§2 and 7).
- **Q95** settles the raw PC and GAS conversions (§§2 and 7).
- **F11** (open): how the runner produces the `ChildSettled` proof in `ChildOutcome` (EthVmRunner §9).

## 10. Gaps

- **MCOPY integration.** The local snapshot handler and action, byte and
  accounting laws are supplied (§§3–5 and §7). Prove the source relation,
  dispatch and composed progress and resource bounds. O12 remains open.

- **Local copies supplied.** CALLDATACOPY and CODECOPY have complete local
  run, memory and accounting laws (§7) and both source and facade controls
  (§4). Dispatch, trace refinement, composed progress and the resource
  bound for paid large windows remain open.

- **Bounded context words.** §§3/4/7 own the nine standalone handlers and
  their local laws and controls. The scalar operations and caller bounds for MSIZE, NUMBER, GASLIMIT, Q93
  and Q95 have separate obligations.
  Source context assembly, dispatch, trace, settlement, composed gas
  progress and guest execution remain open.

- **Stack handlers.** PUSH0–PUSH32, DUP1–DUP16, DUPN, SWAP1–SWAP16,
  SWAPN and EXCHANGE have local run and accounting laws (§7)
  and the §4 facade controls. The full paid source correspondence and its
  fetch premise (§7) still need proofs.
  The MSIZE scalar cast, R25 observation order, dispatch, whole trace,
  O13 classification and guest composition retain their own obligations.

- **RETURN and REVERT supplied.** §§3/4/5/7 own the two Q92
  handlers, the eight ordinary local laws and bounded raw and pinned
  frame controls. Runner settlement, trace, dispatch, composed
  ownership, gas and resource gates remain open.

- **Opcode bytes supplied; dispatch open:** §3 owns the exact 153-member enum, total conversions, two discharged ordinary laws and complete literal byte controls. `opImplementation`, `step`, invalid-opcode halting and the remaining handlers and laws are open. The enum fixes no future `swapN` argument interpretation, CALL staticness or F11 policy. Source-runtime, composed resource, fuel and guest obligations remain open.

- **Raw request carriers supplied; execution open:** §3 owns the exact `CreateRequest` and `CallRequest` types and private complete facade controls. `genericCreate`, CREATE/CREATE2 preflight, ordered state/gas effects, grant computation, collision and source/admission bridge, CALL-family/`genericCall` producers and their source/admission bridge, the CALL child context, ChildOutcome producers and resume remain unimplemented. The raw carriers add no admission/staticness policy and resolve neither F11 nor fuel, host-resource, guest or EEST obligations.

- **Immutable CREATE context supplied.** Sections 3, 4 and 7 own the complete
  constructor, two policy projections and raw and source controls. The runner
  must still assemble it with the mutable child frame and execute the child.

- **Mutable child frame initialization supplied:** §3/§4/§7 cover both inline
  source sites and the private complete facade clients. The runner still needs
  to assemble context and frame, prove the committed-spill clause through
  execution, and bound the returned potential by the child's grant (G2).

- **Typed results/signature supplied; execution open:** §3/§5/§7 own the exact six-constructor indexed `StepResult`, class-free `Handler` alias and private complete facade clients. Only the two strict local child bounds are carried. Section 3 records the supplied standalone handlers and their local laws. Remaining opcode effects, dispatch/step/Step relation, whole source-Evm/control refinement, child execution/settlement/resume, gas/staticness/admission and F11 remain open; these types close no fuel, resource, guest or readiness gate.

- **Settled child outcome supplied, production open.** §3/§4/§5/§7 own exactly the four-field `ChildOutcome` and private full-payload, dependent-proof, clause/boundary and negative elaboration controls. EthVmRunner §3 supplies the proof-taking result adapter. Actual producer reachability, rollback, source-Evm refinement, runner settlement and proof production (F11), incorporation and resume remain open.

- **Core settlement assertion boundary:** EthVmCore §3/§5/§7 supplies the raw
  ChildSettled predicate and constructive Decidable instance. Non-top
  committed-spill-zero preservation, call/create settlement and snapshots,
  returned proof production, incorporation and child/resume remain open.
  This logical decision procedure chooses neither F11 production option and
  supplies no runtime check, settled executor or generic Q83 effect bridge.

- **F8 address inheritance and SELFDESTRUCT:** the CALL child-context equations, composed inheritance through nested execution and actual SELFDESTRUCT emission remain unimplemented. Require complete logs under independently varied nonliteral address and topic, zero balance, unequal/equal beneficiary and existing gas/static/state-fault ordering. Preserve revert/halt log discard through the runner.

- **Standalone SLOAD supplied.** §3/§4/§5/§7 own the handler, private
  action and accounting laws, and bounded direct-source controls. Dispatch,
  reachable source-world refinement and composed execution remain open.

- **Standalone BLOBHASH supplied.** §3/§4/§5/§7 own the handler, local
  laws and bounded direct-source and ownership controls. Dispatch,
  reachable source-world refinement and composed execution remain open.

- **Standalone CALLDATALOAD supplied.** §3/§4/§5/§7 own the handler, its
  private ordinary laws and local controls. Dispatch, composed source
  refinement and guest replay remain open.

- **Standalone TLOAD supplied.** §3/§4/§5/§7 own the handler, its private local
  laws and isolated direct-source tests. Dispatch, interpreter traces, reachable
  source-world refinement and composed execution remain open.

- **Standalone TSTORE supplied.** §3/§4/§5/§7 own the handler, its private
  action and order laws, and paired direct-source controls. Dispatch,
  rollback and transaction lifetime, composed allocation and guest
  execution remain open.

- **Standalone MLOAD, MSTORE and MSTORE8 supplied.** §3/§4/§5/§7 own the
  ordered run equations, exact paid windows, local G2 laws and complete
  standalone controls. Dispatch, trace and whole-runner refinement, composed
  ownership and resource bounds, and guest execution remain open.

- **Standalone KECCAK supplied.** §§3/4/5/7 own its ordered run, byte and
  local Id accounting laws and bounded controls. Source dispatch and trace,
  generic oracle coupling, whole-runner G2 and resource bounds, and guest
  execution remain open.
- **Standalone EXTCODECOPY supplied.** §§3/4/5/7 own the ordered local
  run and State equations, exact bytes, Id accounting and bounded controls.
  Related source traces, dispatcher integration, composed resources and
  guest execution remain open.
- **R-DEL-1 designator functions supplied.** §§3/4/5/7 own the marker,
  recognition, address extraction, complete byte laws and bounded controls.
  Public length exports and the composed caller obligations remain open.

- **R-DEL-3 delegation resolver supplied.** §§3/4/5/7 cover the two ordered
  State reads, their error layer, selected execution payment and warmth, and
  bounded source controls. The caller must carry the returned address, flag,
  paid meter and warm set through `createEvm`. R-DEL-2 quotation and its
  caller contract remain separate.

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **STOP/ADD/SUB/MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND/ADDMOD/MULMOD/EXP supplied; remaining per-opcode laws open.** §3/§7 own `stop_run` and the sixty-eight ADD/SUB/MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND/ADDMOD/MULMOD/EXP local laws, including raw selected-cost accounting and conditional Id progress. Their local source-entry/price boundaries and bounded direct-source tests are explicit; complete source-model, reachable-entry and trace refinement remain open. Remaining per-opcode/precedence lemmas, `step_iff` and determinism are specifications only; private raw-carrier and typed-result/signature clients prove no execution semantics.
- **LT/GT/SLT/SGT/EQ and ISZERO local handlers supplied.** §§3/4/7 own the thirty binary comparison laws, five ISZERO laws and their complete frame controls. The general handler differential, source-model, trace and reachability refinement, dispatch and settlement remain open.
- **AND/OR/XOR/NOT/BYTE/SHL/SHR/SAR/CLZ standalone handlers supplied.** §§3/4/7 own the 52 local laws and complete frame controls. The source entry relation, trace, reachable-world refinement, dispatch, settlement, interpreter ownership, composed G2 and guest replay remain open.

- **POP standalone handler supplied.** §§3/4/7 own the five local laws and complete frame controls. The source entry relation and trace, reachable-world refinement, dispatch, settlement, interpreter ownership, composed G2 and guest replay remain open.

- **JUMPDEST standalone handler supplied.** §§3/4/7 own its four local laws and complete frame controls. Source trace, dispatch, settlement, composed G2 and guest execution remain open.
- **JUMP and JUMPI standalone handlers supplied.** §§3/4/7 own the twelve local laws and complete frame controls. Destination-map provenance, whole source trace and reachability refinement, dispatch, settlement, composed G2 and guest execution remain open.
- **Gas progress for the CALL family** is [I]: the inequality "execution charge of the calling opcode ≥ stipend + 1" must be proved for all four call opcodes, both preflight-failure paths, and the EIP-150 branch where `gas_left < extra + mem` (which fails the charge, so it is a halt, not a continue).
- **Standalone BLOCKHASH supplied.** §3/§4/§5/§7 own the availability
  check, exact fault offset and R27 action. CONTRACT O13 classifies the
  missing-header case and records its pinned witness fixture.
  Dispatch, guest fault propagation, composed source refinement and
  constructor freezing (DECISIONS B14) remain open.
- **BLOBBASEFEE `U256` overflow** (`I/environment.py:607`) is argued reachable on an unanchored parent header (O13), but not witnessed. It also costs `taylor_exponential` time proportional to its result (DISC-002). The NUMBER and GASLIMIT guest bounds are in R-GEN-7.
- **GASPRICE and BASEFEE standalone handlers supplied (Q93).** §§3/4/7 own
  the ordered action equations and complete controls. Actual source entry
  refinement and trace, dispatch, runner propagation and composed progress
  remain open. EthVmCore R-EXC-2 owns the caller-bound obligations.
- **PC and GAS integration (Q95).** The standalone handlers, local laws
  and controls are supplied (§§3–5 and §7). Prove the pinned source relation,
  the actual caller bounds in EthVmCore R-EXC-2, dispatch, runner fault
  propagation and composed progress.
- **Byte-size handlers supplied (Q94).** §§2–5 and §7 cover the three
  standalone entries, local laws and controls. Actual caller field
  relations, dispatch and proof of the pinned source relation remain open.
- **Standalone SELFBALANCE supplied.** §§3/4/5/7 own the handler,
  complete private run equations and bounded direct controls. Interpreter
  traces, dispatch, composed State, fuel and resource gates remain open.
- **Read-order fidelity** (R-GEN-1). §§3/4/5/7 supply BALANCE and
  EXTCODEHASH with their local laws and direct source and ownership
  controls. Section 4 supplies the SELFBALANCE leaf controls. Interpreter
  traces, dispatch, reachable State and composed fuel, ownership and guest
  gates remain open. EEST `eip7928_block_level_access_lists`
  (211 fixtures) indirectly exercises the wider BAL and witness read order.
- **`to_address_masked`** is owned by `EthBase`, and **`compute_contract_address`, `compute_create2_contract_address`** by `EthCodec` (A1, A2) (`utils/address.py`); this spec assumes their behaviour (low 20 bytes; `keccak(rlp([sender, nonce]))[12:]`; `keccak(0xff ‖ sender ‖ salt ‖ keccak(init))[12:]`) [I: not re-read].
- **`account_deployable` ignores storage** [V], so a CREATE to an address with only storage succeeds after `destroy_storage` in `process_create`; relies on EthState's `destroy_storage` semantics.
- **EIP-8246 detail**: the balance-preserving clear is in `fork.py`/`state_tracker.py` (not read here in full); the SELFDESTRUCT handler spec depends on it only through `accounts_to_delete`.
- **LOG integration.** The local action returns the paid expanded frame on
  static failure (§§3–5 and §7). Prove the pinned source relation, dispatch,
  runner rollback and receipt incorporation. Composed progress and resource
  bounds remain open.
- **`Ops` enum line numbers**: the constant block spans `I/__init__.py:32–220`; the `partial` aliases (push1…) are not inventory items and are covered by `pushN`/`dupN`/`swapN`/`logN`.
- **Precompile-addressed code under delegation** (R-DEL-4) is inferred from the runner branch; no dedicated fixture located.
