/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions.CallRequest
import STFSpec.Vm.Instructions.ChildFrame
import STFSpec.Vm.Instructions.ChildOutcome
import STFSpec.Vm.Instructions.CreateRequest
import STFSpec.Vm.Instructions.Handler
import STFSpec.Vm.Instructions.Arithmetic
import STFSpec.Vm.Instructions.Comparison
import STFSpec.Vm.Instructions.Bitwise
import STFSpec.Vm.Instructions.Pop
import STFSpec.Vm.Instructions.ControlFlow
import STFSpec.Vm.Instructions.MemoryWords
import STFSpec.Vm.Instructions.Stop
import STFSpec.Vm.Instructions.Push
import STFSpec.Vm.Instructions.Dup
import STFSpec.Vm.Instructions.ReturnRevert
import STFSpec.Vm.Instructions.ContextWords
import STFSpec.Vm.Instructions.DynamicSwap
import STFSpec.Vm.Instructions.Balance
import STFSpec.Vm.Instructions.SelfBalance
import STFSpec.Vm.Instructions.Sload
import STFSpec.Vm.Instructions.BlobHash
import STFSpec.Vm.Instructions.BlockHash
import STFSpec.Vm.Instructions.CallDataLoad
import STFSpec.Vm.Instructions.Keccak
import STFSpec.Vm.Instructions.Tload
import STFSpec.Vm.Instructions.Tstore
import STFSpec.Vm.Instructions.Ops

/-!
# STFSpec.Vm.Instructions

One handler per opcode, producing a `StepResult`: a successor frame, a halt/revert/exceptional outcome, or a child call/create request.

Library `EthVmInstructions`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). The raw requests, indexed `StepResult`,
class-free `Handler` signature, opcode byte conversions, STOP and its complete
run law are supplied. The arithmetic handlers ADD/SUB/MUL/DIV/SDIV/MOD/SMOD/SIGNEXTEND/
ADDMOD/MULMOD/EXP, comparison handlers LT/GT/SLT/SGT/EQ/ISZERO and bitwise
handlers AND/OR/XOR/NOT/BYTE/SHL/SHR/SAR/CLZ have ordered run and accounting laws.
The standalone stack handler POP has ordered run laws, exact Id accounting and
strict progress at positive prices.
JUMP, JUMPI and JUMPDEST have complete run equations and local Id accounting laws.
Fixed DUP, DUPN, SWAPN and EXCHANGE have ordered run laws and local Id accounting laws.
Nine bounded context-word handlers have complete run and local Id accounting laws.
BALANCE and EXTCODEHASH supply local warmth, charge and State-read equations.
SELFBALANCE and SLOAD have complete local run equations for their State reads.
BLOBHASH and BLOCKHASH supply local lookup and accounting laws. BLOCKHASH also
records the missing-ancestor fault and the State R27 action.
CALLDATALOAD supplies exact frame and padded-word equations.
MLOAD, MSTORE and MSTORE8 have local run, memory and accounting laws.
Standalone KECCAK has local oracle, memory and accounting laws.
RETURN and REVERT have ordered terminal run laws.
Standalone TLOAD and TSTORE have private local action equations.
PUSH0 through PUSH32 have complete run equations and local Id accounting laws.
The settled `ChildOutcome` carrier and its supplied local proof are also available.
The `childFrame` constructor supplies the mutable frame for CALL and CREATE.
Other handlers, dispatch, step, child context construction and resume remain unimplemented.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md`.
-/
