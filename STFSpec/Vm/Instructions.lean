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
import STFSpec.Vm.Instructions.Stop
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
Standalone TLOAD and TSTORE have private local action equations.
The settled `ChildOutcome` carrier and its supplied local proof are also available.
The `childFrame` constructor supplies the mutable frame for CALL and CREATE.
Other handlers, dispatch, step, child context construction and resume remain unimplemented.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md`.
-/
