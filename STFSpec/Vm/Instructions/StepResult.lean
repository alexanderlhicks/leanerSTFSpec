/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core.Context
import STFSpec.Vm.Instructions.CallRequest
import STFSpec.Vm.Instructions.CreateRequest

/-!
# Typed instruction results

Library `EthVmInstructions`. Control results retain the complete mutable frame and
payload under the original fixed context. Child requests carry only the two local
strict bounds; opcode effects and source refinement remain separate.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md` §§3/5/7.
-/

namespace STFSpec.Vm.Instructions
open STFSpec.Base STFSpec.Vm.Core

/-- Instruction control under a fixed context, including bounded child suspension.
This is the guided abstraction of EELS control, not an opcode implementation. -/
inductive StepResult (ctx : FrameCtx) where
  | «continue» (f : Frame)
  | stop (f : Frame) (output : Bytes)
  | revert (f : Frame) (output : Bytes)
  | halt (f : Frame) (e : ExceptionalHalt)
  | call (parent : Frame) (req : CallRequest) (h : ctx.depth < STACK_DEPTH_LIMIT)
      (hs : parent.stack.size < STACK_DEPTH_LIMIT)
  | create (parent : Frame) (req : CreateRequest) (h : ctx.depth < STACK_DEPTH_LIMIT)
      (hs : parent.stack.size < STACK_DEPTH_LIMIT)

end STFSpec.Vm.Instructions
