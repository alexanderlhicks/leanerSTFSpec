/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core.Context
import STFSpec.Vm.Instructions.CreateRequest

/-!
# Immutable CREATE child context

Library `EthVmInstructions`. Build the part of a child CREATE frame that stays
fixed during execution. Spec guidance in `STFSpec/informal/modules/EthVmInstructions.md`
§§3/5/7 and F8.
-/

namespace STFSpec.Vm.Instructions
open STFSpec.Base STFSpec.Vm.Core

/-- Form the immutable CREATE context after the caller has established the depth bound.
EELS `src/ethereum/forks/amsterdam/vm/instructions/system.py:133–150`. -/
def childCtxOfCreate (ctx : FrameCtx) (req : CreateRequest)
    (h : ctx.depth < STACK_DEPTH_LIMIT) : FrameCtx :=
  { ctx with
    caller := req.caller
    currentTarget := req.contractAddress
    value := req.endowment
    callData := Bytes.empty
    codeAddress := none
    code := req.initCode
    jumpdests := validJumpDestinations req.initCode
    depth := ctx.depth + 1
    depth_le := Nat.succ_le_of_lt h
    shouldTransferValue := true
    isStatic := false
    disablePrecompiles := false }

/-- The complete immutable CREATE context and its inherited fields. -/
theorem childCtxOfCreate_eq (ctx : FrameCtx) (req : CreateRequest)
    (h : ctx.depth < STACK_DEPTH_LIMIT) :
    childCtxOfCreate ctx req h =
      { config := ctx.config
        blockEnv := ctx.blockEnv
        txEnv := ctx.txEnv
        caller := req.caller
        currentTarget := req.contractAddress
        value := req.endowment
        callData := Bytes.empty
        codeAddress := none
        code := req.initCode
        jumpdests := validJumpDestinations req.initCode
        depth := ctx.depth + 1
        depth_le := Nat.succ_le_of_lt h
        shouldTransferValue := true
        isStatic := false
        disablePrecompiles := false
        systemAddress := ctx.systemAddress } := rfl

/-- The CREATE child inherits the complete supplied VM configuration. -/
theorem childCtxOfCreate_config (ctx : FrameCtx) (req : CreateRequest)
    (h : ctx.depth < STACK_DEPTH_LIMIT) :
    (childCtxOfCreate ctx req h).config = ctx.config := rfl

/-- The CREATE child inherits the supplied system address under F8. -/
theorem childCtxOfCreate_systemAddress (ctx : FrameCtx) (req : CreateRequest)
    (h : ctx.depth < STACK_DEPTH_LIMIT) :
    (childCtxOfCreate ctx req h).systemAddress = ctx.systemAddress := rfl

end STFSpec.Vm.Instructions
