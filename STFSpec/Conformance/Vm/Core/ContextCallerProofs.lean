/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Complete public call-context and assembled-frame clients

Library `EthConformance`. Every declaration is private. Constructor/projection types,
complete reconstruction and independent replacements use public raw-record reduction.
Provider values, including the abstract JumpdestMap, are retained whole.
Only depth replacement needs a new proof of its own existing local bound.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7.
-/

namespace STFSpec.Conformance.Vm.Core.ContextCallerProofs
open STFSpec.Vm.Core STFSpec.Base

private def constructor_signature :
    (config : VmConfig) → (blockEnv : BlockEnvironment) →
    (txEnv : TransactionEnvironment) → (caller currentTarget : Address) →
    (value : U256) → (callData : Bytes) → (codeAddress : Option Address) →
    (code : Bytes) → (jumpdests : JumpdestMap) → (depth : Nat) →
    depth ≤ STACK_DEPTH_LIMIT → Bool → Bool → Bool → Address → FrameCtx := FrameCtx.mk

private theorem supplied_constructor
    (config : VmConfig)
    (blockEnv : BlockEnvironment)
    (txEnv : TransactionEnvironment)
    (caller : Address)
    (currentTarget : Address)
    (value : U256)
    (callData : Bytes)
    (codeAddress : Option Address)
    (code : Bytes)
    (jumpdests : JumpdestMap)
    (depth : Nat)
    (depth_le : depth ≤ STACK_DEPTH_LIMIT)
    (shouldTransferValue : Bool)
    (isStatic : Bool)
    (disablePrecompiles : Bool)
    (systemAddress : Address) :
    let ctx := FrameCtx.mk config blockEnv txEnv caller currentTarget value callData
      codeAddress code jumpdests depth depth_le shouldTransferValue isStatic disablePrecompiles
      systemAddress
    (ctx.config, ctx.blockEnv, ctx.txEnv, ctx.caller, ctx.currentTarget, ctx.value,
      ctx.callData, ctx.codeAddress, ctx.code, ctx.jumpdests, ctx.depth,
      ctx.shouldTransferValue, ctx.isStatic, ctx.disablePrecompiles, ctx.systemAddress) =
      (config, blockEnv, txEnv, caller, currentTarget, value, callData, codeAddress, code,
        jumpdests, depth, shouldTransferValue, isStatic, disablePrecompiles, systemAddress) ∧
      ctx.depth_le = depth_le := by
  exact ⟨rfl, rfl⟩

private theorem reconstruct (ctx : FrameCtx) :
    FrameCtx.mk ctx.config ctx.blockEnv ctx.txEnv ctx.caller ctx.currentTarget ctx.value
      ctx.callData ctx.codeAddress ctx.code ctx.jumpdests ctx.depth ctx.depth_le
      ctx.shouldTransferValue ctx.isStatic ctx.disablePrecompiles ctx.systemAddress = ctx := by
  rfl

private theorem replace_config (ctx : FrameCtx) (replacement : VmConfig) :
    ({ ctx with config := replacement } : FrameCtx) =
      FrameCtx.mk replacement ctx.blockEnv ctx.txEnv ctx.caller ctx.currentTarget ctx.value
        ctx.callData ctx.codeAddress ctx.code ctx.jumpdests ctx.depth ctx.depth_le
        ctx.shouldTransferValue ctx.isStatic ctx.disablePrecompiles ctx.systemAddress := by
  rfl

private theorem replace_block_env (ctx : FrameCtx) (replacement : BlockEnvironment) :
    ({ ctx with blockEnv := replacement } : FrameCtx) =
      FrameCtx.mk ctx.config replacement ctx.txEnv ctx.caller ctx.currentTarget ctx.value
        ctx.callData ctx.codeAddress ctx.code ctx.jumpdests ctx.depth ctx.depth_le
        ctx.shouldTransferValue ctx.isStatic ctx.disablePrecompiles ctx.systemAddress := by
  rfl

private theorem replace_tx_env (ctx : FrameCtx) (replacement : TransactionEnvironment) :
    ({ ctx with txEnv := replacement } : FrameCtx) =
      FrameCtx.mk ctx.config ctx.blockEnv replacement ctx.caller ctx.currentTarget ctx.value
        ctx.callData ctx.codeAddress ctx.code ctx.jumpdests ctx.depth ctx.depth_le
        ctx.shouldTransferValue ctx.isStatic ctx.disablePrecompiles ctx.systemAddress := by
  rfl

private theorem replace_caller (ctx : FrameCtx) (replacement : Address) :
    ({ ctx with caller := replacement } : FrameCtx) =
      FrameCtx.mk ctx.config ctx.blockEnv ctx.txEnv replacement ctx.currentTarget ctx.value
        ctx.callData ctx.codeAddress ctx.code ctx.jumpdests ctx.depth ctx.depth_le
        ctx.shouldTransferValue ctx.isStatic ctx.disablePrecompiles ctx.systemAddress := by
  rfl

private theorem replace_current_target (ctx : FrameCtx) (replacement : Address) :
    ({ ctx with currentTarget := replacement } : FrameCtx) =
      FrameCtx.mk ctx.config ctx.blockEnv ctx.txEnv ctx.caller replacement ctx.value ctx.callData
        ctx.codeAddress ctx.code ctx.jumpdests ctx.depth ctx.depth_le ctx.shouldTransferValue
        ctx.isStatic ctx.disablePrecompiles ctx.systemAddress := by
  rfl

private theorem replace_value (ctx : FrameCtx) (replacement : U256) :
    ({ ctx with value := replacement } : FrameCtx) =
      FrameCtx.mk ctx.config ctx.blockEnv ctx.txEnv ctx.caller ctx.currentTarget replacement
        ctx.callData ctx.codeAddress ctx.code ctx.jumpdests ctx.depth ctx.depth_le
        ctx.shouldTransferValue ctx.isStatic ctx.disablePrecompiles ctx.systemAddress := by
  rfl

private theorem replace_call_data (ctx : FrameCtx) (replacement : Bytes) :
    ({ ctx with callData := replacement } : FrameCtx) =
      FrameCtx.mk ctx.config ctx.blockEnv ctx.txEnv ctx.caller ctx.currentTarget ctx.value
        replacement ctx.codeAddress ctx.code ctx.jumpdests ctx.depth ctx.depth_le
        ctx.shouldTransferValue ctx.isStatic ctx.disablePrecompiles ctx.systemAddress := by
  rfl

private theorem replace_code_address (ctx : FrameCtx) (replacement : Option Address) :
    ({ ctx with codeAddress := replacement } : FrameCtx) =
      FrameCtx.mk ctx.config ctx.blockEnv ctx.txEnv ctx.caller ctx.currentTarget ctx.value
        ctx.callData replacement ctx.code ctx.jumpdests ctx.depth ctx.depth_le
        ctx.shouldTransferValue ctx.isStatic ctx.disablePrecompiles ctx.systemAddress := by
  rfl

private theorem replace_code (ctx : FrameCtx) (replacement : Bytes) :
    ({ ctx with code := replacement } : FrameCtx) =
      FrameCtx.mk ctx.config ctx.blockEnv ctx.txEnv ctx.caller ctx.currentTarget ctx.value
        ctx.callData ctx.codeAddress replacement ctx.jumpdests ctx.depth ctx.depth_le
        ctx.shouldTransferValue ctx.isStatic ctx.disablePrecompiles ctx.systemAddress := by
  rfl

private theorem replace_jumpdests (ctx : FrameCtx) (replacement : JumpdestMap) :
    ({ ctx with jumpdests := replacement } : FrameCtx) =
      FrameCtx.mk ctx.config ctx.blockEnv ctx.txEnv ctx.caller ctx.currentTarget ctx.value
        ctx.callData ctx.codeAddress ctx.code replacement ctx.depth ctx.depth_le
        ctx.shouldTransferValue ctx.isStatic ctx.disablePrecompiles ctx.systemAddress := by
  rfl

private theorem replace_depth (ctx : FrameCtx) (replacement : Nat)
    (h : replacement ≤ STACK_DEPTH_LIMIT) :
    ({ ctx with depth := replacement, depth_le := h } : FrameCtx) =
      FrameCtx.mk ctx.config ctx.blockEnv ctx.txEnv ctx.caller ctx.currentTarget ctx.value
        ctx.callData ctx.codeAddress ctx.code ctx.jumpdests replacement h
        ctx.shouldTransferValue ctx.isStatic ctx.disablePrecompiles ctx.systemAddress := by
  rfl

private theorem replace_should_transfer_value (ctx : FrameCtx) (replacement : Bool) :
    ({ ctx with shouldTransferValue := replacement } : FrameCtx) =
      FrameCtx.mk ctx.config ctx.blockEnv ctx.txEnv ctx.caller ctx.currentTarget ctx.value
        ctx.callData ctx.codeAddress ctx.code ctx.jumpdests ctx.depth ctx.depth_le replacement
        ctx.isStatic ctx.disablePrecompiles ctx.systemAddress := by
  rfl

private theorem replace_is_static (ctx : FrameCtx) (replacement : Bool) :
    ({ ctx with isStatic := replacement } : FrameCtx) =
      FrameCtx.mk ctx.config ctx.blockEnv ctx.txEnv ctx.caller ctx.currentTarget ctx.value
        ctx.callData ctx.codeAddress ctx.code ctx.jumpdests ctx.depth ctx.depth_le
        ctx.shouldTransferValue replacement ctx.disablePrecompiles ctx.systemAddress := by
  rfl

private theorem replace_disable_precompiles (ctx : FrameCtx) (replacement : Bool) :
    ({ ctx with disablePrecompiles := replacement } : FrameCtx) =
      FrameCtx.mk ctx.config ctx.blockEnv ctx.txEnv ctx.caller ctx.currentTarget ctx.value
        ctx.callData ctx.codeAddress ctx.code ctx.jumpdests ctx.depth ctx.depth_le
        ctx.shouldTransferValue ctx.isStatic replacement ctx.systemAddress := by
  rfl

private theorem replace_system_address (ctx : FrameCtx) (replacement : Address) :
    ({ ctx with systemAddress := replacement } : FrameCtx) =
      FrameCtx.mk ctx.config ctx.blockEnv ctx.txEnv ctx.caller ctx.currentTarget ctx.value
        ctx.callData ctx.codeAddress ctx.code ctx.jumpdests ctx.depth ctx.depth_le
        ctx.shouldTransferValue ctx.isStatic ctx.disablePrecompiles replacement := by
  rfl

private def evm_constructor_signature : FrameCtx → Frame → Evm := Evm.mk

private theorem supplied_evm (ctx : FrameCtx) (f : Frame) :
    let evm := Evm.mk ctx f
    (evm.ctx, evm.frame) = (ctx, f) := by
  rfl

private theorem reconstruct_evm (evm : Evm) : Evm.mk evm.ctx evm.frame = evm := by
  rfl

private theorem replace_ctx (evm : Evm) (ctx : FrameCtx) :
    ({ evm with ctx := ctx } : Evm) = Evm.mk ctx evm.frame := by
  rfl

private theorem replace_frame (evm : Evm) (f : Frame) :
    ({ evm with frame := f } : Evm) = Evm.mk evm.ctx f := by
  rfl

end STFSpec.Conformance.Vm.Core.ContextCallerProofs
