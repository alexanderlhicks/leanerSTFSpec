/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Fork
import STFSpec.Vm.Core

/-!
# Public Amsterdam VM configuration clients

Library `EthConformance`. Use the public Fork values and Core providers/laws;
no private representation or compiler-generated equation is inspected.
Spec guidance: `STFSpec/informal/modules/EthFork.md` §§3–4.
-/

open STFSpec STFSpec.Fork.Amsterdam STFSpec.Vm.Core

private def completeCosts : GasCosts := gasCosts
private def completeStateCosts : StateGasCosts := stateGasCosts
private def completeLimits : VmLimits := vmLimits
private def completeConfiguration : VmConfig := vmConfig

private theorem literal_bound : (Fin vmConfig.limits.stackDepthLimit) = Fin 1024 := rfl

private theorem depth_provider : vmConfig.limits.stackDepthLimit = STACK_DEPTH_LIMIT :=
  vmLimits_depth

private theorem init_price (n : Nat) :
    initCodeCost vmConfig n = (2 * Base.ceil32 n) / 32 := by
  rw [initCodeCost_eq]
  rfl

private theorem memory_price (n : Nat) :
    calculateMemoryGasCost vmConfig n =
      3 * (Base.ceil32 n / 32) + (Base.ceil32 n / 32) ^ 2 / 512 := by
  rw [calculateMemoryGasCost_eq]
  rfl

private theorem reconstruct_configuration :
    VmConfig.mk vmConfig.costs vmConfig.stateCosts vmConfig.limits = vmConfig :=
  VmConfig.eta vmConfig
