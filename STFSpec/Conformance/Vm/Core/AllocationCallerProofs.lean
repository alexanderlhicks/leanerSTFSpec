/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Public local-allocation clients

Library `EthConformance`. Private complete-result arithmetic, policy and actual
meter/charge/observer clients use only public constructors, projections and laws.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7.
-/

namespace STFSpec.Conformance.Vm.Core.AllocationCallerProofs
open STFSpec.Vm.Core

private theorem raw_constructor (execution reservoir : Nat) :
    let a := EvmGasAllocation.mk execution reservoir
    (a.executionGas, a.stateGasReservoir) = (execution, reservoir) ∧
      EvmGasAllocation.mk a.executionGas a.stateGasReservoir = a := by
  exact ⟨rfl, EvmGasAllocation.eta _⟩

private theorem raw_ext (a b : EvmGasAllocation)
    (he : a.executionGas = b.executionGas) (hr : a.stateGasReservoir = b.stateGasReservoir) :
    a = b := EvmGasAllocation.ext a b he hr

section
variable (cfg : VmConfig) (T I : Nat)
variable (hT : I ≤ T) (hC : I ≤ cfg.costs.txMaxGasLimit)

private theorem allocation_observations :
    let a := allocateEvmGas cfg T I hT hC
    (a.executionGas, a.stateGasReservoir) =
      (min (cfg.costs.txMaxGasLimit - I) (T - I),
       T - I - min (cfg.costs.txMaxGasLimit - I) (T - I)) := by
  rw [allocateEvmGas_eq]

private theorem allocation_conservation :
    let a := allocateEvmGas cfg T I hT hC
    I + a.executionGas + a.stateGasReservoir = T ∧
      I + a.executionGas = min cfg.costs.txMaxGasLimit T ∧
      a.stateGasReservoir = T - cfg.costs.txMaxGasLimit ∧
      a.executionGas ≤ T - I ∧ a.executionGas ≤ cfg.costs.txMaxGasLimit - I := by
  rw [allocateEvmGas_eq]
  dsimp only
  omega

private theorem below_cap (h : T ≤ cfg.costs.txMaxGasLimit) :
    allocateEvmGas cfg T I hT hC = EvmGasAllocation.mk (T - I) 0 := by
  rw [allocateEvmGas_eq]
  have hm : min (cfg.costs.txMaxGasLimit - I) (T - I) = T - I := by omega
  simp only [hm, Nat.sub_self]

private theorem above_cap (h : cfg.costs.txMaxGasLimit ≤ T) :
    allocateEvmGas cfg T I hT hC =
      EvmGasAllocation.mk (cfg.costs.txMaxGasLimit - I) (T - cfg.costs.txMaxGasLimit) := by
  rw [allocateEvmGas_eq]
  dsimp only
  have hm : min (cfg.costs.txMaxGasLimit - I) (T - I) = cfg.costs.txMaxGasLimit - I := by
    omega
  rw [hm]
  congr 1
  omega

private theorem zero_cap (h : cfg.costs.txMaxGasLimit = 0) :
    allocateEvmGas cfg T I hT hC = EvmGasAllocation.mk 0 T := by
  have hi : I = 0 := by omega
  rw [above_cap cfg T I hT hC (by omega), h, hi]
  simp only [Nat.sub_zero]

private theorem intrinsic_is_transaction (h : I = T) :
    allocateEvmGas cfg T I hT hC = EvmGasAllocation.mk 0 0 := by
  rw [below_cap cfg T I hT hC (by omega), h, Nat.sub_self]

private theorem intrinsic_is_cap (h : I = cfg.costs.txMaxGasLimit) :
    allocateEvmGas cfg T I hT hC =
      EvmGasAllocation.mk 0 (T - cfg.costs.txMaxGasLimit) := by
  rw [above_cap cfg T I hT hC (by omega), h, Nat.sub_self]

-- The initial meter is a client of the allocation, not an allocation operation.
private def initialMeter : GasMeter :=
  let a := allocateEvmGas cfg T I hT hC
  GasMeter.mk a.executionGas a.stateGasReservoir a.stateGasReservoir 0 0 0

private theorem initial_meter_observations :
    let a := allocateEvmGas cfg T I hT hC
    let m := initialMeter cfg T I hT hC
    (m.gasLeft, m.stateGasLeft, m.stateGasBaseline, m.refundCounter,
      m.stateGasSpilled, m.stateGasCommittedSpill) =
        (a.executionGas, a.stateGasReservoir, a.stateGasReservoir, 0, 0, 0) := rfl

private theorem initial_observer :
    let m := initialMeter cfg T I hT hC
    txStateGasUsed m m.stateGasBaseline (Nat.le_refl _) = 0 := by
  dsimp only
  rw [txStateGasUsed_eq]
  change ((allocateEvmGas cfg T I hT hC).stateGasReservoir : Int) -
    ((allocateEvmGas cfg T I hT hC).stateGasReservoir : Int) + 0 + 0 = 0
  omega

private theorem initial_execution_charge (q : Nat)
    (hq : q ≤ (allocateEvmGas cfg T I hT hC).executionGas) :
    let a := allocateEvmGas cfg T I hT hC
    chargeGas (initialMeter cfg T I hT hC) q =
      .ok (GasMeter.mk (a.executionGas - q) a.stateGasReservoir a.stateGasReservoir 0 0 0) := by
  exact chargeGas_of_le _ q hq

private theorem initial_execution_error (q : Nat) (e : ExceptionalHalt) :
    chargeGas (initialMeter cfg T I hT hC) q = .error e ↔
      (allocateEvmGas cfg T I hT hC).executionGas < q ∧ e = .outOfGas := by
  exact chargeGas_eq_error_iff _ q e

private theorem initial_charge_potential (q : Nat) (post : GasMeter)
    (h : chargeGas (initialMeter cfg T I hT hC) q = .ok post) :
    post.phi + q = (initialMeter cfg T I hT hC).phi := by
  exact chargeGas_phi _ q post h
end

private theorem independent_policy_calls (a b : VmConfig) (T I : Nat)
    (hTA : I ≤ T) (hCA : I ≤ a.costs.txMaxGasLimit)
    (hTB : I ≤ T) (hCB : I ≤ b.costs.txMaxGasLimit)
    (h : a.costs.txMaxGasLimit = b.costs.txMaxGasLimit) :
    allocateEvmGas a T I hTA hCA = allocateEvmGas b T I hTB hCB := by
  exact allocateEvmGas_congr a b T I hTA hCA hTB hCB h

private theorem unrelated_configuration (cfg : VmConfig) (total zeroCost addCost : Nat)
    (refund : Int) (blob : STFSpec.Base.U64) (discount : Array Nat)
    (stateCosts : StateGasCosts) (limits : VmLimits) (T I : Nat)
    (hT : I ≤ T) (hC : I ≤ cfg.costs.txMaxGasLimit) :
    let changed := VmConfig.mk
      { cfg.costs with
        txMaxTotalGasLimit := total
        zero := zeroCost
        opcodeAdd := addCost
        refundStorageClear := refund
        perBlob := blob
        blsG1KDiscount := discount }
      stateCosts limits
    allocateEvmGas cfg T I hT hC = allocateEvmGas changed T I hT hC := by
  exact allocateEvmGas_congr _ _ T I hT hC hT hC rfl

end STFSpec.Conformance.Vm.Core.AllocationCallerProofs
