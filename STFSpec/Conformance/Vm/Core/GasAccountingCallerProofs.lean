/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Public signed refund and maximum-grant clients

Library `EthConformance`. All four provider laws are consumed without unfolding providers.
These are local record/scalar facts, without caller reachability or settlement claims.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/7.
-/

namespace STFSpec.Conformance.Vm.Core.GasAccountingCallerProofs
open STFSpec.Vm.Core

private theorem retained (m : GasMeter) (k : Int) :
    (addRefund m k).gasLeft = m.gasLeft ∧
    (addRefund m k).stateGasLeft = m.stateGasLeft ∧
    (addRefund m k).stateGasBaseline = m.stateGasBaseline ∧
    (addRefund m k).stateGasSpilled = m.stateGasSpilled ∧
    (addRefund m k).stateGasCommittedSpill = m.stateGasCommittedSpill ∧
    (addRefund m k).refundCounter = m.refundCounter + k := by
  rw [addRefund_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem zero_identity (m : GasMeter) : addRefund m 0 = m := by
  rw [addRefund_eq]
  simp only [Int.add_zero]

private theorem addition_composition (m : GasMeter) (k l : Int) :
    addRefund (addRefund m k) l = addRefund m (k + l) := by
  rw [addRefund_eq, addRefund_eq, addRefund_eq]
  simp only [Int.add_assoc]

private theorem addition_inverse (m : GasMeter) (k : Int) :
    addRefund (addRefund m k) (-k) = m := by
  rw [addition_composition]
  have h : k + -k = 0 := by omega
  rw [h, zero_identity]

private theorem potential_twice (m : GasMeter) (k l : Int) :
    (addRefund (addRefund m k) l).phi = m.phi := by
  rw [addRefund_phi, addRefund_phi]

private theorem addition_before_reset (m : GasMeter) (k : Int) :
    restoreStateGas (addRefund m k) = restoreStateGas m := by
  rw [restoreStateGas_eq, restoreStateGas_eq, addRefund_eq]

private theorem addition_after_reset (m : GasMeter) (k : Int) :
    addRefund (restoreStateGas m) k = { m with
      gasLeft := m.gasLeft + m.stateGasSpilled,
      stateGasLeft := m.stateGasBaseline, refundCounter := k, stateGasSpilled := 0 } := by
  rw [addRefund_eq, restoreStateGas_eq]
  simp only [Int.zero_add]

private theorem maximum_bound (g : Nat) : maxMessageCallGas g ≤ g :=
  maxMessageCallGas_le g

private theorem maximum_complement (g : Nat) : maxMessageCallGas g + g / 64 = g := by
  rw [maxMessageCallGas_eq]
  exact Nat.sub_add_cancel (Nat.div_le_self _ _)

private theorem maximum_remainder (g : Nat) : g - maxMessageCallGas g = g / 64 := by
  rw [maxMessageCallGas_eq]
  have h := Nat.div_le_self g 64
  omega

end STFSpec.Conformance.Vm.Core.GasAccountingCallerProofs
