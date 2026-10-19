/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Public state-gas refund clients

Library `EthConformance`. Ordinary generic clients consume all seven refund laws.
Local meter algebra does not establish caller reachability, settlement or fuel adequacy.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/7.
-/

namespace STFSpec.Conformance.Vm.Core.GasRefundCallerProofs
open STFSpec.Vm.Core

private theorem credit_retains_fields (m : GasMeter) (a : Nat) :
    (creditStateGasRefund m a).stateGasBaseline = m.stateGasBaseline ∧
    (creditStateGasRefund m a).refundCounter = m.refundCounter ∧
    (creditStateGasRefund m a).stateGasCommittedSpill = m.stateGasCommittedSpill := by
  rw [creditStateGasRefund_eq]
  exact ⟨rfl, rfl, rfl⟩

private theorem repay_retains_fields (m : GasMeter) :
    (repayStateGasSpill m).stateGasBaseline = m.stateGasBaseline ∧
    (repayStateGasSpill m).refundCounter = m.refundCounter ∧
    (repayStateGasSpill m).stateGasCommittedSpill = m.stateGasCommittedSpill := by
  rw [repayStateGasSpill_eq]
  exact ⟨rfl, rfl, rfl⟩

private theorem credit_of_le (m : GasMeter) (a : Nat) (h : a ≤ m.stateGasSpilled) :
    creditStateGasRefund m a = { m with
      gasLeft := m.gasLeft + a, stateGasSpilled := m.stateGasSpilled - a } := by
  rw [creditStateGasRefund_eq]
  simp only [Nat.min_eq_left h, Nat.sub_self, Nat.add_zero]

private theorem credit_of_lt (m : GasMeter) (a : Nat) (h : m.stateGasSpilled < a) :
    creditStateGasRefund m a = { m with
      gasLeft := m.gasLeft + m.stateGasSpilled,
      stateGasSpilled := 0, stateGasLeft := m.stateGasLeft + (a - m.stateGasSpilled) } := by
  rw [creditStateGasRefund_eq]
  simp only [Nat.min_eq_right (Nat.le_of_lt h), Nat.sub_self]

private theorem repay_of_le (m : GasMeter) (h : m.stateGasLeft ≤ m.stateGasSpilled) :
    repayStateGasSpill m = { m with
      gasLeft := m.gasLeft + m.stateGasLeft,
      stateGasLeft := 0, stateGasSpilled := m.stateGasSpilled - m.stateGasLeft } := by
  rw [repayStateGasSpill_eq]
  simp only [Nat.min_eq_left h, Nat.sub_self]

private theorem repay_of_lt (m : GasMeter) (h : m.stateGasSpilled < m.stateGasLeft) :
    repayStateGasSpill m = { m with
      gasLeft := m.gasLeft + m.stateGasSpilled,
      stateGasLeft := m.stateGasLeft - m.stateGasSpilled, stateGasSpilled := 0 } := by
  rw [repayStateGasSpill_eq]
  simp only [Nat.min_eq_right (Nat.le_of_lt h), Nat.sub_self]

private theorem repay_identity (m : GasMeter)
    (h : m.stateGasLeft = 0 ∨ m.stateGasSpilled = 0) : repayStateGasSpill m = m := by
  rw [repayStateGasSpill_eq]
  have hz : min m.stateGasLeft m.stateGasSpilled = 0 := by
    rcases h with h | h
    · simp only [h, Nat.zero_min]
    · simp only [h, Nat.min_zero]
  rw [hz]
  simp only [Nat.add_zero, Nat.sub_zero]

private theorem repay_again (m : GasMeter) :
    repayStateGasSpill (repayStateGasSpill m) = repayStateGasSpill m :=
  repayStateGasSpill_idempotent m

private theorem exhausted_after_credit (m : GasMeter) (a : Nat) :
    (repayStateGasSpill (creditStateGasRefund m a)).stateGasLeft = 0 ∨
    (repayStateGasSpill (creditStateGasRefund m a)).stateGasSpilled = 0 :=
  repayStateGasSpill_post _

private theorem zero_credit_then_repay (m : GasMeter) :
    repayStateGasSpill (creditStateGasRefund m 0) = repayStateGasSpill m := by
  rw [creditStateGasRefund_zero]

private theorem charge_refund_repay_phi (m n : GasMeter) (a b : Nat)
    (h : chargeStateGas m a = .ok n) :
    (repayStateGasSpill (creditStateGasRefund n b)).phi = m.phi := by
  rw [repayStateGasSpill_phi, creditStateGasRefund_phi]
  exact chargeStateGas_phi m a n h

-- The local zero-pending-spill premise is necessary; B/q/C remain arbitrary.
private theorem charge_refund_inverse (m n : GasMeter) (a : Nat)
    (hS : m.stateGasSpilled = 0) (hc : chargeStateGas m a = .ok n) :
    creditStateGasRefund n a = m := by
  by_cases hR : a ≤ m.stateGasLeft
  · rw [chargeStateGas_of_le m a hR] at hc
    cases hc
    rw [creditStateGasRefund_eq]
    simp only [hS, Nat.min_zero, Nat.add_zero, Nat.sub_zero]
    cases m
    simp only [GasMeter.mk.injEq] at *
    simp only [true_and, and_true]
    omega
  · have hR' : m.stateGasLeft < a := by omega
    have hA : a ≤ m.stateGasLeft + m.gasLeft := by
      by_cases h : a ≤ m.stateGasLeft + m.gasLeft
      · exact h
      · have hf := (chargeStateGas_eq_error_iff m a .outOfGas).2 ⟨by omega, rfl⟩
        rw [hc] at hf
        contradiction
    rw [chargeStateGas_of_lt m a hR' hA] at hc
    cases hc
    rw [creditStateGasRefund_eq]
    simp only [hS, Nat.zero_add]
    have hm : a - m.stateGasLeft ≤ a := Nat.sub_le _ _
    rw [Nat.min_eq_right hm]
    cases m
    simp only [GasMeter.mk.injEq] at *
    simp only [true_and, and_true, Nat.sub_self]
    omega

end STFSpec.Conformance.Vm.Core.GasRefundCallerProofs
