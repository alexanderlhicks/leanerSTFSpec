/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Public local-settlement clients

Library `EthConformance`. Ten private client groups retain complete results,
local arithmetic premises and the public meter/validated-word boundaries.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7.
-/

namespace STFSpec.Conformance.Vm.Core.SettlementCallerProofs
open STFSpec.Vm.Core STFSpec.Base

-- Raw construction and equality impose no producer invariant.
private theorem raw_constructor (used left execution state : Nat) :
    let out := TransactionGasSettlement.mk used left execution state
    (out.gasUsed, out.gasLeft, out.executionGasUsed, out.stateGasUsed) =
      (used, left, execution, state) ∧
      TransactionGasSettlement.mk out.gasUsed out.gasLeft
        out.executionGasUsed out.stateGasUsed = out := by
  exact ⟨rfl, TransactionGasSettlement.eta _⟩

private theorem raw_ext (a b : TransactionGasSettlement)
    (hu : a.gasUsed = b.gasUsed) (hl : a.gasLeft = b.gasLeft)
    (he : a.executionGasUsed = b.executionGasUsed) (hs : a.stateGasUsed = b.stateGasUsed) :
    a = b := TransactionGasSettlement.ext a b hu hl he hs

section
variable (T F gL sL : Nat) (r : U256) (s : Int)
variable (hR : gL + sL ≤ T) (hS : s.toNat ≤ T - gL - sL) (hF : F ≤ T)

-- Complete observations consume the public equation.
private theorem observations :
    let out := settleTransactionGas T F gL sL r s hR hS hF
    let p := T - gL - sL
    let used := max (p - min (p / 5) r.toNat) F
    (out.gasUsed, out.gasLeft, out.executionGasUsed, out.stateGasUsed) =
      (used, T - used, max (p - s.toNat) F, s.toNat) := by
  rw [settleTransactionGas_eq]

-- Sender conservation and both supplied bounds retain their actual result.
private theorem sender_conservation :
    let out := settleTransactionGas T F gL sL r s hR hS hF
    out.gasUsed + out.gasLeft = T ∧ out.gasUsed ≤ T ∧ F ≤ out.executionGasUsed := by
  have hu := settleTransactionGas_gasUsed_le T F gL sL r s hR hS hF
  have he := settleTransactionGas_executionGasUsed_ge_floor T F gL sL r s hR hS hF
  rw [settleTransactionGas_eq] at hu he ⊢
  dsimp only at hu he ⊢
  omega

-- Refund transport retains the whole block pair, with conditional full equality.
private theorem refund_dimensions (r' : U256) :
    let a := settleTransactionGas T F gL sL r s hR hS hF
    let b := settleTransactionGas T F gL sL r' s hR hS hF
    (a.executionGasUsed, a.stateGasUsed) = (b.executionGasUsed, b.stateGasUsed) := by
  rw [settleTransactionGas_eq, settleTransactionGas_eq]

private theorem capped_refund_congr (r' : U256)
    (h : min ((T - gL - sL) / 5) r.toNat = min ((T - gL - sL) / 5) r'.toNat) :
    settleTransactionGas T F gL sL r s hR hS hF =
      settleTransactionGas T F gL sL r' s hR hS hF := by
  rw [settleTransactionGas_eq, settleTransactionGas_eq]
  dsimp only
  rw [h]

-- Only the signed state input is erased when nonpositive.
private theorem negative_state_erasure (hn : s ≤ 0) :
    settleTransactionGas T F gL sL r s hR hS hF =
      settleTransactionGas T F gL sL r 0 hR (Nat.zero_le _) hF := by
  have hz : s.toNat = 0 := by omega
  rw [settleTransactionGas_eq, settleTransactionGas_eq]
  simp only [hz, Int.toNat_zero]

-- Full sender/execution floor and refund-cap branches have explicit local premises.
private theorem sender_floor_below
    (h : F ≤ T - gL - sL - min ((T - gL - sL) / 5) r.toNat) :
    settleTransactionGas T F gL sL r s hR hS hF =
      let used := T - gL - sL - min ((T - gL - sL) / 5) r.toNat
      TransactionGasSettlement.mk used (T - used) (max (T - gL - sL - s.toNat) F)
        s.toNat := by
  rw [settleTransactionGas_eq]
  dsimp only
  rw [Nat.max_eq_left h]

private theorem sender_floor_above
    (h : T - gL - sL - min ((T - gL - sL) / 5) r.toNat ≤ F) :
    settleTransactionGas T F gL sL r s hR hS hF =
      TransactionGasSettlement.mk F (T - F) (max (T - gL - sL - s.toNat) F) s.toNat := by
  rw [settleTransactionGas_eq]
  dsimp only
  rw [Nat.max_eq_right h]

private theorem execution_floor_below (h : F ≤ T - gL - sL - s.toNat) :
    settleTransactionGas T F gL sL r s hR hS hF =
      let used := max (T - gL - sL - min ((T - gL - sL) / 5) r.toNat) F
      TransactionGasSettlement.mk used (T - used) (T - gL - sL - s.toNat) s.toNat := by
  rw [settleTransactionGas_eq]
  dsimp only
  rw [Nat.max_eq_left h]

private theorem execution_floor_above (h : T - gL - sL - s.toNat ≤ F) :
    settleTransactionGas T F gL sL r s hR hS hF =
      let used := max (T - gL - sL - min ((T - gL - sL) / 5) r.toNat) F
      TransactionGasSettlement.mk used (T - used) F s.toNat := by
  rw [settleTransactionGas_eq]
  dsimp only
  rw [Nat.max_eq_right h]

private theorem refund_below_cap (h : r.toNat ≤ (T - gL - sL) / 5) :
    settleTransactionGas T F gL sL r s hR hS hF =
      let used := max (T - gL - sL - r.toNat) F
      TransactionGasSettlement.mk used (T - used) (max (T - gL - sL - s.toNat) F)
        s.toNat := by
  rw [settleTransactionGas_eq]
  dsimp only
  rw [Nat.min_eq_right h]

private theorem refund_above_cap (h : (T - gL - sL) / 5 ≤ r.toNat) :
    settleTransactionGas T F gL sL r s hR hS hF =
      let used := max (T - gL - sL - (T - gL - sL) / 5) F
      TransactionGasSettlement.mk used (T - used) (max (T - gL - sL - s.toNat) F)
        s.toNat := by
  rw [settleTransactionGas_eq]
  dsimp only
  rw [Nat.min_eq_left h]

-- The complete dimensions need not sum to the sender charge or be bounded by T.
private theorem dimension_sum :
    let out := settleTransactionGas T F gL sL r s hR hS hF
    out.executionGasUsed + out.stateGasUsed = max (T - gL - sL) (F + s.toNat) := by
  rw [settleTransactionGas_eq]
  dsimp only
  omega

-- Pure fee algebra uses the actual local price-order premise, without providers.
private theorem fee_decomposition (effective base : Nat) (hPrice : base ≤ effective) :
    let out := settleTransactionGas T F gL sL r s hR hS hF
    T * effective = out.gasLeft * effective + out.gasUsed * base +
      out.gasUsed * (effective - base) := by
  dsimp only
  let out := settleTransactionGas T F gL sL r s hR hS hF
  have hc : out.gasUsed + out.gasLeft = T :=
    (sender_conservation T F gL sL r s hR hS hF).1
  have hp : base + (effective - base) = effective := by omega
  have hm : out.gasUsed * effective =
      out.gasUsed * base + out.gasUsed * (effective - base) := by
    rw [← Nat.mul_add, hp]
  change T * effective = out.gasLeft * effective + out.gasUsed * base +
    out.gasUsed * (effective - base)
  calc
    T * effective = (out.gasUsed + out.gasLeft) * effective := by rw [hc]
    _ = out.gasUsed * effective + out.gasLeft * effective := by rw [Nat.add_mul]
    _ = out.gasLeft * effective + out.gasUsed * base +
        out.gasUsed * (effective - base) := by rw [hm]; omega

-- A Nat observation is used only with its existing checked-word witness.
private theorem validated_nat_bridge (n : Nat) (hWord : U256.ofNat? n = some r) :
    n < 2 ^ 256 ∧ U256.ofNat? r.toNat = some r ∧
      settleTransactionGas T F gL sL r s hR hS hF =
        (let p := T - gL - sL
         let used := max (p - min (p / 5) n) F
         TransactionGasSettlement.mk used (T - used) (max (p - s.toNat) F) s.toNat) := by
  have hr := (U256.ofNat?_eq_some_iff n r).mp hWord
  refine ⟨hr.1, U256.ofNat?_toNat r, ?_⟩
  rw [settleTransactionGas_eq, hr.2]

end

-- Actual meter reads and public signed usage keep all local witnesses explicit.
private theorem meter_boundary (m : GasMeter) (R T F : Nat) (r : U256)
    (hBase : m.stateGasBaseline ≤ R) (hRefund : (r.toNat : Int) = m.refundCounter)
    (hReturned : m.gasLeft + m.stateGasLeft ≤ T)
    (hState : (txStateGasUsed m R hBase).toNat ≤ T - m.gasLeft - m.stateGasLeft)
    (hFloor : F ≤ T) :
    let out := settleTransactionGas T F m.gasLeft m.stateGasLeft r
      (txStateGasUsed m R hBase) hReturned hState hFloor
    let p := T - m.gasLeft - m.stateGasLeft
    let used := max (p - min (p / 5) r.toNat) F
    let state := ((R : Int) - (m.stateGasLeft : Int) + (m.stateGasSpilled : Int) +
      (m.stateGasCommittedSpill : Int)).toNat
    (out, m) = (TransactionGasSettlement.mk used (T - used) (max (p - state) F) state, m) ∧
      0 ≤ m.refundCounter ∧ m.refundCounter < (2 : Int) ^ 256 := by
  constructor
  · simp only [settleTransactionGas_eq, txStateGasUsed_eq]
  · have hr := U256.toNat_lt r
    omega

end STFSpec.Conformance.Vm.Core.SettlementCallerProofs
