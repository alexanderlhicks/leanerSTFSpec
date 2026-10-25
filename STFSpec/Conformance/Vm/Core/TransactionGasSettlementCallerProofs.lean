/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Private settlement public-law clients

Library `EthConformance`. Conditional arithmetic clients on explicit local hypotheses;
no Runner, payment, global meter invariant or whole-guest proof is supplied.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7 (Q66).
-/

namespace STFSpec.Conformance.Vm.Core.TransactionGasSettlementCallerProofs
open STFSpec.Vm.Core STFSpec.Base

private theorem raw (u l x s : Nat) :
    let a := TransactionGasSettlement.mk u l x s
    (a.gasUsed, a.gasLeft, a.executionGasUsed, a.stateGasUsed) = (u, l, x, s) ∧
    TransactionGasSettlement.mk a.gasUsed a.gasLeft a.executionGasUsed a.stateGasUsed = a := by
  exact ⟨rfl, TransactionGasSettlement.eta _⟩

private theorem raw_ext (a b : TransactionGasSettlement)
    (hu : a.gasUsed = b.gasUsed) (hl : a.gasLeft = b.gasLeft)
    (hx : a.executionGasUsed = b.executionGasUsed) (hs : a.stateGasUsed = b.stateGasUsed) :
    a = b := TransactionGasSettlement.ext a b hu hl hx hs

private theorem raw_replace (a : TransactionGasSettlement) (u l x s : Nat) :
    ({ a with gasUsed := u }).gasUsed = u ∧
    ({ a with gasLeft := l }).gasLeft = l ∧
    ({ a with executionGasUsed := x }).executionGasUsed = x ∧
    ({ a with stateGasUsed := s }).stateGasUsed = s ∧
    ({ a with gasUsed := u, gasLeft := l, executionGasUsed := x, stateGasUsed := s }) =
      TransactionGasSettlement.mk u l x s := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem raw_congr (u l x s u' l' x' s' : Nat)
    (hu : u = u') (hl : l = l') (hx : x = x') (hs : s = s') :
    TransactionGasSettlement.mk u l x s = TransactionGasSettlement.mk u' l' x' s' := by
  exact TransactionGasSettlement.ext _ _ hu hl hx hs

private theorem single_field_congr (a : TransactionGasSettlement)
    (u u' l l' x x' s s' : Nat) (hu : u = u') (hl : l = l')
    (hx : x = x') (hs : s = s') :
    { a with gasUsed := u } = { a with gasUsed := u' } ∧
    { a with gasLeft := l } = { a with gasLeft := l' } ∧
    { a with executionGasUsed := x } = { a with executionGasUsed := x' } ∧
    { a with stateGasUsed := s } = { a with stateGasUsed := s' } := by
  exact ⟨TransactionGasSettlement.ext _ _ hu rfl rfl rfl,
    TransactionGasSettlement.ext _ _ rfl hl rfl rfl,
    TransactionGasSettlement.ext _ _ rfl rfl hx rfl,
    TransactionGasSettlement.ext _ _ rfl rfl rfl hs⟩

section
variable (T F E R : Nat) (r : U256) (s : Int)
variable (hReturned : E + R ≤ T) (hState : s.toNat ≤ T - E - R) (hFloor : F ≤ T)

private theorem sender_ranges :
    let q := settleTransactionGas T F E R r s hReturned hState hFloor
    let p := T - E - R
    let c := min (p / 5) r.toNat
    q.gasUsed + q.gasLeft = T ∧ F ≤ q.gasUsed ∧ q.gasUsed ≤ T ∧
      q.gasLeft ≤ T ∧ c ≤ p ∧ p ≤ T := by
  have hu := settleTransactionGas_gasUsed_le T F E R r s hReturned hState hFloor
  rw [settleTransactionGas_eq] at hu ⊢
  dsimp only at hu ⊢
  have hm := Nat.min_le_left ((T - E - R) / 5) r.toNat
  have hd := Nat.div_le_self (T - E - R) 5
  omega

private theorem dimensions :
    let q := settleTransactionGas T F E R r s hReturned hState hFloor
    let p := T - E - R
    let c := min (p / 5) r.toNat
    q.stateGasUsed = s.toNat ∧ q.stateGasUsed ≤ p ∧
      F ≤ q.executionGasUsed ∧ q.executionGasUsed ≤ T ∧
      q.executionGasUsed + q.stateGasUsed = max p (F + s.toNat) ∧
      q.gasUsed + c = max p (F + c) := by
  rw [settleTransactionGas_eq]
  dsimp only
  have hm := Nat.min_le_left ((T - E - R) / 5) r.toNat
  have hd := Nat.div_le_self (T - E - R) 5
  omega

private theorem below_floor_dimensions
    (hx : F ≤ T - E - R - s.toNat)
    (hu : F ≤ T - E - R - min ((T - E - R) / 5) r.toNat) :
    let q := settleTransactionGas T F E R r s hReturned hState hFloor
    q.executionGasUsed + q.stateGasUsed = T - E - R ∧
      q.gasUsed + min ((T - E - R) / 5) r.toNat = T - E - R := by
  rw [settleTransactionGas_eq]
  dsimp only
  have hm := Nat.min_le_left ((T - E - R) / 5) r.toNat
  have hd := Nat.div_le_self (T - E - R) 5
  omega

private theorem refund_dimensions (r' : U256) :
    let a := settleTransactionGas T F E R r s hReturned hState hFloor
    let b := settleTransactionGas T F E R r' s hReturned hState hFloor
    (a.executionGasUsed, a.stateGasUsed) = (b.executionGasUsed, b.stateGasUsed) := by
  rw [settleTransactionGas_eq, settleTransactionGas_eq]

private theorem refund_cap_congr (r' : U256)
    (hc : min ((T - E - R) / 5) r.toNat = min ((T - E - R) / 5) r'.toNat) :
    settleTransactionGas T F E R r s hReturned hState hFloor =
      settleTransactionGas T F E R r' s hReturned hState hFloor := by
  rw [settleTransactionGas_eq, settleTransactionGas_eq]
  dsimp only
  rw [hc]

private theorem signed_congr (s' : Int) (hs' : s'.toNat ≤ T - E - R)
    (hs : s.toNat = s'.toNat) :
    settleTransactionGas T F E R r s hReturned hState hFloor =
      settleTransactionGas T F E R r s' hReturned hs' hFloor := by
  rw [settleTransactionGas_eq, settleTransactionGas_eq, hs]

private theorem negative_erasure (hs : s ≤ 0) :
    settleTransactionGas T F E R r s hReturned hState hFloor =
      settleTransactionGas T F E R r 0 hReturned (by simp) hFloor ∧
    (settleTransactionGas T F E R r s hReturned hState hFloor).executionGasUsed =
      max (T - E - R) F := by
  have hz : s.toNat = 0 := by omega
  rw [settleTransactionGas_eq, settleTransactionGas_eq]
  simp only [hz, Int.toNat_zero, Nat.sub_zero, and_self]

private theorem state_sender_independent (s' : Int) (hs' : s'.toNat ≤ T - E - R) :
    let a := settleTransactionGas T F E R r s hReturned hState hFloor
    let b := settleTransactionGas T F E R r s' hReturned hs' hFloor
    (a.gasUsed, a.gasLeft) = (b.gasUsed, b.gasLeft) := by
  rw [settleTransactionGas_eq, settleTransactionGas_eq]

private theorem floor_branches :
    let q := settleTransactionGas T F E R r s hReturned hState hFloor
    let p := T - E - R
    let c := min (p / 5) r.toNat
    (F ≤ p - c → q.gasUsed = p - c) ∧
      (p - c ≤ F → q.gasUsed = F) ∧
      (F ≤ p - s.toNat → q.executionGasUsed = p - s.toNat) ∧
      (p - s.toNat ≤ F → q.executionGasUsed = F) := by
  rw [settleTransactionGas_eq]
  dsimp only
  omega
end

-- S20/S21 and S22 preserve independent block dimensions even beyond sender/T totals.
private theorem dimensions_above_transaction :
    let q := settleTransactionGas 10 10 0 0 (U256.ofNat 0) 1
      (by decide) (by decide) (by decide)
    q.executionGasUsed + q.stateGasUsed > 10 ∧ q.gasUsed = 10 := by
  rw [settleTransactionGas_eq]
  decide

private theorem dimensions_above_sender :
    let q := settleTransactionGas 10 0 0 0 (U256.ofNat 2) 10
      (by decide) (by decide) (by decide)
    q.executionGasUsed + q.stateGasUsed > q.gasUsed := by
  rw [settleTransactionGas_eq]
  decide

private theorem meter_bound (T I E₀ R₀ : Nat) (m : GasMeter)
    (hEntry : T = I + E₀ + R₀) (hReturned : m.gasLeft + m.stateGasLeft ≤ T)
    (hBaseline : m.stateGasBaseline ≤ R₀)
    (hPotential : m.gasLeft + m.stateGasSpilled + m.stateGasCommittedSpill ≤ I + E₀) :
    (txStateGasUsed m R₀ hBaseline).toNat ≤ T - m.gasLeft - m.stateGasLeft := by
  rw [txStateGasUsed_eq]
  omega

private theorem entry_meter_composition (T I E₀ R₀ F : Nat) (m : GasMeter) (r : U256)
    (hEntry : T = I + E₀ + R₀) (hReturned : m.gasLeft + m.stateGasLeft ≤ T)
    (hBaseline : m.stateGasBaseline ≤ R₀)
    (hPotential : m.gasLeft + m.stateGasSpilled + m.stateGasCommittedSpill ≤ I + E₀)
    (hFloor : F ≤ T) :
    let hs := meter_bound T I E₀ R₀ m hEntry hReturned hBaseline hPotential
    let q := settleTransactionGas T F m.gasLeft m.stateGasLeft r
      (txStateGasUsed m R₀ hBaseline) hReturned hs hFloor
    q.gasUsed + q.gasLeft = T ∧ q.stateGasUsed ≤ T - m.gasLeft - m.stateGasLeft := by
  dsimp only
  have hu := settleTransactionGas_gasUsed_le T F m.gasLeft m.stateGasLeft r
    (txStateGasUsed m R₀ hBaseline) hReturned
    (meter_bound T I E₀ R₀ m hEntry hReturned hBaseline hPotential) hFloor
  have hs := meter_bound T I E₀ R₀ m hEntry hReturned hBaseline hPotential
  rw [settleTransactionGas_eq] at hu ⊢
  dsimp only at hu ⊢
  omega

private theorem allocation_settlement_cap (cfg : VmConfig) (T I F : Nat)
    (hIntrinsicTx : I ≤ T) (hIntrinsicCap : I ≤ cfg.costs.txMaxGasLimit)
    (m : GasMeter) (r : U256)
    (hReturned : m.gasLeft + m.stateGasLeft ≤ T)
    (hBaseline : m.stateGasBaseline ≤
      (allocateEvmGas cfg T I hIntrinsicTx hIntrinsicCap).stateGasReservoir)
    (hPotential : m.gasLeft + m.stateGasSpilled + m.stateGasCommittedSpill ≤
      I + (allocateEvmGas cfg T I hIntrinsicTx hIntrinsicCap).executionGas)
    (hFloorTx : F ≤ T) (hFloorCap : F ≤ cfg.costs.txMaxGasLimit) :
    ∃ hs : (txStateGasUsed m
        (allocateEvmGas cfg T I hIntrinsicTx hIntrinsicCap).stateGasReservoir hBaseline).toNat ≤
        T - m.gasLeft - m.stateGasLeft,
      (settleTransactionGas T F m.gasLeft m.stateGasLeft r
        (txStateGasUsed m (allocateEvmGas cfg T I hIntrinsicTx hIntrinsicCap).stateGasReservoir
          hBaseline) hReturned hs hFloorTx).executionGasUsed ≤ cfg.costs.txMaxGasLimit := by
  have ha := allocateEvmGas_eq cfg T I hIntrinsicTx hIntrinsicCap
  have hm₁ := Nat.min_le_left (cfg.costs.txMaxGasLimit - I) (T - I)
  have hm₂ := Nat.min_le_right (cfg.costs.txMaxGasLimit - I) (T - I)
  have hEntry : T = I + (allocateEvmGas cfg T I hIntrinsicTx hIntrinsicCap).executionGas +
      (allocateEvmGas cfg T I hIntrinsicTx hIntrinsicCap).stateGasReservoir := by
    rw [ha]
    dsimp only
    omega
  have hCap : I + (allocateEvmGas cfg T I hIntrinsicTx hIntrinsicCap).executionGas ≤
      cfg.costs.txMaxGasLimit := by
    rw [ha]
    dsimp only
    omega
  have hs := meter_bound T I _ _ m hEntry hReturned hBaseline hPotential
  refine ⟨hs, ?_⟩
  rw [settleTransactionGas_eq, txStateGasUsed_eq]
  dsimp only
  rw [txStateGasUsed_eq] at hs
  omega

end STFSpec.Conformance.Vm.Core.TransactionGasSettlementCallerProofs
