/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Public-law clients of call and init-code pricing

Library `EthConformance`. All clients are private and use public equations rather
than unfolding providers. Raw configs/meters carry no global invariant. Local
financing hypotheses do not implement CALL or establish whole G2.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7.
-/

namespace STFSpec.Conformance.Vm.Core.CallGasCallerProofs
open STFSpec.Vm.Core STFSpec.Base

private theorem record_ext_client (a b : MessageCallGas)
    (hc : a.cost = b.cost) (hs : a.subCall = b.subCall) : a = b :=
  MessageCallGas.ext a b hc hs

private theorem constructor_eta_client (cost subCall : Nat) :
    let r := MessageCallGas.mk cost subCall
    (r.cost, r.subCall) = (cost, subCall) ∧
      MessageCallGas.mk r.cost r.subCall = r := by
  exact ⟨rfl, MessageCallGas.eta _⟩

private theorem call_result_and_charge_transport
    (cfg₁ cfg₂ : VmConfig) (v : U256) (g L mem extra s₁ s₂ : Nat)
    (meter : GasMeter)
    (h_price : (if v = U256.zero then cfg₁.costs.zero else s₁) =
               (if v = U256.zero then cfg₂.costs.zero else s₂)) :
    let r₁ := calculateMessageCallGas cfg₁ v g L mem extra s₁
    let r₂ := calculateMessageCallGas cfg₂ v g L mem extra s₂
    r₁ = r₂ ∧
      chargeGas meter (r₁.cost + mem) = chargeGas meter (r₂.cost + mem) := by
  have h := calculateMessageCallGas_congr cfg₁ cfg₂ v g L mem extra s₁ s₂ h_price
  exact ⟨h, congrArg (fun r => chargeGas meter (r.cost + mem)) h⟩

private theorem call_default_congr (cfg₁ cfg₂ : VmConfig)
    (v : U256) (g L mem extra : Nat)
    (h_price : (if v = U256.zero then cfg₁.costs.zero else cfg₁.costs.callStipend) =
               (if v = U256.zero then cfg₂.costs.zero else cfg₂.costs.callStipend)) :
    calculateMessageCallGas cfg₁ v g L mem extra =
    calculateMessageCallGas cfg₂ v g L mem extra :=
  calculateMessageCallGas_congr _ _ _ _ _ _ _ _ _ h_price

private theorem zero_value_override_congr (cfg₁ cfg₂ : VmConfig)
    (g L mem extra s₁ s₂ : Nat) (h : cfg₁.costs.zero = cfg₂.costs.zero) :
    calculateMessageCallGas cfg₁ U256.zero g L mem extra s₁ =
    calculateMessageCallGas cfg₂ U256.zero g L mem extra s₂ := by
  apply calculateMessageCallGas_congr
  simpa only [↓reduceIte] using h

private theorem nonzero_explicit_congr (cfg₁ cfg₂ : VmConfig) (v : U256)
    (hv : v ≠ U256.zero) (g L mem extra s : Nat) :
    calculateMessageCallGas cfg₁ v g L mem extra s =
    calculateMessageCallGas cfg₂ v g L mem extra s := by
  apply calculateMessageCallGas_congr
  simp only [ite_eq_right hv]

private theorem unused_state_limits_congr (costs : GasCosts)
    (state₁ state₂ : StateGasCosts) (limits₁ limits₂ : VmLimits)
    (v : U256) (g L mem extra : Nat) :
    calculateMessageCallGas (VmConfig.mk costs state₁ limits₁) v g L mem extra =
    calculateMessageCallGas (VmConfig.mk costs state₂ limits₂) v g L mem extra :=
  call_default_congr _ _ _ _ _ _ _ rfl

private theorem cost_ignores_selection (cfg₁ cfg₂ : VmConfig) (v₁ v₂ : U256)
    (g L mem extra s₁ s₂ : Nat) :
    (calculateMessageCallGas cfg₁ v₁ g L mem extra s₁).cost =
    (calculateMessageCallGas cfg₂ v₂ g L mem extra s₂).cost := by
  rw [calculateMessageCallGas_eq, calculateMessageCallGas_eq]
  split <;> rfl

private theorem call_pair_share (cfg : VmConfig) (v : U256)
    (g L mem extra stipend : Nat) :
    let r := calculateMessageCallGas cfg v g L mem extra stipend
    let t := if v = U256.zero then cfg.costs.zero else stipend
    extra ≤ r.cost ∧ r.subCall = (r.cost - extra) + t := by
  dsimp only
  rw [calculateMessageCallGas_eq]
  split <;> dsimp only <;> omega

private theorem call_local_bounds (cfg : VmConfig) (v : U256)
    (g L mem extra stipend : Nat) (h_afford : mem + extra ≤ L) :
    let r := calculateMessageCallGas cfg v g L mem extra stipend
    let t := if v = U256.zero then cfg.costs.zero else stipend
    r.cost ≤ L - mem ∧
    r.subCall = (r.cost - extra) + t ∧
    r.cost - extra ≤ g ∧
    r.cost - extra ≤ maxMessageCallGas ((L - mem) - extra) ∧
    ((L - mem) - extra) / 64 ≤ L - (r.cost + mem) := by
  dsimp only
  rw [calculateMessageCallGas_eq]
  simp only [ite_eq_right (by omega : ¬ L < extra + mem)]
  have hg := Nat.min_le_left g (maxMessageCallGas ((L - mem) - extra))
  have hm := Nat.min_le_right g (maxMessageCallGas ((L - mem) - extra))
  have hb := maxMessageCallGas_le ((L - mem) - extra)
  have he := maxMessageCallGas_eq ((L - mem) - extra)
  have hd := Nat.div_le_self ((L - mem) - extra) 64
  omega

private theorem call_charge_eq (cfg : VmConfig) (v : U256)
    (g mem extra stipend : Nat) (meter : GasMeter) :
    let r := calculateMessageCallGas cfg v g meter.gasLeft mem extra stipend
    chargeGas meter (r.cost + mem) =
      if meter.gasLeft < extra + mem then .error .outOfGas
      else .ok { meter with gasLeft := meter.gasLeft - (r.cost + mem) } := by
  dsimp only
  by_cases h : meter.gasLeft < extra + mem
  · rw [calculateMessageCallGas_eq]
    simp only [ite_eq_left h]
    exact (chargeGas_eq_error_iff _ _ _).mpr ⟨by omega, rfl⟩
  · have hb := call_local_bounds cfg v g meter.gasLeft mem extra stipend (by omega)
    dsimp only at hb
    have ha : (calculateMessageCallGas cfg v g meter.gasLeft mem extra stipend).cost
        + mem ≤ meter.gasLeft := by omega
    rw [chargeGas_of_le _ _ ha]
    simp only [ite_eq_right h]

private theorem call_charge_ok_iff (cfg : VmConfig) (v : U256)
    (g mem extra stipend : Nat) (meter : GasMeter) :
    let r := calculateMessageCallGas cfg v g meter.gasLeft mem extra stipend
    (∃ post, chargeGas meter (r.cost + mem) = .ok post) ↔
      mem + extra ≤ meter.gasLeft := by
  dsimp only
  rw [call_charge_eq]
  split <;> simp_all <;> omega

private theorem call_charge_error_iff (cfg : VmConfig) (v : U256)
    (g mem extra stipend : Nat) (meter : GasMeter) (e : ExceptionalHalt) :
    let r := calculateMessageCallGas cfg v g meter.gasLeft mem extra stipend
    chargeGas meter (r.cost + mem) = .error e ↔
      meter.gasLeft < mem + extra ∧ e = .outOfGas := by
  dsimp only
  rw [call_charge_eq]
  split <;> simp_all [eq_comm] <;> omega

private theorem call_paid_potential_bound (cfg : VmConfig) (v : U256)
    (g mem extra stipend : Nat) (meter post : GasMeter) :
    let r := calculateMessageCallGas cfg v g meter.gasLeft mem extra stipend
    let t := if v = U256.zero then cfg.costs.zero else stipend
    chargeGas meter (r.cost + mem) = .ok post →
    t + 1 ≤ mem + extra →
    post.phi + r.subCall + 1 ≤ meter.phi := by
  dsimp only
  intro hc hp
  have hphi := chargeGas_phi _ _ _ hc
  have hs := call_pair_share cfg v g meter.gasLeft mem extra stipend
  dsimp only at hs
  omega

private theorem call_paid_potential_nonincrease (cfg : VmConfig) (v : U256)
    (g mem extra stipend : Nat) (meter post : GasMeter) :
    let r := calculateMessageCallGas cfg v g meter.gasLeft mem extra stipend
    let t := if v = U256.zero then cfg.costs.zero else stipend
    chargeGas meter (r.cost + mem) = .ok post →
    t ≤ mem + extra →
    post.phi + r.subCall ≤ meter.phi := by
  dsimp only
  intro hc hp
  have hphi := chargeGas_phi _ _ _ hc
  have hs := call_pair_share cfg v g meter.gasLeft mem extra stipend
  dsimp only at hs
  omega

private theorem init_word_form (cfg : VmConfig) (n : Nat) :
    initCodeCost cfg n = cfg.costs.codeInitPerWord * (ceil32 n / 32) := by
  rw [initCodeCost_eq]
  have hz := ceil32_mod_eq_zero n
  have hd := Nat.div_add_mod (ceil32 n) 32
  have he : ceil32 n = ceil32 n / 32 * 32 := by omega
  calc
    cfg.costs.codeInitPerWord * ceil32 n / 32 =
        (cfg.costs.codeInitPerWord * (ceil32 n / 32)) * 32 / 32 := by
      rw [Nat.mul_assoc, ← he]
    _ = cfg.costs.codeInitPerWord * (ceil32 n / 32) :=
      Nat.mul_div_cancel _ (by decide : 0 < 32)

private theorem init_zero_length (cfg : VmConfig) : initCodeCost cfg 0 = 0 := by
  rw [init_word_form, ceil32_zero]
  simp only [Nat.zero_div, Nat.mul_zero]

private theorem init_zero_price (cfg : VmConfig) (h : cfg.costs.codeInitPerWord = 0)
    (n : Nat) : initCodeCost cfg n = 0 := by
  rw [init_word_form, h, Nat.zero_mul]

private theorem init_aligned (cfg : VmConfig) (n : Nat) (h : n % 32 = 0) :
    initCodeCost cfg n = cfg.costs.codeInitPerWord * (n / 32) := by
  rw [init_word_form, ceil32_eq_self_of_mod_eq_zero n h]

private theorem init_charge_transport (cfg₁ cfg₂ : VmConfig)
    (h_price : cfg₁.costs.codeInitPerWord = cfg₂.costs.codeInitPerWord)
    (n otherCharge : Nat) (meter : GasMeter) :
    chargeGas meter (otherCharge + initCodeCost cfg₁ n) =
    chargeGas meter (otherCharge + initCodeCost cfg₂ n) := by
  rw [initCodeCost_congr cfg₁ cfg₂ h_price n]

private theorem init_charge_eq (cfg : VmConfig) (n otherCharge : Nat)
    (meter : GasMeter) :
    let a := otherCharge + initCodeCost cfg n
    chargeGas meter a =
      if meter.gasLeft < a then .error .outOfGas
      else .ok { meter with gasLeft := meter.gasLeft - a } := by
  dsimp only
  split
  · exact (chargeGas_eq_error_iff _ _ _).mpr ⟨by assumption, rfl⟩
  · apply chargeGas_of_le
    omega

end STFSpec.Conformance.Vm.Core.CallGasCallerProofs
