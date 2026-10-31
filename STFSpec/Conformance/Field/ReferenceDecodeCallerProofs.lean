/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Field

/-!
# Checked byte decoding public-contract clients

Library `EthConformance`. Private clients use the Field facade and public byte laws
for complete rejection, positional equality, zero and metadata observations.
Spec guidance: `STFSpec/informal/modules/EthField.md` §§3–7.
-/

namespace STFSpec.Conformance.Field
open STFSpec.Field
open PrimeFieldRef
open STFSpec.Base

variable {p : Nat} [FieldModulus p]

private theorem decode_none_iff (b : ByteArray) :
    ofBytesBE? (p := p) b = none ↔ p ≤ Uint.ofBeBytes (Bytes.ofByteArray b) := by
  constructor
  · intro hn
    by_cases hl : Uint.ofBeBytes (Bytes.ofByteArray b) < p
    · have hs := (ofBytesBE?_eq_some_iff b
        (ofNat (Uint.ofBeBytes (Bytes.ofByteArray b)) : PrimeFieldRef p)).mpr
        ⟨hl, by rw [toNat_ofNat, Nat.mod_eq_of_lt hl]⟩
      rw [hn] at hs
      cases hs
    · omega
  · intro hn
    cases he : ofBytesBE? (p := p) b with
    | none => rfl
    | some a =>
      have h := (ofBytesBE?_eq_some_iff b a).mp he
      omega

private theorem decode_some_range (b : ByteArray) (a : PrimeFieldRef p)
    (h : ofBytesBE? b = some a) :
    a.toNat = Uint.ofBeBytes (Bytes.ofByteArray b) ∧ a.toNat < p := by
  obtain ⟨hr, he⟩ := (ofBytesBE?_eq_some_iff b a).mp h
  exact ⟨he, he ▸ hr⟩

private theorem decode_ext (a b : ByteArray)
    (h : Uint.ofBeBytes (Bytes.ofByteArray a) = Uint.ofBeBytes (Bytes.ofByteArray b)) :
    ofBytesBE? (p := p) a = ofBytesBE? b := by
  cases ha : ofBytesBE? (p := p) a with
  | none =>
    apply Eq.symm
    apply (decode_none_iff b).mpr
    rw [← h]
    exact (decode_none_iff a).mp ha
  | some x =>
    apply Eq.symm
    apply (ofBytesBE?_eq_some_iff b x).mpr
    rw [← h]
    exact (ofBytesBE?_eq_some_iff a x).mp ha

private theorem decode_zero (b : ByteArray)
    (h : Uint.ofBeBytes (Bytes.ofByteArray b) = 0) :
    ofBytesBE? (p := p) b = some zero := by
  apply (ofBytesBE?_eq_some_iff b zero).mpr
  rw [h, toNat_zero]
  have := FieldModulus.one_lt (p := p)
  exact ⟨by omega, rfl⟩

private theorem decode_empty : ofBytesBE? (p := p) ByteArray.empty = some zero := by
  apply decode_zero
  rw [Uint.ofBeBytes_eq_fold, Bytes.toList_ofByteArray]
  rfl

private theorem decode_all_zero (b : ByteArray) (h : ∀ x ∈ b.data.toList, x = 0) :
    ofBytesBE? (p := p) b = some zero := by
  apply decode_zero
  rw [Uint.ofBeBytes_eq_fold, Bytes.toList_ofByteArray]
  generalize b.data.toList = xs at h ⊢
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    simp only [List.foldl_cons, hx]
    exact ih (fun y hy ↦ h y (by simp [hy]))

private theorem decode_leading_zero (a b : ByteArray)
    (h : a.data.toList = 0 :: b.data.toList) :
    ofBytesBE? (p := p) a = ofBytesBE? b := by
  apply decode_ext
  rw [Uint.ofBeBytes_eq_fold, Uint.ofBeBytes_eq_fold,
    Bytes.toList_ofByteArray, Bytes.toList_ofByteArray, h]
  rfl

private theorem decode_observation (b : ByteArray) :
    (ofBytesBE? (p := p) b).map toNat =
      if Uint.ofBeBytes (Bytes.ofByteArray b) < p then
        some (Uint.ofBeBytes (Bytes.ofByteArray b)) else none := by
  cases he : ofBytesBE? (p := p) b with
  | none =>
    have hn := (decode_none_iff b).mp he
    simp only [Option.map_none,
      ite_eq_right (show ¬ Uint.ofBeBytes (Bytes.ofByteArray b) < p from by omega)]
  | some a =>
    obtain ⟨hr, hv⟩ := (ofBytesBE?_eq_some_iff b a).mp he
    simp only [Option.map_some, hv, ite_eq_left hr]

-- Only Option Nat observations are compared across different instance carriers.
private theorem decode_metadata_irrelevance (p : Nat) (hp : 1 < p)
    (left right : Option Nat) (b : ByteArray) :
    (@ofBytesBE? p ⟨hp, left⟩ b).map (@toNat p ⟨hp, left⟩) =
      (@ofBytesBE? p ⟨hp, right⟩ b).map (@toNat p ⟨hp, right⟩) := by
  rw [@decode_observation p ⟨hp, left⟩ b, @decode_observation p ⟨hp, right⟩ b]

end STFSpec.Conformance.Field
