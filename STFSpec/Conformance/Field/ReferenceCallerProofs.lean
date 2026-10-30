/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Field

/-!
# Reference residue public-contract clients

Library `EthConformance`. All proofs use only the six public observer laws.
Spec guidance: `STFSpec/informal/modules/EthField.md` §§3–7.
-/

namespace STFSpec.Conformance.Field
open STFSpec.Field
open PrimeFieldRef

variable {p : Nat} [FieldModulus p]

private theorem checked_none (n : Nat) :
    ofNat? (p := p) n = none ↔ p ≤ n := by
  constructor
  · intro h
    by_cases hn' : n < p
    · have he := (ofNat?_eq_some_iff n (ofNat n)).mpr
        ⟨hn', by rw [toNat_ofNat, Nat.mod_eq_of_lt hn']⟩
      rw [h] at he
      cases he
    · omega
  · intro hn
    cases h : ofNat? (p := p) n with
    | none => rfl
    | some a =>
      have := (ofNat?_eq_some_iff n a).mp h
      omega

private theorem reducing_roundtrip (a : PrimeFieldRef p) : ofNat a.toNat = a := by
  apply ext
  rw [toNat_ofNat, Nat.mod_eq_of_lt (toNat_lt a)]

private theorem reduction_idempotent (n : Nat) :
    ofNat (p := p) ((ofNat (p := p) n).toNat) = ofNat n :=
  reducing_roundtrip _

private theorem checked_roundtrip (a : PrimeFieldRef p) : ofNat? a.toNat = some a :=
  (ofNat?_eq_some_iff _ _).mpr ⟨toNat_lt a, rfl⟩

private theorem checked_preserves (n : Nat) (a : PrimeFieldRef p)
    (h : ofNat? n = some a) : a.toNat = n ∧ ofNat n = a := by
  obtain ⟨hn, ha⟩ := (ofNat?_eq_some_iff _ _).mp h
  refine ⟨ha, ext ?_⟩
  rw [toNat_ofNat, Nat.mod_eq_of_lt hn, ha]

private theorem equality_iff (a b : PrimeFieldRef p) : a = b ↔ a.toNat = b.toNat :=
  ⟨fun h ↦ congrArg toNat h, ext⟩

private theorem zero_iff (a : PrimeFieldRef p) : a = zero ↔ a.toNat = 0 := by
  rw [equality_iff, toNat_zero]

private theorem one_iff (a : PrimeFieldRef p) : a = one ↔ a.toNat = 1 := by
  rw [equality_iff, toNat_one]

end STFSpec.Conformance.Field
