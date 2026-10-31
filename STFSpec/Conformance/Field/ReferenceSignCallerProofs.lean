/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Field

/-!
# Canonical sign public-contract clients

Library `EthConformance`. Private clients derive sign recognition, canonical
construction and arbitrary-metadata irrelevance using only public observer laws.
Spec guidance: `STFSpec/informal/modules/EthField.md` §§3–7.
-/

namespace STFSpec.Conformance.Field
open STFSpec.Field
open PrimeFieldRef

variable {p : Nat} [FieldModulus p]

private theorem sign_true_iff (a : PrimeFieldRef p) :
    sgn0 a = true ↔ a.toNat % 2 = 1 := by
  rw [sgn0_eq]
  simp

private theorem sign_false_iff (a : PrimeFieldRef p) :
    sgn0 a = false ↔ a.toNat % 2 = 0 := by
  rw [sgn0_eq]
  simp only [decide_eq_false_iff_not]
  omega

private theorem sign_zero : sgn0 (zero : PrimeFieldRef p) = false := by
  rw [sgn0_eq, toNat_zero]
  rfl

private theorem sign_one : sgn0 (one : PrimeFieldRef p) = true := by
  rw [sgn0_eq, toNat_one]
  rfl

private theorem sign_ofNat (raw : Nat) :
    sgn0 (ofNat raw : PrimeFieldRef p) = decide ((raw % p) % 2 = 1) := by
  rw [sgn0_eq, toNat_ofNat]

private theorem arbitrary_metadata (p : Nat) (hp : 1 < p) (metadata : Option Nat)
    (raw : Nat) :
    letI : FieldModulus p := ⟨hp, metadata⟩
    sgn0 (ofNat raw : PrimeFieldRef p) = decide ((raw % p) % 2 = 1) := by
  letI : FieldModulus p := ⟨hp, metadata⟩
  rw [sgn0_eq, toNat_ofNat]

-- Compare observations, never elements whose instance parameters differ.
private theorem metadata_irrelevance (p : Nat) (hp : 1 < p) (left right : Option Nat)
    (a : @PrimeFieldRef p ⟨hp, left⟩) (b : @PrimeFieldRef p ⟨hp, right⟩)
    (h : @toNat p ⟨hp, left⟩ a = @toNat p ⟨hp, right⟩ b) :
    @sgn0 p ⟨hp, left⟩ a = @sgn0 p ⟨hp, right⟩ b := by
  rw [@sgn0_eq p ⟨hp, left⟩ a, @sgn0_eq p ⟨hp, right⟩ b, h]

end STFSpec.Conformance.Field
