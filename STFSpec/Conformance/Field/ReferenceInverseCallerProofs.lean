/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Field

/-!
# Natural-reference inverse public-contract clients

Library `EthConformance`. Private clients consume only the public graph and observer laws.
Spec guidance: `STFSpec/informal/modules/EthField.md` §§3–7.
-/

namespace STFSpec.Conformance.Field
open STFSpec.Field
open PrimeFieldRef

variable {p : Nat} [FieldModulus p]

private theorem complete_result (a : PrimeFieldRef p) (y : Nat) (hy : Inv0Model a y) :
    (inv0 a).toNat = y := (toNat_inv0_iff a y).mp hy

private theorem inverse_range (a : PrimeFieldRef p) : (inv0 a).toNat < p := by
  apply inv0Model_lt a
  exact (toNat_inv0_iff a _).mpr rfl

private theorem unique_result (a : PrimeFieldRef p) (x y : Nat)
    (hx : Inv0Model a x) (hy : Inv0Model a y) : x = y := by
  have ex := (toNat_inv0_iff a x).mp hx
  have ey := (toNat_inv0_iff a y).mp hy
  omega

private theorem zero_result : (inv0 (zero : PrimeFieldRef p)).toNat = 0 := by
  rw [inv0_zero, toNat_zero]

private theorem unit_result (a : PrimeFieldRef p) (hg : Nat.gcd a.toNat p = 1) :
    (a.toNat * (inv0 a).toNat) % p = 1 := by
  have h := congrArg toNat (mul_inv0_of_gcd_one a hg)
  rw [toNat_mul, toNat_one] at h
  exact h

private theorem canonical_input_reduction (raw : Nat) :
    inv0 (ofNat raw : PrimeFieldRef p) = inv0 (ofNat (raw % p)) := by
  congr 1
  apply ext
  rw [toNat_ofNat, toNat_ofNat, Nat.mod_mod]

-- These are observer equalities between possibly different instance carriers.
private theorem metadata_irrelevance (p : Nat) (hp : 1 < p) (left right : Option Nat)
    (a : @PrimeFieldRef p ⟨hp, left⟩) (b : @PrimeFieldRef p ⟨hp, right⟩)
    (h : @toNat p ⟨hp, left⟩ a = @toNat p ⟨hp, right⟩ b) :
    @toNat p ⟨hp, left⟩ (@inv0 p ⟨hp, left⟩ a) =
      @toNat p ⟨hp, right⟩ (@inv0 p ⟨hp, right⟩ b) := by
  have ha := (@toNat_inv0_iff p ⟨hp, left⟩ a _).mpr rfl
  have hb : @Inv0Model p ⟨hp, right⟩ b
      (@toNat p ⟨hp, left⟩ (@inv0 p ⟨hp, left⟩ a)) := by
    simpa only [Inv0Model, h] using ha
  exact ((@toNat_inv0_iff p ⟨hp, right⟩ b _).mp hb).symm

private theorem graph_result (raw y : Nat) (hzero : raw % p ≠ 0) (z : Int)
    (hz : EuclideanCoefficient (raw % p) p 1 0 z)
    (hy : y = (z % (p : Int)).toNat) :
    (inv0 (ofNat raw : PrimeFieldRef p)).toNat = y := by
  apply (toNat_inv0_iff _ _).mp
  simpa [Inv0Model, toNat_ofNat, hzero] using
    (show ∃ w : Int, EuclideanCoefficient (raw % p) p 1 0 w ∧
      y = (w % (p : Int)).toNat from ⟨z, hz, hy⟩)

private theorem composite_nonunit_four :
    letI : FieldModulus 4 := ⟨by decide, none⟩
    (inv0 (ofNat 2 : PrimeFieldRef 4)).toNat = 2 := by
  letI : FieldModulus 4 := ⟨by decide, none⟩
  apply graph_result 2 2 (by decide) (-2)
  · apply EuclideanCoefficient.step 2 4 1 0 (-2) (by decide)
    simpa using (EuclideanCoefficient.done 0 2 (-2) 1 (by decide))
  · decide

private theorem composite_nonunit_six :
    letI : FieldModulus 6 := ⟨by decide, some 0⟩
    (inv0 (ofNat 2 : PrimeFieldRef 6)).toNat = 3 := by
  letI : FieldModulus 6 := ⟨by decide, some 0⟩
  apply graph_result 2 3 (by decide) (-3)
  · apply EuclideanCoefficient.step 2 6 1 0 (-3) (by decide)
    simpa using (EuclideanCoefficient.done 0 2 (-3) 1 (by decide))
  · decide

private theorem composite_nonunit_nine :
    letI : FieldModulus 9 := ⟨by decide, none⟩
    (inv0 (ofNat 3 : PrimeFieldRef 9)).toNat = 6 := by
  letI : FieldModulus 9 := ⟨by decide, none⟩
  apply graph_result 3 6 (by decide) (-3)
  · apply EuclideanCoefficient.step 3 9 1 0 (-3) (by decide)
    simpa using (EuclideanCoefficient.done 0 3 (-3) 1 (by decide))
  · decide

private theorem composite_unit_fifteen :
    letI : FieldModulus 15 := ⟨by decide, none⟩
    (inv0 (ofNat 2 : PrimeFieldRef 15)).toNat = 8 := by
  letI : FieldModulus 15 := ⟨by decide, none⟩
  apply graph_result 2 8 (by decide) (-7)
  · apply EuclideanCoefficient.step 2 15 1 0 (-7) (by decide)
    simpa using (EuclideanCoefficient.done 1 2 (-7) 1 (by decide))
  · decide

private theorem negative_normalization_trap :
    letI : FieldModulus 3 := ⟨by decide, some (2 ^ 4096 + 17)⟩
    (inv0 (ofNat 2 : PrimeFieldRef 3)).toNat = 2 := by
  letI : FieldModulus 3 := ⟨by decide, some (2 ^ 4096 + 17)⟩
  apply graph_result 2 2 (by decide) (-1)
  · apply EuclideanCoefficient.step 2 3 1 0 (-1) (by decide)
    simpa using (EuclideanCoefficient.done 1 2 (-1) 1 (by decide))
  · decide

end STFSpec.Conformance.Field
