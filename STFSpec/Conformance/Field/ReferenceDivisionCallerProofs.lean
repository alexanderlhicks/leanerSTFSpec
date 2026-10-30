/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Field

/-!
# Natural-reference division public-contract clients

Library `EthConformance`. Private generic clients use public provider laws and graph
constructors, for every p>1 and arbitrary square-root metadata.
Spec guidance: `STFSpec/informal/modules/EthField.md` §§3–7.
-/

namespace STFSpec.Conformance.Field
open STFSpec.Field
open PrimeFieldRef

variable {p : Nat} [FieldModulus p]

private theorem defining_equation (a b : PrimeFieldRef p) :
    div a b = mul a (inv0 b) := rfl

private theorem notation_delegation (a b : PrimeFieldRef p) : a / b = div a b := rfl

private theorem observer_signature (a b : PrimeFieldRef p) :
    (div a b).toNat = (a.toNat * (inv0 b).toNat) % p := toNat_div a b

private theorem notation_observer (a b : PrimeFieldRef p) :
    (a / b).toNat = (a.toNat * (inv0 b).toNat) % p := toNat_div a b

private theorem result_range (a b : PrimeFieldRef p) : (a / b).toNat < p := toNat_lt _

private theorem graph_composition (a b : PrimeFieldRef p) (y : Nat)
    (hy : Inv0Model b y) : (a / b).toNat = (a.toNat * y) % p := by
  rw [notation_observer, (toNat_inv0_iff b y).mp hy]

private theorem graph_determines_value (a b c : PrimeFieldRef p) (y : Nat)
    (hy : Inv0Model b y) (hc : c.toNat = (a.toNat * y) % p) : a / b = c := by
  apply ext
  rw [graph_composition a b y hy, hc]

private theorem denominator_zero (a : PrimeFieldRef p) : a / zero = zero := by
  apply ext
  rw [notation_observer, inv0_zero, toNat_zero, Nat.mul_zero, Nat.zero_mod]

private theorem numerator_zero (b : PrimeFieldRef p) : zero / b = zero := by
  apply ext
  rw [notation_observer, toNat_zero, Nat.zero_mul, Nat.zero_mod]

private theorem self_division_of_unit (a : PrimeFieldRef p) (hg : Nat.gcd a.toNat p = 1) :
    a / a = one := by
  rw [notation_delegation, defining_equation, mul_inv0_of_gcd_one a hg]

private theorem canonical_input_reduction (rawA rawB : Nat) :
    (ofNat rawA : PrimeFieldRef p) / ofNat rawB = ofNat (rawA % p) / ofNat (rawB % p) := by
  have ha : (ofNat rawA : PrimeFieldRef p) = ofNat (rawA % p) := by
    apply ext
    rw [toNat_ofNat, toNat_ofNat, Nat.mod_mod]
  have hb : (ofNat rawB : PrimeFieldRef p) = ofNat (rawB % p) := by
    apply ext
    rw [toNat_ofNat, toNat_ofNat, Nat.mod_mod]
  rw [ha, hb]

private theorem metadata_irrelevance (p : Nat) (hp : 1 < p) (left right : Option Nat)
    (a b : @PrimeFieldRef p ⟨hp, left⟩) (c d : @PrimeFieldRef p ⟨hp, right⟩)
    (ha : @toNat p ⟨hp, left⟩ a = @toNat p ⟨hp, right⟩ c)
    (hb : @toNat p ⟨hp, left⟩ b = @toNat p ⟨hp, right⟩ d) :
    @toNat p ⟨hp, left⟩ (@div p ⟨hp, left⟩ a b) =
      @toNat p ⟨hp, right⟩ (@div p ⟨hp, right⟩ c d) := by
  have hm := (@toNat_inv0_iff p ⟨hp, left⟩ b _).mpr rfl
  have hn : @Inv0Model p ⟨hp, right⟩ d
      (@toNat p ⟨hp, left⟩ (@inv0 p ⟨hp, left⟩ b)) := by
    simpa only [Inv0Model, hb] using hm
  rw [@toNat_div p ⟨hp, left⟩, @toNat_div p ⟨hp, right⟩,
    (@toNat_inv0_iff p ⟨hp, right⟩ d _).mp hn, ha]

end STFSpec.Conformance.Field
