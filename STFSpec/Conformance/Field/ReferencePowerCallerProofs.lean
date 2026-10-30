/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Field

/-!
# Natural-reference power public-contract clients

Library `EthConformance`. Private clients use the facade's public observer laws
and direct operator delegation for arbitrary modulus instances and unread metadata.
Spec guidance: `STFSpec/informal/modules/EthField.md` §§3–7.
-/

namespace STFSpec.Conformance.Field
open STFSpec.Field
open PrimeFieldRef

variable {p : Nat} [FieldModulus p]

private theorem named_and_notation (a : PrimeFieldRef p) (e : Nat) :
    (pow a e).toNat = a.toNat ^ e % p ∧
    (a ^ e).toNat = a.toNat ^ e % p :=
  ⟨toNat_pow a e, toNat_pow a e⟩

private theorem canonical_power (a : PrimeFieldRef p) (e : Nat) :
    (pow a e).toNat < p ∧ (a ^ e).toNat < p :=
  ⟨toNat_lt _, toNat_lt _⟩

private theorem exponent_zero (a : PrimeFieldRef p) : a ^ (0 : Nat) = one := by
  apply ext
  change (pow a 0).toNat = one.toNat
  rw [toNat_pow, Nat.pow_zero, Nat.mod_eq_of_lt (FieldModulus.one_lt (p := p)),
    toNat_one]

private theorem exponent_one (a : PrimeFieldRef p) : a ^ (1 : Nat) = a := by
  apply ext
  change (pow a 1).toNat = a.toNat
  rw [toNat_pow, Nat.pow_one, Nat.mod_eq_of_lt (toNat_lt a)]

private theorem zero_positive (e : Nat) (he : 0 < e) :
    (zero : PrimeFieldRef p) ^ e = zero := by
  apply ext
  change (pow (zero : PrimeFieldRef p) e).toNat = zero.toNat
  rw [toNat_pow, toNat_zero, Nat.zero_pow he, Nat.zero_mod]

private theorem one_power (e : Nat) : (one : PrimeFieldRef p) ^ e = one := by
  apply ext
  change (pow (one : PrimeFieldRef p) e).toNat = one.toNat
  rw [toNat_pow, toNat_one, Nat.one_pow,
    Nat.mod_eq_of_lt (FieldModulus.one_lt (p := p))]

private theorem exponent_add (a : PrimeFieldRef p) (e f : Nat) :
    a ^ (e + f) = (a ^ e) * (a ^ f) := by
  apply ext
  change (pow a (e + f)).toNat = (mul (pow a e) (pow a f)).toNat
  rw [toNat_pow, toNat_mul, toNat_pow, toNat_pow, ← Nat.mul_mod, Nat.pow_add]

private theorem square (a : PrimeFieldRef p) : a ^ (2 : Nat) = a * a := by
  apply ext
  change (pow a 2).toNat = (mul a a).toNat
  rw [toNat_pow, toNat_mul, Nat.pow_two]

private theorem product_power (a b : PrimeFieldRef p) (e : Nat) :
    (a * b) ^ e = (a ^ e) * (b ^ e) := by
  apply ext
  change (pow (mul a b) e).toNat = (mul (pow a e) (pow b e)).toNat
  rw [toNat_pow, toNat_mul, toNat_mul, toNat_pow, toNat_pow,
    ← Nat.pow_mod, ← Nat.mul_mod, Nat.mul_pow]

private theorem power_power (a : PrimeFieldRef p) (e f : Nat) :
    (a ^ e) ^ f = a ^ (e * f) := by
  apply ext
  change (pow (pow a e) f).toNat = (pow a (e * f)).toNat
  rw [toNat_pow, toNat_pow, toNat_pow, ← Nat.pow_mod, Nat.pow_mul]

-- The class instance is universally quantified: no metadata value is inspected.
private theorem arbitrary_metadata (p : Nat) (hp : 1 < p) (metadata : Option Nat)
    (raw e : Nat) :
    letI : FieldModulus p := ⟨hp, metadata⟩
    (pow (ofNat raw : PrimeFieldRef p) e).toNat = (raw % p) ^ e % p := by
  letI : FieldModulus p := ⟨hp, metadata⟩
  rw [toNat_pow, toNat_ofNat]

end STFSpec.Conformance.Field
