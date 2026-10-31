/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Field

/-!
# Reference arithmetic public-contract clients

Library `EthConformance`. Generic clients use only stable observer laws and the
four notation instances, for arbitrary admitted modulus and unread metadata.
Spec guidance: `STFSpec/informal/modules/EthField.md` §§3–7.
-/

namespace STFSpec.Conformance.Field
open STFSpec.Field
open PrimeFieldRef

variable {p : Nat} [FieldModulus p]

private theorem named_equations (a b : PrimeFieldRef p) :
    (add a b).toNat = (a.toNat + b.toNat) % p ∧
    (sub a b).toNat = (a.toNat + p - b.toNat) % p ∧
    (neg a).toNat = (p - a.toNat) % p ∧
    (mul a b).toNat = (a.toNat * b.toNat) % p ∧
    isZero a = decide (a.toNat = 0) :=
  ⟨toNat_add a b, toNat_sub a b, toNat_neg a, toNat_mul a b, isZero_eq a⟩

private theorem notation_equations (a b : PrimeFieldRef p) :
    (a + b).toNat = (a.toNat + b.toNat) % p ∧
    (a - b).toNat = (a.toNat + p - b.toNat) % p ∧
    (-a).toNat = (p - a.toNat) % p ∧
    (a * b).toNat = (a.toNat * b.toNat) % p :=
  ⟨toNat_add a b, toNat_sub a b, toNat_neg a, toNat_mul a b⟩

private theorem canonical_results (a b : PrimeFieldRef p) :
    (a + b).toNat < p ∧ (a - b).toNat < p ∧ (-a).toNat < p ∧
    (a * b).toNat < p :=
  ⟨toNat_lt _, toNat_lt _, toNat_lt _, toNat_lt _⟩

private theorem zero_recognition (a : PrimeFieldRef p) :
    (isZero a = true ↔ a = zero) ∧ (isZero a = false ↔ a ≠ zero) := by
  have he : a = zero ↔ a.toNat = 0 :=
    ⟨fun h ↦ by rw [h, toNat_zero], fun h ↦ ext (by rw [h, toNat_zero])⟩
  rw [isZero_eq]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact ⟨he.symm, not_congr he.symm⟩

private theorem sub_zero (a : PrimeFieldRef p) : a - zero = a := by
  apply ext
  change (sub a zero).toNat = a.toNat
  rw [toNat_sub, toNat_zero, Nat.sub_zero, Nat.add_mod_right,
    Nat.mod_eq_of_lt (toNat_lt a)]

private theorem sub_self (a : PrimeFieldRef p) : a - a = zero := by
  apply ext
  change (sub a a).toNat = zero.toNat
  rw [toNat_sub, Nat.add_sub_cancel_left, Nat.mod_self, toNat_zero]

private theorem neg_zero : -(zero : PrimeFieldRef p) = zero := by
  apply ext
  change (neg (zero : PrimeFieldRef p)).toNat = zero.toNat
  rw [toNat_neg, toNat_zero, Nat.sub_zero, Nat.mod_self]

private theorem sub_add_cancel (a b : PrimeFieldRef p) : (a - b) + b = a := by
  apply ext
  change (add (sub a b) b).toNat = a.toNat
  rw [toNat_add, toNat_sub, Nat.mod_add_mod,
    Nat.sub_add_cancel (show b.toNat ≤ a.toNat + p by have := toNat_lt b; omega),
    Nat.add_mod_right, Nat.mod_eq_of_lt (toNat_lt a)]

private theorem neg_add_cancel (a : PrimeFieldRef p) : (-a) + a = zero := by
  apply ext
  change (add (neg a) a).toNat = zero.toNat
  rw [toNat_add, toNat_neg, Nat.mod_add_mod,
    Nat.sub_add_cancel (Nat.le_of_lt (toNat_lt a)), Nat.mod_self, toNat_zero]

private theorem signed_sub_model (a b : PrimeFieldRef p) :
    ((a.toNat : Int) - (b.toNat : Int)) % (p : Int) = ((a - b).toNat : Int) := by
  change _ = ((sub a b).toNat : Int)
  rw [toNat_sub, Int.natCast_emod,
    Int.ofNat_sub (show b.toNat ≤ a.toNat + p by have := toNat_lt b; omega),
    Int.natCast_add]
  have h : (a.toNat : Int) + (p : Int) - (b.toNat : Int) =
      ((a.toNat : Int) - (b.toNat : Int)) + (p : Int) := by omega
  rw [h, Int.add_emod_right]

private theorem signed_neg_model (a : PrimeFieldRef p) :
    (-(a.toNat : Int)) % (p : Int) = ((-a).toNat : Int) := by
  change _ = ((neg a).toNat : Int)
  rw [toNat_neg, Int.natCast_emod, Int.ofNat_sub (Nat.le_of_lt (toNat_lt a))]
  have h : (p : Int) - (a.toNat : Int) = -(a.toNat : Int) + (p : Int) := by omega
  rw [h, Int.add_emod_right]

end STFSpec.Conformance.Field
