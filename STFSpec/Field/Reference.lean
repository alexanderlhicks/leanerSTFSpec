/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import Std.Tactic

/-!
# Canonical natural residue reference

Library `EthField`. This legible reference admits every modulus greater than one,
including composites; its residue arithmetic is separate from the executable Montgomery backend.
Spec guidance: `STFSpec/informal/modules/EthField.md` §§3–7.
-/

namespace STFSpec.Field

/-- Modulus bound and optional, unconstrained square-root metadata.
The reference carrier does not read `sqrtExp?`. -/
class FieldModulus (p : Nat) where
  one_lt : 1 < p
  sqrtExp? : Option Nat

/-- Canonical natural residue reference. The constructor is private; projections
remain internal by convention, and clients use `toNat` and its public laws. -/
structure PrimeFieldRef (p : Nat) [FieldModulus p] where
  private mk ::
  val : Nat
  isLt : val < p

namespace PrimeFieldRef

variable {p : Nat} [FieldModulus p]

/-- Stable canonical natural observation; corresponds to `FQ.__int__` in pinned
`py_ecc/fields/optimized_field_elements.py:190–191`. -/
def toNat (a : PrimeFieldRef p) : Nat := a.val

/-- Reducing construction on every natural input, as `FQ.__init__` in pinned
`py_ecc/fields/optimized_field_elements.py:57–68`. -/
def ofNat (n : Nat) : PrimeFieldRef p :=
  ⟨n % p, Nat.mod_lt n (by have := FieldModulus.one_lt (p := p); omega)⟩

/-- Checked mathematical constructor: reject exactly `n ≥ p` without reduction.
This guided helper is not a method of the dependency's `FQ` class. -/
def ofNat? (n : Nat) : Option (PrimeFieldRef p) :=
  if h : n < p then some ⟨n, h⟩ else none

/-- Canonical zero, as `FQ.zero` in pinned
`py_ecc/fields/optimized_field_elements.py:221–223`. -/
def zero : PrimeFieldRef p := ofNat 0

/-- Canonical one, as `FQ.one` in pinned
`py_ecc/fields/optimized_field_elements.py:217–219`. -/
def one : PrimeFieldRef p := ofNat 1

/-- Every reference observation is canonical. -/
theorem toNat_lt (a : PrimeFieldRef p) : a.toNat < p := a.isLt

/-- Reducing construction observes ordinary natural remainder. -/
theorem toNat_ofNat (n : Nat) : (ofNat (p := p) n).toNat = n % p := rfl

/-- Canonical observation determines actual reference equality. -/
theorem ext {a b : PrimeFieldRef p} (h : a.toNat = b.toNat) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- Checked construction succeeds exactly at the original canonical value. -/
theorem ofNat?_eq_some_iff (n : Nat) (a : PrimeFieldRef p) :
    ofNat? (p := p) n = some a ↔ n < p ∧ a.toNat = n := by
  unfold ofNat?
  split
  next h =>
    constructor
    · intro ha
      cases ha
      exact ⟨h, rfl⟩
    · rintro ⟨_, ha⟩
      congr 1
      exact ext ha.symm
  next h =>
    constructor
    · intro ha
      cases ha
    · rintro ⟨hn, _⟩
      exact False.elim (h hn)

/-- Zero observes zero for every admitted modulus. -/
theorem toNat_zero : (zero : PrimeFieldRef p).toNat = 0 := by
  exact Nat.zero_mod p

/-- One observes one for every admitted modulus. -/
theorem toNat_one : (one : PrimeFieldRef p).toNat = 1 := by
  exact Nat.mod_eq_of_lt (FieldModulus.one_lt (p := p))

/-- Decide actual canonical equality through natural observations. -/
instance : DecidableEq (PrimeFieldRef p) := fun a b ↦
  if h : a.toNat = b.toNat then isTrue (ext h)
  else isFalse (fun hab ↦ h (congrArg toNat hab))

/-- The default reference value is canonical zero. -/
instance : Inhabited (PrimeFieldRef p) where
  default := zero

/-- Print the canonical natural observation, as `FQ.__repr__` in pinned
`py_ecc/fields/optimized_field_elements.py:187–188`. -/
instance : Repr (PrimeFieldRef p) where
  reprPrec a prec := reprPrec a.toNat prec

/-- Residue addition, as `FQ.__add__` in pinned
`py_ecc/fields/optimized_field_elements.py:70–80`. -/
def add (a b : PrimeFieldRef p) : PrimeFieldRef p := ofNat (a.toNat + b.toNat)

/-- Residue subtraction, as `FQ.__sub__` in pinned
`py_ecc/fields/optimized_field_elements.py:112–122`.
The canonical bound on `b` makes `a + p - b` ordinary nontruncating subtraction. -/
def sub (a b : PrimeFieldRef p) : PrimeFieldRef p := ofNat (a.toNat + p - b.toNat)

/-- Residue negation, as `FQ.__neg__` in pinned
`py_ecc/fields/optimized_field_elements.py:184–185`. -/
def neg (a : PrimeFieldRef p) : PrimeFieldRef p := ofNat (p - a.toNat)

/-- Residue multiplication, as `FQ.__mul__` in pinned
`py_ecc/fields/optimized_field_elements.py:82–92`. -/
def mul (a b : PrimeFieldRef p) : PrimeFieldRef p := ofNat (a.toNat * b.toNat)

/-- Recognize canonical zero, as comparison with integer zero through `FQ.__eq__`
in pinned `py_ecc/fields/optimized_field_elements.py:171–175`. -/
def isZero (a : PrimeFieldRef p) : Bool := decide (a.toNat = 0)

/-- Addition observes natural addition followed by reduction. -/
theorem toNat_add (a b : PrimeFieldRef p) :
    (add a b).toNat = (a.toNat + b.toNat) % p := rfl

/-- Subtraction observes the nonnegative representative of the signed difference. -/
theorem toNat_sub (a b : PrimeFieldRef p) :
    (sub a b).toNat = (a.toNat + p - b.toNat) % p := rfl

/-- Negation observes the reduced complement to the modulus. -/
theorem toNat_neg (a : PrimeFieldRef p) :
    (neg a).toNat = (p - a.toNat) % p := rfl

/-- Multiplication observes natural multiplication followed by reduction. -/
theorem toNat_mul (a b : PrimeFieldRef p) :
    (mul a b).toNat = (a.toNat * b.toNat) % p := rfl

/-- Zero recognition decides exactly equality of the canonical observation to zero. -/
theorem isZero_eq (a : PrimeFieldRef p) : isZero a = decide (a.toNat = 0) := rfl

/-- Addition notation delegates to the named reference operation. -/
instance : Add (PrimeFieldRef p) where
  add := add

/-- Subtraction notation delegates to the named reference operation. -/
instance : Sub (PrimeFieldRef p) where
  sub := sub

/-- Negation notation delegates to the named reference operation. -/
instance : Neg (PrimeFieldRef p) where
  neg := neg

/-- Multiplication notation delegates to the named reference operation. -/
instance : Mul (PrimeFieldRef p) where
  mul := mul

end PrimeFieldRef
end STFSpec.Field
