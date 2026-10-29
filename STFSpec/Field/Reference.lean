/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import Std.Tactic

/-!
# Canonical natural residue reference

Library `EthField`. This legible reference admits every modulus greater than one,
including composites; it supplies no field arithmetic or executable Montgomery backend.
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

end PrimeFieldRef
end STFSpec.Field
