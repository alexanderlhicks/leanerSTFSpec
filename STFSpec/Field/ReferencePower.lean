/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Field.Reference

/-!
# Natural-reference residue powers

Library `EthField`. Binary exponentiation reduces every square and product, for
all natural exponents and every admitted modulus, including even composites.
Spec guidance: `STFSpec/informal/modules/EthField.md` §§3–7.
-/

namespace STFSpec.Field.PrimeFieldRef

-- The positive-modulus helper chooses no public zero-modulus behavior.
private def residuePower (b e p : Nat) (hp : 0 < p) : Nat :=
  if h : e = 0 then
    1 % p
  else
    let half := residuePower b (e / 2) p hp
    let square := (half * half) % p
    if e % 2 = 0 then square else (square * (b % p)) % p
termination_by e
decreasing_by exact Nat.div_lt_self (Nat.zero_lt_of_ne_zero h) (by decide)

private theorem residuePower_eq_model (b e p : Nat) (hp : 0 < p) :
    residuePower b e p hp = b ^ e % p := by
  induction e using Nat.strongRecOn with
  | ind e ih =>
    rw [residuePower]
    split
    next he => simp [he]
    next he =>
      rw [ih (e / 2) (Nat.div_lt_self (Nat.zero_lt_of_ne_zero he) (by decide))]
      have hs : (b ^ (e / 2) % p * (b ^ (e / 2) % p)) % p =
          b ^ (e / 2 + e / 2) % p := by
        rw [← Nat.mul_mod, ← Nat.pow_add]
      dsimp only
      rw [hs]
      split
      next hbit =>
        have heq : e / 2 + e / 2 = e := by omega
        rw [heq]
      next hbit =>
        have heq : (e / 2 + e / 2).succ = e := by omega
        rw [← Nat.mul_mod, ← Nat.pow_succ, heq]

variable {p : Nat} [FieldModulus p]

/-- Natural residue power, as `FQ.__pow__` in pinned
`py_ecc/fields/optimized_field_elements.py:161–169`.
Halving the exponent and squaring the returned half-power gives the same binary
recurrence, with every intermediate square/product reduced. Metadata is unread. -/
def pow (a : PrimeFieldRef p) (e : Nat) : PrimeFieldRef p :=
  ofNat (residuePower a.toNat e p (by have := FieldModulus.one_lt (p := p); omega))

/-- Every natural exponent observes the full natural power followed by reduction. -/
theorem toNat_pow (a : PrimeFieldRef p) (e : Nat) :
    (pow a e).toNat = a.toNat ^ e % p := by
  rw [pow, toNat_ofNat, residuePower_eq_model, Nat.mod_mod]

/-- Natural exponent notation delegates directly to the named reference operation. -/
instance : HPow (PrimeFieldRef p) Nat (PrimeFieldRef p) where
  hPow := pow

end STFSpec.Field.PrimeFieldRef
