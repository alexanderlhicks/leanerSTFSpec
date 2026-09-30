/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.U256Arithmetic

/-!
# Modular U256 exponentiation

Library `EthBase`: unsigned EVM EXP values, in first-popped operand order.
The executable square-and-multiply definition equals a legible modular reference.
Stack, gas and PC effects belong to `EthVmInstructions`.
Citations refer to the pin in `reference.toml`.
Spec guidance: `STFSpec/informal/modules/EthBase.md`.
-/

namespace STFSpec.Base.U256

/-- Proof reference with one multiplication/reduction per exponent unit (linear cost).
Zero exponent is one. Use `exp` for executable callers. -/
def expReferenceNat (a : U256) : Nat → U256
  | 0 => one
  | n + 1 => mul (expReferenceNat a n) a

/-- Square-and-multiply with an explicit decreasing exponent and reduced word products. -/
private def expNat (a : U256) (n : Nat) : U256 :=
  if n = 0 then one else
    let half := expNat a (n / 2)
    let square := mul half half
    if n % 2 = 0 then square else mul square a
termination_by n
decreasing_by omega

/-- EVM EXP value, base first and unsigned exponent second;
EELS `src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py:297,326`;
`ethereum_types/numeric.py:223` supplies modular power. In particular, `0^0 = 1`. -/
def exp (a b : U256) : U256 := expNat a b.toNat

/-- Proof reference for EXP, linear in the full unsigned exponent (up to `2^256 - 1`
steps). Use the logarithmic `exp` operation for execution. -/
def expReference (a b : U256) : U256 := expReferenceNat a b.toNat

private theorem toNat_expReferenceNat (a : U256) (n : Nat) :
    (expReferenceNat a n).toNat = a.toNat ^ n % 2 ^ 256 := by
  induction n with
  | zero => simp [expReferenceNat, toNat_one]
  | succ n ih =>
    rw [expReferenceNat, toNat_mul, ih, Nat.mod_mul_mod, ← Nat.pow_succ]

private theorem toNat_expNat (a : U256) (n : Nat) :
    (expNat a n).toNat = a.toNat ^ n % 2 ^ 256 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [expNat]
    split
    next h => simp [h, toNat_one]
    next h =>
      have hh := ih (n / 2) (Nat.div_lt_self (by omega) (by decide))
      have hsq : a.toNat ^ (n / 2 * 2) = a.toNat ^ (n / 2) * a.toNat ^ (n / 2) := by
        rw [Nat.pow_mul, Nat.pow_two]
      split
      next he =>
        rw [toNat_mul, hh, ← Nat.mul_mod, ← hsq,
          Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero he)]
      next ho =>
        rw [toNat_mul, toNat_mul, hh, ← Nat.mul_mod, Nat.mod_mul_mod, ← hsq,
          ← Nat.pow_succ]
        congr 2
        omega

/-- The logarithmic executable implementation equals its legible modular reference. -/
theorem exp_eq_reference (a b : U256) : exp a b = expReference a b := by
  apply toNat_inj.mp
  exact (toNat_expNat a b.toNat).trans (toNat_expReferenceNat a b.toNat).symm

/-- The unsigned value of EXP is the natural power reduced modulo `2^256`. -/
theorem toNat_exp (a b : U256) : (exp a b).toNat = a.toNat ^ b.toNat % 2 ^ 256 :=
  toNat_expNat a b.toNat

/-- Exponent zero returns one, including for base zero. -/
theorem exp_zero (a : U256) : exp a zero = one := by
  apply toNat_inj.mp
  rw [toNat_exp, toNat_zero, Nat.pow_zero, toNat_one]

/-- Exponent one returns the base. -/
theorem exp_one (a : U256) : exp a one = a := by
  apply toNat_inj.mp
  rw [toNat_exp, toNat_one, Nat.pow_one, Nat.mod_eq_of_lt (toNat_lt a)]

/-- Base one returns one for every exponent. -/
theorem one_exp (b : U256) : exp one b = one := by
  apply toNat_inj.mp
  rw [toNat_exp, toNat_one, Nat.one_pow]

/-- Base zero returns zero for every nonzero unsigned exponent. -/
theorem zero_exp (b : U256) (h : b.toNat ≠ 0) : exp zero b = zero := by
  apply toNat_inj.mp
  rw [toNat_exp, toNat_zero, Nat.zero_pow (by omega : 0 < b.toNat), Nat.zero_mod]

end STFSpec.Base.U256
