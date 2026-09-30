/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

/-!
# Checked natural subtraction and rounding to words

Library `EthBase`: unbounded unsigned integers, checked subtraction and `ceil32`.
The reference is pinned EELS `src/ethereum/utils/numeric.py:43` and locked
`ethereum-types` 0.4.1; all inputs here are natural numbers, without a width limit.
A checked source reference beside `ceil32` proves its subtraction cannot underflow.

Spec guidance: `STFSpec/informal/modules/EthBase.md`.
-/

namespace STFSpec.Base

/-- Unbounded unsigned integers, modelled directly by `Nat`;
`ethereum_types/numeric.py:517,539` (`Uint` and its nonnegative range). -/
abbrev Uint := Nat

namespace Uint

/-- Checked unbounded subtraction; `ethereum_types/numeric.py:103` (`__sub__`).
Check underflow before subtracting; `none` represents the source's `OverflowError`.
Callers handle `none` through their component's error contract (D14/B14). -/
def sub? (n m : Nat) : Option Nat := if n < m then none else some (n - m)

/-- Checked subtraction succeeds exactly without underflow, with the exact difference. -/
theorem sub?_eq_some_iff (n m r : Nat) : sub? n m = some r ↔ m ≤ n ∧ r = n - m := by
  unfold sub?
  split
  next h =>
    constructor
    · intro heq
      cases heq
    · intro hs
      omega
  next h =>
    simp only [Option.some.injEq]
    omega

/-- Checked subtraction fails exactly when the subtrahend exceeds the minuend. -/
theorem sub?_eq_none_iff (n m : Nat) : sub? n m = none ↔ n < m := by
  simp [sub?]

/-- A successful checked difference is characterised by reconstructing the minuend. -/
theorem sub?_eq_some_iff_add (n m r : Nat) : sub? n m = some r ↔ m + r = n := by
  rw [sub?_eq_some_iff]
  omega

/-- Subtracting zero succeeds without changing the value. -/
theorem sub?_zero (n : Nat) : sub? n 0 = some n :=
  (sub?_eq_some_iff_add _ _ _).mpr (Nat.zero_add _)

/-- Subtracting a value from itself succeeds with zero. -/
theorem sub?_self (n : Nat) : sub? n n = some 0 :=
  (sub?_eq_some_iff_add _ _ _).mpr (Nat.add_zero _)

/-- Subtracting the second summand from an unbounded sum always succeeds. -/
theorem sub?_add_cancel (n m : Nat) : sub? (n + m) m = some n :=
  (sub?_eq_some_iff_add _ _ _).mpr (Nat.add_comm _ _)

end Uint

/-- Round upward to the least multiple of 32; EELS `src/ethereum/utils/numeric.py:43`.
The quotient formula is proved equal to the checked source reference below, on all inputs. -/
def ceil32 (n : Nat) : Nat := (n + 31) / 32 * 32

/-- EELS remainder case split with checked subtraction; `src/ethereum/utils/numeric.py:43`. -/
def ceil32Reference (n : Nat) : Option Nat :=
  let remainder := n % 32
  if remainder = 0 then some n else Uint.sub? (n + 32) remainder

/-- The rounding result is a multiple of 32. -/
theorem ceil32_mod_eq_zero (n : Nat) : ceil32 n % 32 = 0 := by
  simp [ceil32]

/-- Rounding never decreases its input. -/
theorem le_ceil32 (n : Nat) : n ≤ ceil32 n := by
  have hm := Nat.mod_lt (n + 31) (by decide : 0 < 32)
  have hd := Nat.div_add_mod (n + 31) 32
  unfold ceil32
  omega

/-- Rounding adds less than one full word. -/
theorem ceil32_lt_add (n : Nat) : ceil32 n < n + 32 := by
  have hd := Nat.div_add_mod (n + 31) 32
  unfold ceil32
  omega

/-- Any multiple of 32 above the input is at least its rounding result. -/
theorem ceil32_le_of_mod_eq_zero (n k : Nat) (hn : n ≤ k) (hk : k % 32 = 0) :
    ceil32 n ≤ k := by
  have hc := ceil32_mod_eq_zero n
  have hb := ceil32_lt_add n
  have hd := Nat.div_add_mod k 32
  have hdc := Nat.div_add_mod (ceil32 n) 32
  omega

/-- An input already divisible by 32 is unchanged. -/
theorem ceil32_eq_self_of_mod_eq_zero (n : Nat) (h : n % 32 = 0) : ceil32 n = n := by
  have hlo := le_ceil32 n
  have hhi := ceil32_le_of_mod_eq_zero n n (Nat.le_refl _) h
  omega

/-- The quotient definition agrees with EELS's remainder case split. -/
theorem ceil32_eq_cond (n : Nat) :
    ceil32 n = if n % 32 = 0 then n else n + 32 - n % 32 := by
  split
  next h => exact ceil32_eq_self_of_mod_eq_zero n h
  next h =>
    have hm := Nat.mod_lt n (by decide : 0 < 32)
    have hd := Nat.div_add_mod n 32
    have hc := ceil32_mod_eq_zero n
    have hdc := Nat.div_add_mod (ceil32 n) 32
    have hlo := le_ceil32 n
    have hhi := ceil32_lt_add n
    omega

/-- The source's checked subtraction is always admitted, for the fixed modulus 32. -/
theorem Uint.sub?_add32_mod32 (n : Nat) :
    Uint.sub? (n + 32) (n % 32) = some (n + 32 - n % 32) := by
  apply (Uint.sub?_eq_some_iff _ _ _).mpr
  have hm := Nat.mod_lt n (by decide : 0 < 32)
  exact ⟨by omega, rfl⟩

/-- The checked source reference returns exactly the quotient-form rounding result. -/
theorem ceil32Reference_eq_some (n : Nat) : ceil32Reference n = some (ceil32 n) := by
  unfold ceil32Reference
  dsimp only
  rw [ceil32_eq_cond]
  split
  · rfl
  · exact Uint.sub?_add32_mod32 n

/-- Zero needs no rounding. -/
theorem ceil32_zero : ceil32 0 = 0 := rfl

/-- Rounding an already rounded value is idempotent. -/
theorem ceil32_ceil32 (n : Nat) : ceil32 (ceil32 n) = ceil32 n :=
  ceil32_eq_self_of_mod_eq_zero _ (ceil32_mod_eq_zero n)

end STFSpec.Base
