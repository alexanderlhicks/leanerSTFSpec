/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.U256

/-!
# Signed U256 division and remainder

Library `EthBase`: the total EVM SDIV and SMOD operation values, in first-popped
argument order. Stack, gas and program-counter effects belong to `EthVmInstructions`.
Signed construction corresponds to `ethereum_types/numeric.py:594`
(`from_signed`); the laws below prove its range guard succeeds on every result.
Spec guidance: `STFSpec/informal/modules/EthBase.md`.
EELS citations are at the commit in `reference.toml`.
-/

namespace STFSpec.Base.U256

/-- EVM SDIV: zero divisor first, then signed minimum divided by −1, then division
truncated toward zero. EELS `src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py:142`.
Signed observations use `ethereum_types/numeric.py:675` (`to_signed`). -/
def sdiv (a b : U256) : U256 :=
  if b.toInt = 0 then zero else
    if a.toInt = -(2 : Int) ^ 255 ∧ b.toInt = -1 then a else
      ofBitVec (BitVec.ofInt 256 (a.toInt.tdiv b.toInt))

/-- EVM SMOD: a zero divisor returns zero; otherwise the remainder has the dividend's
sign. EELS `src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py:205`.
Signed observations use `ethereum_types/numeric.py:675` (`to_signed`). -/
def smod (a b : U256) : U256 :=
  if b.toInt = 0 then zero else ofBitVec (BitVec.ofInt 256 (a.toInt.tmod b.toInt))

/-- Truncated division fits the signed word range outside the explicit minimum/−1 case. -/
theorem tdiv_signed_bounds (a b : U256)
    (h : ¬ (a.toInt = -(2 : Int) ^ 255 ∧ b.toInt = -1)) :
    -(2 : Int) ^ 255 ≤ a.toInt.tdiv b.toInt ∧
      a.toInt.tdiv b.toInt < (2 : Int) ^ 255 := by
  have hlo := le_toInt a
  have hhi := toInt_lt a
  have hd := Nat.div_le_self a.toInt.natAbs b.toInt.natAbs
  have hz := Int.natCast_nonneg (a.toInt.natAbs / b.toInt.natAbs)
  rcases ha : a.toInt with m | m <;> rcases hb : b.toInt with n | n <;>
    simp only [ha, hb, Int.tdiv, Int.natAbs,
      Int.ofNat_eq_natCast, Nat.succ_eq_add_one] at *
  · omega
  · omega
  · omega
  · by_cases hm : m + 1 < 2 ^ 255
    · omega
    · have hn : 1 < n + 1 := by omega
      have hlt := Nat.div_lt_self (by omega : 0 < m + 1) hn
      omega

/-- Truncated remainder fits the signed word range, even before the EVM zero guard. -/
theorem tmod_signed_bounds (a b : U256) :
    -(2 : Int) ^ 255 ≤ a.toInt.tmod b.toInt ∧
      a.toInt.tmod b.toInt < (2 : Int) ^ 255 := by
  have hlo := le_toInt a
  have hhi := toInt_lt a
  have hr := Nat.mod_le a.toInt.natAbs b.toInt.natAbs
  rcases ha : a.toInt with m | m <;> rcases hb : b.toInt with n | n <;>
    simp only [ha, hb, Int.tmod, Int.natAbs,
      Int.ofNat_eq_natCast, Nat.succ_eq_add_one] at * <;> omega

/-! ### Operation and checked-conversion contract -/

/-- EELS's ordinary SDIV branch always passes the checked signed constructor. -/
theorem ofInt?_tdiv (a b : U256)
    (h : ¬ (a.toInt = -(2 : Int) ^ 255 ∧ b.toInt = -1)) :
    ofInt? (a.toInt.tdiv b.toInt) =
      some (ofBitVec (BitVec.ofInt 256 (a.toInt.tdiv b.toInt))) := by
  have hr := tdiv_signed_bounds a b h
  apply (ofInt?_eq_some_iff _ _).mpr
  exact ⟨hr.1, hr.2, BitVec.toInt_ofInt_eq_self (by decide) hr.1 hr.2⟩

/-- Every truncated remainder passes the checked signed constructor. -/
theorem ofInt?_tmod (a b : U256) :
    ofInt? (a.toInt.tmod b.toInt) =
      some (ofBitVec (BitVec.ofInt 256 (a.toInt.tmod b.toInt))) := by
  have hr := tmod_signed_bounds a b
  apply (ofInt?_eq_some_iff _ _).mpr
  exact ⟨hr.1, hr.2, BitVec.toInt_ofInt_eq_self (by decide) hr.1 hr.2⟩

/-- SDIV equals the exact signed EELS case split, including the unique overflow case. -/
theorem toInt_sdiv (a b : U256) :
    (sdiv a b).toInt = if b.toInt = 0 then 0 else
      if a.toInt = -(2 : Int) ^ 255 ∧ b.toInt = -1 then -(2 : Int) ^ 255
      else a.toInt.tdiv b.toInt := by
  unfold sdiv
  split
  · exact toInt_zero
  · split
    next h => exact h.1
    next h =>
      have hr := tdiv_signed_bounds a b h
      exact BitVec.toInt_ofInt_eq_self (by decide) hr.1 hr.2

/-- SMOD equals dividend-sign truncated remainder, with EVM's zero-divisor guard. -/
theorem toInt_smod (a b : U256) :
    (smod a b).toInt = if b.toInt = 0 then 0 else a.toInt.tmod b.toInt := by
  unfold smod
  split
  · exact toInt_zero
  · have hr := tmod_signed_bounds a b
    exact BitVec.toInt_ofInt_eq_self (by decide) hr.1 hr.2

/-- EELS's checked construction of the full guarded SDIV model always succeeds. -/
theorem ofInt?_sdiv (a b : U256) :
    ofInt? (if b.toInt = 0 then 0 else
      if a.toInt = -(2 : Int) ^ 255 ∧ b.toInt = -1 then -(2 : Int) ^ 255
      else a.toInt.tdiv b.toInt) = some (sdiv a b) := by
  rw [← toInt_sdiv]
  exact ofInt?_toInt _

/-- EELS's checked construction of the full guarded SMOD model always succeeds. -/
theorem ofInt?_smod (a b : U256) :
    ofInt? (if b.toInt = 0 then 0 else a.toInt.tmod b.toInt) = some (smod a b) := by
  rw [← toInt_smod]
  exact ofInt?_toInt _

/-- SDIV's zero-divisor branch returns zero before testing signed overflow. -/
theorem sdiv_eq_zero_of_toInt_eq_zero (a b : U256) (h : b.toInt = 0) :
    sdiv a b = zero := by
  simp only [sdiv, h, ite_true]

/-- SMOD's zero-divisor branch returns zero rather than the dividend. -/
theorem smod_eq_zero_of_toInt_eq_zero (a b : U256) (h : b.toInt = 0) :
    smod a b = zero := by
  simp only [smod, h, ite_true]

/-- Signed division by the word zero returns zero. -/
theorem sdiv_zero (a : U256) : sdiv a zero = zero :=
  sdiv_eq_zero_of_toInt_eq_zero a zero toInt_zero

/-- Signed remainder by the word zero returns zero. -/
theorem smod_zero (a : U256) : smod a zero = zero :=
  smod_eq_zero_of_toInt_eq_zero a zero toInt_zero

/-- The signed minimum divided by −1 returns the dividend word unchanged. -/
theorem sdiv_eq_left_of_min_neg_one (a b : U256)
    (ha : a.toInt = -(2 : Int) ^ 255) (hb : b.toInt = -1) : sdiv a b = a := by
  simp only [sdiv, ha, hb, show ¬ (-1 : Int) = 0 by decide, ite_false,
    and_self, ite_true]

end STFSpec.Base.U256
