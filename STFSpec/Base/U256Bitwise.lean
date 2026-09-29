/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.U256

/-!
# U256 comparisons and bitwise operations

Library `EthBase`: total EVM operation values in first-popped argument order.
Stack, gas and program-counter effects belong to `EthVmInstructions`.
The equations use the stable public observers, so callers do not depend on storage.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §§2–8.
All EELS citations are at the commit in `reference.toml`.
-/

namespace STFSpec.Base.U256

/-- Unsigned strict comparison helper; `ethereum_types/numeric.py:357` (`__lt__`). -/
def ult (a b : U256) : Bool := decide (a.toNat < b.toNat)

/-- Unsigned non-strict comparison helper; `ethereum_types/numeric.py:343` (`__le__`). -/
def ule (a b : U256) : Bool := decide (a.toNat ≤ b.toNat)

/-- Signed strict comparison helper; `ethereum_types/numeric.py:357,675` (via `to_signed`). -/
def slt' (a b : U256) : Bool := decide (a.toInt < b.toInt)

/-- EVM LT result; EELS `src/ethereum/forks/amsterdam/vm/instructions/comparison.py:24`. -/
def lt (a b : U256) : U256 := ofBool (ult a b)

/-- EVM GT result; EELS `src/ethereum/forks/amsterdam/vm/instructions/comparison.py:77`. -/
def gt (a b : U256) : U256 := ofBool (ult b a)

/-- EVM SLT result; EELS `src/ethereum/forks/amsterdam/vm/instructions/comparison.py:51`. -/
def slt (a b : U256) : U256 := ofBool (slt' a b)

/-- EVM SGT result; EELS `src/ethereum/forks/amsterdam/vm/instructions/comparison.py:104`. -/
def sgt (a b : U256) : U256 := ofBool (slt' b a)

/-- EVM EQ result; EELS `src/ethereum/forks/amsterdam/vm/instructions/comparison.py:130`. -/
def eq (a b : U256) : U256 := ofBool (decide (a.toNat = b.toNat))

/-- EVM ISZERO result; EELS `src/ethereum/forks/amsterdam/vm/instructions/comparison.py:157`. -/
def iszero (x : U256) : U256 := ofBool (decide (x.toNat = 0))

/-- EVM AND; EELS `src/ethereum/forks/amsterdam/vm/instructions/bitwise.py:24`. -/
def and (a b : U256) : U256 := ofBitVec (a.toBitVec &&& b.toBitVec)

/-- EVM OR; EELS `src/ethereum/forks/amsterdam/vm/instructions/bitwise.py:49`. -/
def or (a b : U256) : U256 := ofBitVec (a.toBitVec ||| b.toBitVec)

/-- EVM XOR; EELS `src/ethereum/forks/amsterdam/vm/instructions/bitwise.py:74`. -/
def xor (a b : U256) : U256 := ofBitVec (a.toBitVec ^^^ b.toBitVec)

/-- Masked EVM NOT; EELS `src/ethereum/forks/amsterdam/vm/instructions/bitwise.py:99`. -/
def not (x : U256) : U256 := ofBitVec (~~~x.toBitVec)

/-- EVM BYTE, most-significant byte first, with its range guard before arithmetic.
EELS `src/ethereum/forks/amsterdam/vm/instructions/bitwise.py:123` (`get_byte`). -/
def byte (i x : U256) : U256 :=
  if 32 ≤ i.toNat then zero else ofNat (x.toNat / 2 ^ (8 * (31 - i.toNat)) % 256)

/-- EVM SIGNEXTEND, counting bytes from the least-significant end.
EELS `src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py:334`. -/
def signextend (k x : U256) : U256 :=
  if 31 < k.toNat then x else
    ofBitVec ((x.toBitVec.setWidth (8 * (k.toNat + 1))).signExtend 256)

/-- EVM SHL, guarding the full word amount before shifting.
EELS `src/ethereum/forks/amsterdam/vm/instructions/bitwise.py:159` (`bitwise_shl`). -/
def shl (shift value : U256) : U256 :=
  if 256 ≤ shift.toNat then zero else ofBitVec (value.toBitVec <<< shift.toNat)

/-- EVM SHR, guarding the full word amount before shifting.
EELS `src/ethereum/forks/amsterdam/vm/instructions/bitwise.py:189` (`bitwise_shr`). -/
def shr (shift value : U256) : U256 :=
  if 256 ≤ shift.toNat then zero else ofBitVec (value.toBitVec >>> shift.toNat)

/-- EVM SAR, including the explicit sign-dependent saturation branch.
EELS `src/ethereum/forks/amsterdam/vm/instructions/bitwise.py:219` (`bitwise_sar`). -/
def sar (shift value : U256) : U256 :=
  if 256 ≤ shift.toNat then
    if 0 ≤ value.toInt then zero else max
  else ofBitVec (value.toBitVec.sshiftRight shift.toNat)

/-- Python integer bit length, including zero; `ethereum_types/numeric.py:509`.
Used by EELS `src/ethereum/forks/amsterdam/vm/instructions/bitwise.py:271`. -/
def bitLength (x : U256) : Nat := if x.toNat = 0 then 0 else x.toNat.log2 + 1

/-- EVM CLZ; EELS `src/ethereum/forks/amsterdam/vm/instructions/bitwise.py:251`
(`count_leading_zeros`). -/
def clz (x : U256) : U256 := ofNat (256 - bitLength x)

/-! ### Comparison and logic contract -/

/-- `ult` is comparison of the public numeric models. -/
theorem ult_eq (a b : U256) : ult a b = decide (a.toNat < b.toNat) := rfl

/-- `ule` is comparison of the public numeric models. -/
theorem ule_eq (a b : U256) : ule a b = decide (a.toNat ≤ b.toNat) := rfl

/-- `slt'` is comparison of the public numeric models. -/
theorem slt'_eq (a b : U256) : slt' a b = decide (a.toInt < b.toInt) := rfl

/-- The LT word is exactly 0 or 1 according to its numeric model. -/
theorem toNat_lt_word (a b : U256) :
    (lt a b).toNat = if a.toNat < b.toNat then 1 else 0 := by
  simp only [lt, ult, toNat_ofBool, decide_eq_true_eq]

/-- The GT word is exactly 0 or 1 according to its numeric model. -/
theorem toNat_gt (a b : U256) :
    (gt a b).toNat = if b.toNat < a.toNat then 1 else 0 := by
  simp only [gt, ult, toNat_ofBool, decide_eq_true_eq]

/-- The SLT word is exactly 0 or 1 according to its numeric model. -/
theorem toNat_slt (a b : U256) :
    (slt a b).toNat = if a.toInt < b.toInt then 1 else 0 := by
  simp only [slt, slt', toNat_ofBool, decide_eq_true_eq]

/-- The SGT word is exactly 0 or 1 according to its numeric model. -/
theorem toNat_sgt (a b : U256) :
    (sgt a b).toNat = if b.toInt < a.toInt then 1 else 0 := by
  simp only [sgt, slt', toNat_ofBool, decide_eq_true_eq]

/-- The EQ word is exactly 0 or 1 according to its numeric model. -/
theorem toNat_eq_word (a b : U256) :
    (eq a b).toNat = if a.toNat = b.toNat then 1 else 0 := by
  simp only [eq, toNat_ofBool, decide_eq_true_eq]

/-- ISZERO uses numeric equality with zero. -/
theorem toNat_iszero (x : U256) : (iszero x).toNat = if x.toNat = 0 then 1 else 0 := by
  simp only [iszero, toNat_ofBool, decide_eq_true_eq]

/-- `and` commutes with the public bit-vector model. -/
theorem toBitVec_and (a b : U256) :
    (and a b).toBitVec = a.toBitVec &&& b.toBitVec := rfl

/-- `or` commutes with the public bit-vector model. -/
theorem toBitVec_or (a b : U256) :
    (or a b).toBitVec = a.toBitVec ||| b.toBitVec := rfl

/-- `xor` commutes with the public bit-vector model. -/
theorem toBitVec_xor (a b : U256) :
    (xor a b).toBitVec = a.toBitVec ^^^ b.toBitVec := rfl

/-- NOT commutes with the public bit-vector model. -/
theorem toBitVec_not (x : U256) : (not x).toBitVec = ~~~x.toBitVec := rfl

/-! ### Byte selection and sign extension contract -/

/-- BYTE is guarded positional byte selection on the unsigned model. -/
theorem toNat_byte (i x : U256) :
    (byte i x).toNat = if 32 ≤ i.toNat then 0 else
      x.toNat / 2 ^ (8 * (31 - i.toNat)) % 256 := by
  unfold byte
  split
  · exact toNat_zero
  · rw [toNat_ofNat, Nat.mod_eq_of_lt]
    exact Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)

/-- Every out-of-range byte index selects zero, including maximum-word indices. -/
theorem byte_eq_zero_of_le (i x : U256) (h : 32 ≤ i.toNat) : byte i x = zero := by
  simp only [byte, h, ite_true]

/-- SIGNEXTEND commutes with truncation followed by bit-vector sign extension. -/
theorem toBitVec_signextend (k x : U256) :
    (signextend k x).toBitVec = if 31 < k.toNat then x.toBitVec else
      (x.toBitVec.setWidth (8 * (k.toNat + 1))).signExtend 256 := by
  unfold signextend
  split <;> rfl

/-- Out-of-range SIGNEXTEND leaves the word unchanged. -/
theorem signextend_eq_self_of_lt (k x : U256) (h : 31 < k.toNat) :
    signextend k x = x := by
  simp only [signextend, h, ite_true]

/-- Extending from byte 31 leaves all 256 bits unchanged. -/
theorem signextend_eq_self_of_eq (k x : U256) (h : k.toNat = 31) :
    signextend k x = x := by
  apply ext
  rw [toBitVec_signextend, h]
  simp

/-- The retained bytes and the sign-fill bytes agree with EELS's byte construction. -/
theorem getLsbD_signextend (k x : U256) (h : k.toNat ≤ 31) (i : Nat) :
    (signextend k x).toBitVec.getLsbD i =
      (decide (i < 256) && if i < 8 * (k.toNat + 1) then x.toBitVec.getLsbD i
        else x.toBitVec.getLsbD (8 * (k.toNat + 1) - 1)) := by
  rw [toBitVec_signextend, ite_eq_right (by omega), BitVec.getLsbD_signExtend,
    BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth]
  have hw : 0 < 8 * (k.toNat + 1) := by omega
  have hl : 8 * (k.toNat + 1) - 1 < 8 * (k.toNat + 1) := by omega
  simp only [hl, decide_true, Bool.true_and]
  split <;> simp_all

/-- SIGNEXTEND's numeric result retains the low bytes, then prepends all-one bytes
exactly when their top bit is set, matching the EELS byte construction. -/
theorem toNat_signextend (k x : U256) :
    (signextend k x).toNat = if 31 < k.toNat then x.toNat else
      x.toNat % 2 ^ (8 * (k.toNat + 1)) +
        if x.toBitVec.getLsbD (8 * (k.toNat + 1) - 1) then
          2 ^ 256 - 2 ^ (8 * (k.toNat + 1)) else 0 := by
  rw [toNat_eq, toBitVec_signextend]
  split
  · rfl
  next h =>
    have hw : 8 * (k.toNat + 1) ≤ 256 := by omega
    rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
        (Nat.pow_le_pow_right Nat.two_pos hw)),
      BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_setWidth]
    simp only [← toNat_eq]
    simp only [show 8 * (k.toNat + 1) - 1 < 8 * (k.toNat + 1) by omega,
      decide_true, Bool.true_and]

/-! ### Shift contract -/

/-- SHL's model includes the full-word saturation guard. -/
theorem toBitVec_shl (shift value : U256) :
    (shl shift value).toBitVec = if 256 ≤ shift.toNat then 0 else
      value.toBitVec <<< shift.toNat := by
  unfold shl
  split <;> rfl

/-- SHR's model includes the full-word saturation guard. -/
theorem toBitVec_shr (shift value : U256) :
    (shr shift value).toBitVec = if 256 ≤ shift.toNat then 0 else
      value.toBitVec >>> shift.toNat := by
  unfold shr
  split <;> rfl

/-- SHL reduces an unbounded natural left shift modulo the word modulus. -/
theorem toNat_shl (shift value : U256) :
    (shl shift value).toNat = if 256 ≤ shift.toNat then 0 else
      (value.toNat * 2 ^ shift.toNat) % 2 ^ 256 := by
  rw [toNat_eq, toBitVec_shl]
  split
  · rfl
  · simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, toNat_eq]

/-- SHR is natural division by a power of two below its saturation guard. -/
theorem toNat_shr (shift value : U256) :
    (shr shift value).toNat = if 256 ≤ shift.toNat then 0 else
      value.toNat / 2 ^ shift.toNat := by
  rw [toNat_eq, toBitVec_shr]
  split
  · rfl
  · simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, toNat_eq]

/-- A saturated SHL returns zero without performing the enormous shift. -/
theorem shl_eq_zero_of_le (shift value : U256) (h : 256 ≤ shift.toNat) :
    shl shift value = zero := by
  simp only [shl, h, ite_true]

/-- A saturated SHR returns zero without performing the enormous shift. -/
theorem shr_eq_zero_of_le (shift value : U256) (h : 256 ≤ shift.toNat) :
    shr shift value = zero := by
  simp only [shr, h, ite_true]

/-- SAR has EELS's explicit signed saturation cases and its signed shift below 256. -/
theorem toInt_sar (shift value : U256) :
    (sar shift value).toInt = if 256 ≤ shift.toNat then
      if 0 ≤ value.toInt then 0 else -1 else value.toInt >>> shift.toNat := by
  unfold sar
  split
  · split
    · exact toInt_zero
    · exact toInt_max
  · exact BitVec.toInt_sshiftRight

/-- EELS's checked `from_signed` succeeds on every below-256 SAR result. -/
theorem ofInt?_sar_shift (shift value : U256) :
    ofInt? (value.toInt >>> shift.toNat) =
      some (ofBitVec (value.toBitVec.sshiftRight shift.toNat)) := by
  apply ofInt?_eq_some_iff.mpr
  exact ⟨BitVec.le_toInt_shiftRight, BitVec.toInt_shiftRight_lt,
    BitVec.toInt_sshiftRight⟩

/-- Saturated nonnegative SAR returns zero. -/
theorem sar_eq_zero_of_le (shift value : U256) (h : 256 ≤ shift.toNat)
    (hv : 0 ≤ value.toInt) : sar shift value = zero := by
  simp only [sar, h, hv, ite_true]

/-- Saturated negative SAR returns the all-ones word. -/
theorem sar_eq_max_of_le (shift value : U256) (h : 256 ≤ shift.toNat)
    (hv : value.toInt < 0) : sar shift value = max := by
  simp only [sar, h, ite_true, ite_eq_right (by omega : ¬ 0 ≤ value.toInt)]

/-- The explicit EELS saturation agrees with the unguarded BitVec arithmetic shift model. -/
theorem toBitVec_sar (shift value : U256) :
    (sar shift value).toBitVec = value.toBitVec.sshiftRight shift.toNat := by
  unfold sar
  split
  next h =>
    have hs : value.toBitVec.msb = decide (value.toInt < 0) := BitVec.msb_eq_toInt
    split
    next hv =>
      have hm : value.toBitVec.msb = false := by simpa [show ¬ value.toInt < 0 by omega] using hs
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      change (0 : BitVec 256).getLsbD i = _
      rw [BitVec.getLsbD_sshiftRight, hm]
      simp [show ¬ shift.toNat + i < 256 by omega]
    next hv =>
      have hm : value.toBitVec.msb = true := by
        simpa [show value.toInt < 0 by omega] using hs
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      change (BitVec.ofNat 256 (2 ^ 256 - 1)).getLsbD i = _
      rw [BitVec.getLsbD_sshiftRight, hm, BitVec.getLsbD_ofNat,
        Nat.testBit_two_pow_sub_one]
      simp only [hi, decide_true, Bool.and_true,
        show ¬ 256 ≤ i by omega, decide_false, Bool.not_false,
        show ¬ shift.toNat + i < 256 by omega, ite_false]
  next h => rfl

/-! ### Bit length and leading-zero contract -/

/-- Bit length is zero at zero and one more than floor(log₂) otherwise. -/
theorem bitLength_eq (x : U256) :
    bitLength x = if x.toNat = 0 then 0 else x.toNat.log2 + 1 := rfl

/-- Word bit length cannot exceed the width, discharging CLZ subtraction's range. -/
theorem bitLength_le (x : U256) : bitLength x ≤ 256 := by
  rw [bitLength_eq]
  split
  · omega
  next h =>
    have := (Nat.log2_lt h).mpr (toNat_lt x)
    omega

/-- CLZ is width minus bit length, without modular wrapping. -/
theorem toNat_clz (x : U256) : (clz x).toNat = 256 - bitLength x := by
  rw [clz, toNat_ofNat, Nat.mod_eq_of_lt]
  omega

/-- CLZ's numeric model handles zero separately. -/
theorem toNat_clz_eq (x : U256) :
    (clz x).toNat = if x.toNat = 0 then 256 else 256 - x.toNat.log2 - 1 := by
  rw [toNat_clz, bitLength_eq]
  split <;> omega

/-- CLZ at zero is the word width. -/
theorem clz_zero : (clz zero).toNat = 256 := by
  rw [toNat_clz_eq, toNat_zero]
  rfl

/-- CLZ at the all-ones word is zero. -/
theorem clz_max : (clz max).toNat = 0 := by
  rw [toNat_clz_eq, toNat_max]
  have hl : (2 ^ 256 - 1 : Nat).log2 = 255 := by
    apply (Nat.log2_eq_iff (by omega)).mpr
    constructor <;> omega
  simp only [show (2 ^ 256 - 1 : Nat) ≠ 0 by omega, ite_false, hl]

end STFSpec.Base.U256
