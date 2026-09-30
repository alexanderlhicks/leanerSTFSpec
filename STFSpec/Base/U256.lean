/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

/-!
# U256 values and constructors

Library `EthBase`: the stable word observers, constructors and unsigned ordering.
The stored representation is internal by convention; callers use the laws below.

Spec guidance: `STFSpec/informal/modules/EthBase.md`.
Citations follow the source/dependency convention in EthBase §3.
-/

namespace STFSpec.Base

/-- An EVM word, modelled by `BitVec 256` through `U256.toBitVec`.
Corresponds to `ethereum_types/numeric.py:690` (`U256`). The field is internal by convention. -/
structure U256 where
  private ofBitVecRaw ::
  /-- Internal stored value; consumers use the stable observers. -/
  val : BitVec 256

namespace U256

/-- The stable bit-vector observer. -/
def toBitVec (x : U256) : BitVec 256 := x.val

/-- The unsigned numeric observer; `ethereum_types/numeric.py:321` (`__int__`). -/
def toNat (x : U256) : Nat := x.toBitVec.toNat

/-- Two's-complement signed interpretation; `ethereum_types/numeric.py:675` (`to_signed`). -/
def toInt (x : U256) : Int := x.toBitVec.toInt

/-- Construct a word from its bit-vector model. -/
def ofBitVec (x : BitVec 256) : U256 := ofBitVecRaw x

/-- Reduce a natural number modulo 2²⁵⁶. This wrapping constructor is a Lean model helper,
not the checked Python constructor (`ethereum_types/numeric.py:44`). -/
def ofNat (n : Nat) : U256 := ofBitVec (BitVec.ofNat 256 n)

/-- Checked Python `U256(n)` on natural inputs; `ethereum_types/numeric.py:44,611`.
Returns `none` exactly for unsigned overflow. -/
def ofNat? (n : Nat) : Option U256 :=
  if n < 2 ^ 256 then some (ofNat n) else none

/-- Checked `from_signed`; `ethereum_types/numeric.py:594`.
Checks the exclusive upper bound before the inclusive lower bound, returning `none`
for either overflow; accepted inputs are encoded in two's complement. -/
def ofInt? (i : Int) : Option U256 :=
  if i < (2 : Int) ^ 255 then
    if -(2 : Int) ^ 255 ≤ i then some (ofBitVec (BitVec.ofInt 256 i)) else none
  else none

/-- The word zero; `ethereum_types/numeric.py:44` with input 0. -/
def zero : U256 := ofNat 0

/-- The word one; `ethereum_types/numeric.py:44` with input 1. -/
def one : U256 := ofNat 1

/-- The maximum unsigned word; `ethereum_types/numeric.py:711–712` (`MAX_VALUE`). -/
def max : U256 := ofNat (2 ^ 256 - 1)

/-- Encode a Boolean as 0 or 1; `ethereum_types/numeric.py:44` on a Python `bool`.
EELS `src/ethereum/forks/amsterdam/vm/instructions/comparison.py:43` uses this conversion. -/
def ofBool (b : Bool) : U256 := if b then one else zero

/-- Unsigned numeric ordering; `ethereum_types/numeric.py:343–369`. -/
instance : Ord U256 where
  compare := compareOn toNat

/-! ### Observer contract -/

/-- Equal bit-vector observations determine equal words. -/
@[ext] theorem ext {x y : U256} (h : x.toBitVec = y.toBitVec) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- The bit-vector observer is injective. -/
theorem toBitVec_inj {x y : U256} : x.toBitVec = y.toBitVec ↔ x = y :=
  ⟨ext, congrArg toBitVec⟩

/-- Word equality is decidable through the bit-vector model;
`ethereum_types/numeric.py:325` (`__eq__`) on two U256 values. -/
instance : DecidableEq U256 := fun x y ↦
  decidable_of_iff (x.toBitVec = y.toBitVec) toBitVec_inj

/-- The unsigned observer is injective. -/
theorem toNat_inj {x y : U256} : x.toNat = y.toNat ↔ x = y := by
  constructor
  · intro h
    exact ext (BitVec.eq_of_toNat_eq h)
  · exact congrArg toNat

/-- The default word is zero. -/
instance : Inhabited U256 where
  default := zero

/-- Display a word by its unsigned observation. -/
instance : Repr U256 where
  reprPrec x prec := reprPrec x.toNat prec

/-- The signed observer is injective. -/
theorem toInt_inj {x y : U256} : x.toInt = y.toInt ↔ x = y := by
  constructor
  · intro h
    exact ext (BitVec.eq_of_toInt_eq h)
  · exact congrArg toInt

/-- Every unsigned observation is below 2²⁵⁶. -/
theorem toNat_lt (x : U256) : x.toNat < 2 ^ 256 := x.toBitVec.isLt

/-- The unsigned observer agrees with the bit-vector model. -/
theorem toNat_def (x : U256) : x.toNat = x.toBitVec.toNat := rfl

/-- The signed observer agrees with the bit-vector model. -/
theorem toInt_def (x : U256) : x.toInt = x.toBitVec.toInt := rfl

/-- Two's-complement interpretation agrees with EELS's sign-bit case split. -/
theorem toInt_eq_toNat_cond (x : U256) :
    x.toInt = if x.toNat < 2 ^ 255 then (x.toNat : Int) else
      (x.toNat : Int) - (2 ^ 256 : Nat) := by
  rw [toInt, BitVec.toInt_eq_toNat_cond]
  change (if 2 * x.toNat < 2 ^ 256 then (x.toNat : Int) else
    (x.toNat : Int) - (2 ^ 256 : Nat)) = _
  have h : 2 * x.toNat < 2 ^ 256 ↔ x.toNat < 2 ^ 255 := by omega
  simp only [h]

/-- Every signed observation is at least −2²⁵⁵. -/
theorem le_toInt (x : U256) : -(2 : Int) ^ 255 ≤ x.toInt :=
  BitVec.le_toInt x.toBitVec

/-- Every signed observation is below 2²⁵⁵. -/
theorem toInt_lt (x : U256) : x.toInt < (2 : Int) ^ 255 :=
  BitVec.toInt_lt

/-! ### Constructor contract -/

/-- Observing a word built from the bit-vector model returns that model. -/
theorem toBitVec_ofBitVec (x : BitVec 256) : (ofBitVec x).toBitVec = x := rfl

/-- Reconstructing a word from its bit-vector observation returns the word. -/
theorem ofBitVec_toBitVec (x : U256) : ofBitVec x.toBitVec = x := rfl

/-- Wrapping construction commutes with the bit-vector model. -/
theorem toBitVec_ofNat (n : Nat) : (ofNat n).toBitVec = BitVec.ofNat 256 n := rfl

/-- Wrapping construction is reduction modulo 2²⁵⁶. -/
theorem toNat_ofNat (n : Nat) : (ofNat n).toNat = n % 2 ^ 256 := rfl

/-- Reconstructing a word from its unsigned observation returns the word. -/
theorem ofNat_toNat (x : U256) : ofNat x.toNat = x := by
  apply toNat_inj.mp
  rw [toNat_ofNat, Nat.mod_eq_of_lt (toNat_lt x)]

/-- In-range wrapping construction retains the unsigned input. -/
theorem toNat_ofNat_of_lt {n : Nat} (h : n < 2 ^ 256) : (ofNat n).toNat = n := by
  rw [toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Checked natural construction succeeds exactly with the original unsigned value. -/
theorem ofNat?_eq_some_iff (n : Nat) (x : U256) :
    ofNat? n = some x ↔ n < 2 ^ 256 ∧ x.toNat = n := by
  unfold ofNat?
  split
  next h =>
    simp only [Option.some.injEq, ← toNat_inj, toNat_ofNat_of_lt h, h, true_and,
      eq_comm]
  next h => simp [h]

/-- Checked natural construction fails exactly on unsigned overflow. -/
theorem ofNat?_eq_none_iff (n : Nat) : ofNat? n = none ↔ 2 ^ 256 ≤ n := by
  simp [ofNat?, Nat.not_lt]

/-- Checked reconstruction from every unsigned observation succeeds. -/
theorem ofNat?_toNat (x : U256) : ofNat? x.toNat = some x :=
  (ofNat?_eq_some_iff _ _).mpr ⟨toNat_lt x, rfl⟩

/-- Checked signed construction succeeds exactly with the original signed value. -/
theorem ofInt?_eq_some_iff (i : Int) (x : U256) :
    ofInt? i = some x ↔ -(2 : Int) ^ 255 ≤ i ∧ i < (2 : Int) ^ 255 ∧ x.toInt = i := by
  unfold ofInt?
  split
  next hi =>
    split
    next hlo =>
      have hm : (ofBitVec (BitVec.ofInt 256 i)).toInt = i :=
        BitVec.toInt_ofInt_eq_self (by decide) hlo hi
      simp only [Option.some.injEq, ← toInt_inj, hm, hlo, hi, true_and, eq_comm]
    next hlo =>
      simp only [hlo, false_and, iff_false]
      exact fun h ↦ Option.some_ne_none _ h.symm
  next hi =>
    simp only [hi, false_and, and_false, iff_false]
    exact fun h ↦ Option.some_ne_none _ h.symm

/-- Checked signed construction fails exactly outside the two's-complement range. -/
theorem ofInt?_eq_none_iff (i : Int) :
    ofInt? i = none ↔ i < -(2 : Int) ^ 255 ∨ (2 : Int) ^ 255 ≤ i := by
  by_cases hi : i < (2 : Int) ^ 255
  · by_cases hlo : -(2 : Int) ^ 255 ≤ i
    · simp only [ofInt?, hi, hlo, ite_true, Option.some_ne_none, false_iff]
      omega
    · simp only [ofInt?, hi, hlo, ite_true, ite_false, true_iff]
      omega
  · simp only [ofInt?, hi, ite_false, true_iff]
    omega

/-- Checked reconstruction from every signed observation succeeds. -/
theorem ofInt?_toInt (x : U256) : ofInt? x.toInt = some x :=
  (ofInt?_eq_some_iff _ _).mpr ⟨le_toInt x, toInt_lt x, rfl⟩

/-- Accepted signed construction has the expected unsigned two's-complement encoding. -/
theorem toNat_ofInt? {i : Int} {x : U256} (h : ofInt? i = some x) :
    x.toNat = if 0 ≤ i then i.toNat else (i + (2 ^ 256 : Nat)).toNat := by
  have hs := ((ofInt?_eq_some_iff _ _).mp h).2.2
  have hr := toNat_lt x
  rw [toInt_eq_toNat_cond] at hs
  split at hs <;> split <;> omega

/-- Zero observes as the zero bit vector. -/
theorem toBitVec_zero : zero.toBitVec = 0#256 := rfl

/-- One observes as the unit bit vector. -/
theorem toBitVec_one : one.toBitVec = 1#256 := rfl

/-- The maximum word observes as the all-ones bit vector. -/
theorem toBitVec_max : max.toBitVec = BitVec.ofNat 256 (2 ^ 256 - 1) := rfl

/-- The unsigned value of zero. -/
theorem toNat_zero : zero.toNat = 0 := rfl

/-- The unsigned value of one. -/
theorem toNat_one : one.toNat = 1 := rfl

/-- The unsigned value of the maximum word. -/
theorem toNat_max : max.toNat = 2 ^ 256 - 1 := by
  apply toNat_ofNat_of_lt
  omega

/-- Boolean construction has the numeric value 0 or 1. -/
theorem toNat_ofBool (b : Bool) : (ofBool b).toNat = if b then 1 else 0 := by
  cases b <;> rfl

/-- The signed value of zero. -/
theorem toInt_zero : zero.toInt = 0 := by
  rw [toInt_eq_toNat_cond, toNat_zero]
  rfl

/-- The signed value of one. -/
theorem toInt_one : one.toInt = 1 := by
  rw [toInt_eq_toNat_cond, toNat_one]
  rfl

/-- The maximum unsigned word represents signed −1. -/
theorem toInt_max : max.toInt = -1 := by
  rw [toInt_eq_toNat_cond, toNat_max]
  rfl

/-- Boolean construction has the signed value 0 or 1. -/
theorem toInt_ofBool (b : Bool) : (ofBool b).toInt = if b then 1 else 0 := by
  cases b
  · exact toInt_zero
  · exact toInt_one

/-- Boolean construction agrees with the wrapping numeric constructor. -/
theorem ofBool_eq_ofNat (b : Bool) : ofBool b = ofNat (if b then 1 else 0) := by
  cases b <;> rfl

/-! ### Unsigned order contract -/

/-- Word comparison is exactly comparison of unsigned observations. -/
theorem compare_def (x y : U256) : compare x y = compare x.toNat y.toNat := rfl

/-- A comparison is equal exactly when the words are equal. -/
theorem compare_eq_eq_iff (x y : U256) : compare x y = .eq ↔ x = y := by
  rw [compare_def, Nat.compare_eq_eq, toNat_inj]

/-- A less comparison is exactly unsigned strict order. -/
theorem compare_eq_lt_iff (x y : U256) : compare x y = .lt ↔ x.toNat < y.toNat :=
  Nat.compare_eq_lt

/-- A greater comparison is exactly the reverse unsigned strict order. -/
theorem compare_eq_gt_iff (x y : U256) : compare x y = .gt ↔ y.toNat < x.toNat :=
  Nat.compare_eq_gt

/-- Unsigned word comparison is transitive. -/
instance : Std.TransOrd U256 := inferInstanceAs (Std.TransCmp (compareOn toNat))

/-- Unsigned word comparison reflects word equality. -/
instance : Std.LawfulEqOrd U256 where
  eq_of_compare h := (compare_eq_eq_iff _ _).mp h

end U256
end STFSpec.Base
