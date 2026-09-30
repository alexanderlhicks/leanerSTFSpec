/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

/-!
# U8 values and arithmetic

Library `EthBase`: private `UInt8` storage, stable unsigned observers and lawful
ordering, wrapping arithmetic and checked Python-operator arithmetic. Consumers
use the public model laws.

Spec guidance: `STFSpec/informal/modules/EthBase.md`.
Dependency citations refer to `ethereum-types` 0.4.1 at the pin in `reference.toml`.
-/

namespace STFSpec.Base

/-- An unsigned 8-bit value; `ethereum_types/numeric.py:716` (`U8`). -/
structure U8 where
  private ofUIntRaw ::
  /-- Internal executable storage; consumers use `toNat` and `toBitVec`. -/
  private val : UInt8

namespace U8

/-- Stable unsigned observer; `ethereum_types/numeric.py:321` (`__int__`). -/
def toNat (x : U8) : Nat := x.val.toNat

/-- Stable reference-model observer. -/
def toBitVec (x : U8) : BitVec 8 := x.val.toBitVec

/-- Reduce a natural input modulo 2^8. This model helper is distinct from
checked Python `U8(n)` (`ethereum_types/numeric.py:44,611`). -/
def ofNat (n : Nat) : U8 := ofUIntRaw (UInt8.ofNat n)

/-- Checked Python construction on natural inputs; `ethereum_types/numeric.py:44,611`.
Unsigned overflow returns `none`; the caller maps it to its error under D14. -/
def ofNat? (n : Nat) : Option U8 :=
  if n < 2 ^ 8 then some (ofNat n) else none

/-- Zero; `ethereum_types/numeric.py:44` with input 0. -/
def zero : U8 := ofNat 0

/-- One; `ethereum_types/numeric.py:44` with input 1. -/
def one : U8 := ofNat 1

/-- Maximum unsigned value; `ethereum_types/numeric.py:738–739` (`MAX_VALUE`). -/
def max : U8 := ofNat (2 ^ 8 - 1)

/-- Unsigned numeric order; `ethereum_types/numeric.py:343–369`. -/
instance : Ord U8 where
  compare := compareOn toNat

/-! ### Observer and constructor contract -/

/-- Unsigned observations agree with the bit-vector model. -/
theorem toNat_def (x : U8) : x.toNat = x.toBitVec.toNat := rfl

/-- Equal unsigned observations determine equal values. -/
theorem toNat_inj {x y : U8} : x.toNat = y.toNat ↔ x = y := by
  constructor
  · intro h
    have hv : x.val = y.val := UInt8.toNat_inj.mp h
    cases x
    cases y
    cases hv
    rfl
  · exact congrArg toNat

/-- Equal bit-vector observations determine equal values. -/
@[ext] theorem ext {x y : U8} (h : x.toBitVec = y.toBitVec) : x = y :=
  toNat_inj.mp (congrArg BitVec.toNat h)

/-- The bit-vector observer is injective. -/
theorem toBitVec_inj {x y : U8} : x.toBitVec = y.toBitVec ↔ x = y :=
  ⟨ext, congrArg toBitVec⟩

/-- Equality of same-width values is numeric equality;
`ethereum_types/numeric.py:325` (`__eq__`). -/
instance : DecidableEq U8 := fun x y ↦
  decidable_of_iff (x.toNat = y.toNat) toNat_inj

/-- Every unsigned observation is strictly below 2^8. -/
theorem toNat_lt (x : U8) : x.toNat < 2 ^ 8 := UInt8.toNat_lt_size x.val

/-- Wrapping construction commutes with the bit-vector model. -/
theorem toBitVec_ofNat (n : Nat) : (ofNat n).toBitVec = BitVec.ofNat 8 n := rfl

/-- Wrapping construction is exact modular reduction. -/
theorem toNat_ofNat (n : Nat) : (ofNat n).toNat = n % 2 ^ 8 :=
  UInt8.toNat_ofNat'

/-- In-range wrapping construction retains its unsigned input. -/
theorem toNat_ofNat_of_lt {n : Nat} (h : n < 2 ^ 8) : (ofNat n).toNat = n := by
  rw [toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Constructing from any bit-vector's unsigned observation returns that model. -/
theorem toBitVec_ofNat_toNat (bits : BitVec 8) :
    (ofNat bits.toNat).toBitVec = bits := by
  rw [toBitVec_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Reconstructing a value from its unsigned observation returns that value. -/
theorem ofNat_toNat (x : U8) : ofNat x.toNat = x := by
  apply toNat_inj.mp
  rw [toNat_ofNat, Nat.mod_eq_of_lt (toNat_lt x)]

/-- Checked construction succeeds exactly with the original unsigned value. -/
theorem ofNat?_eq_some_iff (n : Nat) (x : U8) :
    ofNat? n = some x ↔ n < 2 ^ 8 ∧ x.toNat = n := by
  unfold ofNat?
  split
  next h =>
    simp only [Option.some.injEq]
    constructor
    · intro hx
      subst x
      exact ⟨h, toNat_ofNat_of_lt h⟩
    · intro hx
      apply toNat_inj.mp
      rw [toNat_ofNat_of_lt h, hx.2]
  next h => simp [h]

/-- Checked construction fails exactly on unsigned overflow. -/
theorem ofNat?_eq_none_iff (n : Nat) : ofNat? n = none ↔ 2 ^ 8 ≤ n := by
  simp [ofNat?, Nat.not_lt]

/-- Checked reconstruction succeeds for every unsigned observation. -/
theorem ofNat?_toNat (x : U8) : ofNat? x.toNat = some x :=
  (ofNat?_eq_some_iff _ _).mpr ⟨toNat_lt x, rfl⟩

/-- Zero has unsigned observation 0. -/
theorem toNat_zero : zero.toNat = 0 := rfl

/-- One has unsigned observation 1. -/
theorem toNat_one : one.toNat = 1 := rfl

/-- Maximum has unsigned observation 2^8−1. -/
theorem toNat_max : max.toNat = 2 ^ 8 - 1 := rfl

/-! ### Unsigned order contract -/

/-- Comparison is exactly comparison of unsigned observations. -/
theorem compare_def (x y : U8) : compare x y = compare x.toNat y.toNat := rfl

/-- Equal comparison reflects value equality. -/
theorem compare_eq_eq_iff (x y : U8) : compare x y = .eq ↔ x = y := by
  rw [compare_def, Nat.compare_eq_eq, toNat_inj]

/-- Less comparison is unsigned strict order. -/
theorem compare_eq_lt_iff (x y : U8) : compare x y = .lt ↔ x.toNat < y.toNat :=
  Nat.compare_eq_lt

/-- Greater comparison is reverse unsigned strict order. -/
theorem compare_eq_gt_iff (x y : U8) : compare x y = .gt ↔ y.toNat < x.toNat :=
  Nat.compare_eq_gt

/-- Unsigned comparison is transitive. -/
instance : Std.TransOrd U8 := inferInstanceAs (Std.TransCmp (compareOn toNat))

/-- Unsigned comparison reflects equality. -/
instance : Std.LawfulEqOrd U8 where
  eq_of_compare h := (compare_eq_eq_iff _ _).mp h

/-! ### Wrapping arithmetic -/

/-- Wrapping addition; `ethereum_types/numeric.py:614` (`wrapping_add`). -/
def wrappingAdd (a b : U8) : U8 := ofUIntRaw (a.val + b.val)

/-- Wrapping subtraction; `ethereum_types/numeric.py:625` (`wrapping_sub`). -/
def wrappingSub (a b : U8) : U8 := ofUIntRaw (a.val - b.val)

/-- Wrapping multiplication; `ethereum_types/numeric.py:636` (`wrapping_mul`). -/
def wrappingMul (a b : U8) : U8 := ofUIntRaw (a.val * b.val)

/-- Wrapping addition commutes with the bit-vector reference. -/
theorem toBitVec_wrappingAdd (a b : U8) :
    (wrappingAdd a b).toBitVec = a.toBitVec + b.toBitVec := rfl

/-- Wrapping subtraction commutes with the bit-vector reference. -/
theorem toBitVec_wrappingSub (a b : U8) :
    (wrappingSub a b).toBitVec = a.toBitVec - b.toBitVec := rfl

/-- Wrapping multiplication commutes with the bit-vector reference. -/
theorem toBitVec_wrappingMul (a b : U8) :
    (wrappingMul a b).toBitVec = a.toBitVec * b.toBitVec := rfl

/-- Wrapping addition reduces the unbounded sum. -/
theorem toNat_wrappingAdd (a b : U8) :
    (wrappingAdd a b).toNat = (a.toNat + b.toNat) % 2 ^ 8 :=
  UInt8.toNat_add _ _

/-- Wrapping subtraction reduces the modular difference. -/
theorem toNat_wrappingSub (a b : U8) :
    (wrappingSub a b).toNat = (2 ^ 8 - b.toNat + a.toNat) % 2 ^ 8 :=
  UInt8.toNat_sub _ _

/-- Wrapping multiplication reduces the unbounded product. -/
theorem toNat_wrappingMul (a b : U8) :
    (wrappingMul a b).toNat = (a.toNat * b.toNat) % 2 ^ 8 :=
  UInt8.toNat_mul _ _

/-! ### Checked arithmetic -/

/-- Checked addition; `ethereum_types/numeric.py:91,44,611`.
The unreduced sum is checked before any wrapping result is returned. -/
def checkedAdd (a b : U8) : Option U8 :=
  if a.toNat + b.toNat < 2 ^ 8 then some (wrappingAdd a b) else none

/-- Checked subtraction; `ethereum_types/numeric.py:103`.
Underflow returns `none`; otherwise the result is the exact difference. -/
def checkedSub (a b : U8) : Option U8 :=
  if b.toNat ≤ a.toNat then some (wrappingSub a b) else none

/-- Checked multiplication; `ethereum_types/numeric.py:131,44,611`.
The unreduced product is checked before any wrapping result is returned. -/
def checkedMul (a b : U8) : Option U8 :=
  if a.toNat * b.toNat < 2 ^ 8 then some (wrappingMul a b) else none

/-- Checked addition succeeds exactly when the unreduced sum fits. -/
theorem checkedAdd_eq_some_iff (a b c : U8) :
    checkedAdd a b = some c ↔ a.toNat + b.toNat < 2 ^ 8 ∧
      c.toNat = a.toNat + b.toNat := by
  rw [checkedAdd, Option.ite_none_right_eq_some, Option.some.injEq,
    ← toNat_inj, toNat_wrappingAdd]
  apply and_congr_right
  intro h
  rw [Nat.mod_eq_of_lt h, eq_comm]

/-- Checked addition fails exactly on unsigned overflow. -/
theorem checkedAdd_eq_none_iff (a b : U8) :
    checkedAdd a b = none ↔ 2 ^ 8 ≤ a.toNat + b.toNat := by
  simp [checkedAdd, Nat.not_lt]

/-- Checked subtraction succeeds exactly without underflow. -/
theorem checkedSub_eq_some_iff (a b c : U8) :
    checkedSub a b = some c ↔ b.toNat ≤ a.toNat ∧ c.toNat = a.toNat - b.toNat := by
  rw [checkedSub, Option.ite_none_right_eq_some, Option.some.injEq, ← toNat_inj]
  apply and_congr_right
  intro h
  rw [show (wrappingSub a b).toNat = a.toNat - b.toNat from
    UInt8.toNat_sub_of_le _ _ h, eq_comm]

/-- Checked subtraction fails exactly on underflow. -/
theorem checkedSub_eq_none_iff (a b : U8) :
    checkedSub a b = none ↔ a.toNat < b.toNat := by
  simp [checkedSub, Nat.not_le]

/-- Checked multiplication succeeds exactly when the unreduced product fits. -/
theorem checkedMul_eq_some_iff (a b c : U8) :
    checkedMul a b = some c ↔ a.toNat * b.toNat < 2 ^ 8 ∧
      c.toNat = a.toNat * b.toNat := by
  rw [checkedMul, Option.ite_none_right_eq_some, Option.some.injEq,
    ← toNat_inj, toNat_wrappingMul]
  apply and_congr_right
  intro h
  rw [Nat.mod_eq_of_lt h, eq_comm]

/-- Checked multiplication fails exactly on unsigned overflow. -/
theorem checkedMul_eq_none_iff (a b : U8) :
    checkedMul a b = none ↔ 2 ^ 8 ≤ a.toNat * b.toNat := by
  simp [checkedMul, Nat.not_lt]

end U8
end STFSpec.Base
