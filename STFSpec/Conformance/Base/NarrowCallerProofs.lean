/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base

/-!
# Narrow unsigned client proofs

Library `EthConformance`: fixed consumer proofs use public observer and operation laws,
without representation unfolding.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §§3–4.
-/

open STFSpec.Base

-- U8: these scripts depend only on its public contract.
example (x : U8) : U8.ofNat x.toNat = x := U8.ofNat_toNat x

example (x : U8) : U8.ofNat? x.toNat = some x := U8.ofNat?_toNat x

example (x y : U8) (h : x.toNat = y.toNat) : x = y := U8.toNat_inj.mp h

example (x y : U8) (h : x.toBitVec = y.toBitVec) : x = y := U8.ext h

example (x : U8) : U8.checkedAdd x U8.zero = some x := by
  apply (U8.checkedAdd_eq_some_iff _ _ _).mpr
  rw [U8.toNat_zero, Nat.add_zero]
  exact ⟨U8.toNat_lt x, rfl⟩

example (x : U8) : U8.checkedSub x x = some U8.zero := by
  apply (U8.checkedSub_eq_some_iff _ _ _).mpr
  rw [U8.toNat_zero, Nat.sub_self]
  exact ⟨Nat.le_refl _, rfl⟩

example : U8.checkedAdd U8.max U8.one = none := by
  apply (U8.checkedAdd_eq_none_iff _ _).mpr
  rw [U8.toNat_max, U8.toNat_one]
  decide

example : U8.checkedSub U8.zero U8.one = none := by
  apply (U8.checkedSub_eq_none_iff _ _).mpr
  rw [U8.toNat_zero, U8.toNat_one]
  decide

example (x : U8) : U8.checkedMul x U8.one = some x := by
  apply (U8.checkedMul_eq_some_iff _ _ _).mpr
  rw [U8.toNat_one, Nat.mul_one]
  exact ⟨U8.toNat_lt x, rfl⟩

example (x y : U8) : U8.wrappingAdd x y = U8.wrappingAdd y x := by
  apply U8.ext
  rw [U8.toBitVec_wrappingAdd, U8.toBitVec_wrappingAdd, BitVec.add_comm]

example (x y : U8) : U8.wrappingSub (U8.wrappingAdd x y) y = x := by
  apply U8.ext
  rw [U8.toBitVec_wrappingSub, U8.toBitVec_wrappingAdd, BitVec.add_sub_cancel]

example (x y : U8) (h : U8.checkedSub x y = none) : x.toNat < y.toNat :=
  (U8.checkedSub_eq_none_iff _ _).mp h

example (x y : U8) (h : compare x y = .eq) : x = y :=
  (U8.compare_eq_eq_iff _ _).mp h

example : Std.TransOrd U8 := inferInstance

example : Std.LawfulEqOrd U8 := inferInstance

-- U16: these scripts depend only on its public contract.
example (x : U16) : U16.ofNat x.toNat = x := U16.ofNat_toNat x

example (x : U16) : U16.ofNat? x.toNat = some x := U16.ofNat?_toNat x

example (x y : U16) (h : x.toNat = y.toNat) : x = y := U16.toNat_inj.mp h

example (x y : U16) (h : x.toBitVec = y.toBitVec) : x = y := U16.ext h

example (x : U16) : U16.checkedAdd x U16.zero = some x := by
  apply (U16.checkedAdd_eq_some_iff _ _ _).mpr
  rw [U16.toNat_zero, Nat.add_zero]
  exact ⟨U16.toNat_lt x, rfl⟩

example (x : U16) : U16.checkedSub x x = some U16.zero := by
  apply (U16.checkedSub_eq_some_iff _ _ _).mpr
  rw [U16.toNat_zero, Nat.sub_self]
  exact ⟨Nat.le_refl _, rfl⟩

example : U16.checkedAdd U16.max U16.one = none := by
  apply (U16.checkedAdd_eq_none_iff _ _).mpr
  rw [U16.toNat_max, U16.toNat_one]
  decide

example : U16.checkedSub U16.zero U16.one = none := by
  apply (U16.checkedSub_eq_none_iff _ _).mpr
  rw [U16.toNat_zero, U16.toNat_one]
  decide

example (x : U16) : U16.checkedMul x U16.one = some x := by
  apply (U16.checkedMul_eq_some_iff _ _ _).mpr
  rw [U16.toNat_one, Nat.mul_one]
  exact ⟨U16.toNat_lt x, rfl⟩

example (x y : U16) : U16.wrappingAdd x y = U16.wrappingAdd y x := by
  apply U16.ext
  rw [U16.toBitVec_wrappingAdd, U16.toBitVec_wrappingAdd, BitVec.add_comm]

example (x y : U16) : U16.wrappingSub (U16.wrappingAdd x y) y = x := by
  apply U16.ext
  rw [U16.toBitVec_wrappingSub, U16.toBitVec_wrappingAdd, BitVec.add_sub_cancel]

example (x y : U16) (h : U16.checkedSub x y = none) : x.toNat < y.toNat :=
  (U16.checkedSub_eq_none_iff _ _).mp h

example (x y : U16) (h : compare x y = .eq) : x = y :=
  (U16.compare_eq_eq_iff _ _).mp h

example : Std.TransOrd U16 := inferInstance

example : Std.LawfulEqOrd U16 := inferInstance

-- U32: these scripts depend only on its public contract.
example (x : U32) : U32.ofNat x.toNat = x := U32.ofNat_toNat x

example (x : U32) : U32.ofNat? x.toNat = some x := U32.ofNat?_toNat x

example (x y : U32) (h : x.toNat = y.toNat) : x = y := U32.toNat_inj.mp h

example (x y : U32) (h : x.toBitVec = y.toBitVec) : x = y := U32.ext h

example (x : U32) : U32.checkedAdd x U32.zero = some x := by
  apply (U32.checkedAdd_eq_some_iff _ _ _).mpr
  rw [U32.toNat_zero, Nat.add_zero]
  exact ⟨U32.toNat_lt x, rfl⟩

example (x : U32) : U32.checkedSub x x = some U32.zero := by
  apply (U32.checkedSub_eq_some_iff _ _ _).mpr
  rw [U32.toNat_zero, Nat.sub_self]
  exact ⟨Nat.le_refl _, rfl⟩

example : U32.checkedAdd U32.max U32.one = none := by
  apply (U32.checkedAdd_eq_none_iff _ _).mpr
  rw [U32.toNat_max, U32.toNat_one]
  decide

example : U32.checkedSub U32.zero U32.one = none := by
  apply (U32.checkedSub_eq_none_iff _ _).mpr
  rw [U32.toNat_zero, U32.toNat_one]
  decide

example (x : U32) : U32.checkedMul x U32.one = some x := by
  apply (U32.checkedMul_eq_some_iff _ _ _).mpr
  rw [U32.toNat_one, Nat.mul_one]
  exact ⟨U32.toNat_lt x, rfl⟩

example (x y : U32) : U32.wrappingAdd x y = U32.wrappingAdd y x := by
  apply U32.ext
  rw [U32.toBitVec_wrappingAdd, U32.toBitVec_wrappingAdd, BitVec.add_comm]

example (x y : U32) : U32.wrappingSub (U32.wrappingAdd x y) y = x := by
  apply U32.ext
  rw [U32.toBitVec_wrappingSub, U32.toBitVec_wrappingAdd, BitVec.add_sub_cancel]

example (x y : U32) (h : U32.checkedSub x y = none) : x.toNat < y.toNat :=
  (U32.checkedSub_eq_none_iff _ _).mp h

example (x y : U32) (h : compare x y = .eq) : x = y :=
  (U32.compare_eq_eq_iff _ _).mp h

example : Std.TransOrd U32 := inferInstance

example : Std.LawfulEqOrd U32 := inferInstance

-- U64: these scripts depend only on its public contract.
example (x : U64) : U64.ofNat x.toNat = x := U64.ofNat_toNat x

example (x : U64) : U64.ofNat? x.toNat = some x := U64.ofNat?_toNat x

example (x y : U64) (h : x.toNat = y.toNat) : x = y := U64.toNat_inj.mp h

example (x y : U64) (h : x.toBitVec = y.toBitVec) : x = y := U64.ext h

example (x : U64) : U64.checkedAdd x U64.zero = some x := by
  apply (U64.checkedAdd_eq_some_iff _ _ _).mpr
  rw [U64.toNat_zero, Nat.add_zero]
  exact ⟨U64.toNat_lt x, rfl⟩

example (x : U64) : U64.checkedSub x x = some U64.zero := by
  apply (U64.checkedSub_eq_some_iff _ _ _).mpr
  rw [U64.toNat_zero, Nat.sub_self]
  exact ⟨Nat.le_refl _, rfl⟩

example : U64.checkedAdd U64.max U64.one = none := by
  apply (U64.checkedAdd_eq_none_iff _ _).mpr
  rw [U64.toNat_max, U64.toNat_one]
  decide

example : U64.checkedSub U64.zero U64.one = none := by
  apply (U64.checkedSub_eq_none_iff _ _).mpr
  rw [U64.toNat_zero, U64.toNat_one]
  decide

example (x : U64) : U64.checkedMul x U64.one = some x := by
  apply (U64.checkedMul_eq_some_iff _ _ _).mpr
  rw [U64.toNat_one, Nat.mul_one]
  exact ⟨U64.toNat_lt x, rfl⟩

example (x y : U64) : U64.wrappingAdd x y = U64.wrappingAdd y x := by
  apply U64.ext
  rw [U64.toBitVec_wrappingAdd, U64.toBitVec_wrappingAdd, BitVec.add_comm]

example (x y : U64) : U64.wrappingSub (U64.wrappingAdd x y) y = x := by
  apply U64.ext
  rw [U64.toBitVec_wrappingSub, U64.toBitVec_wrappingAdd, BitVec.add_sub_cancel]

example (x y : U64) (h : U64.checkedSub x y = none) : x.toNat < y.toNat :=
  (U64.checkedSub_eq_none_iff _ _).mp h

example (x y : U64) (h : compare x y = .eq) : x = y :=
  (U64.compare_eq_eq_iff _ _).mp h

example : Std.TransOrd U64 := inferInstance

example : Std.LawfulEqOrd U64 := inferInstance
