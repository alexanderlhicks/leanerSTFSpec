/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.Bytes
import Init.Data.Ord

/-!
# Packed byte-content comparison

Library `EthBase`. Unsigned lexicographic order with a proper prefix first.
An ordinary equality theorem connects the direct bounded packed scan to its
legible List model on every finite sequence; existing equality is retained.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §3/§5/§7 (Q54).
-/

namespace STFSpec.Base.Bytes

-- The scan uses bounded packed access; it never constructs either list model.
private def byteAt (a : Bytes) (i : Nat) : UInt8 :=
  if hi : i < a.size then a[i] else 0

private def compareScan (a b : Bytes) : Nat → Nat → Ordering
  | 0, _ => Ord.compare a.size b.size
  | remaining + 1, i =>
    match Ord.compare (byteAt a i) (byteAt b i) with
    | .lt => .lt
    | .eq => compareScan a b remaining (i + 1)
    | .gt => .gt

/-- Legible unsigned byte-lexicographic model, with a proper prefix first.
Corresponds to inherited builtin bytes ordering, `ethereum_types/bytes.py:165` (0.4.1). -/
def compareReference (a b : Bytes) : Ordering := Ord.compare a.toList b.toList

/-- Compare packed bytes directly, stopping at the first mismatch or shared end.
Every finite sequence participates; leading zeros are significant. -/
def compare (a b : Bytes) : Ordering :=
  compareScan a b (min a.size b.size) 0

private theorem compareScan_model (a b : Bytes) (remaining i : Nat)
    (h : remaining + i = min a.size b.size) :
    compareScan a b remaining i = Ord.compare (a.toList.drop i) (b.toList.drop i) := by
  induction remaining generalizing i with
  | zero =>
    by_cases hlt : a.size < b.size
    · have ha : a.toList.drop i = [] := by
        apply List.drop_of_length_le
        rw [Bytes.length_toList]
        omega
      have hb : b.toList.drop i ≠ [] := by
        intro he
        have hl := congrArg List.length he
        simp only [List.length_drop, Bytes.length_toList, List.length_nil] at hl
        omega
      rw [compareScan, ha]
      cases he : b.toList.drop i with
      | nil => exact False.elim (hb he)
      | cons x xs => simpa only [List.compare_nil_cons] using (Nat.compare_eq_lt.mpr hlt)
    · by_cases heq : a.size = b.size
      · have ha : a.toList.drop i = [] := by
          apply List.drop_of_length_le
          rw [Bytes.length_toList]
          omega
        have hb : b.toList.drop i = [] := by
          apply List.drop_of_length_le
          rw [Bytes.length_toList]
          omega
        simp [compareScan, ha, hb, heq]
      · have hgt : b.size < a.size := by omega
        have hb : b.toList.drop i = [] := by
          apply List.drop_of_length_le
          rw [Bytes.length_toList]
          omega
        have ha : a.toList.drop i ≠ [] := by
          intro he
          have hl := congrArg List.length he
          simp only [List.length_drop, Bytes.length_toList, List.length_nil] at hl
          omega
        rw [compareScan, hb]
        cases he : a.toList.drop i with
        | nil => exact False.elim (ha he)
        | cons x xs => simpa only [List.compare_cons_nil] using (Nat.compare_eq_gt.mpr hgt)
  | succ remaining ih =>
    have ha : i < a.size := by omega
    have hb : i < b.size := by omega
    have ea : a.toList.drop i = a[i] :: a.toList.drop (i + 1) := by
      rw [← List.getElem_cons_drop (by rw [Bytes.length_toList]; exact ha),
        Bytes.getElem_toList a i ha]
    have eb : b.toList.drop i = b[i] :: b.toList.drop (i + 1) := by
      rw [← List.getElem_cons_drop (by rw [Bytes.length_toList]; exact hb),
        Bytes.getElem_toList b i hb]
    rw [compareScan, ea, eb, List.compare_cons_cons]
    simp only [byteAt, dite_eq_left ha, dite_eq_left hb]
    cases hc : Ord.compare a[i] b[i] with
    | lt => rfl
    | gt => rfl
    | eq => exact ih (i + 1) (by omega)

/-- Packed comparison equals the legible model for every finite pair. -/
theorem compare_eq_reference (a b : Bytes) :
    compare a b = compareReference a b := by
  rw [compare, compareReference, compareScan_model a b _ _ (by omega)]
  simp only [List.drop_zero]

/-- Byte-content order on every finite byte sequence, including empty values. -/
instance : Ord Bytes where compare := compare

/-- The public order commutes with the stable byte-list observation. -/
theorem compare_toList (a b : Bytes) : Ord.compare a b = Ord.compare a.toList b.toList :=
  compare_eq_reference a b

/-- Transitivity and orientation transfer from the stable List model. -/
instance : Std.TransOrd Bytes where
  eq_swap := by
    intro a b
    rw [compare_toList, compare_toList]
    exact Std.OrientedCmp.eq_swap
  isLE_trans := by
    intro a b c hab hbc
    rw [compare_toList] at hab hbc ⊢
    exact Std.TransCmp.isLE_trans hab hbc

/-- Comparison equality is the existing byte-content equality. -/
instance : Std.LawfulEqOrd Bytes where
  compare_self := by
    intro a
    rw [compare_toList]
    exact Std.ReflCmp.compare_self
  eq_of_compare := by
    intro a b h
    rw [compare_toList] at h
    exact Bytes.ext (Std.LawfulEqCmp.eq_of_compare h)

/-- Equal comparison results are equivalent to actual Bytes equality. -/
theorem compare_eq_eq_iff (a b : Bytes) : Ord.compare a b = .eq ↔ a = b :=
  Std.LawfulEqOrd.compare_eq_iff_eq

-- Ordinary core bridge needed because ByteArray.toList uses a reverse accumulator.
private theorem core_toList_loop (b : ByteArray) (n i : Nat) (r : List UInt8)
    (h : n + i = b.size) :
    ByteArray.toList.loop b i r = r.reverse ++ b.data.toList.drop i := by
  induction n generalizing i r with
  | zero =>
    have hi : ¬ i < b.size := by omega
    rw [ByteArray.toList.loop, ite_eq_right hi]
    rw [List.drop_of_length_le
      (by simp only [Array.length_toList, ByteArray.size] at *; omega), List.append_nil]
  | succ n ih =>
    have hi : i < b.size := by omega
    rw [ByteArray.toList.loop, ite_eq_left hi, ih (i + 1) _ (by omega)]
    rw [List.reverse_cons, List.append_assoc]
    congr 1
    rw (occs := [2]) [← List.getElem_cons_drop
      (by simpa only [Array.length_toList, ByteArray.size] using hi)]
    simp only [List.singleton_append, ByteArray.get!, Array.getElem!_eq_getD,
      Array.getD_eq_getD_getElem?, getElem?_pos b.data i hi, Option.getD_some,
      Array.getElem_toList]

/-- Core packed export list observation agrees with the stable Bytes model. -/
theorem toByteArray_toList (a : Bytes) : a.toByteArray.toList = a.toList := by
  rw [show a.toByteArray.toList = a.toByteArray.data.toList from
    core_toList_loop a.toByteArray a.toByteArray.size 0 [] (Nat.add_zero _)]
  exact Bytes.toList_toByteArray a

end STFSpec.Base.Bytes
