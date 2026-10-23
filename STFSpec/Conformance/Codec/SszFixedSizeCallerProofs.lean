/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Structural SSZ sizing through the public equation

Library `EthConformance`. Six private client groups use only the Codec facade,
public constructors, `SszType.fixedSize?_eq` and ordinary core arithmetic/list laws.
Slots below are prospective mathematical widths, without offsets, bytes or schemas.
No codec, source admission, root, positive-width or resource result follows.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–4/§7.
-/

namespace STFSpec.Conformance.Codec.SszFixedSizeCallerProofs

open STFSpec.Codec

-- 1. Arbitrary consequences for all nine constructors.
private theorem uint_case (w : Nat) : (SszType.uint w).fixedSize? = some w := by
  rw [SszType.fixedSize?_eq]
private theorem bool_case : SszType.bool.fixedSize? = some 1 := by
  rw [SszType.fixedSize?_eq]
private theorem vector_case (n : Nat) : (SszType.byteVector n).fixedSize? = some n := by
  rw [SszType.fixedSize?_eq]
private theorem bytes_case (k : Nat) : (SszType.byteList k).fixedSize? = none := by
  rw [SszType.fixedSize?_eq]
private theorem list_case (t : SszType) (k : Nat) : (.list t k : SszType).fixedSize? = none := by
  rw [SszType.fixedSize?_eq]
private theorem progressive_list_case (t : SszType) :
    (.progressiveList t : SszType).fixedSize? = none := by
  rw [SszType.fixedSize?_eq]
private theorem progressive_bytes_case : SszType.progressiveByteList.fixedSize? = none := by
  rw [SszType.fixedSize?_eq]

private def combine (a b : Option Nat) : Option Nat :=
  match a, b with
  | some n, some m => some (n + m)
  | _, _ => none

private def widths (fs : List SszType) : Option Nat :=
  fs.foldr (fun t acc ↦ combine t.fixedSize? acc) (some 0)

private theorem container_case (fs : List SszType) :
    (.container fs : SszType).fixedSize? = widths fs := by
  rw [SszType.fixedSize?_eq]
  rfl
private theorem progressive_container_case (ms : List Bool) (fs : List SszType) :
    (.progressiveContainer ms fs : SszType).fixedSize? = widths fs := by
  rw [SszType.fixedSize?_eq]
  rfl

-- 2. Complete optional sums and arbitrary append composition.
private theorem combine_cases (n m : Nat) :
    combine (some n) (some m) = some (n + m) ∧
    combine none (some m) = none ∧ combine (some n) none = none ∧
    combine none none = none := by
  exact ⟨rfl, rfl, rfl, rfl⟩
private theorem combine_zero_left (a : Option Nat) : combine (some 0) a = a := by
  cases a <;> simp [combine]
private theorem combine_zero_right (a : Option Nat) : combine a (some 0) = a := by
  cases a <;> rfl
private theorem combine_assoc (a b c : Option Nat) :
    combine (combine a b) c = combine a (combine b c) := by
  cases a <;> cases b <;> cases c <;> simp [combine, Nat.add_assoc]
private theorem widths_append (xs ys : List SszType) :
    widths (xs ++ ys) = combine (widths xs) (widths ys) := by
  induction xs with
  | nil => exact (combine_zero_left _).symm
  | cons x xs ih =>
    change combine x.fixedSize? (widths (xs ++ ys)) =
      combine (combine x.fixedSize? (widths xs)) (widths ys)
    rw [ih, combine_assoc]
private theorem empty_containers (ms : List Bool) :
    (SszType.container []).fixedSize? = some 0 ∧
    (SszType.progressiveContainer ms []).fixedSize? = some 0 := by
  rw [container_case, progressive_container_case]
  exact ⟨rfl, rfl⟩
private theorem singleton (t : SszType) :
    (SszType.container [t]).fixedSize? = t.fixedSize? := by
  rw [container_case]
  exact combine_zero_right _
private theorem pair (s t : SszType) :
    (SszType.container [s, t]).fixedSize? = combine s.fixedSize? t.fixedSize? := by
  rw [container_case]
  change combine s.fixedSize? (combine t.fixedSize? (some 0)) = _
  rw [combine_zero_right]
private theorem triple (s t u : SszType) :
    (SszType.container [s, t, u]).fixedSize? =
      combine s.fixedSize? (combine t.fixedSize? u.fixedSize?) := by
  rw [container_case]
  change combine _ (combine _ (combine _ (some 0))) = _
  rw [combine_zero_right]
private theorem pair_fixed (s t : SszType) (n m : Nat)
    (hs : s.fixedSize? = some n) (ht : t.fixedSize? = some m) :
    (SszType.container [s, t]).fixedSize? = some (n + m) := by
  rw [pair, hs, ht]
  rfl
private theorem triple_fixed (s t u : SszType) (n m k : Nat)
    (hs : s.fixedSize? = some n) (ht : t.fixedSize? = some m)
    (hu : u.fixedSize? = some k) :
    (SszType.container [s, t, u]).fixedSize? = some (n + (m + k)) := by
  rw [triple, hs, ht, hu]
  rfl
private theorem container_append (xs ys : List SszType) :
    (SszType.container (xs ++ ys)).fixedSize? =
      combine (SszType.container xs).fixedSize? (SszType.container ys).fixedSize? := by
  rw [container_case, container_case, container_case, widths_append]
private theorem progressive_append (ms ns : List Bool) (xs ys : List SszType) :
    (SszType.progressiveContainer ms (xs ++ ys)).fixedSize? =
      combine (SszType.progressiveContainer ms xs).fixedSize?
        (SszType.progressiveContainer ns ys).fixedSize? := by
  rw [progressive_container_case, progressive_container_case,
    progressive_container_case, widths_append]
private theorem mixed_append (ms : List Bool) (xs ys : List SszType) :
    (SszType.progressiveContainer ms (xs ++ ys)).fixedSize? =
      combine (SszType.container xs).fixedSize? (SszType.container ys).fixedSize? := by
  rw [progressive_container_case, container_case, container_case, widths_append]

private theorem append_empty (fs : List SszType) :
    (SszType.container ([] ++ fs)).fixedSize? = (SszType.container fs).fixedSize? ∧
    (SszType.container (fs ++ [])).fixedSize? = (SszType.container fs).fixedSize? := by
  simp only [List.nil_append, List.append_nil, and_self]
private theorem append_results (xs ys : List SszType) (n m : Nat) :
    ((SszType.container xs).fixedSize? = some n →
      (SszType.container ys).fixedSize? = some m →
      (SszType.container (xs ++ ys)).fixedSize? = some (n + m)) ∧
    ((SszType.container xs).fixedSize? = none →
      (SszType.container (xs ++ ys)).fixedSize? = none) ∧
    ((SszType.container ys).fixedSize? = none →
      (SszType.container (xs ++ ys)).fixedSize? = none) := by
  rw [container_append]
  constructor
  · intro hx hy
    rw [hx, hy]
    rfl
  constructor
  · intro hx
    rw [hx]
    rfl
  · intro hy
    rw [hy]
    cases (SszType.container xs).fixedSize? <;> rfl

-- 3. Mask independence is equality of results only.
private theorem masks (ms ns : List Bool) (fs : List SszType) :
    (SszType.progressiveContainer ms fs).fixedSize? =
      (SszType.progressiveContainer ns fs).fixedSize? ∧
    (SszType.progressiveContainer ns fs).fixedSize? = (SszType.container fs).fixedSize? := by
  simp only [progressive_container_case, container_case, and_self]
private theorem malformed_masks (fs : List SszType) :
    (SszType.progressiveContainer [] fs).fixedSize? =
      (SszType.progressiveContainer [true, false] fs).fixedSize? ∧
    (SszType.progressiveContainer (List.replicate 257 false) fs).fixedSize? =
      (SszType.container fs).fixedSize? := by
  simp only [progressive_container_case, container_case, and_self]

-- 4. List children/limits do not become admission premises.
private theorem variable_lists (s t : SszType) (k l : Nat) :
    (SszType.list s k).fixedSize? = (SszType.list t l).fixedSize? ∧
    (SszType.list t l).fixedSize? = none ∧
    (SszType.progressiveList s).fixedSize? = (SszType.progressiveList t).fixedSize? ∧
    (SszType.progressiveList t).fixedSize? = none := by
  simp only [list_case, progressive_list_case, and_self]
private theorem raw_list_boundaries :
    (SszType.list (.uint 3) 0).fixedSize? = none ∧
    (SszType.list (.progressiveContainer [] [.uint (2 ^ 256 + 17)])
      (2 ^ 256 + 17)).fixedSize? = none := by
  simp only [list_case, and_self]
private theorem variable_left (s t : SszType) (hs : s.fixedSize? = none) :
    (SszType.container [s, t]).fixedSize? = none := by
  rw [pair, hs]
  rfl
private theorem variable_right (s t : SszType) (ht : t.fixedSize? = none) :
    (SszType.container [s, t]).fixedSize? = none := by
  rw [pair, ht]
  cases s.fixedSize? <;> rfl
private theorem triple_variable (s t u : SszType)
    (h : s.fixedSize? = none ∨ t.fixedSize? = none ∨ u.fixedSize? = none) :
    (SszType.container [s, t, u]).fixedSize? = none := by
  rw [triple]
  rcases h with hs | ht | hu
  · rw [hs]
    rfl
  · rw [ht]
    cases s.fixedSize? <;> rfl
  · rw [hu]
    cases s.fixedSize? <;> cases t.fixedSize? <;> rfl
private theorem progressive_variable (ms : List Bool) (s t : SszType) :
    (s.fixedSize? = none ∨ t.fixedSize? = none) →
    (SszType.progressiveContainer ms [s, t]).fixedSize? = none := by
  intro h
  rw [(masks ms ms [s, t]).2]
  rcases h with hs | ht
  · exact variable_left s t hs
  · exact variable_right s t ht
private theorem nested_variable (ms : List Bool) (s t : SszType) (k : Nat) :
    (SszType.container [.container [s, .list t k], s]).fixedSize? = none ∧
    (SszType.progressiveContainer ms [s, .container [.progressiveList t, s]]).fixedSize? =
      none := by
  constructor
  · exact variable_left _ _ (variable_right _ _ (list_case t k))
  · exact progressive_variable _ _ _ (Or.inr (variable_left _ _ (progressive_list_case t)))

-- 5. Prospective field-table slots; these do not serialize offsets or bytes.
private def slot (t : SszType) : Nat :=
  match t.fixedSize? with
  | some n => n
  | none => 4
private def slots (fs : List SszType) : List Nat := fs.map slot
private def tableWidth (fs : List SszType) : Nat := (slots fs).sum
private theorem table_arbitrary (w n limit k : Nat) (t : SszType) :
    tableWidth [.uint w, .byteVector n, .byteList limit, .list t k] = w + n + 8 := by
  simp only [tableWidth, slots, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    slot, uint_case, vector_case, bytes_case, list_case]
  omega
private theorem zero_slots : slots [.byteVector 0, .byteList 0] = [0, 4] := by
  simp only [slots, List.map_cons, List.map_nil, slot, vector_case, bytes_case]
private theorem worked_table :
    slots [.uint 2, .bool, .byteVector 0, .byteList 0, .container [.bool, .byteVector 2],
      .progressiveContainer [] [.uint 3, .byteVector 5]] = [2, 1, 0, 4, 3, 8] ∧
    tableWidth [.uint 2, .bool, .byteVector 0, .byteList 0,
      .container [.bool, .byteVector 2],
      .progressiveContainer [] [.uint 3, .byteVector 5]] = 18 ∧
    (SszType.container [.uint 2, .bool, .byteVector 0, .byteList 0,
      .container [.bool, .byteVector 2],
      .progressiveContainer [] [.uint 3, .byteVector 5]]).fixedSize? = none := by
  simp [slots, tableWidth, slot, container_case, progressive_container_case, widths,
    combine, uint_case, bool_case, vector_case, bytes_case]
private theorem prospective_guest_table :
    slots [.byteVector 32, .bool, .uint 8, .uint 2] = [32, 1, 8, 2] ∧
    tableWidth [.byteVector 32, .bool, .uint 8, .uint 2] = 43 := by
  simp [slots, tableWidth, slot, uint_case, bool_case, vector_case]

-- 6. Sizing supplies no positive divisor or unique zero-width element count.
private theorem fixed_zero (k : Nat) :
    (SszType.byteVector 0).fixedSize? = some 0 ∧
    (SszType.container [.byteVector 0]).fixedSize? = some 0 ∧
    (SszType.list (.byteVector 0) k).fixedSize? = none := by
  rw [vector_case, singleton, vector_case, list_case]
  exact ⟨rfl, rfl, rfl⟩
private theorem positivity_false :
    ¬ (∀ (t : SszType) (n : Nat), t.fixedSize? = some n → 0 < n) := by
  intro h
  exact Nat.lt_irrefl 0 (h (.byteVector 0) 0 (vector_case 0))
private theorem zero_count_ambiguous (k : Nat) :
    k * 0 = 0 ∧ (k + 1) * 0 = 0 ∧ k ≠ k + 1 := by
  omega
private theorem positive_divisor (k n : Nat) (hn : 0 < n) :
    (k * n) / n = k ∧ (k * n) % n = 0 := by
  exact ⟨Nat.mul_div_cancel k hn, Nat.mul_mod_left k n⟩

end STFSpec.Conformance.Codec.SszFixedSizeCallerProofs
