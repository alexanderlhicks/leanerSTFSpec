/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Local SSZ root-support controls

Library `EthConformance`. rootableP0–rootableP9 are private complete propositions, using only the
Codec facade and its public laws. Count ceilings are symbolic; no huge payload is
allocated. No source execution, class admission, root result or security claim.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–4/§7.
-/

namespace STFSpec.Conformance.Codec

open STFSpec.Codec

private theorem rootableP0 (t : SszType) (v : SszValue) :
    Ssz.Rootable t v ↔
      match t, v with
      | .uint w, .uint n =>
          w ∈ [1, 2, 4, 8, 16, 32] ∧ n < 2 ^ (8 * w)
      | .bool, .bool _ => True
      | .byteVector n, .bytes b => b.size = n
      | .byteList limit, .bytes b =>
          b.size ≤ limit ∧ b.size < 2 ^ 256
      | .list elem limit, .list xs =>
          xs.length ≤ limit ∧
          xs.length < 2 ^ 256 ∧
          (∀ x ∈ xs, Ssz.Rootable elem x) ∧
          match elem with
          | .uint w => w ∈ [1, 2, 4, 8, 16, 32]
          | .bool => True
          | .byteVector _ | .byteList _ | .list _ _ | .progressiveList _ |
            .progressiveByteList | .container _ | .progressiveContainer _ _ => True
      | .progressiveList elem, .list xs =>
          xs.length < 2 ^ 256 ∧
          (∀ x ∈ xs, Ssz.Rootable elem x) ∧
          match elem with
          | .uint w => w ∈ [1, 2, 4, 8, 16, 32]
          | .bool => True
          | .byteVector _ | .byteList _ | .list _ _ | .progressiveList _ |
            .progressiveByteList | .container _ | .progressiveContainer _ _ => True
      | .progressiveByteList, .bytes b => b.size < 2 ^ 256
      | .container fields, .container xs =>
          fields ≠ [] ∧
          fields.length = xs.length ∧
          ∀ pair ∈ fields.zip xs, Ssz.Rootable pair.1 pair.2
      | .progressiveContainer mask fields, .container xs =>
          mask.getLast? = some true ∧
          mask.length ≤ 256 ∧
          (mask.filter id).length = fields.length ∧
          fields.length = xs.length ∧
          ∀ pair ∈ fields.zip xs, Ssz.Rootable pair.1 pair.2
      | _, _ => False := Ssz.rootable_iff t v

-- rootableP1: the complete scalar range, concrete width set, and exact boundary.
private theorem rootableP1_uint (w n : Nat) :
    Ssz.Rootable (.uint w) (.uint n) ↔
      w ∈ [1, 2, 4, 8, 16, 32] ∧ n < 2 ^ (8 * w) := Ssz.rootable_iff _ _

private theorem rootableP1_widths :
    Ssz.Rootable (.uint 1) (.uint 0) ∧ Ssz.Rootable (.uint 2) (.uint 0) ∧
    Ssz.Rootable (.uint 4) (.uint 0) ∧ Ssz.Rootable (.uint 8) (.uint 0) ∧
    Ssz.Rootable (.uint 16) (.uint 0) ∧ Ssz.Rootable (.uint 32) (.uint 0) ∧
    ¬ Ssz.Rootable (.uint 0) (.uint 0) ∧ ¬ Ssz.Rootable (.uint 3) (.uint 0) := by
  simp [Ssz.rootable_iff (.uint _) (.uint _)]

private theorem rootableP1_large (w n : Nat) (hw : 32 < w) :
    ¬ Ssz.Rootable (.uint w) (.uint n) := by
  rw [rootableP1_uint]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

private theorem rootableP1_boundary (w : Nat) (hw : w ∈ [1, 2, 4, 8, 16, 32]) :
    Ssz.Rootable (.uint w) (.uint (2 ^ (8 * w) - 1)) ∧
    ¬ Ssz.Rootable (.uint w) (.uint (2 ^ (8 * w))) := by
  have hp : 0 < 2 ^ (8 * w) := Nat.two_pow_pos _
  simp only [rootableP1_uint, hw, true_and, Nat.lt_irrefl, and_false, not_false_eq_true, and_true]
  omega

private theorem rootableP1_bool (b : Bool) :
    Ssz.Rootable .bool (.bool b) ∧ ¬ Ssz.Rootable .bool (.uint 0) ∧
    ¬ Ssz.Rootable (.uint 1) (.bool b) := by
  simp only [Ssz.rootable_iff .bool _, Ssz.rootable_iff (.uint 1) (.bool _),
    not_false_eq_true, and_self]

-- rootableP2: vectors have exact lengths, with no added count-mix-in bound.
private theorem rootableP2 (n limit : Nat) (b : ByteArray) :
    (Ssz.Rootable (.byteVector n) (.bytes b) ↔ b.size = n) ∧
    Ssz.Rootable (.byteVector b.size) (.bytes b) ∧
    (Ssz.Rootable (.byteList limit) (.bytes b) ↔
      b.size ≤ limit ∧ b.size < 2 ^ 256) := by
  simp only [Ssz.rootable_iff (.byteVector _) (.bytes _),
    Ssz.rootable_iff (.byteList _) (.bytes _), iff_self, and_self]

private theorem rootableP2_zero :
    Ssz.Rootable (.byteVector 0) (.bytes ByteArray.empty) ∧
    Ssz.Rootable (.byteList 0) (.bytes ByteArray.empty) ∧
    ¬ Ssz.Rootable (.byteList 0) (.bytes (ByteArray.mk #[0])) := by
  simp [Ssz.rootable_iff (.byteVector _) (.bytes _),
    Ssz.rootable_iff (.byteList _) (.bytes _)] <;> decide

-- rootableP3: actual element count is independent of basic byte-packing classification.
private theorem rootableP3_list (elem : SszType) (limit : Nat) (xs : List SszValue) :
    Ssz.Rootable (.list elem limit) (.list xs) ↔
      xs.length ≤ limit ∧ Ssz.Rootable (.progressiveList elem) (.list xs) := by
  rw [Ssz.rootable_iff (.list _ _) (.list _),
    Ssz.rootable_iff (.progressiveList _) (.list _)]

private theorem rootableP3_basic (w limit : Nat) :
    (Ssz.Rootable (.list (.uint w) limit) (.list []) ↔
      w ∈ [1, 2, 4, 8, 16, 32]) ∧
    (Ssz.Rootable (.progressiveList (.uint w)) (.list []) ↔
      w ∈ [1, 2, 4, 8, 16, 32]) := by
  simp [Ssz.rootable_iff (.list _ _) (.list _),
    Ssz.rootable_iff (.progressiveList _) (.list _)]

private theorem rootableP3_bool_vector (limit : Nat) (xs : List SszValue) (n : Nat) :
    (Ssz.Rootable (.list .bool limit) (.list xs) ↔
      xs.length ≤ limit ∧ xs.length < 2 ^ 256 ∧
        ∀ x ∈ xs, Ssz.Rootable .bool x) ∧
    (Ssz.Rootable (.list (.byteVector n) limit) (.list xs) ↔
      xs.length ≤ limit ∧ xs.length < 2 ^ 256 ∧
        ∀ x ∈ xs, Ssz.Rootable (.byteVector n) x) ∧
    SszType.bool ≠ SszType.byteVector n := by
  simp [Ssz.rootable_iff (.list _ _) (.list _)]

private theorem rootableP3_children (elem : SszType) (limit : Nat) (xs : List SszValue)
    (h : Ssz.Rootable (.list elem limit) (.list xs)) :
    xs.length ≤ limit ∧ xs.length < 2 ^ 256 ∧ ∀ x ∈ xs, Ssz.Rootable elem x := by
  have hs := (Ssz.rootable_iff _ _).mp h
  exact ⟨hs.1, hs.2.1, hs.2.2.1⟩

-- rootableP4: progressive lists have actual counts/children, without an ordinary cap.
private theorem rootableP4_progressive (elem : SszType) (xs : List SszValue) (b : ByteArray) :
    (Ssz.Rootable (.progressiveList elem) (.list xs) ↔
      xs.length < 2 ^ 256 ∧ (∀ x ∈ xs, Ssz.Rootable elem x) ∧
      match elem with
      | .uint w => w ∈ [1, 2, 4, 8, 16, 32]
      | .bool => True
      | .byteVector _ | .byteList _ | .list _ _ | .progressiveList _ |
        .progressiveByteList | .container _ | .progressiveContainer _ _ => True) ∧
    (Ssz.Rootable .progressiveByteList (.bytes b) ↔ b.size < 2 ^ 256) :=
  ⟨Ssz.rootable_iff _ _, Ssz.rootable_iff _ _⟩

private theorem rootableP4_ceilings (elem : SszType) (limit : Nat)
    (xs : List SszValue) (b : ByteArray) :
    (2 ^ 256 ≤ b.size → ¬ Ssz.Rootable (.byteList limit) (.bytes b)) ∧
    (2 ^ 256 ≤ b.size → ¬ Ssz.Rootable .progressiveByteList (.bytes b)) ∧
    (2 ^ 256 ≤ xs.length → ¬ Ssz.Rootable (.list elem limit) (.list xs)) ∧
    (2 ^ 256 ≤ xs.length → ¬ Ssz.Rootable (.progressiveList elem) (.list xs)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hn h; exact Nat.not_lt_of_ge hn ((Ssz.rootable_iff _ _).mp h).2
  · intro hn h; exact Nat.not_lt_of_ge hn ((Ssz.rootable_iff _ _).mp h)
  · intro hn h; exact Nat.not_lt_of_ge hn ((Ssz.rootable_iff _ _).mp h).2.1
  · intro hn h; exact Nat.not_lt_of_ge hn ((Ssz.rootable_iff _ _).mp h).1

-- rootableP5: ordinary fields have no extra count bound and cannot silently truncate zip.
private theorem rootableP5 (fields : List SszType) (xs : List SszValue) :
    Ssz.Rootable (.container fields) (.container xs) ↔
      fields ≠ [] ∧ fields.length = xs.length ∧
        ∀ pair ∈ fields.zip xs, Ssz.Rootable pair.1 pair.2 := Ssz.rootable_iff _ _

private theorem rootableP5_failures :
    ¬ Ssz.Rootable (.container []) (.container []) ∧
    ¬ Ssz.Rootable (.container [.bool]) (.container []) ∧
    ¬ Ssz.Rootable (.container [.bool]) (.container [.bool true, .bool false]) ∧
    ¬ Ssz.Rootable (.container [.bool, .uint 1]) (.container [.uint 0, .bool true]) := by
  simp [Ssz.rootable_iff (.container _) (.container _),
    Ssz.rootable_iff .bool (.uint _)]

-- rootableP6: sparse positions constrain activity, population, arity and every actual pair.
private theorem rootableP6 (mask : List Bool) (fields : List SszType) (xs : List SszValue) :
    Ssz.Rootable (.progressiveContainer mask fields) (.container xs) ↔
      mask.getLast? = some true ∧ mask.length ≤ 256 ∧
      (mask.filter id).length = fields.length ∧ fields.length = xs.length ∧
      ∀ pair ∈ fields.zip xs, Ssz.Rootable pair.1 pair.2 := Ssz.rootable_iff _ _

private theorem rootableP6_sparse :
    Ssz.Rootable (.progressiveContainer [false, true, false, true] [.bool, .uint 1])
      (.container [.bool false, .uint 255]) ∧
    ¬ Ssz.Rootable (.progressiveContainer [false, true] [.bool, .bool])
      (.container [.bool false, .bool true]) ∧
    ¬ Ssz.Rootable (.progressiveContainer [false, true] [.bool]) (.container []) ∧
    ¬ Ssz.Rootable (.progressiveContainer [false, true] [.bool])
      (.container [.bool false, .bool true]) := by
  simp [Ssz.rootable_iff (.progressiveContainer _ _) (.container _),
    Ssz.rootable_iff .bool (.bool _), Ssz.rootable_iff (.uint _) (.uint _)]

-- rootableP7: raw masks through 256 need no encoded source name premise (Q77 is broader).
private theorem rootableP7_sparse (n : Nat) :
    Ssz.Rootable (.progressiveContainer (List.replicate n false ++ [true]) [.bool])
      (.container [.bool true]) ↔ n + 1 ≤ 256 := by
  simp [Ssz.rootable_iff (.progressiveContainer _ _) (.container _),
    Ssz.rootable_iff .bool (.bool _), List.filter_append ]

private theorem rootableP7_widths :
    Ssz.Rootable (.progressiveContainer (List.replicate 254 false ++ [true]) [.bool])
      (.container [.bool true]) ∧
    Ssz.Rootable (.progressiveContainer (List.replicate 255 false ++ [true]) [.bool])
      (.container [.bool true]) ∧
    ¬ Ssz.Rootable (.progressiveContainer (List.replicate 256 false ++ [true]) [.bool])
      (.container [.bool true]) := by
  simp only [rootableP7_sparse]
  decide

private theorem rootableP7_bad_masks :
    ¬ Ssz.Rootable (.progressiveContainer [] []) (.container []) ∧
    ¬ Ssz.Rootable (.progressiveContainer [false, false] []) (.container []) ∧
    ¬ Ssz.Rootable (.progressiveContainer [true, false] [.bool]) (.container [.bool true]) := by
  simp [Ssz.rootable_iff (.progressiveContainer _ _) (.container _)]

-- rootableP8: unused composite schema validity is deliberately not a global requirement.
private theorem rootableP8_non_global :
    Ssz.Rootable (.list (.container [.uint 3]) 0) (.list []) ∧
    ¬ (SszType.list (.container [.uint 3]) 0).WellFormed ∧
    Ssz.Rootable (.progressiveList (.container [])) (.list []) ∧
    ¬ (SszType.progressiveList (.container [])).WellFormed ∧
    ¬ Ssz.Rootable (.list (.uint 3) 0) (.list []) ∧
    ¬ Ssz.Rootable (.progressiveList (.uint 3)) (.list []) := by
  simp [Ssz.rootable_iff (.list _ _) (.list _),
    Ssz.rootable_iff (.progressiveList _) (.list _),
    SszType.wellFormed_iff (.list _ _), SszType.wellFormed_iff (.progressiveList _),
    SszType.wellFormed_iff (.container _), SszType.wellFormed_iff (.uint _)]

private theorem rootableP8_actual :
    ¬ Ssz.Rootable (.list (.container [.uint 3]) 1) (.list [.container [.uint 0]]) ∧
    ¬ Ssz.Rootable (.progressiveList (.container [])) (.list [.container []]) ∧
    ¬ Ssz.Rootable (.list (.container [.bool]) 1) (.list [.container [.uint 0]]) ∧
    ¬ Ssz.Rootable (.list (.container [.bool]) 1) (.list [.container []]) := by
  simp [Ssz.rootable_iff (.list _ _) (.list _),
    Ssz.rootable_iff (.progressiveList _) (.list _),
    Ssz.rootable_iff (.container _) (.container _),
    Ssz.rootable_iff (.uint _) (.uint _), Ssz.rootable_iff .bool (.uint _)]

private theorem zip_value_mem (fields : List SszType) (xs : List SszValue)
    (pair : SszType × SszValue) (hp : pair ∈ fields.zip xs) : pair.2 ∈ xs := by
  induction fields generalizing xs with
  | nil => simp at hp
  | cons field fields ih =>
    cases xs with
    | nil => simp at hp
    | cons x xs =>
      simp only [List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem x (ih xs hp)

-- rootableP9: all actual recursion supports payload typing, by value induction only.
private theorem rootableP9 (t : SszType) (v : SszValue)
    (h : Ssz.Rootable t v) : SszValue.WellTyped t v := by
  have allValues : ∀ v : SszValue, ∀ t : SszType,
      Ssz.Rootable t v → SszValue.WellTyped t v := by
    intro v
    refine SszValue.rec
      (motive_1 := fun v => ∀ t : SszType, Ssz.Rootable t v → SszValue.WellTyped t v)
      (motive_2 := fun xs => ∀ x ∈ xs, ∀ t : SszType,
        Ssz.Rootable t x → SszValue.WellTyped t x) ?_ ?_ ?_ ?_ ?_ ?_ ?_ v
    · intro n t h
      cases t <;> simp only [Ssz.rootable_iff _ (.uint n),
        SszValue.wellTyped_iff _ (.uint n)] at h ⊢
      exact h.2
    · intro b t h
      cases t <;> simp only [Ssz.rootable_iff _ (.bool b),
        SszValue.wellTyped_iff _ (.bool b)] at h ⊢
    · intro b t h
      cases t <;> simp only [Ssz.rootable_iff _ (.bytes b),
        SszValue.wellTyped_iff _ (.bytes b)] at h ⊢
      · exact h
      · exact h.1
    · intro xs ih t h
      cases t <;> simp only [Ssz.rootable_iff _ (.list xs),
        SszValue.wellTyped_iff _ (.list xs)] at h ⊢
      · exact ⟨h.1, fun x hx => ih x hx _ (h.2.2.1 x hx)⟩
      · exact fun x hx => ih x hx _ (h.2.1 x hx)
    · intro xs ih t h
      cases t <;> simp only [Ssz.rootable_iff _ (.container xs),
        SszValue.wellTyped_iff _ (.container xs)] at h ⊢
      · exact ⟨h.2.1, fun pair hp => ih pair.2 (zip_value_mem _ _ _ hp) _ (h.2.2 pair hp)⟩
      · exact ⟨h.2.2.2.1, fun pair hp =>
          ih pair.2 (zip_value_mem _ _ _ hp) _ (h.2.2.2.2 pair hp)⟩
    · intro x hx
      exact False.elim (List.not_mem_nil hx)
    · intro x xs ihx ihxs y hy t h
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ihx t h
      · exact ihxs y hy t h
  exact allValues v t h

end STFSpec.Conformance.Codec
