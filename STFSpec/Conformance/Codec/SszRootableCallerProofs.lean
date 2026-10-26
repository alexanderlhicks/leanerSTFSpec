/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Local SSZ root-support facade clients

Library `EthConformance`. rootableC0–rootableC9 are private complete propositions, using only the
Codec facade and its public laws. Count ceilings are symbolic; no huge payload is
allocated. No source execution, class admission, root result or security claim.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–4/§7.
-/

namespace STFSpec.Conformance.Codec

open STFSpec.Codec

private theorem rootableC0 (t : SszType) (v : SszValue) :
    Ssz.Rootable (t := t) (v := v) ↔
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
      | _, _ => False := Ssz.rootable_iff (t := t) (v := v)

-- rootableC1: the complete scalar range, concrete width set, and exact boundary.
private theorem rootableC1_uint (w n : Nat) :
    Ssz.Rootable (.uint w) (.uint n) ↔
      w ∈ [1, 2, 4, 8, 16, 32] ∧ n < 2 ^ (8 * w) := Ssz.rootable_iff _ _

private theorem rootableC1_widths :
    Ssz.Rootable (.uint 1) (.uint 0) ∧ Ssz.Rootable (.uint 2) (.uint 0) ∧
    Ssz.Rootable (.uint 4) (.uint 0) ∧ Ssz.Rootable (.uint 8) (.uint 0) ∧
    Ssz.Rootable (.uint 16) (.uint 0) ∧ Ssz.Rootable (.uint 32) (.uint 0) ∧
    ¬ Ssz.Rootable (.uint 0) (.uint 0) ∧ ¬ Ssz.Rootable (.uint 3) (.uint 0) := by
  simp [Ssz.rootable_iff (.uint _) (.uint _)]

private theorem rootableC1_large (w n : Nat) (hw : 32 < w) :
    ¬ Ssz.Rootable (.uint w) (.uint n) := by
  rw [rootableC1_uint]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

private theorem rootableC1_boundary (w : Nat) (hw : w ∈ [1, 2, 4, 8, 16, 32]) :
    Ssz.Rootable (.uint w) (.uint (2 ^ (8 * w) - 1)) ∧
    ¬ Ssz.Rootable (.uint w) (.uint (2 ^ (8 * w))) := by
  have hp : 0 < 2 ^ (8 * w) := Nat.two_pow_pos _
  simp only [rootableC1_uint, hw, true_and, Nat.lt_irrefl, and_false, not_false_eq_true, and_true]
  omega

private theorem rootableC1_bool (b : Bool) :
    Ssz.Rootable .bool (.bool b) ∧ ¬ Ssz.Rootable .bool (.uint 0) ∧
    ¬ Ssz.Rootable (.uint 1) (.bool b) := by
  simp only [Ssz.rootable_iff .bool _, Ssz.rootable_iff (.uint 1) (.bool _),
    not_false_eq_true, and_self]

-- rootableC2: vectors have exact lengths, with no added count-mix-in bound.
private theorem rootableC2 (n limit : Nat) (b : ByteArray) :
    (Ssz.Rootable (.byteVector n) (.bytes b) ↔ b.size = n) ∧
    Ssz.Rootable (.byteVector b.size) (.bytes b) ∧
    (Ssz.Rootable (.byteList limit) (.bytes b) ↔
      b.size ≤ limit ∧ b.size < 2 ^ 256) := by
  simp only [Ssz.rootable_iff (.byteVector _) (.bytes _),
    Ssz.rootable_iff (.byteList _) (.bytes _), iff_self, and_self]

private theorem rootableC2_zero :
    Ssz.Rootable (.byteVector 0) (.bytes ByteArray.empty) ∧
    Ssz.Rootable (.byteList 0) (.bytes ByteArray.empty) ∧
    ¬ Ssz.Rootable (.byteList 0) (.bytes (ByteArray.mk #[0])) := by
  simp [Ssz.rootable_iff (.byteVector _) (.bytes _),
    Ssz.rootable_iff (.byteList _) (.bytes _)] <;> decide

-- rootableC3: Bool is a one-byte basic element; byte vectors are composite, including
-- zero vectors. These support clauses supply no typed packer or root operation.
private theorem rootableC3_list (elem : SszType) (limit : Nat) (xs : List SszValue) :
    Ssz.Rootable (.list elem limit) (.list xs) ↔
      xs.length ≤ limit ∧ Ssz.Rootable (.progressiveList elem) (.list xs) := by
  rw [Ssz.rootable_iff (.list _ _) (.list _),
    Ssz.rootable_iff (.progressiveList _) (.list _)]

private theorem rootableC3_basic (w limit : Nat) :
    (Ssz.Rootable (.list (.uint w) limit) (.list []) ↔
      w ∈ [1, 2, 4, 8, 16, 32]) ∧
    (Ssz.Rootable (.progressiveList (.uint w)) (.list []) ↔
      w ∈ [1, 2, 4, 8, 16, 32]) := by
  simp [Ssz.rootable_iff (.list _ _) (.list _),
    Ssz.rootable_iff (.progressiveList _) (.list _)]

private theorem rootableC3_bool_vector (limit : Nat) (xs : List SszValue) (n : Nat) :
    (Ssz.Rootable (.list .bool limit) (.list xs) ↔
      xs.length ≤ limit ∧ xs.length < 2 ^ 256 ∧
        ∀ x ∈ xs, Ssz.Rootable .bool x) ∧
    (Ssz.Rootable (.list (.byteVector n) limit) (.list xs) ↔
      xs.length ≤ limit ∧ xs.length < 2 ^ 256 ∧
        ∀ x ∈ xs, Ssz.Rootable (.byteVector n) x) ∧
    SszType.bool ≠ SszType.byteVector n := by
  simp [Ssz.rootable_iff (.list _ _) (.list _)]

private theorem rootableC3_children (elem : SszType) (limit : Nat) (xs : List SszValue)
    (h : Ssz.Rootable (.list elem limit) (.list xs)) :
    xs.length ≤ limit ∧ xs.length < 2 ^ 256 ∧ ∀ x ∈ xs, Ssz.Rootable elem x := by
  have hs := (Ssz.rootable_iff _ _).mp h
  exact ⟨hs.1, hs.2.1, hs.2.2.1⟩

-- rootableC4: progressive lists have actual counts/children, without an ordinary cap.
private theorem rootableC4_progressive (elem : SszType) (xs : List SszValue) (b : ByteArray) :
    (Ssz.Rootable (.progressiveList elem) (.list xs) ↔
      xs.length < 2 ^ 256 ∧ (∀ x ∈ xs, Ssz.Rootable elem x) ∧
      match elem with
      | .uint w => w ∈ [1, 2, 4, 8, 16, 32]
      | .bool => True
      | .byteVector _ | .byteList _ | .list _ _ | .progressiveList _ |
        .progressiveByteList | .container _ | .progressiveContainer _ _ => True) ∧
    (Ssz.Rootable .progressiveByteList (.bytes b) ↔ b.size < 2 ^ 256) :=
  ⟨Ssz.rootable_iff _ _, Ssz.rootable_iff _ _⟩

private theorem rootableC4_ceilings (elem : SszType) (limit : Nat)
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

-- rootableC5: ordinary fields have no extra count bound and cannot silently truncate zip.
private theorem rootableC5 (fields : List SszType) (xs : List SszValue) :
    Ssz.Rootable (.container fields) (.container xs) ↔
      fields ≠ [] ∧ fields.length = xs.length ∧
        ∀ pair ∈ fields.zip xs, Ssz.Rootable pair.1 pair.2 := Ssz.rootable_iff _ _

private theorem rootableC5_failures :
    ¬ Ssz.Rootable (.container []) (.container []) ∧
    ¬ Ssz.Rootable (.container [.bool]) (.container []) ∧
    ¬ Ssz.Rootable (.container [.bool]) (.container [.bool true, .bool false]) ∧
    ¬ Ssz.Rootable (.container [.bool, .uint 1]) (.container [.uint 0, .bool true]) := by
  simp [Ssz.rootable_iff (.container _) (.container _),
    Ssz.rootable_iff .bool (.uint _)]

-- rootableC6: sparse positions constrain activity, population, arity and every actual pair.
private theorem rootableC6 (mask : List Bool) (fields : List SszType) (xs : List SszValue) :
    Ssz.Rootable (.progressiveContainer mask fields) (.container xs) ↔
      mask.getLast? = some true ∧ mask.length ≤ 256 ∧
      (mask.filter id).length = fields.length ∧ fields.length = xs.length ∧
      ∀ pair ∈ fields.zip xs, Ssz.Rootable pair.1 pair.2 := Ssz.rootable_iff _ _

private theorem rootableC6_sparse :
    Ssz.Rootable (.progressiveContainer [false, true, false, true] [.bool, .uint 1])
      (.container [.bool false, .uint 255]) ∧
    ¬ Ssz.Rootable (.progressiveContainer [false, true] [.bool, .bool])
      (.container [.bool false, .bool true]) ∧
    ¬ Ssz.Rootable (.progressiveContainer [false, true] [.bool]) (.container []) ∧
    ¬ Ssz.Rootable (.progressiveContainer [false, true] [.bool])
      (.container [.bool false, .bool true]) := by
  simp [Ssz.rootable_iff (.progressiveContainer _ _) (.container _),
    Ssz.rootable_iff .bool (.bool _), Ssz.rootable_iff (.uint _) (.uint _)]

-- rootableC7: raw masks through 256 need no encoded source name premise (Q77 is broader).
private theorem rootableC7_sparse (n : Nat) :
    Ssz.Rootable (.progressiveContainer (List.replicate n false ++ [true]) [.bool])
      (.container [.bool true]) ↔ n + 1 ≤ 256 := by
  simp [Ssz.rootable_iff (.progressiveContainer _ _) (.container _),
    Ssz.rootable_iff .bool (.bool _), List.filter_append ]

private theorem rootableC7_widths :
    Ssz.Rootable (.progressiveContainer (List.replicate 254 false ++ [true]) [.bool])
      (.container [.bool true]) ∧
    Ssz.Rootable (.progressiveContainer (List.replicate 255 false ++ [true]) [.bool])
      (.container [.bool true]) ∧
    ¬ Ssz.Rootable (.progressiveContainer (List.replicate 256 false ++ [true]) [.bool])
      (.container [.bool true]) := by
  simp only [rootableC7_sparse]
  decide

private theorem rootableC7_bad_masks :
    ¬ Ssz.Rootable (.progressiveContainer [] []) (.container []) ∧
    ¬ Ssz.Rootable (.progressiveContainer [false, false] []) (.container []) ∧
    ¬ Ssz.Rootable (.progressiveContainer [true, false] [.bool]) (.container [.bool true]) := by
  simp [Ssz.rootable_iff (.progressiveContainer _ _) (.container _)]

-- rootableC8: unused composite schema validity is deliberately not a global requirement.
private theorem rootableC8_non_global :
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

private theorem rootableC8_actual :
    ¬ Ssz.Rootable (.list (.container [.uint 3]) 1) (.list [.container [.uint 0]]) ∧
    ¬ Ssz.Rootable (.progressiveList (.container [])) (.list [.container []]) ∧
    ¬ Ssz.Rootable (.list (.container [.bool]) 1) (.list [.container [.uint 0]]) ∧
    ¬ Ssz.Rootable (.list (.container [.bool]) 1) (.list [.container []]) := by
  simp [Ssz.rootable_iff (.list _ _) (.list _),
    Ssz.rootable_iff (.progressiveList _) (.list _),
    Ssz.rootable_iff (.container _) (.container _),
    Ssz.rootable_iff (.uint _) (.uint _), Ssz.rootable_iff .bool (.uint _)]

private theorem zip_field_mem (fields : List SszType) (xs : List SszValue)
    (pair : SszType × SszValue) (hp : pair ∈ fields.zip xs) : pair.1 ∈ fields := by
  induction xs generalizing fields with
  | nil => simp at hp
  | cons x xs ih =>
    cases fields with
    | nil => simp at hp
    | cons field fields =>
      rcases (show pair = (field, x) ∨ pair ∈ fields.zip xs by simpa using hp) with rfl | hp
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem field (ih fields hp)

-- rootableC9: an independent descriptor induction derives actual payload typing, without WF.
private theorem rootableC9 (t : SszType) (v : SszValue)
    (h : Ssz.Rootable t v) : SszValue.WellTyped t v := by
  have allTypes : ∀ t : SszType, ∀ v : SszValue,
      Ssz.Rootable t v → SszValue.WellTyped t v := by
    intro t
    refine SszType.rec
      (motive_1 := fun t => ∀ v : SszValue, Ssz.Rootable t v → SszValue.WellTyped t v)
      (motive_2 := fun fields => ∀ field ∈ fields, ∀ v : SszValue,
        Ssz.Rootable field v → SszValue.WellTyped field v) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t
    · intro w v h
      cases v <;> simp only [Ssz.rootable_iff (.uint w) _,
        SszValue.wellTyped_iff (.uint w) _] at h ⊢
      exact h.2
    · intro v h
      cases v <;> simp only [Ssz.rootable_iff .bool _,
        SszValue.wellTyped_iff .bool _] at h ⊢
    · intro n v h
      cases v <;> simp only [Ssz.rootable_iff (.byteVector n) _,
        SszValue.wellTyped_iff (.byteVector n) _] at h ⊢
      exact h
    · intro limit v h
      cases v <;> simp only [Ssz.rootable_iff (.byteList limit) _,
        SszValue.wellTyped_iff (.byteList limit) _] at h ⊢
      exact h.1
    · intro elem limit ih v h
      cases v <;> simp only [Ssz.rootable_iff (.list elem limit) _,
        SszValue.wellTyped_iff (.list elem limit) _] at h ⊢
      exact ⟨h.1, fun x hx => ih x (h.2.2.1 x hx)⟩
    · intro elem ih v h
      cases v <;> simp only [Ssz.rootable_iff (.progressiveList elem) _,
        SszValue.wellTyped_iff (.progressiveList elem) _] at h ⊢
      exact fun x hx => ih x (h.2.1 x hx)
    · intro v h
      cases v <;> simp only [Ssz.rootable_iff .progressiveByteList _,
        SszValue.wellTyped_iff .progressiveByteList _] at h ⊢
    · intro fields ih v h
      cases v <;> simp only [Ssz.rootable_iff (.container fields) _,
        SszValue.wellTyped_iff (.container fields) _] at h ⊢
      exact ⟨h.2.1, fun pair hp => ih pair.1 (zip_field_mem _ _ _ hp) _ (h.2.2 pair hp)⟩
    · intro mask fields ih v h
      cases v <;> simp only [Ssz.rootable_iff (.progressiveContainer mask fields) _,
        SszValue.wellTyped_iff (.progressiveContainer mask fields) _] at h ⊢
      exact ⟨h.2.2.2.1, fun pair hp =>
        ih pair.1 (zip_field_mem _ _ _ hp) _ (h.2.2.2.2 pair hp)⟩
    · intro field hf
      exact False.elim (List.not_mem_nil hf)
    · intro field fields ih ihs f hf v h
      rcases List.mem_cons.mp hf with rfl | hf
      · exact ih v h
      · exact ihs f hf v h
  exact allTypes t v h

end STFSpec.Conformance.Codec
