/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Structural SSZ payload facade clients

Library `EthConformance`. Private public-law clients retain actual member, positional,
size and range obligations independently of schema well-formedness and operation domains.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–4/§7.
-/

namespace STFSpec.Conformance.Codec

open STFSpec.Codec

private theorem wtP01 (w limit n : Nat) (xs : List SszValue)
    (h : SszValue.WellTyped (.list (.uint w) limit) (.list xs)) (hn : .uint n ∈ xs) :
    n < 2 ^ (8 * w) := by
  exact (SszValue.wellTyped_iff _ _).mp (((SszValue.wellTyped_iff _ _).mp h).2 _ hn)

private theorem wtP02 (w limit : Nat) (xs : List SszValue) (b : Bool)
    (h : SszValue.WellTyped (.list (.uint w) limit) (.list xs)) : .bool b ∉ xs := by
  intro hb
  exact (SszValue.wellTyped_iff _ _).mp (((SszValue.wellTyped_iff _ _).mp h).2 _ hb)

private theorem wtP03 (t : SszType) (limit larger : Nat) (xs : List SszValue)
    (hle : limit ≤ larger) (h : SszValue.WellTyped (.list t limit) (.list xs)) :
    SszValue.WellTyped (.list t larger) (.list xs) := by
  obtain ⟨hc, he⟩ := (SszValue.wellTyped_iff _ _).mp h
  exact (SszValue.wellTyped_iff _ _).mpr ⟨Nat.le_trans hc hle, he⟩

private theorem wtP04 (t : SszType) (limit : Nat) (xs : List SszValue) :
    SszValue.WellTyped (.list t limit) (.list xs) ↔
      xs.length ≤ limit ∧ SszValue.WellTyped (.progressiveList t) (.list xs) := by
  rw [SszValue.wellTyped_iff (.list _ _) (.list _),
    SszValue.wellTyped_iff (.progressiveList _) (.list _)]

private theorem aligned_get (fs : List SszType) (xs : List SszValue)
    (h : ∀ pair ∈ fs.zip xs, SszValue.WellTyped pair.1 pair.2)
    (i : Nat) (t : SszType) (v : SszValue)
    (ht : fs[i]? = some t) (hv : xs[i]? = some v) : SszValue.WellTyped t v := by
  induction fs generalizing xs i with
  | nil => simp at ht
  | cons f fs ih =>
    cases xs with
    | nil => simp at hv
    | cons x xs =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at ht hv
        subst t
        subst v
        exact h (f, x) (by simp)
      | succ i =>
        apply ih xs (fun pair hp ↦ h pair (by simp [hp])) i
        · exact ht
        · exact hv

private theorem wtP05 (fs : List SszType) (xs : List SszValue) (i : Nat)
    (t : SszType) (v : SszValue)
    (h : SszValue.WellTyped (.container fs) (.container xs)) :
    fs.length = xs.length ∧ (fs[i]? = some t → xs[i]? = some v → SszValue.WellTyped t v) := by
  obtain ⟨hl, hp⟩ := (SszValue.wellTyped_iff _ _).mp h
  exact ⟨hl, aligned_get fs xs hp i t v⟩

private theorem wtP06 (a c : Nat) (b : ByteArray) :
    SszValue.WellTyped (.container [.uint 1, .byteVector 2, .uint 1])
      (.container [.uint a, .bytes b, .uint c]) ↔
      a < 256 ∧ b.size = 2 ∧ c < 256 := by
  simp [SszValue.wellTyped_iff (.container _) (.container _),
    SszValue.wellTyped_iff (.uint _) (.uint _),
    SszValue.wellTyped_iff (.byteVector _) (.bytes _)]

private theorem wtP07 (w n m : Nat) :
    ¬ SszValue.WellTyped (.container [.uint w, .bool]) (.container [.uint n, .uint m]) := by
  simp [SszValue.wellTyped_iff (.container _) (.container _),
    SszValue.wellTyped_iff .bool (.uint _)]

private theorem wtP08 (n : Nat) (b : ByteArray)
    (h : SszValue.WellTyped (.byteVector n) (.bytes b)) :
    b.size = n ∧ SszValue.WellTyped .progressiveByteList (.bytes b) := by
  exact ⟨(SszValue.wellTyped_iff _ _).mp h, (SszValue.wellTyped_iff _ _).mpr True.intro⟩

private theorem wtP09_limit (limit larger : Nat) (b : ByteArray) (hle : limit ≤ larger)
    (h : SszValue.WellTyped (.byteList limit) (.bytes b)) :
    SszValue.WellTyped (.byteList larger) (.bytes b) := by
  exact (SszValue.wellTyped_iff _ _).mpr
    (Nat.le_trans ((SszValue.wellTyped_iff _ _).mp h) hle)

private theorem wtP09_vector (n : Nat) (b : ByteArray)
    (h : SszValue.WellTyped (.byteVector n) (.bytes b)) :
    SszValue.WellTyped (.byteList n) (.bytes b) := by
  exact (SszValue.wellTyped_iff _ _).mpr (Nat.le_of_eq ((SszValue.wellTyped_iff _ _).mp h))

private theorem wtP10 (w u n : Nat) (hle : w ≤ u)
    (h : SszValue.WellTyped (.uint w) (.uint n)) :
    SszValue.WellTyped (.uint u) (.uint n) := by
  apply (SszValue.wellTyped_iff _ _).mpr
  exact Nat.lt_of_lt_of_le ((SszValue.wellTyped_iff _ _).mp h)
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 8 hle))

private theorem wtP11 (m k : List Bool) (fs : List SszType) (v : SszValue) :
    (SszValue.WellTyped (.progressiveContainer m fs) v ↔
      SszValue.WellTyped (.progressiveContainer k fs) v) ∧
    (SszValue.WellTyped (.container fs) v ↔
      SszValue.WellTyped (.progressiveContainer m fs) v) := by
  cases v <;> simp only [SszValue.wellTyped_iff (.container _) _,
    SszValue.wellTyped_iff (.progressiveContainer _ _) _, and_self, iff_self]

private theorem wtP12 :
    (SszType.progressiveContainer [false, true] [.bool]).WellFormed ∧
    ¬ (SszType.progressiveContainer [true, false] [.bool]).WellFormed ∧
    SszValue.WellTyped (.progressiveContainer [false, true] [.bool])
      (.container [.bool true]) ∧
    SszValue.WellTyped (.progressiveContainer [true, false] [.bool])
      (.container [.bool true]) ∧
    (SszType.progressiveContainer [false, true] [.bool]).fixedSize? =
      (SszType.progressiveContainer [true, false] [.bool]).fixedSize? := by
  simp [SszType.wellFormed_iff (.progressiveContainer _ _), SszType.wellFormed_iff .bool,
    SszValue.wellTyped_iff (.progressiveContainer _ _) (.container _),
    SszValue.wellTyped_iff .bool (.bool _), SszType.fixedSize?_eq (.progressiveContainer _ _)]

private theorem wtP13_uint :
    SszValue.WellTyped (.uint 3) (.uint 0) ∧ ¬ (SszType.uint 3).WellFormed := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _), SszType.wellFormed_iff (.uint _)]

private theorem wtP13_empty :
    SszValue.WellTyped (.list (.uint 3) 0) (.list []) ∧
      ¬ (SszType.list (.uint 3) 0).WellFormed := by
  simp [SszValue.wellTyped_iff (.list _ _) (.list _), SszType.wellFormed_iff (.list _ _),
    SszType.wellFormed_iff (.uint _)]

private theorem wtP13 :
    ¬ (∀ (t : SszType) (v : SszValue), SszValue.WellTyped t v → t.WellFormed) := by
  intro h
  exact wtP13_uint.2 (h _ _ wtP13_uint.1)

private theorem wtP14 :
    (SszType.uint 1).WellFormed ∧ ¬ SszValue.WellTyped (.uint 1) (.uint 256) ∧
    SszType.bool.WellFormed ∧ ¬ SszValue.WellTyped .bool (.uint 0) := by
  simp [SszType.wellFormed_iff (.uint _), SszType.wellFormed_iff .bool,
    SszValue.wellTyped_iff (.uint _) (.uint _), SszValue.wellTyped_iff .bool (.uint _)]

private theorem wtP15 :
    (SszType.list (.byteVector 0) 1).WellFormed ∧
    SszValue.WellTyped (.list (.byteVector 0) 1) (.list []) ∧
    SszValue.WellTyped (.list (.byteVector 0) 1) (.list [.bytes ByteArray.empty]) ∧
    ([] : List SszValue) ≠ [.bytes ByteArray.empty] ∧
    ([] : List SszValue).length * 0 = [SszValue.bytes ByteArray.empty].length * 0 ∧
    (SszType.byteVector 0).fixedSize? = some 0 := by
  simp [SszType.wellFormed_iff (.list _ _), SszType.wellFormed_iff (.byteVector _),
    SszValue.wellTyped_iff (.list _ _) (.list _),
    SszValue.wellTyped_iff (.byteVector _) (.bytes _), SszType.fixedSize?_eq (.byteVector _)]

private theorem wtP16_assemble (t : SszType) (v : SszValue) (h : SszValue.WellTyped t v) :
    SszValue.WellTyped (.container [.list t 2, .progressiveContainer [false, true] [t]])
      (.container [.list [v, v], .container [v]]) := by
  simp [SszValue.wellTyped_iff (.container _) (.container _),
    SszValue.wellTyped_iff (.list _ _) (.list _),
    SszValue.wellTyped_iff (.progressiveContainer _ _) (.container _), h]

private theorem wtP16_project (t : SszType) (xs : List SszValue) (y : SszValue)
    (h : SszValue.WellTyped (.container [.list t 2, .progressiveContainer [false, true] [t]])
      (.container [.list xs, .container [y]])) :
    (∀ x ∈ xs, SszValue.WellTyped t x) ∧ SszValue.WellTyped t y := by
  have hp := ((SszValue.wellTyped_iff _ _).mp h).2
  have hx : SszValue.WellTyped (.list t 2) (.list xs) := hp (.list t 2, .list xs) (by simp)
  have hy : SszValue.WellTyped (.progressiveContainer [false, true] [t])
      (.container [y]) := hp (.progressiveContainer [false, true] [t], .container [y]) (by simp)
  exact ⟨((SszValue.wellTyped_iff _ _).mp hx).2,
    ((SszValue.wellTyped_iff _ _).mp hy).2 (t, y) (by simp)⟩

end STFSpec.Conformance.Codec
