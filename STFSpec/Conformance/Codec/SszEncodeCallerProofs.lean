/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Independent SSZ serialization callers

Library `EthConformance`. These private clients use only the public support,
result and classifier equations. Symbolic offset boundaries allocate no huge
payloads. Mathematical extensions supply no source-class or inverse theorem.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/

namespace STFSpec.Conformance.Codec

open STFSpec.Codec

private theorem supported_scalar (w n : Nat)
    (h : Ssz.Serializable (.uint w) (.uint n)) :
    (w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8 ∨ w = 16 ∨ w = 32) ∧
      n < 2 ^ (8 * w) := (Ssz.serializable_iff _ _).mp h

private theorem scalar_bytes (w n : Nat)
    (h : Ssz.Serializable (.uint w) (.uint n)) :
    (Ssz.encode (t := .uint w) (v := .uint n) (h := h)).data.toList =
      (List.range w).map (fun i ↦ UInt8.ofNat ((n / 256 ^ i) % 256)) :=
  Ssz.encode_eq _ _ h

private theorem bytes_preserved (b : ByteArray)
    (h : Ssz.Serializable .progressiveByteList (.bytes b)) :
    Ssz.encode .progressiveByteList (.bytes b) h = b := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  exact Ssz.encode_eq _ _ h

private theorem children_supported (e : SszType) (limit : Nat) (xs : List SszValue)
    (h : Ssz.Serializable (.list e limit) (.list xs)) :
    xs.length ≤ limit ∧ ∀ x ∈ xs, Ssz.Serializable e x := by
  have hs := (Ssz.serializable_iff _ _).mp h
  exact ⟨hs.1, hs.2.1⟩

private theorem fields_supported (mask : List Bool) (fs : List SszType)
    (xs : List SszValue)
    (h : Ssz.Serializable (.progressiveContainer mask fs) (.container xs)) :
    fs.length = xs.length ∧ ∀ p ∈ fs.zip xs, Ssz.Serializable p.1 p.2 := by
  have hs := (Ssz.serializable_iff _ _).mp h
  exact ⟨hs.1, hs.2.1⟩

private theorem masks_ignore_support (a b : List Bool) (fs : List SszType)
    (xs : List SszValue) :
    Ssz.Serializable (.progressiveContainer a fs) (.container xs) ↔
      Ssz.Serializable (.progressiveContainer b fs) (.container xs) := by
  rw [Ssz.serializable_iff, Ssz.serializable_iff]

private theorem masks_ignore_bytes (a b : List Bool) (fs : List SszType)
    (xs : List SszValue)
    (ha : Ssz.Serializable (.progressiveContainer a fs) (.container xs))
    (hb : Ssz.Serializable (.progressiveContainer b fs) (.container xs))
    (bs : List ByteArray) (hl : (fs.zip xs).length = bs.length)
    (hc : ∀ p ∈ (fs.zip xs).zip bs, ∀ h : Ssz.Serializable p.1.1 p.1.2,
      Ssz.encode p.1.1 p.1.2 h = p.2) :
    Ssz.encode (.progressiveContainer a fs) (.container xs) ha =
      Ssz.encode (.progressiveContainer b fs) (.container xs) hb := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  have h1 := Ssz.encode_eq (.progressiveContainer a fs) (.container xs) ha
  have h2 := Ssz.encode_eq (.progressiveContainer b fs) (.container xs) hb
  exact (h1 bs ⟨hl, hc⟩).trans (h2 bs ⟨hl, hc⟩).symm

private theorem progressive_list_same_bytes (e : SszType) (limit : Nat)
    (xs : List SszValue)
    (ha : Ssz.Serializable (.list e limit) (.list xs))
    (hb : Ssz.Serializable (.progressiveList e) (.list xs))
    (bs : List ByteArray) (hl : (xs.map (fun x ↦ (e, x))).length = bs.length)
    (hc : ∀ p ∈ (xs.map (fun x ↦ (e, x))).zip bs,
      ∀ h : Ssz.Serializable p.1.1 p.1.2, Ssz.encode p.1.1 p.1.2 h = p.2) :
    Ssz.encode (.list e limit) (.list xs) ha =
      Ssz.encode (.progressiveList e) (.list xs) hb := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  have h1 := Ssz.encode_eq (.list e limit) (.list xs) ha
  have h2 := Ssz.encode_eq (.progressiveList e) (.list xs) hb
  exact (h1 bs ⟨hl, hc⟩).trans (h2 bs ⟨hl, hc⟩).symm

private theorem zero_width_scalar_unsupported :
    ¬ Ssz.Serializable (.uint 0) (.uint 0) := by
  rw [Ssz.serializable_iff]
  decide

private theorem odd_width_scalar_unsupported :
    ¬ Ssz.Serializable (.uint 3) (.uint 0) := by
  rw [Ssz.serializable_iff]
  decide

private theorem overflow_scalar_unsupported :
    ¬ Ssz.Serializable (.uint 1) (.uint 256) := by
  rw [Ssz.serializable_iff]
  decide

private theorem vector_length_unsupported :
    ¬ Ssz.Serializable (.byteVector 1) (.bytes ByteArray.empty) := by
  rw [Ssz.serializable_iff]
  decide

private theorem list_limit_unsupported :
    ¬ Ssz.Serializable (.list .bool 0) (.list [.bool false]) := by
  intro h
  have hs := (Ssz.serializable_iff _ _).mp h
  exact (by decide : ¬ 1 ≤ 0) hs.1

private theorem container_arity_unsupported :
    ¬ Ssz.Serializable (.container [.bool]) (.container []) := by
  intro h
  have hs := (Ssz.serializable_iff _ _).mp h
  exact (by decide : ¬ 1 = 0) hs.1

private theorem wrong_tag_unsupported (n : Nat) :
    ¬ Ssz.Serializable .bool (.uint n) := by
  rw [Ssz.serializable_iff]
  exact id

private theorem unused_bad_schema_supported :
    Ssz.Serializable (.list (.uint 3) 0) (.list []) := by
  apply (Ssz.serializable_iff _ _).mpr
  exact ⟨by decide, by simp, by simp⟩

private theorem visited_bad_schema_unsupported :
    ¬ Ssz.Serializable (.list (.uint 3) 1) (.list [.uint 0]) := by
  intro h
  exact odd_width_scalar_unsupported ((children_supported _ _ _ h).2 _ (by simp))

private theorem empty_container_supported :
    Ssz.Serializable (.container []) (.container []) := by
  apply (Ssz.serializable_iff _ _).mpr
  exact ⟨rfl, by simp, by simp⟩

-- A symbolic head at the largest representable start; the final payload size is
-- unrestricted. There is no allocation of the quantified prefix or payload.
private theorem final_payload_unbounded (leading payload : ByteArray)
    (hp : leading.size = 2 ^ 32 - 5) :
    Ssz.Serializable (.container [.byteVector (2 ^ 32 - 5), .progressiveByteList])
      (.container [.bytes leading, .bytes payload]) := by
  have hv : Ssz.Serializable (.byteVector (2 ^ 32 - 5)) (.bytes leading) :=
    (Ssz.serializable_iff _ _).mpr hp
  have hb : Ssz.Serializable .progressiveByteList (.bytes payload) :=
    (Ssz.serializable_iff _ _).mpr True.intro
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨rfl, ?_, ?_⟩
  · simpa using And.intro hv hb
  · change ∀ o ∈ [2 ^ 32 - 1], o < 2 ^ 32
    decide

private theorem written_start_overflow (leading payload : ByteArray) :
    ¬ Ssz.Serializable (.container [.byteVector (2 ^ 32 - 4), .progressiveByteList])
      (.container [.bytes leading, .bytes payload]) := by
  intro h
  have hs := (Ssz.serializable_iff _ _).mp h
  have hf : (2 ^ 32 : Nat) < 2 ^ 32 := hs.2.2 (2 ^ 32) (by
    change (2 ^ 32 : Nat) ∈ [2 ^ 32]
    simp)
  exact (Nat.lt_irrefl _) hf

private theorem two_dynamic_starts (a b : ByteArray) :
    Ssz.Serializable (.container [.progressiveByteList, .progressiveByteList])
      (.container [.bytes a, .bytes b]) ↔ 8 + a.size < 2 ^ 32 := by
  have ha : Ssz.Serializable .progressiveByteList (.bytes a) :=
    (Ssz.serializable_iff _ _).mpr True.intro
  have hb : Ssz.Serializable .progressiveByteList (.bytes b) :=
    (Ssz.serializable_iff _ _).mpr True.intro
  rw [Ssz.serializable_iff]
  change (2 = 2 ∧
    (∀ p ∈ [(.progressiveByteList, .bytes a), (.progressiveByteList, .bytes b)],
      Ssz.Serializable p.1 p.2) ∧
    (∀ o ∈ [8, 8 + a.size], o < 2 ^ 32)) ↔ 8 + a.size < 2 ^ 32
  simp [ha, hb]

private theorem later_empty_start_overflow (a : ByteArray)
    (ha : a.size = 2 ^ 32 - 8) :
    ¬ Ssz.Serializable (.container [.progressiveByteList, .progressiveByteList])
      (.container [.bytes a, .bytes ByteArray.empty]) := by
  rw [two_dynamic_starts]
  omega

private theorem serializable_wellTyped (t : SszType) (v : SszValue)
    (h : Ssz.Serializable t v) : SszValue.WellTyped t v := by
  have allTypes : ∀ t : SszType, ∀ v : SszValue,
      Ssz.Serializable t v → SszValue.WellTyped t v := by
    intro t
    refine SszType.rec
      (motive_1 := fun t ↦ ∀ v : SszValue, Ssz.Serializable t v → SszValue.WellTyped t v)
      (motive_2 := fun fields ↦ ∀ field ∈ fields, ∀ v : SszValue,
        Ssz.Serializable field v → SszValue.WellTyped field v) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t
    · intro w v h
      cases v <;> simp only [Ssz.serializable_iff (.uint w) _,
        SszValue.wellTyped_iff (.uint w) _] at h ⊢
      exact h.2
    · intro v h
      cases v <;> simp only [Ssz.serializable_iff .bool _,
        SszValue.wellTyped_iff .bool _] at h ⊢
    · intro n v h
      cases v <;> simp only [Ssz.serializable_iff (.byteVector n) _,
        SszValue.wellTyped_iff (.byteVector n) _] at h ⊢
      exact h
    · intro limit v h
      cases v <;> simp only [Ssz.serializable_iff (.byteList limit) _,
        SszValue.wellTyped_iff (.byteList limit) _] at h ⊢
      exact h
    · intro elem limit ih v h
      cases v <;> simp only [Ssz.serializable_iff (.list elem limit) _,
        SszValue.wellTyped_iff (.list elem limit) _] at h ⊢
      exact ⟨h.1, fun x hx ↦ ih x (h.2.1 x hx)⟩
    · intro elem ih v h
      cases v <;> simp only [Ssz.serializable_iff (.progressiveList elem) _,
        SszValue.wellTyped_iff (.progressiveList elem) _] at h ⊢
      exact fun x hx ↦ ih x (h.1 x hx)
    · intro v h
      cases v <;> simp only [Ssz.serializable_iff .progressiveByteList _,
        SszValue.wellTyped_iff .progressiveByteList _] at h ⊢
    · intro fields ih v h
      cases v <;> simp only [Ssz.serializable_iff (.container fields) _,
        SszValue.wellTyped_iff (.container fields) _] at h ⊢
      exact ⟨h.1, fun pair hp ↦ ih pair.1 (List.of_mem_zip hp).1 _ (h.2.1 pair hp)⟩
    · intro mask fields ih v h
      cases v <;> simp only [Ssz.serializable_iff (.progressiveContainer mask fields) _,
        SszValue.wellTyped_iff (.progressiveContainer mask fields) _] at h ⊢
      exact ⟨h.1, fun pair hp ↦
        ih pair.1 (List.of_mem_zip hp).1 _ (h.2.1 pair hp)⟩
    · intro field hf
      exact False.elim (List.not_mem_nil hf)
    · intro field fields ih ihs f hf v h
      rcases List.mem_cons.mp hf with rfl | hf
      · exact ih v h
      · exact ihs f hf v h
  exact allTypes t v h

private def ClientCertificate (ps : List (SszType × SszValue))
    (bs : List ByteArray) : Prop :=
  ps.length = bs.length ∧ ∀ p ∈ ps.zip bs,
    ∀ h : Ssz.Serializable p.1.1 p.1.2, Ssz.encode p.1.1 p.1.2 h = p.2

private theorem client_certificates (ps : List (SszType × SszValue))
    (hs : ∀ p ∈ ps, Ssz.Serializable p.1 p.2) : ∃ bs, ClientCertificate ps bs := by
  induction ps with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons p ps ih =>
    obtain ⟨bs, hl, hc⟩ := ih (fun q hq ↦ hs q (by simp [hq]))
    refine ⟨Ssz.encode p.1 p.2 (hs p (by simp)) :: bs, ?_, ?_⟩
    · simp only [List.length_cons, hl]
    · intro q hq h
      simp only [List.zip_cons_cons, List.mem_cons] at hq
      rcases hq with rfl | hq
      · rfl
      · exact hc q hq h

private def nestedListType : SszType := .list (.byteList 2) 3
private def nestedListValue : SszValue :=
  .list [.bytes ⟨#[170, 187]⟩, .bytes ByteArray.empty]
private def nestedListBytes : ByteArray := ⟨#[8, 0, 0, 0, 10, 0, 0, 0, 170, 187]⟩

private theorem nested_list_supported : Ssz.Serializable nestedListType nestedListValue := by
  have ha : Ssz.Serializable (.byteList 2) (.bytes ⟨#[170, 187]⟩) :=
    (Ssz.serializable_iff _ _).mpr (by decide)
  have hb : Ssz.Serializable (.byteList 2) (.bytes ByteArray.empty) :=
    (Ssz.serializable_iff _ _).mpr (by decide)
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa using And.intro ha hb

private theorem nested_list_result (h : Ssz.Serializable nestedListType nestedListValue) :
    Ssz.encode nestedListType nestedListValue h = nestedListBytes := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  apply (Ssz.encode_eq nestedListType nestedListValue h)
    [⟨#[170, 187]⟩, ByteArray.empty]
  refine ⟨rfl, ?_⟩
  intro q hq hc
  simp only [List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_left,
    List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  all_goals
    apply ByteArray.ext
    apply Array.toList_inj.mp
    exact Ssz.encode_eq _ _ hc

private def nestedType : SszType := .container [nestedListType, .bool]
private def nestedValue : SszValue := .container [nestedListValue, .bool true]

private theorem nested_supported : Ssz.Serializable nestedType nestedValue := by
  have hb : Ssz.Serializable .bool (.bool true) :=
    (Ssz.serializable_iff _ _).mpr True.intro
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨rfl, ?_, by decide⟩
  simpa using And.intro nested_list_supported hb

private theorem nested_complete_bytes (h : Ssz.Serializable nestedType nestedValue) :
    (Ssz.encode nestedType nestedValue h).data.toList =
      [5, 0, 0, 0, 1, 8, 0, 0, 0, 10, 0, 0, 0, 170, 187] := by
  apply (Ssz.encode_eq nestedType nestedValue h) [nestedListBytes, ⟨#[1]⟩]
  refine ⟨rfl, ?_⟩
  intro q hq hc
  simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
    List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact nested_list_result hc
  · apply ByteArray.ext
    apply Array.toList_inj.mp
    exact Ssz.encode_eq _ _ hc

end STFSpec.Conformance.Codec
