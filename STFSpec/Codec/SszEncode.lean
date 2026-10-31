/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.SszFixedSize

/-!
# Supported SSZ serialization

Library `EthCodec`. Actual-value byte support and a two-pass packed serializer.
Source: `src/ethereum/utils/ssz.py:129–131,179–258,263–296` and locked
eth-remerkleable 0.1.31 `basic.py`, `complex.py`, `byte_arrays.py`, `progressive.py`.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7 (Q80).
-/

namespace STFSpec.Codec

private noncomputable def byteLengthModel : SszType → SszValue → Nat := fun t v ↦
    SszValue.rec (motive_1 := fun _ ↦ SszType → Nat)
      (motive_2 := fun _ ↦ List (SszType → Nat))
      (fun _ t ↦ match t with | .uint w => w | _ => 0)
      (fun _ t ↦ match t with | .bool => 1 | _ => 0)
      (fun b t ↦ match t with
        | .byteVector _ | .byteList _ | .progressiveByteList => b.size
        | _ => 0)
      (fun xs lengths t ↦ match t with
        | .list e _ | .progressiveList e =>
          match SszType.fixedSize? e with
          | some w => w * xs.length
          | none => 4 * xs.length + (lengths.map (fun k ↦ k e)).sum
        | _ => 0)
      (fun _ lengths t ↦ match t with
        | .container fs | .progressiveContainer _ fs =>
          ((fs.zip lengths).map (fun (f, k) ↦
            match SszType.fixedSize? f with | some w => w | none => 4 + k f)).sum
        | _ => 0)
      [] (fun _ _ child rest ↦ child :: rest) v t

private noncomputable def childLengths (xs : List SszValue) : List (SszType → Nat) :=
  SszValue.rec_1 (motive_1 := fun _ ↦ SszType → Nat)
      (motive_2 := fun _ ↦ List (SszType → Nat))
      (fun _ t ↦ match t with | .uint w => w | _ => 0)
      (fun _ t ↦ match t with | .bool => 1 | _ => 0)
      (fun b t ↦ match t with
        | .byteVector _ | .byteList _ | .progressiveByteList => b.size
        | _ => 0)
      (fun xs lengths t ↦ match t with
        | .list e _ | .progressiveList e =>
          match SszType.fixedSize? e with
          | some w => w * xs.length
          | none => 4 * xs.length + (lengths.map (fun k ↦ k e)).sum
        | _ => 0)
      (fun _ lengths t ↦ match t with
        | .container fs | .progressiveContainer _ fs =>
          ((fs.zip lengths).map (fun (f, k) ↦
            match SszType.fixedSize? f with | some w => w | none => 4 + k f)).sum
        | _ => 0)
      [] (fun _ _ child rest ↦ child :: rest) xs

private theorem child_byteLengthModels (xs : List SszValue) :
    childLengths xs = xs.map (fun x t ↦ byteLengthModel t x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (fun t ↦ byteLengthModel t x) :: childLengths xs = _
    rw [ih]
    rfl

private theorem byteLengthModel_recurrence (t : SszType) (v : SszValue) :
  byteLengthModel t v = match t, v with
    | .uint w, .uint _ => w
    | .bool, .bool _ => 1
    | .byteVector _, .bytes b => b.size
    | .byteList _, .bytes b => b.size
    | .progressiveByteList, .bytes b => b.size
    | .list e _, .list xs | .progressiveList e, .list xs =>
      match SszType.fixedSize? e with
      | some w => w * xs.length
      | none => 4 * xs.length + (xs.map (fun x ↦ byteLengthModel e x)).sum
    | .container fs, .container xs | .progressiveContainer _ fs, .container xs =>
      ((fs.zip xs).map (fun (f, x) ↦
        match SszType.fixedSize? f with | some w => w | none => 4 + byteLengthModel f x)).sum
    | _, _ => 0 := by
  cases v with
  | uint n => cases t <;> rfl
  | bool b => cases t <;> rfl
  | bytes b => cases t <;> rfl
  | list xs =>
    cases t with
    | list e limit =>
      change (match SszType.fixedSize? e with
        | some w => w * xs.length
        | none => 4 * xs.length + ((childLengths xs).map (fun (k : SszType → Nat) ↦ k e)).sum) = _
      rw [child_byteLengthModels]
      simp only [List.map_map]
      rfl
    | progressiveList e =>
      change (match SszType.fixedSize? e with
        | some w => w * xs.length
        | none => 4 * xs.length + ((childLengths xs).map (fun (k : SszType → Nat) ↦ k e)).sum) = _
      rw [child_byteLengthModels]
      simp only [List.map_map]
      rfl
    | _ => rfl
  | container xs =>
    cases t with
    | container fs =>
      change (((fs.zip (childLengths xs)).map (fun (f, k) ↦
        match SszType.fixedSize? f with | some w => w | none => 4 + k f)).sum) = _
      rw [child_byteLengthModels, List.zip_map_right, List.map_map]
      rfl
    | progressiveContainer mask fs =>
      change (((fs.zip (childLengths xs)).map (fun (f, k) ↦
        match SszType.fixedSize? f with | some w => w | none => 4 + k f)).sum) = _
      rw [child_byteLengthModels, List.zip_map_right, List.map_map]
      rfl
    | _ => rfl

private def headSize (ps : List (SszType × SszValue)) : Nat :=
  (ps.map (fun p ↦ p.1.fixedSize?.getD 4)).sum

private def starts (ps : List (SszType × SszValue)) (ls : List Nat) : List Nat :=
  ((ps.zip ls).foldl (fun (state : Nat × List Nat) p ↦
    match p.1.1.fixedSize? with
    | some _ => state
    | none => (state.1 + p.2, state.2 ++ [state.1])) (headSize ps, [])).2

private def fits (ps : List (SszType × SszValue)) : Prop :=
  ∀ o ∈ starts ps (ps.map (fun p ↦ byteLengthModel p.1 p.2)), o < 2 ^ 32

mutual
  private def serializable : SszType → SszValue → Prop
    | .uint w, .uint n =>
        (w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8 ∨ w = 16 ∨ w = 32) ∧ n < 2 ^ (8 * w)
    | .bool, .bool _ => True
    | .byteVector n, .bytes b => b.size = n
    | .byteList limit, .bytes b => b.size ≤ limit
    | .progressiveByteList, .bytes _ => True
    | .list e limit, .list xs =>
        xs.length ≤ limit ∧ serializableValues e xs ∧ fits (xs.map (fun x ↦ (e, x)))
    | .progressiveList e, .list xs =>
        serializableValues e xs ∧ fits (xs.map (fun x ↦ (e, x)))
    | .container fs, .container xs | .progressiveContainer _ fs, .container xs =>
        serializableFields fs xs ∧ fits (fs.zip xs)
    | _, _ => False
  private def serializableValues (e : SszType) : List SszValue → Prop
    | [] => True
    | x :: xs => serializable e x ∧ serializableValues e xs
  private def serializableFields : List SszType → List SszValue → Prop
    | [], [] => True
    | f :: fs, x :: xs => serializable f x ∧ serializableFields fs xs
    | _, _ => False
end

/-- Byte-local actual-value support. Only emitted offset starts must fit uint32;
unused schemas, raw progressive masks and backing count widths add no premise. -/
def Ssz.Serializable (t : SszType) (v : SszValue) : Prop := serializable t v

private theorem serializableValues_iff (e : SszType) (xs : List SszValue) :
    serializableValues e xs ↔ ∀ x ∈ xs, Ssz.Serializable e x := by
  induction xs with
  | nil => simp [serializableValues]
  | cons x xs ih => simp [serializableValues, ih, Ssz.Serializable]

private theorem serializableFields_iff (fs : List SszType) (xs : List SszValue) :
    serializableFields fs xs ↔ fs.length = xs.length ∧
      ∀ p ∈ fs.zip xs, Ssz.Serializable p.1 p.2 := by
  induction fs generalizing xs with
  | nil => cases xs <;> simp [serializableFields]
  | cons f fs ih =>
    cases xs with
    | nil => simp [serializableFields]
    | cons x xs =>
      simp only [serializableFields, ih, List.length_cons, Nat.succ.injEq,
        List.zip_cons_cons, List.mem_cons, forall_eq_or_imp, Ssz.Serializable]
      exact and_left_comm

/-- Complete decoupled support equation with a self-contained mathematical byte
length. Every actual child is visited; empty actual composites need no unused WF. -/
theorem Ssz.serializable_iff (t : SszType) (v : SszValue) :
  Ssz.Serializable t v ↔
  let byteLength : SszType → SszValue → Nat := fun t v ↦
    SszValue.rec (motive_1 := fun _ ↦ SszType → Nat)
      (motive_2 := fun _ ↦ List (SszType → Nat))
      (fun _ t ↦ match t with | .uint w => w | _ => 0)
      (fun _ t ↦ match t with | .bool => 1 | _ => 0)
      (fun b t ↦ match t with
        | .byteVector _ | .byteList _ | .progressiveByteList => b.size
        | _ => 0)
      (fun xs lengths t ↦ match t with
        | .list e _ | .progressiveList e =>
          match SszType.fixedSize? e with
          | some w => w * xs.length
          | none => 4 * xs.length + (lengths.map (fun k ↦ k e)).sum
        | _ => 0)
      (fun _ lengths t ↦ match t with
        | .container fs | .progressiveContainer _ fs =>
          ((fs.zip lengths).map (fun (f, k) ↦
            match SszType.fixedSize? f with | some w => w | none => 4 + k f)).sum
        | _ => 0)
      [] (fun _ _ child rest ↦ child :: rest) v t
  let headSize := fun (ps : List (SszType × SszValue)) ↦
    (ps.map (fun q ↦ (SszType.fixedSize? q.1).getD 4)).sum
  let starts := fun (ps : List (SszType × SszValue)) (ls : List Nat) ↦
    ((ps.zip ls).foldl (fun (state : Nat × List Nat) q ↦
      match SszType.fixedSize? q.1.1 with
      | some _ => state
      | none => (state.1 + q.2, state.2 ++ [state.1])) (headSize ps, [])).2
  let fits := fun (ps : List (SszType × SszValue)) (ls : List Nat) ↦
    ∀ o ∈ starts ps ls, o < 2 ^ 32
  match t, v with
  | .uint w, .uint n => (w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8 ∨ w = 16 ∨ w = 32) ∧
    n < 2 ^ (8 * w)
  | .bool, .bool _ => True
  | .byteVector n, .bytes b => b.size = n
  | .byteList limit, .bytes b => b.size ≤ limit
  | .progressiveByteList, .bytes _ => True
  | .list e limit, .list xs =>
    let ps := xs.map (fun x ↦ (e, x))
    xs.length ≤ limit ∧ (∀ x ∈ xs, Ssz.Serializable e x) ∧
      fits ps (ps.map (fun q ↦ byteLength q.1 q.2))
  | .progressiveList e, .list xs =>
    let ps := xs.map (fun x ↦ (e, x))
    (∀ x ∈ xs, Ssz.Serializable e x) ∧ fits ps (ps.map (fun q ↦ byteLength q.1 q.2))
  | .container fs, .container xs =>
    let ps := fs.zip xs
    fs.length = xs.length ∧ (∀ q ∈ ps, Ssz.Serializable q.1 q.2) ∧
      fits ps (ps.map (fun q ↦ byteLength q.1 q.2))
  | .progressiveContainer _ fs, .container xs =>
    let ps := fs.zip xs
    fs.length = xs.length ∧ (∀ q ∈ ps, Ssz.Serializable q.1 q.2) ∧
      fits ps (ps.map (fun q ↦ byteLength q.1 q.2))
  | _, _ => False
 := by
  change serializable t v ↔ _
  cases t <;> cases v <;>
    simp only [serializable, serializableValues_iff, serializableFields_iff,
      fits, starts, headSize, and_assoc] <;> rfl

private def littleEndian (w n : Nat) : List UInt8 :=
  (List.range w).map (fun i ↦ UInt8.ofNat ((n / 256 ^ i) % 256))

private structure Writer where
  size : Nat
  write : ByteArray → ByteArray

private def emptyWriter : Writer := ⟨0, id⟩

private def bytesWriter (b : ByteArray) : Writer := ⟨b.size, fun acc ↦ acc ++ b⟩

private def appendWriter (a b : Writer) : Writer :=
  ⟨a.size + b.size, fun acc ↦ b.write (a.write acc)⟩

private def digitsWriter (w n : Nat) : Writer := bytesWriter (littleEndian w n).toByteArray

private def writerHeadSize (ps : List (SszType × Writer)) : Nat :=
  (ps.map (fun p ↦ p.1.fixedSize?.getD 4)).sum

private def planFields : List (SszType × Writer) → Nat → Writer × Writer
  | [], _ => (emptyWriter, emptyWriter)
  | (t, child) :: ps, cursor =>
      match t.fixedSize? with
      | some _ =>
          let rest := planFields ps cursor
          (appendWriter child rest.1, rest.2)
      | none =>
          let rest := planFields ps (cursor + child.size)
          (appendWriter (digitsWriter 4 cursor) rest.1, appendWriter child rest.2)

private def layoutWriter (ps : List (SszType × Writer)) : Writer :=
  let parts := planFields ps (writerHeadSize ps)
  appendWriter parts.1 parts.2

private def modelHeadSize (ps : List (SszType × List UInt8)) : Nat :=
  (ps.map (fun p ↦ p.1.fixedSize?.getD 4)).sum

private def modelFields : List (SszType × List UInt8) → Nat → List UInt8 × List UInt8
  | [], _ => ([], [])
  | (t, child) :: ps, cursor =>
      match t.fixedSize? with
      | some _ =>
          let rest := modelFields ps cursor
          (child ++ rest.1, rest.2)
      | none =>
          let rest := modelFields ps (cursor + child.length)
          (littleEndian 4 cursor ++ rest.1, child ++ rest.2)

private def layoutModel (ps : List (SszType × List UInt8)) : List UInt8 :=
  let parts := modelFields ps (modelHeadSize ps)
  parts.1 ++ parts.2

mutual
  private def reference : SszType → SszValue → List UInt8
    | .uint w, .uint n => littleEndian w n
    | .bool, .bool b => [if b then 1 else 0]
    | .byteVector _, .bytes b | .byteList _, .bytes b |
      .progressiveByteList, .bytes b => b.data.toList
    | .list e _, .list xs | .progressiveList e, .list xs =>
        layoutModel (referenceValues e xs)
    | .container fs, .container xs | .progressiveContainer _ fs, .container xs =>
        layoutModel (referenceFields fs xs)
    | _, _ => []
  private def referenceValues (e : SszType) : List SszValue → List (SszType × List UInt8)
    | [] => []
    | x :: xs => (e, reference e x) :: referenceValues e xs
  private def referenceFields : List SszType → List SszValue → List (SszType × List UInt8)
    | f :: fs, x :: xs => (f, reference f x) :: referenceFields fs xs
    | _, _ => []
end

mutual
  private def prepare : SszType → SszValue → Writer
    | .uint w, .uint n => digitsWriter w n
    | .bool, .bool b => bytesWriter ⟨#[if b then 1 else 0]⟩
    | .byteVector _, .bytes b | .byteList _, .bytes b |
      .progressiveByteList, .bytes b => bytesWriter b
    | .list e _, .list xs | .progressiveList e, .list xs => layoutWriter (prepareValues e xs)
    | .container fs, .container xs | .progressiveContainer _ fs, .container xs =>
        layoutWriter (prepareFields fs xs)
    | _, _ => emptyWriter
  private def prepareValues (e : SszType) : List SszValue → List (SszType × Writer)
    | [] => []
    | x :: xs => (e, prepare e x) :: prepareValues e xs
  private def prepareFields : List SszType → List SszValue → List (SszType × Writer)
    | f :: fs, x :: xs => (f, prepare f x) :: prepareFields fs xs
    | _, _ => []
end

private def Models (w : Writer) (bs : List UInt8) : Prop :=
  w.size = bs.length ∧ ∀ acc, (w.write acc).data.toList = acc.data.toList ++ bs

private theorem empty_models : Models emptyWriter [] := by
  exact ⟨rfl, fun acc ↦ by simp [emptyWriter]⟩

private theorem bytes_models (b : ByteArray) : Models (bytesWriter b) b.data.toList := by
  exact ⟨Array.length_toList.symm, fun acc ↦ ByteArray.toList_data_append⟩

private theorem append_models {a b : Writer} {as bs : List UInt8}
    (ha : Models a as) (hb : Models b bs) : Models (appendWriter a b) (as ++ bs) := by
  constructor
  · simp only [appendWriter, List.length_append, ha.1, hb.1]
  · intro acc
    simp only [appendWriter, hb.2, ha.2, List.append_assoc]

private theorem digits_models (w n : Nat) : Models (digitsWriter w n) (littleEndian w n) := by
  simpa only [digitsWriter, List.toList_data_toByteArray] using
    bytes_models (littleEndian w n).toByteArray

private inductive Aligned : List (SszType × Writer) → List (SszType × List UInt8) → Prop
  | nil : Aligned [] []
  | cons {p : SszType × Writer} {q : SszType × List UInt8}
      {ps : List (SszType × Writer)} {qs : List (SszType × List UInt8)} :
      p.1 = q.1 ∧ Models p.2 q.2 → Aligned ps qs →
      Aligned (p :: ps) (q :: qs)

private theorem planFields_models (ps : List (SszType × Writer))
    (qs : List (SszType × List UInt8))
    (h : Aligned ps qs) (cursor : Nat) :
    Models (planFields ps cursor).1 (modelFields qs cursor).1 ∧
      Models (planFields ps cursor).2 (modelFields qs cursor).2 := by
  induction h generalizing cursor with
  | nil => exact ⟨empty_models, empty_models⟩
  | cons h hs ih =>
    rcases h with ⟨ht, hc⟩
    rename_i p q ps qs
    rcases p with ⟨t, child⟩
    rcases q with ⟨u, bytes⟩
    dsimp only at ht hc
    subst u
    simp only [planFields, modelFields]
    split
    · exact ⟨append_models hc (ih cursor).1, (ih cursor).2⟩
    · rw [hc.1]
      exact ⟨append_models (digits_models 4 cursor) (ih _).1,
        append_models hc (ih _).2⟩

private theorem layout_models (ps : List (SszType × Writer))
    (qs : List (SszType × List UInt8))
    (h : Aligned ps qs) :
    Models (layoutWriter ps) (layoutModel qs) := by
  have hh : writerHeadSize ps = modelHeadSize qs := by
    induction h with
    | nil => rfl
    | cons h hs ih =>
      simp only [writerHeadSize, modelHeadSize, List.map_cons, List.sum_cons] at *
      rw [h.1, ih]
  simp only [layoutWriter, layoutModel, hh]
  have hm := planFields_models ps qs h (modelHeadSize qs)
  exact append_models hm.1 hm.2

mutual
  private theorem prepare_models (t : SszType) (v : SszValue) :
      Models (prepare t v) (reference t v) := by
    cases t <;> cases v <;>
      first
      | exact digits_models _ _
      | exact bytes_models _
      | exact layout_models _ _ (prepareValues_models _ _)
      | exact layout_models _ _ (prepareFields_models _ _)
      | exact empty_models
  private theorem prepareValues_models (e : SszType) (xs : List SszValue) :
      Aligned
        (prepareValues e xs) (referenceValues e xs) := by
    cases xs with
    | nil => exact .nil
    | cons x xs => exact .cons ⟨rfl, prepare_models e x⟩ (prepareValues_models e xs)
  private theorem prepareFields_models (fs : List SszType) (xs : List SszValue) :
      Aligned
        (prepareFields fs xs) (referenceFields fs xs) := by
    cases fs <;> cases xs <;> first
      | exact .nil
      | exact .cons ⟨rfl, prepare_models _ _⟩ (prepareFields_models _ _)
end

-- Cache structural classification once, including descriptors of unused schemas.
-- This computes metadata only; it neither checks nor assumes schema admission.
private inductive SchemaCache where
  | node (type : SszType) (width : Option Nat) (children : List SchemaCache)

private def SchemaCache.type : SchemaCache → SszType
  | .node t _ _ => t

private def SchemaCache.width : SchemaCache → Option Nat
  | .node _ w _ => w

private def cacheWidths (cs : List SchemaCache) : Option Nat :=
  cs.foldr (fun c acc ↦ match c.width, acc with
    | some n, some m => some (n + m)
    | _, _ => none) (some 0)

mutual
  private def cacheSchema : SszType → SchemaCache
    | .uint w => .node (.uint w) (some w) []
    | .bool => .node .bool (some 1) []
    | .byteVector n => .node (.byteVector n) (some n) []
    | .byteList n => .node (.byteList n) none []
    | .progressiveByteList => .node .progressiveByteList none []
    | .list e limit => .node (.list e limit) none [cacheSchema e]
    | .progressiveList e => .node (.progressiveList e) none [cacheSchema e]
    | .container fs =>
        let cs := cacheSchemas fs
        .node (.container fs) (cacheWidths cs) cs
    | .progressiveContainer mask fs =>
        let cs := cacheSchemas fs
        .node (.progressiveContainer mask fs) (cacheWidths cs) cs
  private def cacheSchemas : List SszType → List SchemaCache
    | [] => []
    | f :: fs => cacheSchema f :: cacheSchemas fs
end

private theorem cacheSchema_type (t : SszType) : (cacheSchema t).type = t := by
  cases t <;> rfl

mutual
  private theorem cacheSchema_width (t : SszType) :
      (cacheSchema t).width = t.fixedSize? := by
    rw [SszType.fixedSize?_eq]
    cases t <;> first | exact cacheSchemas_width _ | rfl
  private theorem cacheSchemas_width (fs : List SszType) :
      cacheWidths (cacheSchemas fs) = fs.foldr
        (fun f acc ↦ match f.fixedSize?, acc with
          | some n, some m => some (n + m)
          | _, _ => none) (some 0) := by
    cases fs with
    | nil => rfl
    | cons f fs =>
      change (match (cacheSchema f).width, cacheWidths (cacheSchemas fs) with
        | some n, some m => some (n + m)
        | _, _ => none) = _
      rw [cacheSchema_width, cacheSchemas_width]
      rfl
end

private def cachedHeadSize (ps : List (Option Nat × Writer)) : Nat :=
  (ps.map (fun p ↦ p.1.getD 4)).sum

private def cachedPlanFields : List (Option Nat × Writer) → Nat → Writer × Writer
  | [], _ => (emptyWriter, emptyWriter)
  | (width, child) :: ps, cursor =>
      match width with
      | some _ =>
          let rest := cachedPlanFields ps cursor
          (appendWriter child rest.1, rest.2)
      | none =>
          let rest := cachedPlanFields ps (cursor + child.size)
          (appendWriter (digitsWriter 4 cursor) rest.1, appendWriter child rest.2)

private def cachedLayout (ps : List (Option Nat × Writer)) : Writer :=
  let parts := cachedPlanFields ps (cachedHeadSize ps)
  appendWriter parts.1 parts.2

private theorem cachedPlanFields_eq (ps : List (SszType × Writer)) (cursor : Nat) :
    cachedPlanFields (ps.map (fun p ↦ (p.1.fixedSize?, p.2))) cursor =
      planFields ps cursor := by
  induction ps generalizing cursor with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, cachedPlanFields, planFields]
    split <;> rw [ih]

private theorem cachedLayout_eq (ps : List (SszType × Writer)) :
    cachedLayout (ps.map (fun p ↦ (p.1.fixedSize?, p.2))) = layoutWriter ps := by
  simp only [cachedLayout, cachedHeadSize, List.map_map, layoutWriter,
    writerHeadSize, Function.comp_def, cachedPlanFields_eq]

mutual
  private def prepareCached : SchemaCache → SszValue → Writer
    | .node t _ children, v =>
        match t, v with
        | .uint w, .uint n => digitsWriter w n
        | .bool, .bool b => bytesWriter ⟨#[if b then 1 else 0]⟩
        | .byteVector _, .bytes b | .byteList _, .bytes b |
          .progressiveByteList, .bytes b => bytesWriter b
        | .list _ _, .list xs | .progressiveList _, .list xs =>
            match children with
            | [] => emptyWriter
            | c :: _ => cachedLayout (prepareCachedValues c xs)
        | .container _, .container xs | .progressiveContainer _ _, .container xs =>
            cachedLayout (prepareCachedFields children xs)
        | _, _ => emptyWriter
  private def prepareCachedValues (c : SchemaCache) :
      List SszValue → List (Option Nat × Writer)
    | [] => []
    | x :: xs => (c.width, prepareCached c x) :: prepareCachedValues c xs
  private def prepareCachedFields : List SchemaCache → List SszValue →
      List (Option Nat × Writer)
    | c :: cs, x :: xs => (c.width, prepareCached c x) :: prepareCachedFields cs xs
    | _, _ => []
end

mutual
  private theorem prepareCached_eq (t : SszType) (v : SszValue) :
      prepareCached (cacheSchema t) v = prepare t v := by
    cases t <;> cases v <;>
      simp only [cacheSchema, prepareCached, prepare]
    all_goals first
      | rfl
      | (rw [prepareCachedValues_eq, cachedLayout_eq])
      | (rw [prepareCachedFields_eq, cachedLayout_eq])
  private theorem prepareCachedValues_eq (e : SszType) (xs : List SszValue) :
      prepareCachedValues (cacheSchema e) xs =
        (prepareValues e xs).map (fun p ↦ (p.1.fixedSize?, p.2)) := by
    cases xs with
    | nil => rfl
    | cons x xs =>
      simp only [prepareCachedValues, prepareValues, List.map_cons]
      rw [cacheSchema_width, prepareCached_eq, prepareCachedValues_eq]
  private theorem prepareCachedFields_eq (fs : List SszType) (xs : List SszValue) :
      prepareCachedFields (cacheSchemas fs) xs =
        (prepareFields fs xs).map (fun p ↦ (p.1.fixedSize?, p.2)) := by
    cases fs <;> cases xs <;> first
      | rfl
      | (simp only [cacheSchemas, prepareCachedFields, prepareFields, List.map_cons]
         rw [cacheSchema_width, prepareCached_eq, prepareCachedFields_eq])
end

/-- Serialize a byte-supported actual SSZ value using cached sizes and packed
writers. Source: EELS `src/ethereum/utils/ssz.py:129–131,263–296` and locked
eth-remerkleable 0.1.31 serialization. Raw masks do not affect emitted bytes. -/
def Ssz.encode (t : SszType) (v : SszValue) (h : Ssz.Serializable t v) : ByteArray :=
  let _ := h
  let plan := prepareCached (cacheSchema t) v
  plan.write (ByteArray.emptyWithCapacity plan.size)

private theorem encode_reference (t : SszType) (v : SszValue)
    (h : Ssz.Serializable t v) : (Ssz.encode t v h).data.toList = reference t v := by
  simp only [Ssz.encode, prepareCached_eq]
  exact (prepare_models t v).2 (ByteArray.emptyWithCapacity (prepare t v).size)

private theorem referenceValues_map (e : SszType) (xs : List SszValue) :
    referenceValues e xs = xs.map (fun x ↦ (e, reference e x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [referenceValues, List.map_cons, ih]

private theorem referenceFields_map (fs : List SszType) (xs : List SszValue) :
    referenceFields fs xs = (fs.zip xs).map (fun p ↦ (p.1, reference p.1 p.2)) := by
  induction fs generalizing xs with
  | nil => cases xs <;> rfl
  | cons f fs ih =>
    cases xs with
    | nil => rfl
    | cons x xs => simp only [referenceFields, List.zip_cons_cons, List.map_cons, ih]

private def layoutStep (s : Nat × List UInt8 × List UInt8)
    (p : SszType × List UInt8) : Nat × List UInt8 × List UInt8 :=
  match p.1.fixedSize? with
  | some _ => (s.1, s.2.1 ++ p.2, s.2.2)
  | none => (s.1 + p.2.length, s.2.1 ++ littleEndian 4 s.1, s.2.2 ++ p.2)

private theorem modelFields_fold (ps : List (SszType × List UInt8))
    (cursor : Nat) (head tail : List UInt8) :
    let s := ps.foldl layoutStep (cursor, head, tail)
    s.2.1 ++ s.2.2 =
      (head ++ (modelFields ps cursor).1) ++ (tail ++ (modelFields ps cursor).2) := by
  induction ps generalizing cursor head tail with
  | nil => simp [modelFields]
  | cons p ps ih =>
    rcases p with ⟨t, bytes⟩
    simp only [List.foldl_cons, layoutStep, modelFields]
    split <;> simp only [ih, List.append_assoc]

private def layoutBytes (ps : List (SszType × SszValue))
    (bs : List ByteArray) : List UInt8 :=
  let s := (ps.zip bs).foldl (fun (s : Nat × List UInt8 × List UInt8) p ↦
    match p.1.1.fixedSize? with
    | some _ => (s.1, s.2.1 ++ p.2.data.toList, s.2.2)
    | none => (s.1 + p.2.size, s.2.1 ++ littleEndian 4 s.1,
        s.2.2 ++ p.2.data.toList)) (headSize ps, [], [])
  s.2.1 ++ s.2.2

private theorem zip_headSize (ps : List (SszType × SszValue)) (bs : List ByteArray)
    (h : ps.length = bs.length) :
    modelHeadSize ((ps.zip bs).map (fun p ↦ (p.1.1, p.2.data.toList))) = headSize ps := by
  induction ps generalizing bs with
  | nil => cases bs <;> simp_all [headSize, modelHeadSize]
  | cons p ps ih =>
    cases bs with
    | nil => simp at h
    | cons b bs =>
      simp only [modelHeadSize, headSize, List.zip_cons_cons, List.map_cons,
        List.sum_cons]
      congr 1
      exact ih bs (by simpa using h)

private theorem layoutModel_bytes (ps : List (SszType × SszValue)) (bs : List ByteArray)
    (h : ps.length = bs.length) :
    layoutModel ((ps.zip bs).map (fun p ↦ (p.1.1, p.2.data.toList))) =
      layoutBytes ps bs := by
  unfold layoutModel
  rw [zip_headSize ps bs h]
  have hm := modelFields_fold ((ps.zip bs).map (fun p ↦ (p.1.1, p.2.data.toList)))
    (headSize ps) [] []
  simp only [List.nil_append, List.foldl_map, layoutStep, Array.length_toList] at hm
  exact hm.symm

private theorem cert_reference (ps : List (SszType × SszValue))
    (hs : ∀ p ∈ ps, Ssz.Serializable p.1 p.2) (bs : List ByteArray)
    (hl : ps.length = bs.length)
    (hc : ∀ p ∈ ps.zip bs, ∀ hp : Ssz.Serializable p.1.1 p.1.2,
      Ssz.encode p.1.1 p.1.2 hp = p.2) :
    ps.map (fun p ↦ (p.1, reference p.1 p.2)) =
      (ps.zip bs).map (fun p ↦ (p.1.1, p.2.data.toList)) := by
  induction ps generalizing bs with
  | nil => cases bs <;> simp_all
  | cons p ps ih =>
    cases bs with
    | nil => simp at hl
    | cons b bs =>
      simp only [List.map_cons, List.zip_cons_cons]
      congr 1
      · have he := hc (p, b) (by simp) (hs p (by simp))
        have hr := encode_reference p.1 p.2 (hs p (by simp))
        rw [he] at hr
        exact congrArg (fun bytes ↦ (p.1, bytes)) hr.symm
      · apply ih (fun p hp ↦ hs p (by simp [hp])) bs (by simpa using hl)
        intro q hq hp
        exact hc q (by simp [hq]) hp

private theorem values_support (e : SszType) (xs : List SszValue)
    (hs : ∀ x ∈ xs, Ssz.Serializable e x) :
    ∀ p ∈ xs.map (fun x ↦ (e, x)), Ssz.Serializable p.1 p.2 := by
  intro p hp
  rcases List.mem_map.mp hp with ⟨x, hx, rfl⟩
  exact hs x hx

private theorem encode_values (e : SszType) (xs : List SszValue)
    (hs : ∀ x ∈ xs, Ssz.Serializable e x) (bs : List ByteArray)
    (hc : (xs.map (fun x ↦ (e, x))).length = bs.length ∧
      ∀ p ∈ (xs.map (fun x ↦ (e, x))).zip bs,
        ∀ hp : Ssz.Serializable p.1.1 p.1.2, Ssz.encode p.1.1 p.1.2 hp = p.2) :
    layoutModel (referenceValues e xs) = layoutBytes (xs.map (fun x ↦ (e, x))) bs := by
  rw [referenceValues_map]
  have hm := cert_reference (xs.map (fun x ↦ (e, x)))
    (values_support e xs hs) bs hc.1 hc.2
  simp only [List.map_map, Function.comp_def] at hm
  rw [hm]
  exact layoutModel_bytes _ _ hc.1

private theorem encode_fields (fs : List SszType) (xs : List SszValue)
    (hs : ∀ p ∈ fs.zip xs, Ssz.Serializable p.1 p.2) (bs : List ByteArray)
    (hc : (fs.zip xs).length = bs.length ∧
      ∀ p ∈ (fs.zip xs).zip bs,
        ∀ hp : Ssz.Serializable p.1.1 p.1.2, Ssz.encode p.1.1 p.1.2 hp = p.2) :
    layoutModel (referenceFields fs xs) = layoutBytes (fs.zip xs) bs := by
  rw [referenceFields_map, cert_reference (fs.zip xs) hs bs hc.1 hc.2]
  exact layoutModel_bytes _ _ hc.1

private def fieldWidth (p : SszType × List UInt8) : Nat :=
  match p.1.fixedSize? with
  | some _ => p.2.length
  | none => 4 + p.2.length

private theorem modelFields_width (ps : List (SszType × List UInt8)) (cursor : Nat) :
    (modelFields ps cursor).1.length + (modelFields ps cursor).2.length =
      (ps.map fieldWidth).sum := by
  induction ps generalizing cursor with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨t, bytes⟩
    simp only [modelFields, List.map_cons, List.sum_cons, fieldWidth]
    split <;> simp only [List.length_append, littleEndian, List.length_map,
      List.length_range] <;> have hr := ih (cursor + bytes.length) <;>
      have hs := ih cursor <;> omega

private theorem layoutModel_width (ps : List (SszType × List UInt8)) :
    (layoutModel ps).length = (ps.map fieldWidth).sum := by
  simp only [layoutModel, List.length_append, modelFields_width]

private def fixedWidths (fs : List SszType) : Option Nat :=
  fs.foldr (fun f acc ↦ match f.fixedSize?, acc with
    | some n, some m => some (n + m)
    | _, _ => none) (some 0)

mutual
  private theorem reference_fixed_width (t : SszType) (v : SszValue)
      (h : Ssz.Serializable t v) (w : Nat) (hf : t.fixedSize? = some w) :
      (reference t v).length = w := by
    rw [SszType.fixedSize?_eq] at hf
    cases t <;> cases v <;> dsimp only at hf
    all_goals first
      | exact False.elim (show False from h)
      | contradiction
      | skip
    case uint.uint n value =>
      cases hf
      simp [reference, littleEndian]
    case bool.bool b => cases hf; rfl
    case byteVector.bytes n b =>
      cases hf
      exact h
    case container.container fs xs =>
      rw [reference, layoutModel_width]
      exact referenceFields_fixed fs xs h.1 w hf
    case progressiveContainer.container mask fs xs =>
      rw [reference, layoutModel_width]
      exact referenceFields_fixed fs xs h.1 w hf
  private theorem referenceFields_fixed (fs : List SszType) (xs : List SszValue)
      (h : serializableFields fs xs) (w : Nat) (hf : fixedWidths fs = some w) :
      ((referenceFields fs xs).map fieldWidth).sum = w := by
    cases fs with
    | nil =>
      cases xs with
      | nil => cases hf; rfl
      | cons x xs => exact h.elim
    | cons f fs =>
      cases xs with
      | nil => exact h.elim
      | cons x xs =>
        change (match f.fixedSize?, fixedWidths fs with
          | some n, some m => some (n + m)
          | _, _ => none) = some w at hf
        cases he : f.fixedSize? with
        | none => simp [he] at hf
        | some n =>
          cases ht : fixedWidths fs with
          | none => simp [he, ht] at hf
          | some m =>
            have hw : n + m = w := by simpa [he, ht] using hf
            simp only [referenceFields, List.map_cons, List.sum_cons, fieldWidth, he]
            rw [reference_fixed_width f x h.1 n he,
              referenceFields_fixed fs xs h.2 m ht, hw]
end

mutual
  private theorem reference_size (t : SszType) (v : SszValue)
      (h : Ssz.Serializable t v) : (reference t v).length = byteLengthModel t v := by
    rw [byteLengthModel_recurrence]
    cases t <;> cases v <;> first
      | exact False.elim (show False from h)
      | rfl
      | exact Array.length_toList
      | (solve | simp only [reference, littleEndian, List.length_map, List.length_range])
      | (rw [reference, layoutModel_width]; exact referenceValues_size _ _ h.2.1)
      | (rw [reference, layoutModel_width]; exact referenceValues_size _ _ h.1)
      | (rw [reference, layoutModel_width]; exact referenceFields_size _ _ h.1)
  private theorem referenceValues_size (e : SszType) (xs : List SszValue)
      (h : serializableValues e xs) :
      ((referenceValues e xs).map fieldWidth).sum =
        match e.fixedSize? with
        | some w => w * xs.length
        | none => 4 * xs.length + (xs.map (fun x ↦ byteLengthModel e x)).sum := by
    cases xs with
    | nil => cases e.fixedSize? <;> simp [referenceValues]
    | cons x xs =>
      have hr := referenceValues_size e xs h.2
      simp only [referenceValues, List.map_cons, List.sum_cons, fieldWidth,
        List.length_cons]
      cases he : e.fixedSize? with
      | none =>
        simp only [he] at hr ⊢
        rw [reference_size e x h.1, hr]
        omega
      | some w =>
        simp only [he] at hr ⊢
        rw [reference_fixed_width e x h.1 w he, hr]
        simp only [Nat.mul_add, Nat.mul_one]
        omega
  private theorem referenceFields_size (fs : List SszType) (xs : List SszValue)
      (h : serializableFields fs xs) :
      ((referenceFields fs xs).map fieldWidth).sum =
        ((fs.zip xs).map (fun p ↦
          match p.1.fixedSize? with
          | some w => w
          | none => 4 + byteLengthModel p.1 p.2)).sum := by
    cases fs with
    | nil => cases xs <;> rfl
    | cons f fs =>
      cases xs with
      | nil => rfl
      | cons x xs =>
        simp only [referenceFields, List.map_cons, List.sum_cons, fieldWidth,
          List.zip_cons_cons]
        rw [referenceFields_size fs xs h.2]
        cases he : f.fixedSize? with
        | none => rw [reference_size f x h.1]
        | some w => rw [reference_fixed_width f x h.1 w he]
end

private theorem encode_size (t : SszType) (v : SszValue)
    (h : Ssz.Serializable t v) : (Ssz.encode t v h).size = byteLengthModel t v := by
  change (Ssz.encode t v h).data.size = _
  rw [← Array.length_toList, encode_reference, reference_size t v h]

private theorem encode_proof_independent (t : SszType) (v : SszValue)
    (h h' : Ssz.Serializable t v) : Ssz.encode t v h = Ssz.encode t v h' := rfl

/-- Complete whole-byte constructor equation. Ordered child certificates exist
under support; the final cursor is never encoded merely because it is final. -/
theorem Ssz.encode_eq (t : SszType) (v : SszValue) (h : Ssz.Serializable t v) :
  let r := (Ssz.encode t v h).data.toList
  let littleEndian := fun (w n : Nat) ↦
    (List.range w).map (fun i ↦ UInt8.ofNat ((n / 256 ^ i) % 256))
  let headSize := fun (ps : List (SszType × SszValue)) ↦
    (ps.map (fun q ↦ (SszType.fixedSize? q.1).getD 4)).sum
  let layout := fun (ps : List (SszType × SszValue)) (bs : List ByteArray) ↦
    let state := (ps.zip bs).foldl
      (fun (state : Nat × List UInt8 × List UInt8) q ↦
        match SszType.fixedSize? q.1.1 with
        | some _ => (state.1, state.2.1 ++ q.2.data.toList, state.2.2)
        | none => (state.1 + q.2.size, state.2.1 ++ littleEndian 4 state.1,
          state.2.2 ++ q.2.data.toList)) (headSize ps, [], [])
    state.2.1 ++ state.2.2
  let cert := fun (ps : List (SszType × SszValue)) (bs : List ByteArray) ↦
    ps.length = bs.length ∧
      ∀ q ∈ ps.zip bs, ∀ hc : Ssz.Serializable q.1.1 q.1.2, Ssz.encode q.1.1 q.1.2 hc = q.2
  match t, v with
  | .uint w, .uint n => r = littleEndian w n
  | .bool, .bool b => r = [if b then 1 else 0]
  | .byteVector _, .bytes b => r = b.data.toList
  | .byteList _, .bytes b => r = b.data.toList
  | .progressiveByteList, .bytes b => r = b.data.toList
  | .list e _, .list xs =>
    let ps := xs.map (fun x ↦ (e, x))
    ∀ bs : List ByteArray, cert ps bs → r = layout ps bs
  | .progressiveList e, .list xs =>
    let ps := xs.map (fun x ↦ (e, x))
    ∀ bs : List ByteArray, cert ps bs → r = layout ps bs
  | .container fs, .container xs =>
    let ps := fs.zip xs
    ∀ bs : List ByteArray, cert ps bs → r = layout ps bs
  | .progressiveContainer _ fs, .container xs =>
    let ps := fs.zip xs
    ∀ bs : List ByteArray, cert ps bs → r = layout ps bs
  | _, _ => False
 := by
  change (let r := (Ssz.encode t v h).data.toList; _)
  rw [encode_reference]
  cases t <;> cases v <;> dsimp only [reference]
  all_goals first
    | rfl
    | exact False.elim (show False from h)
    | skip
  case list.list e limit xs =>
    intro bs hc
    exact encode_values e xs ((serializableValues_iff e xs).mp h.2.1) bs hc
  case progressiveList.list e xs =>
    intro bs hc
    exact encode_values e xs ((serializableValues_iff e xs).mp h.1) bs hc
  case container.container fs xs =>
    intro bs hc
    exact encode_fields fs xs ((serializableFields_iff fs xs).mp h.1).2 bs hc
  case progressiveContainer.container mask fs xs =>
    intro bs hc
    exact encode_fields fs xs ((serializableFields_iff fs xs).mp h.1).2 bs hc

private def Certificate
    (E : (t : SszType) → (v : SszValue) → Ssz.Serializable t v → ByteArray)
    (ps : List (SszType × SszValue)) (bs : List ByteArray) : Prop :=
  ps.length = bs.length ∧ ∀ p ∈ ps.zip bs,
    ∀ h : Ssz.Serializable p.1.1 p.1.2, E p.1.1 p.1.2 h = p.2

private theorem certificate_exists (ps : List (SszType × SszValue))
    (hs : ∀ p ∈ ps, Ssz.Serializable p.1 p.2) :
    ∃ bs, Certificate Ssz.encode ps bs := by
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

private def ResultLaw
    (E : (t : SszType) → (v : SszValue) → Ssz.Serializable t v → ByteArray)
    (t : SszType) (v : SszValue) (h : Ssz.Serializable t v) : Prop :=
  let r := (E t v h).data.toList
  match t, v with
  | .uint w, .uint n => r = littleEndian w n
  | .bool, .bool b => r = [if b then 1 else 0]
  | .byteVector _, .bytes b | .byteList _, .bytes b |
    .progressiveByteList, .bytes b => r = b.data.toList
  | .list e _, .list xs | .progressiveList e, .list xs =>
      ∀ bs, Certificate E (xs.map (fun x ↦ (e, x))) bs →
        r = layoutBytes (xs.map (fun x ↦ (e, x))) bs
  | .container fs, .container xs | .progressiveContainer _ fs, .container xs =>
      ∀ bs, Certificate E (fs.zip xs) bs → r = layoutBytes (fs.zip xs) bs
  | _, _ => False

private theorem bytes_ext {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b :=
  ByteArray.ext (Array.toList_inj.mp h)

private theorem certified_layout_unique
    (E : (t : SszType) → (v : SszValue) → Ssz.Serializable t v → ByteArray)
    (ps : List (SszType × SszValue)) (hs : ∀ p ∈ ps, Ssz.Serializable p.1 p.2)
    (a b : ByteArray)
    (ha : ∀ bs, Certificate E ps bs → a.data.toList = layoutBytes ps bs)
    (hb : ∀ bs, Certificate Ssz.encode ps bs → b.data.toList = layoutBytes ps bs)
    (children : ∀ p ∈ ps, ∀ h, E p.1 p.2 h = Ssz.encode p.1 p.2 h) : a = b := by
  obtain ⟨bs, hc⟩ := certificate_exists ps hs
  have he : Certificate E ps bs := by
    refine ⟨hc.1, ?_⟩
    intro q hq h
    rw [children q.1 (List.of_mem_zip hq).1 h]
    exact hc.2 q hq h
  exact bytes_ext ((ha bs he).trans (hb bs hc).symm)

mutual
  private theorem result_determined
      (E : (t : SszType) → (v : SszValue) → Ssz.Serializable t v → ByteArray)
      (law : ∀ t v h, ResultLaw E t v h)
      (t : SszType) (v : SszValue) (h : Ssz.Serializable t v) :
      E t v h = Ssz.encode t v h := by
    have he := law t v h
    have hr : ResultLaw Ssz.encode t v h := Ssz.encode_eq t v h
    cases t <;> cases v <;> first
      | exact False.elim (show False from h)
      | exact bytes_ext (he.trans hr.symm)
      | skip
    case list.list e limit xs =>
      exact certified_layout_unique E _
        (values_support e xs ((serializableValues_iff e xs).mp h.2.1)) _ _ he hr
        (determinedValues E law e xs)
    case progressiveList.list e xs =>
      exact certified_layout_unique E _
        (values_support e xs ((serializableValues_iff e xs).mp h.1)) _ _ he hr
        (determinedValues E law e xs)
    case container.container fs xs =>
      exact certified_layout_unique E _ ((serializableFields_iff fs xs).mp h.1).2
        _ _ he hr (determinedFields E law fs xs)
    case progressiveContainer.container mask fs xs =>
      exact certified_layout_unique E _ ((serializableFields_iff fs xs).mp h.1).2
        _ _ he hr (determinedFields E law fs xs)
  private theorem determinedValues
      (E : (t : SszType) → (v : SszValue) → Ssz.Serializable t v → ByteArray)
      (law : ∀ t v h, ResultLaw E t v h) (e : SszType) (xs : List SszValue) :
      ∀ p ∈ xs.map (fun x ↦ (e, x)), ∀ h,
        E p.1 p.2 h = Ssz.encode p.1 p.2 h := by
    cases xs with
    | nil => simp
    | cons x xs =>
      intro p hp h
      simp only [List.map_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact result_determined E law e x h
      · exact determinedValues E law e xs p hp h
  private theorem determinedFields
      (E : (t : SszType) → (v : SszValue) → Ssz.Serializable t v → ByteArray)
      (law : ∀ t v h, ResultLaw E t v h) (fs : List SszType) (xs : List SszValue) :
      ∀ p ∈ fs.zip xs, ∀ h, E p.1 p.2 h = Ssz.encode p.1 p.2 h := by
    cases fs with
    | nil => simp
    | cons f fs =>
      cases xs with
      | nil => simp
      | cons x xs =>
        intro p hp h
        simp only [List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact result_determined E law f x h
        · exact determinedFields E law fs xs p hp h
end

end STFSpec.Codec
