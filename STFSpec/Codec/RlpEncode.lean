/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.RlpTyped

/-!
# Two-pass RLP encoding

Library `EthCodec`. Locked ethereum-rlp 0.1.6 `ethereum_rlp/rlp.py:66–135`.
A structural planning pass caches sizes and writers; one pre-sized packed output
is passed through those writers in child order. The readable byte-list model and
ordinary observation laws apply to every item. Pinned/standard correspondence
requires `Encodable`; Q47 owns the modular-tag total completion outside it.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§2–7.
-/

namespace STFSpec.Codec.Rlp

open STFSpec.Base

/-- Total length-prefix byte model. Tags wrap in UInt8; length digits remain exact.
Locked `ethereum_rlp/rlp.py:100–108,119–126`; standard-domain scope is Q47. -/
def lengthPrefixModel (short long : UInt8) (len : Nat) : List UInt8 :=
  if len < 56 then [UInt8.ofNat (short.toNat + len)] else
    UInt8.ofNat (long.toNat + (Uint.toBeBytes len).size) :: (Uint.toBeBytes len).toList

/-- Packed internal length-prefix helper; locked `rlp.py:100–108,119–126`.
Q47 selects modular tags and exact unbounded minimal digits for totality. -/
def encodeLengthPrefix (short long : UInt8) (len : Nat) : ByteArray :=
  if len < 56 then ⟨#[UInt8.ofNat (short.toNat + len)]⟩ else
    let digits := Uint.toBeBytes len
    ⟨#[UInt8.ofNat (long.toNat + digits.size)]⟩ ++ digits.toByteArray

/-- Packed prefixes equal their readable list model for every natural length. -/
theorem toList_encodeLengthPrefix (short long : UInt8) (len : Nat) :
    (encodeLengthPrefix short long len).data.toList = lengthPrefixModel short long len := by
  unfold encodeLengthPrefix lengthPrefixModel
  split
  · rfl
  · rw [ByteArray.toList_data_append, Bytes.toList_toByteArray]
    rfl

/-- Short prefixes contain exactly the one short tag. -/
theorem lengthPrefixModel_short (short long : UInt8) (len : Nat) (h : len < 56) :
    lengthPrefixModel short long len = [UInt8.ofNat (short.toNat + len)] := by
  simp only [lengthPrefixModel, ite_eq_left h]

/-- Long prefixes preserve the ordered minimal length digits after one tag. -/
theorem lengthPrefixModel_long (short long : UInt8) (len : Nat) (h : 56 ≤ len) :
    lengthPrefixModel short long len =
      UInt8.ofNat (long.toNat + (Uint.toBeBytes len).size) ::
        (Uint.toBeBytes len).toList := by
  simp only [lengthPrefixModel, ite_eq_right (by omega : ¬len < 56)]

/-- Prefix width is one tag plus exactly the minimal length digits in long form. -/
theorem size_encodeLengthPrefix (short long : UInt8) (len : Nat) :
    (encodeLengthPrefix short long len).size =
      if len < 56 then 1 else 1 + (Uint.toBeBytes len).size := by
  change (encodeLengthPrefix short long len).data.size = _
  rw [← Array.length_toList, toList_encodeLengthPrefix]
  unfold lengthPrefixModel
  split
  · rfl
  · rw [List.length_cons, Bytes.length_toList]
    omega

/-- The helper's short tag has the specified unwrapped value when it fits a byte. -/
theorem short_tag_toNat (short : UInt8) (len : Nat) (h : short.toNat + len < 256) :
    (UInt8.ofNat (short.toNat + len)).toNat = short.toNat + len :=
  UInt8.toNat_ofNat_of_lt' h

/-- At most eight length digits give exact standard string/list long tags. -/
theorem long_tag_toNat (long : UInt8) (len : Nat)
    (hl : long.toNat ≤ 247) (h : (Uint.toBeBytes len).size ≤ 8) :
    (UInt8.ofNat (long.toNat + (Uint.toBeBytes len).size)).toNat =
      long.toNat + (Uint.toBeBytes len).size := by
  apply UInt8.toNat_ofNat_of_lt'
  change _ < 256
  omega

/-- The length digits recover the complete length, with no truncation. -/
theorem length_digits_value (len : Nat) :
    (Uint.toBeBytes len).toList.foldl (fun a b ↦ 256 * a + b.toNat) 0 = len := by
  rw [← Uint.ofBeBytes_eq_fold, Uint.ofBeBytes_toBeBytes]

/-- Complete minimal-width characterization, including zero's empty digits. -/
theorem length_digits_width (len k : Nat) :
    (Uint.toBeBytes len).size ≤ k ↔ len < 256 ^ k := by
  rw [Uint.size_toBeBytes_le_iff, Nat.pow_mul]

/-- A positive length has a nonzero first minimal digit. -/
theorem length_digits_head (len : Nat) (h : len ≠ 0) :
    (Uint.toBeBytes len).toList.head? ≠ some 0 :=
  Uint.toList_toBeBytes_head_ne_zero len h

/-- Every length digit appears in high-to-low significance order. -/
theorem length_digits_order (len : Nat) :
    (Uint.toBeBytes len).toList =
      (List.range (Uint.toBeBytes len).size).map
        (fun i ↦ UInt8.ofNat (len >>> (8 * ((Uint.toBeBytes len).size - 1 - i)))) := by
  let b := Uint.toBeBytes len
  let k := b.size
  have hb : b.size = k := rfl
  cases hc : (FixedBytes.ofBytes? b : Option (FixedBytes k)) with
  | none => exact False.elim (FixedBytes.ofBytes?_eq_none_iff.mp hc hb)
  | some z =>
    have hz : z.toBytes = b := (FixedBytes.ofBytes?_eq_some_iff.mp hc).2
    have hv : z.toNat = len := by
      rw [FixedBytes.toNat_eq_fold, hz, ← Uint.ofBeBytes_eq_fold,
        Uint.ofBeBytes_toBeBytes]
    have hn : len < 2 ^ (8 * k) :=
      (Uint.size_toBeBytes_le_iff len k).mp (Nat.le_refl _)
    have he : (FixedBytes.ofNat len : FixedBytes k) = z := by
      apply FixedBytes.toNat_inj.mp
      rw [FixedBytes.toNat_ofNat_of_lt len hn, hv]
    change b.toList = (List.range k).map (fun i ↦ UInt8.ofNat (len >>> (8 * (k - 1 - i))))
    rw [← hz, ← he, FixedBytes.toBytes_ofNat, Bytes.toList_generate]

private def single (b : ByteArray) : Prop :=
  b.size = 1 ∧ (b[0]?.getD 128).toNat < 128

private instance (b : ByteArray) : Decidable (single b) :=
  inferInstanceAs (Decidable (_ ∧ _))

mutual
  /-- Readable total RLP byte-list reference; `rlp.py:66–128`, with Q47 completion. -/
  def encodeModel : RlpItem → List UInt8
    | .bytes b => if single b then b.data.toList else
        lengthPrefixModel 128 183 b.size ++ b.data.toList
    | .list xs => let bs := encodePayloadModel xs
        lengthPrefixModel 192 247 bs.length ++ bs
  /-- Ordered concatenation of encoded child models; `rlp.py:130–135`. -/
  def encodePayloadModel : List RlpItem → List UInt8
    | [] => []
    | x :: xs => encodeModel x ++ encodePayloadModel xs
end

-- The temporary cache contains sizes and packed writers, never subtree wire outputs.
private structure Writer where
  size : Nat
  write : ByteArray → ByteArray

mutual
  private def prepare : RlpItem → Writer
    | .bytes b => if single b then ⟨b.size, fun acc ↦ acc ++ b⟩ else
        let hdr := encodeLengthPrefix 128 183 b.size
        ⟨hdr.size + b.size, fun acc ↦ (acc ++ hdr) ++ b⟩
    | .list xs =>
        let payload := prepareList xs
        let hdr := encodeLengthPrefix 192 247 payload.size
        ⟨hdr.size + payload.size, fun acc ↦ payload.write (acc ++ hdr)⟩
  private def prepareList : List RlpItem → Writer
    | [] => ⟨0, id⟩
    | x :: xs =>
        let head := prepare x
        let tail := prepareList xs
        ⟨head.size + tail.size, fun acc ↦ tail.write (head.write acc)⟩
end

mutual
  private theorem prepare_width (x : RlpItem) :
      (prepare x).size = (encodeModel x).length := by
    cases x with
    | bytes b =>
      simp only [prepare, encodeModel]
      split
      · rfl
      · rw [List.length_append, ← toList_encodeLengthPrefix, Array.length_toList]
        rfl
    | list xs =>
      simp only [prepare, encodeModel, List.length_append]
      rw [prepareList_width, ← toList_encodeLengthPrefix, Array.length_toList]
      rfl
  private theorem prepareList_width (xs : List RlpItem) :
      (prepareList xs).size = (encodePayloadModel xs).length := by
    cases xs with
    | nil => rfl
    | cons x xs =>
      simp only [prepareList, encodePayloadModel, List.length_append]
      rw [prepare_width, prepareList_width]
end

mutual
  private theorem prepare_model (x : RlpItem) (acc : ByteArray) :
      ((prepare x).write acc).data.toList = acc.data.toList ++ encodeModel x := by
    cases x with
    | bytes b =>
      simp only [prepare, encodeModel]
      split <;> simp only [ByteArray.toList_data_append, toList_encodeLengthPrefix,
        List.append_assoc]
    | list xs =>
      simp only [prepare, encodeModel, prepareList_model, ByteArray.toList_data_append,
        toList_encodeLengthPrefix, List.append_assoc, prepareList_width]
  private theorem prepareList_model (xs : List RlpItem) (acc : ByteArray) :
      ((prepareList xs).write acc).data.toList = acc.data.toList ++ encodePayloadModel xs := by
    cases xs with
    | nil => simp [prepareList, encodePayloadModel]
    | cons x xs =>
      simp only [prepareList, encodePayloadModel, prepare_model, prepareList_model,
        List.append_assoc]
end

/-- Encoded width computed by the structural planning pass. -/
def encodedSize (x : RlpItem) : Nat := (prepare x).size

/-- Pure total two-pass encoder; locked `rlp.py:66–135` on `Encodable` items.
Q47 owns the total byte-model completion. The output buffer is allocated once
with its planned capacity and passed linearly through cached writers. -/
def encode (x : RlpItem) : ByteArray :=
  let plan := prepare x
  plan.write (ByteArray.emptyWithCapacity plan.size)

/-- Byte-string wire encoding via the same packed writer; locked `rlp.py:90–109`. -/
def encodeBytes (b : ByteArray) : ByteArray := encode (.bytes b)

/-- The packed encoder equals its total byte-list model for every item. -/
theorem toList_encode (x : RlpItem) : (encode x).data.toList = encodeModel x := by
  rw [encode, prepare_model]
  rfl

/-- The size pass equals the readable reference width for every item. -/
theorem encodedSize_eq_model_length (x : RlpItem) :
    encodedSize x = (encodeModel x).length := prepare_width x

/-- The final packed byte width equals the computed size pass. -/
theorem size_encode (x : RlpItem) : (encode x).size = encodedSize x := by
  rw [encodedSize_eq_model_length]
  change (encode x).data.size = _
  rw [← Array.length_toList, toList_encode]

/-- Byte-string encoding preserves the same whole-byte model relation. -/
theorem toList_encodeBytes (b : ByteArray) :
    (encodeBytes b).data.toList = encodeModel (.bytes b) := toList_encode _

/-- A singleton below 0x80 is emitted without a header. -/
theorem encodeBytes_single (b : ByteArray) (value : UInt8) (hs : b.size = 1)
    (hv : b[0]? = some value) (h : value.toNat < 128) : encodeBytes b = b := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [toList_encodeBytes, encodeModel, ite_eq_left]
  exact ⟨hs, by simpa only [hv, Option.getD_some] using h⟩

/-- Every other short string has one exact tag followed by its original bytes. -/
theorem encodeBytes_short (b : ByteArray) (hs : b.size < 56)
    (h : ¬ (b.size = 1 ∧ (b[0]?.getD 128).toNat < 128)) :
    (encodeBytes b).data.toList = UInt8.ofNat (128 + b.size) :: b.data.toList := by
  have hn : ¬single b := h
  rw [toList_encodeBytes, encodeModel, ite_eq_right hn,
    lengthPrefixModel_short 128 183 b.size hs]
  rfl

/-- Every long string has its length tag, exact minimal digits, then original bytes. -/
theorem encodeBytes_long (b : ByteArray) (h : 56 ≤ b.size) :
    (encodeBytes b).data.toList =
      UInt8.ofNat (183 + (Uint.toBeBytes b.size).size) ::
        (Uint.toBeBytes b.size).toList ++ b.data.toList := by
  have hn : ¬single b := by intro hs; unfold single at hs; omega
  rw [toList_encodeBytes, encodeModel, ite_eq_right hn,
    lengthPrefixModel_long 128 183 b.size h]
  rfl

/-- Exact singleton/short/long byte-string output widths. -/
theorem size_encodeBytes (b : ByteArray) :
    (encodeBytes b).size =
      if b.size = 1 ∧ (b[0]?.getD 128).toNat < 128 then b.size else
        (if b.size < 56 then 1 else 1 + (Uint.toBeBytes b.size).size) + b.size := by
  rw [encodeBytes, size_encode]
  change (prepare (.bytes b)).size = _
  simp only [prepare, single, size_encodeLengthPrefix]
  split <;> rfl

/-- Empty list payload. -/
theorem encodePayloadModel_nil : encodePayloadModel [] = [] := rfl

/-- Payload concatenation preserves the complete first child and remaining order. -/
theorem encodePayloadModel_cons (x : RlpItem) (xs : List RlpItem) :
    encodePayloadModel (x :: xs) = encodeModel x ++ encodePayloadModel xs := rfl

/-- Concatenating item lists concatenates their encoded payloads in the same order. -/
theorem encodePayloadModel_append (xs ys : List RlpItem) :
    encodePayloadModel (xs ++ ys) = encodePayloadModel xs ++ encodePayloadModel ys := by
  induction xs with
  | nil => simp [encodePayloadModel]
  | cons x xs ih => simp [encodePayloadModel, ih, List.append_assoc]

/-- Payloads are exactly the ordered whole-byte encodings of their children. -/
theorem encodePayloadModel_eq_flatMap (xs : List RlpItem) :
    encodePayloadModel xs = xs.flatMap (fun x ↦ (encode x).data.toList) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [encodePayloadModel, List.flatMap_cons, toList_encode, ih]

/-- List encoding prepends the header computed from encoded payload length. -/
theorem toList_encode_list (xs : List RlpItem) :
    (encode (.list xs)).data.toList =
      lengthPrefixModel 192 247 (encodePayloadModel xs).length ++ encodePayloadModel xs := by
  rw [toList_encode, encodeModel]

/-- Exact list width: prefix width plus the encoded child-payload width. -/
theorem size_encode_list (xs : List RlpItem) :
    (encode (.list xs)).size =
      (if (encodePayloadModel xs).length < 56 then 1 else
        1 + (Uint.toBeBytes (encodePayloadModel xs).length).size) +
      (encodePayloadModel xs).length := by
  rw [size_encode, encodedSize_eq_model_length, encodeModel, List.length_append,
    ← toList_encodeLengthPrefix, Array.length_toList]
  exact congrArg (fun n ↦ n + (encodePayloadModel xs).length)
    (size_encodeLengthPrefix 192 247 _)

/-- Standard-domain predicate: each byte length and each recursively encoded list
payload length has at most eight minimal length digits. This is a refinement
hypothesis, never a new protocol acceptance bound (Q47). -/
def Encodable : RlpItem → Prop
  | .bytes b => (Uint.toBeBytes b.size).size ≤ 8
  | .list xs => (∀ x ∈ xs, Encodable x) ∧
      (Uint.toBeBytes (encodePayloadModel xs).length).size ≤ 8

/-- Byte-domain characterization includes the complete unbounded numeric bound. -/
theorem encodable_bytes_iff (b : ByteArray) :
    Encodable (.bytes b) ↔ b.size < 2 ^ 64 := by
  simpa only [Encodable] using Uint.size_toBeBytes_le_iff b.size 8

/-- List-domain characterization includes every child and encoded payload length. -/
theorem encodable_list_iff (xs : List RlpItem) :
    Encodable (.list xs) ↔ (∀ x ∈ xs, Encodable x) ∧
      (encodePayloadModel xs).length < 2 ^ 64 := by
  simp only [Encodable, Uint.size_toBeBytes_le_iff]

/-- The standard list long tag does not wrap when the list is encodable. -/
theorem encodable_list_tag (xs : List RlpItem) (h : Encodable (.list xs)) :
    (UInt8.ofNat (247 + (Uint.toBeBytes (encodePayloadModel xs).length).size)).toNat =
      247 + (Uint.toBeBytes (encodePayloadModel xs).length).size :=
by
  unfold Encodable at h
  exact long_tag_toNat 247 _ (by decide) h.2

/-- Byte constructors use exactly the dedicated byte-string entry point. -/
theorem encode_bytes (b : ByteArray) : encode (.bytes b) = encodeBytes b := rfl

/-- Encoded payload width is the sum of the computed child widths, not item count. -/
theorem length_encodePayloadModel (xs : List RlpItem) :
    (encodePayloadModel xs).length = (xs.map encodedSize).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [encodePayloadModel_cons, List.length_append, ih,
      ← encodedSize_eq_model_length x]
    rfl

/-- Short lists have one exact tag followed by their ordered encoded payload. -/
theorem encode_list_short (xs : List RlpItem) (h : (encodePayloadModel xs).length < 56) :
    (encode (.list xs)).data.toList =
      UInt8.ofNat (192 + (encodePayloadModel xs).length) :: encodePayloadModel xs := by
  rw [toList_encode_list, lengthPrefixModel_short 192 247 _ h]
  rfl

/-- Long lists have one tag, exact minimal payload-length digits, then the payload. -/
theorem encode_list_long (xs : List RlpItem) (h : 56 ≤ (encodePayloadModel xs).length) :
    (encode (.list xs)).data.toList =
      UInt8.ofNat (247 + (Uint.toBeBytes (encodePayloadModel xs).length).size) ::
        (Uint.toBeBytes (encodePayloadModel xs).length).toList ++ encodePayloadModel xs := by
  rw [toList_encode_list, lengthPrefixModel_long 192 247 _ h]
  rfl

/-- The standard string long tag does not wrap on the encodable byte domain. -/
theorem encodable_bytes_tag (b : ByteArray) (h : Encodable (.bytes b)) :
    (UInt8.ofNat (183 + (Uint.toBeBytes b.size).size)).toNat =
      183 + (Uint.toBeBytes b.size).size :=
  long_tag_toNat 183 _ (by decide) (by simpa only [Encodable] using h)

end STFSpec.Codec.Rlp
