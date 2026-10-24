/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Fixed-byte RLP public-law callers

Library `EthConformance`. Eight private groups retain exact bytes, widths, wires
and diagnostics, using public model laws and the explicit wire-domain premise.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/

namespace STFSpec.Conformance.Codec.RlpFixedBytesCallerProofs
open STFSpec.Codec STFSpec.Codec.Rlp STFSpec.Base

variable {n : Nat}

-- 1. Adapter equations and the intentionally public encoder semantic model.
private theorem encoder (x : FixedBytes n) :
    RlpEncode.toRlp x = .bytes x.toBytes.toByteArray := rfl
private theorem decoder (item : RlpItem) :
    RlpDecode.ofRlp (α := FixedBytes n) item = toFixed n item := rfl
private theorem bytes_model (x : FixedBytes n) :
    (encodeOf x).data.toList = encodeModel (.bytes x.toBytes.toByteArray) := toList_encode _
private theorem wire_size (x : FixedBytes n) :
    (encodeOf x).size = encodedSize (.bytes x.toBytes.toByteArray) := size_encode _

-- 2. All-n raw item inversion does not need a wire-domain premise.
private theorem model_inverse (x : FixedBytes n) :
    RlpDecode.ofRlp (RlpEncode.toRlp x) = .ok x :=
  (toFixed_eq_ok_item_iff n _ x).mpr rfl

-- 3. Both directions preserve complete bytes, list/leaf shape and exact width.
private theorem success_iff (item : RlpItem) (x : FixedBytes n) :
    RlpDecode.ofRlp item = .ok x ↔ item = .bytes x.toBytes.toByteArray :=
  toFixed_eq_ok_item_iff n item x
private theorem success_bytes (b : ByteArray) (x : FixedBytes n) :
    RlpDecode.ofRlp (.bytes b) = .ok x ↔ b.size = n ∧ x.toBytes.toByteArray = b :=
  toFixed_eq_ok_iff n b x

-- 4. Checked construction and the exact packed/Base byte adapters.
private theorem checked_success (b : Bytes) (x : FixedBytes n) :
    FixedBytes.ofBytes? b = some x ↔ b.size = n ∧ x.toBytes = b :=
  FixedBytes.ofBytes?_eq_some_iff
private theorem checked_mismatch (b : Bytes) :
    (FixedBytes.ofBytes? b : Option (FixedBytes n)) = none ↔ b.size ≠ n :=
  FixedBytes.ofBytes?_eq_none_iff
private theorem checked_inverse (x : FixedBytes n) :
    FixedBytes.ofBytes? x.toBytes = some x := FixedBytes.ofBytes?_toBytes x
private theorem packed_inverse (b : ByteArray) :
    (Bytes.ofByteArray b).toByteArray = b := Bytes.toByteArray_ofByteArray b
private theorem bytes_inverse (b : Bytes) :
    Bytes.ofByteArray b.toByteArray = b := Bytes.ofByteArray_toByteArray b

-- 5. The public wire inverse retains its actual premise at arbitrary width.
private theorem inverse (x : FixedBytes n) (h : Encodable (.bytes x.toBytes.toByteArray)) :
    decodeTo (encodeOf x) = .ok x := decodeTo_encodeOf_fixedBytes x h
private theorem generic_composition {α : Type} [RlpEncode α] [RlpDecode α] (x : α)
    (h : Encodable (RlpEncode.toRlp x))
    (hi : RlpDecode.ofRlp (RlpEncode.toRlp x) = .ok x) :
    decodeTo (encodeOf x) = .ok x := by
  unfold decodeTo encodeOf
  rw [decode_encode _ h]
  exact hi

-- 6. Successful wire recovery, domain, full reencoding and complete size/bytes.
private theorem raw_success (wire : ByteArray) (x : FixedBytes n)
    (h : decodeTo wire = .ok x) : decode wire = .ok (.bytes x.toBytes.toByteArray) := by
  cases hd : decode wire with
  | error e => unfold decodeTo at h; rw [hd] at h; contradiction
  | ok item =>
    have ht : RlpDecode.ofRlp item = .ok x := by unfold decodeTo at h; rw [hd] at h; exact h
    rw [(success_iff item x).mp ht]
private theorem success_domain (wire : ByteArray) (x : FixedBytes n)
    (h : decodeTo wire = .ok x) : Encodable (.bytes x.toBytes.toByteArray) :=
  decode_success_encodable wire _ (raw_success wire x h)
private theorem reencode (wire : ByteArray) (x : FixedBytes n)
    (h : decodeTo wire = .ok x) : encodeOf x = wire :=
  encode_eq_of_decode_eq_ok wire _ (raw_success wire x h)
private theorem recovered_bytes (wire : ByteArray) (x : FixedBytes n)
    (h : decodeTo wire = .ok x) :
    decode wire = .ok (.bytes x.toBytes.toByteArray) ∧ x.toBytes.toByteArray.size = n :=
  ⟨raw_success wire x h, by rw [Bytes.size_toByteArray, FixedBytes.size_toBytes]⟩

-- 7. Exact failures remain separate from external Unit observations.
private theorem raw_error (wire : ByteArray) (e : RlpError) (h : decode wire = .error e) :
    decodeTo (α := FixedBytes n) wire = .error e := by unfold decodeTo; rw [h]
private theorem model_error (wire : ByteArray) (item : RlpItem) (e : RlpError)
    (h : decode wire = .ok item) (ht : toFixed n item = .error e) :
    decodeTo (α := FixedBytes n) wire = .error e := by unfold decodeTo; rw [h]; exact ht
private theorem error_observation (wire : ByteArray) (e : RlpError)
    (h : decodeTo (α := FixedBytes n) wire = .error e) :
    (decodeTo (α := FixedBytes n) wire).mapError (fun (_ : RlpError) => ()) = .error () := by
  rw [h]; rfl
private theorem success_observation (wire : ByteArray) (x : FixedBytes n)
    (h : decodeTo wire = .ok x) :
    (decodeTo (α := FixedBytes n) wire).mapError (fun (_ : RlpError) => ()) = .ok x := by
  rw [h]; rfl

-- 8. Private domain equivalence, finite discharges and symbolic above-bound omission.
private theorem domain (x : FixedBytes n) :
    Encodable (RlpEncode.toRlp x) ↔ n < 2 ^ 64 := by
  rw [encoder, encodable_bytes_iff, Bytes.size_toByteArray, FixedBytes.size_toBytes]
private theorem finite_domain (n : Nat) (h : n ∈ [0, 1, 20, 32, 55, 56, 255, 256])
    (x : FixedBytes n) : Encodable (RlpEncode.toRlp x) := by
  apply (domain x).mpr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h <;> subst n <;> decide
private theorem finite_inverse (n : Nat) (h : n ∈ [0, 1, 20, 32, 55, 56, 255, 256])
    (x : FixedBytes n) : decodeTo (encodeOf x) = .ok x :=
  decodeTo_encodeOf_fixedBytes x (finite_domain n h x)
private theorem omitted_domain (x : FixedBytes n) (h : 2 ^ 64 ≤ n) :
    ¬ Encodable (RlpEncode.toRlp x) := by rw [domain]; exact Nat.not_lt.mpr h
private theorem empty_model (x : FixedBytes 0) : x.toBytes.toByteArray = ByteArray.empty := by
  apply ByteArray.ext
  apply Array.ext
  · simp only [ByteArray.size_data, Bytes.size_toByteArray, FixedBytes.size_toBytes]
    rfl
  · intro i hi _
    have : x.toBytes.toByteArray.size = 0 := by
      rw [Bytes.size_toByteArray, FixedBytes.size_toBytes]
    change i < x.toBytes.toByteArray.size at hi
    omega
private theorem empty_inverse (x : FixedBytes 0) : decodeTo (encodeOf x) = .ok x :=
  decodeTo_encodeOf_fixedBytes x ((domain x).mpr (by decide))

end STFSpec.Conformance.Codec.RlpFixedBytesCallerProofs
