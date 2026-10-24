/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Hash32 RLP public-law callers

Library `EthConformance`. Eight private caller groups preserve nominal values,
complete bytes, wires and diagnostics through public model contracts.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/

namespace STFSpec.Conformance.Codec.RlpHash32CallerProofs
open STFSpec.Codec STFSpec.Codec.Rlp STFSpec.Base

-- 1. Exact adapters and the public byte conversion diagram.
private theorem encoder (x : Hash32) :
    RlpEncode.toRlp x = .bytes x.toBytes.toByteArray := rfl
private theorem decoder (item : RlpItem) :
    RlpDecode.ofRlp (α := Hash32) item = (toFixed 32 item).map Hash32.ofBytes32 := rfl
private theorem encoder_bytes32 (x : Hash32) :
    RlpEncode.toRlp x = .bytes x.toBytes32.toBytes.toByteArray := by
  rw [encoder, Hash32.toBytes_toBytes32]

-- 2. Item inversion needs no wire-domain premise.
private theorem model_inverse (x : Hash32) :
    RlpDecode.ofRlp (RlpEncode.toRlp x) = .ok x := by
  rw [encoder, decoder]
  have h := (toFixed_eq_ok_item_iff 32 (.bytes x.toBytes.toByteArray) x.toBytes32).mpr
    (by rw [Hash32.toBytes_toBytes32])
  rw [h]
  exact congrArg Except.ok (Hash32.ofBytes32_toBytes32 x)

-- 3. Complete acceptance in both directions, including nominal reconstruction.
private theorem success_iff (item : RlpItem) (x : Hash32) :
    RlpDecode.ofRlp item = .ok x ↔ item = .bytes x.toBytes.toByteArray := by
  rw [decoder]
  constructor
  · intro h
    cases ht : toFixed 32 item with
    | error e => rw [ht] at h; contradiction
    | ok b =>
      have hx : Hash32.ofBytes32 b = x := by simpa only [ht, Except.map, Except.ok.injEq] using h
      have hb := (toFixed_eq_ok_item_iff 32 item b).mp ht
      rw [← hx, Hash32.toBytes_ofBytes32]
      exact hb
  · intro h
    rw [h]
    have ht := (toFixed_eq_ok_item_iff 32 (.bytes x.toBytes.toByteArray) x.toBytes32).mpr
      (by rw [Hash32.toBytes_toBytes32])
    rw [ht]
    exact congrArg Except.ok (Hash32.ofBytes32_toBytes32 x)
private theorem success_bytes (b : ByteArray) (x : Hash32) :
    RlpDecode.ofRlp (.bytes b) = .ok x ↔ b.size = 32 ∧ x.toBytes.toByteArray = b := by
  rw [success_iff, RlpItem.bytes.injEq]
  constructor
  · intro h
    subst b
    exact ⟨by rw [Bytes.size_toByteArray, Hash32.size_toBytes], rfl⟩
  · exact fun h => h.2.symm

-- 4. Checked construction, both nominal inverses, both byte laws and packed adapters.
private theorem checked_success (b : Bytes) (x : Hash32) :
    Hash32.ofBytes? b = some x ↔ b.size = 32 ∧ x.toBytes = b :=
  Hash32.ofBytes?_eq_some_iff
private theorem checked_mismatch (b : Bytes) :
    Hash32.ofBytes? b = none ↔ b.size ≠ 32 := Hash32.ofBytes?_eq_none_iff
private theorem checked_inverse (x : Hash32) :
    Hash32.ofBytes? x.toBytes = some x := Hash32.ofBytes?_toBytes x
private theorem nominal_inverse (x : Hash32) :
    Hash32.ofBytes32 x.toBytes32 = x := Hash32.ofBytes32_toBytes32 x
private theorem bytes32_inverse (b : Bytes32) :
    (Hash32.ofBytes32 b).toBytes32 = b := Hash32.toBytes32_ofBytes32 b
private theorem forget_bytes (x : Hash32) :
    x.toBytes32.toBytes = x.toBytes := Hash32.toBytes_toBytes32 x
private theorem restore_bytes (b : Bytes32) :
    (Hash32.ofBytes32 b).toBytes = b.toBytes := Hash32.toBytes_ofBytes32 b
private theorem packed_inverse (b : ByteArray) :
    (Bytes.ofByteArray b).toByteArray = b := Bytes.toByteArray_ofByteArray b
private theorem bytes_inverse (b : Bytes) :
    Bytes.ofByteArray b.toByteArray = b := Bytes.ofByteArray_toByteArray b

-- 5. The single public inverse is unconditional at every nominal hash.
private theorem inverse (x : Hash32) : decodeTo (encodeOf x) = .ok x :=
  decodeTo_encodeOf_hash32 x
private theorem generic_composition {α : Type} [RlpEncode α] [RlpDecode α] (x : α)
    (h : Encodable (RlpEncode.toRlp x))
    (hi : RlpDecode.ofRlp (RlpEncode.toRlp x) = .ok x) :
    decodeTo (encodeOf x) = .ok x := by
  unfold decodeTo encodeOf
  rw [decode_encode _ h]
  exact hi

-- 6. Successful wire recovery preserves every byte and proves its domain.
private theorem raw_success (wire : ByteArray) (x : Hash32)
    (h : decodeTo wire = .ok x) : decode wire = .ok (.bytes x.toBytes.toByteArray) := by
  cases hd : decode wire with
  | error e => unfold decodeTo at h; rw [hd] at h; contradiction
  | ok item =>
    have ht : RlpDecode.ofRlp item = .ok x := by unfold decodeTo at h; rw [hd] at h; exact h
    rw [(success_iff item x).mp ht]
private theorem success_domain (wire : ByteArray) (x : Hash32)
    (h : decodeTo wire = .ok x) : Encodable (.bytes x.toBytes.toByteArray) :=
  decode_success_encodable wire _ (raw_success wire x h)
private theorem reencode (wire : ByteArray) (x : Hash32)
    (h : decodeTo wire = .ok x) : encodeOf x = wire :=
  encode_eq_of_decode_eq_ok wire _ (raw_success wire x h)
private theorem recovered_bytes (wire : ByteArray) (x : Hash32)
    (h : decodeTo wire = .ok x) :
    decode wire = .ok (.bytes x.toBytes.toByteArray) ∧ x.toBytes.toByteArray.size = 32 :=
  ⟨raw_success wire x h, by rw [Bytes.size_toByteArray, Hash32.size_toBytes]⟩

-- 7. Exact failures and separate external Unit observations.
private theorem raw_error (wire : ByteArray) (e : RlpError) (h : decode wire = .error e) :
    decodeTo (α := Hash32) wire = .error e := by unfold decodeTo; rw [h]
private theorem list_error (items : List RlpItem) :
    RlpDecode.ofRlp (α := Hash32) (.list items) = .error (.shape "bytes") := by
  rw [decoder, toFixed]
  rfl
private theorem length_error (b : ByteArray) (h : b.size ≠ 32) :
    RlpDecode.ofRlp (α := Hash32) (.bytes b) = .error (.shape "fixed bytes length") := by
  rw [decoder, toFixed]
  have hn : (FixedBytes.ofBytes? (Bytes.ofByteArray b) : Option Bytes32) = none :=
    FixedBytes.ofBytes?_eq_none_iff.mpr (by simpa only [Bytes.size_ofByteArray] using h)
  rw [hn]
  rfl
private theorem error_observation (wire : ByteArray) (e : RlpError)
    (h : decodeTo (α := Hash32) wire = .error e) :
    (decodeTo (α := Hash32) wire).mapError (fun (_ : RlpError) => ()) = .error () := by
  rw [h]; rfl
private theorem success_observation (wire : ByteArray) (x : Hash32)
    (h : decodeTo wire = .ok x) :
    (decodeTo (α := Hash32) wire).mapError (fun (_ : RlpError) => ()) = .ok x := by
  rw [h]; rfl

-- 8. Finite domain and complete conversion diagrams, separate from other accept sets.
private theorem finite_domain (x : Hash32) : Encodable (RlpEncode.toRlp x) := by
  rw [encoder, encodable_bytes_iff, Bytes.size_toByteArray, Hash32.size_toBytes]
  decide
private theorem checked_diagram (b : Bytes32) :
    Hash32.ofBytes? b.toBytes = some (Hash32.ofBytes32 b) := by
  apply Hash32.ofBytes?_eq_some_iff.mpr
  exact ⟨FixedBytes.size_toBytes b, Hash32.toBytes_ofBytes32 b⟩
private theorem success_size (item : RlpItem) (x : Hash32)
    (h : RlpDecode.ofRlp item = .ok x) :
    ∃ b : ByteArray, item = .bytes b ∧ b.size = 32 :=
  ⟨x.toBytes.toByteArray, (success_iff item x).mp h,
    by rw [Bytes.size_toByteArray, Hash32.size_toBytes]⟩
private theorem other_lengths (b : ByteArray) (h : b.size ∈ [0, 31, 33]) :
    RlpDecode.ofRlp (α := Hash32) (.bytes b) = .error (.shape "fixed bytes length") := by
  apply length_error
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  omega
private theorem bytearray_accepts (b : ByteArray) :
    RlpDecode.ofRlp (α := ByteArray) (.bytes b) = .ok b := rfl
private theorem nat_zero_not_success (n : Nat) :
    RlpDecode.ofRlp (α := Nat) (.bytes ⟨#[0]⟩) ≠ .ok n := by
  intro h
  have hn := (toNat_eq_ok_bytes_iff ⟨#[0]⟩ n).mp h
  exact hn.1 rfl

end STFSpec.Conformance.Codec.RlpHash32CallerProofs
