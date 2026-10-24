/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Address RLP public-law callers

Library `EthConformance`. Eight private caller groups preserve nominal addresses,
complete bytes, wires and diagnostics through public model contracts.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/

namespace STFSpec.Conformance.Codec.RlpAddressCallerProofs
open STFSpec.Codec STFSpec.Codec.Rlp STFSpec.Base

-- 1. Exact adapter equations retain the checked constructor and every byte.
private theorem encoder (x : Address) :
    RlpEncode.toRlp x = .bytes x.toBytes.toByteArray := rfl
private theorem decoder (item : RlpItem) :
    RlpDecode.ofRlp (α := Address) item = (toBytes item).bind
      (fun b => (Address.ofBytes? (Bytes.ofByteArray b)).elim
        (.error (.shape "fixed bytes length")) Except.ok) := rfl
private theorem decoder_bytes (b : ByteArray) :
    RlpDecode.ofRlp (α := Address) (.bytes b) =
      (Address.ofBytes? (Bytes.ofByteArray b)).elim
        (.error (.shape "fixed bytes length")) Except.ok := rfl

-- 2. Item inversion needs no wire-domain premise.
private theorem model_inverse (x : Address) :
    RlpDecode.ofRlp (RlpEncode.toRlp x) = .ok x := by
  rw [encoder, decoder_bytes, Bytes.ofByteArray_toByteArray, Address.ofBytes?_toBytes]
  rfl

-- 3. Complete acceptance recovers the nominal value and the whole byte leaf.
private theorem success_iff (item : RlpItem) (x : Address) :
    RlpDecode.ofRlp item = .ok x ↔ item = .bytes x.toBytes.toByteArray := by
  cases item with
  | list items => simp only [decoder, toBytes, Except.bind, reduceCtorEq]
  | bytes b =>
    rw [decoder_bytes]
    constructor
    · intro h
      cases hc : Address.ofBytes? (Bytes.ofByteArray b) with
      | none => simp only [hc, Option.elim, reduceCtorEq] at h
      | some y =>
        have hy : y = x := by simpa only [hc, Option.elim, Except.ok.injEq] using h
        have hb := (Address.ofBytes?_eq_some_iff).mp hc
        rw [← hy, hb.2, Bytes.toByteArray_ofByteArray]
    · intro h
      have hb : b = x.toBytes.toByteArray := RlpItem.bytes.inj h
      rw [hb, Bytes.ofByteArray_toByteArray, Address.ofBytes?_toBytes]
      rfl
private theorem success_bytes (b : ByteArray) (x : Address) :
    RlpDecode.ofRlp (.bytes b) = .ok x ↔ b.size = 20 ∧ x.toBytes.toByteArray = b := by
  rw [success_iff, RlpItem.bytes.injEq]
  constructor
  · intro h
    subst b
    exact ⟨by rw [Bytes.size_toByteArray, Address.size_toBytes], rfl⟩
  · exact fun h => h.2.symm

-- 4. Checked construction and both packed inverses preserve all leading zeros.
private theorem checked_success (b : Bytes) (x : Address) :
    Address.ofBytes? b = some x ↔ b.size = 20 ∧ x.toBytes = b :=
  Address.ofBytes?_eq_some_iff
private theorem checked_mismatch (b : Bytes) :
    Address.ofBytes? b = none ↔ b.size ≠ 20 := Address.ofBytes?_eq_none_iff
private theorem checked_inverse (x : Address) :
    Address.ofBytes? x.toBytes = some x := Address.ofBytes?_toBytes x
private theorem byte_injective (x y : Address) : x.toBytes = y.toBytes ↔ x = y :=
  Address.toBytes_inj
private theorem packed_inverse (b : ByteArray) :
    (Bytes.ofByteArray b).toByteArray = b := Bytes.toByteArray_ofByteArray b
private theorem bytes_inverse (b : Bytes) :
    Bytes.ofByteArray b.toByteArray = b := Bytes.ofByteArray_toByteArray b
private theorem checked_transport (b : ByteArray) (x : Address)
    (h : Address.ofBytes? (Bytes.ofByteArray b) = some x) :
    b.size = 20 ∧ x.toBytes.toByteArray = b := by
  have hb := (checked_success _ x).mp h
  exact ⟨by simpa only [Bytes.size_ofByteArray] using hb.1,
    by rw [hb.2, Bytes.toByteArray_ofByteArray]⟩

-- 5. The single public wire inverse is unconditional at every nominal address.
private theorem inverse (x : Address) : decodeTo (encodeOf x) = .ok x :=
  decodeTo_encodeOf_address x
private theorem generic_composition {α : Type} [RlpEncode α] [RlpDecode α] (x : α)
    (h : Encodable (RlpEncode.toRlp x))
    (hi : RlpDecode.ofRlp (RlpEncode.toRlp x) = .ok x) :
    decodeTo (encodeOf x) = .ok x := by
  unfold decodeTo encodeOf
  rw [decode_encode _ h]
  exact hi

-- 6. Successful wire recovery preserves every byte and proves its domain.
private theorem raw_success (wire : ByteArray) (x : Address)
    (h : decodeTo wire = .ok x) : decode wire = .ok (.bytes x.toBytes.toByteArray) := by
  cases hd : decode wire with
  | error e => unfold decodeTo at h; rw [hd] at h; contradiction
  | ok item =>
    have ht : RlpDecode.ofRlp item = .ok x := by unfold decodeTo at h; rw [hd] at h; exact h
    rw [(success_iff item x).mp ht]
private theorem success_domain (wire : ByteArray) (x : Address)
    (h : decodeTo wire = .ok x) : Encodable (.bytes x.toBytes.toByteArray) :=
  decode_success_encodable wire _ (raw_success wire x h)
private theorem reencode (wire : ByteArray) (x : Address)
    (h : decodeTo wire = .ok x) : encodeOf x = wire :=
  encode_eq_of_decode_eq_ok wire _ (raw_success wire x h)
private theorem recovered_bytes (wire : ByteArray) (x : Address)
    (h : decodeTo wire = .ok x) :
    decode wire = .ok (.bytes x.toBytes.toByteArray) ∧ x.toBytes.toByteArray.size = 20 :=
  ⟨raw_success wire x h, by rw [Bytes.size_toByteArray, Address.size_toBytes]⟩

-- 7. Exact failures and separate external Unit observations.
private theorem raw_error (wire : ByteArray) (e : RlpError) (h : decode wire = .error e) :
    decodeTo (α := Address) wire = .error e := by unfold decodeTo; rw [h]
private theorem list_error (items : List RlpItem) :
    RlpDecode.ofRlp (α := Address) (.list items) = .error (.shape "bytes") := rfl
private theorem length_error (b : ByteArray) (h : b.size ≠ 20) :
    RlpDecode.ofRlp (α := Address) (.bytes b) = .error (.shape "fixed bytes length") := by
  rw [decoder_bytes]
  have hn : Address.ofBytes? (Bytes.ofByteArray b) = none :=
    Address.ofBytes?_eq_none_iff.mpr (by simpa only [Bytes.size_ofByteArray] using h)
  rw [hn]
  rfl
private theorem length_error_iff (b : ByteArray) :
    RlpDecode.ofRlp (α := Address) (.bytes b) = .error (.shape "fixed bytes length") ↔
      b.size ≠ 20 := by
  constructor
  · intro h
    rw [decoder_bytes] at h
    cases hc : Address.ofBytes? (Bytes.ofByteArray b) with
    | none => simpa only [Bytes.size_ofByteArray] using Address.ofBytes?_eq_none_iff.mp hc
    | some x => simp only [hc, Option.elim, reduceCtorEq] at h
  · exact length_error b
private theorem error_observation (wire : ByteArray) (e : RlpError)
    (h : decodeTo (α := Address) wire = .error e) :
    (decodeTo (α := Address) wire).mapError (fun (_ : RlpError) => ()) = .error () := by
  rw [h]; rfl
private theorem success_observation (wire : ByteArray) (x : Address)
    (h : decodeTo wire = .ok x) :
    (decodeTo (α := Address) wire).mapError (fun (_ : RlpError) => ()) = .ok x := by
  rw [h]; rfl

-- 8. The exact finite domain and complete checked diagram remain nominal.
private theorem finite_domain (x : Address) : Encodable (RlpEncode.toRlp x) := by
  rw [encoder, encodable_bytes_iff, Bytes.size_toByteArray, Address.size_toBytes]
  decide
private theorem checked_diagram (b : Bytes) (x : Address)
    (h : Address.ofBytes? b = some x) :
    RlpDecode.ofRlp (α := Address) (.bytes b.toByteArray) = .ok x := by
  rw [decoder_bytes, Bytes.ofByteArray_toByteArray, h]
  rfl
private theorem success_size (item : RlpItem) (x : Address)
    (h : RlpDecode.ofRlp item = .ok x) :
    ∃ b : ByteArray, item = .bytes b ∧ b.size = 20 :=
  ⟨x.toBytes.toByteArray, (success_iff item x).mp h,
    by rw [Bytes.size_toByteArray, Address.size_toBytes]⟩
private theorem other_lengths (b : ByteArray) (h : b.size ∈ [0, 19, 21]) :
    RlpDecode.ofRlp (α := Address) (.bytes b) = .error (.shape "fixed bytes length") := by
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

end STFSpec.Conformance.Codec.RlpAddressCallerProofs
