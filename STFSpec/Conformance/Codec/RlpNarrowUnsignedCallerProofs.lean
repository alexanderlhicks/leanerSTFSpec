/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Codec

/-!
# Narrow unsigned RLP public-law callers

Library `EthConformance`. Twenty-four private groups preserve exact words, models,
wires and diagnostics through the public Codec facade.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/
namespace STFSpec.Conformance.Codec.RlpNarrowUnsignedCallerProofs
open STFSpec.Codec STFSpec.Codec.Rlp STFSpec.Base

namespace U64
-- 1. The adapter, complete wire model and complete size.
private theorem encoder (x : U64) : RlpEncode.toRlp x = ofNat x.toNat := rfl
private theorem bytes_model (x : U64) :
    (encodeOf x).data.toList = encodeModel (ofNat x.toNat) := toList_encode _
private theorem wire_size (x : U64) :
    (encodeOf x).size = encodedSize (ofNat x.toNat) := size_encode _

-- 2. Every value lies in the encoder domain, through public size/range laws.
private theorem domain (x : U64) : Encodable (RlpEncode.toRlp x) := by
  apply (encodable_bytes_iff _).mpr
  have h : (Uint.toBeBytes x.toNat).size ≤ 8 :=
    (Uint.size_toBeBytes_le_iff x.toNat 8).mpr (U64.toNat_lt x)
  change (Uint.toBeBytes x.toNat).toByteArray.size < 2 ^ 64
  rw [Bytes.size_toByteArray]
  exact Nat.lt_of_le_of_lt h (by decide)

-- 3. The model inverse composes bounded acceptance with reconstruction.
private theorem model_inverse (x : U64) :
    RlpDecode.ofRlp (RlpEncode.toRlp x) = .ok x := by
  change (toNatBounded 8 (ofNat x.toNat)).map U64.ofNat = .ok x
  rw [(toNatBounded_eq_ok_item_iff 8 _ x.toNat).mpr ⟨rfl, U64.toNat_lt x⟩]
  exact congrArg Except.ok (U64.ofNat_toNat x)

-- 4. The public inverse discharges its finite encoder domain privately.
private theorem inverse (x : U64) : decodeTo (encodeOf x) = .ok x :=
  decodeTo_encodeOf_u64 x

-- 5. Success recovers the exact model; bounded admission rules out wrapping.
private theorem success_iff (item : RlpItem) (x : U64) :
    RlpDecode.ofRlp (α := U64) item = .ok x ↔ item = ofNat x.toNat := by
  constructor
  · intro h
    change (toNatBounded 8 item).map U64.ofNat = .ok x at h
    cases hn : toNatBounded 8 item with
    | error e => rw [hn] at h; contradiction
    | ok n =>
      have hx : U64.ofNat n = x := by simpa only [hn, Except.map, Except.ok.injEq] using h
      obtain ⟨hi, hr⟩ := (toNatBounded_eq_ok_item_iff 8 item n).mp hn
      have he : x.toNat = n := by rw [← hx]; exact U64.toNat_ofNat_of_lt hr
      rw [he]; exact hi
  · intro h
    rw [h]
    exact model_inverse x

-- Successful wires recover the raw item, its domain and every original byte.
private theorem raw_success (wire : ByteArray) (x : U64) (h : decodeTo wire = .ok x) :
    decode wire = .ok (ofNat x.toNat) := by
  cases hd : decode wire with
  | error e => unfold decodeTo at h; rw [hd] at h; contradiction
  | ok item =>
    have ht : RlpDecode.ofRlp item = .ok x := by unfold decodeTo at h; rw [hd] at h; exact h
    rw [(success_iff item x).mp ht]
private theorem success_domain (wire : ByteArray) (x : U64) (h : decodeTo wire = .ok x) :
    Encodable (ofNat x.toNat) := decode_success_encodable wire _ (raw_success wire x h)
private theorem reencode (wire : ByteArray) (x : U64) (h : decodeTo wire = .ok x) :
    encodeOf x = wire := encode_eq_of_decode_eq_ok wire _ (raw_success wire x h)

-- 6. Complete decoder equation and raw failure forwarding.
private theorem decoder (item : RlpItem) :
    RlpDecode.ofRlp (α := U64) item = (toNatBounded 8 item).map U64.ofNat := rfl
private theorem raw_error (wire : ByteArray) (e : RlpError) (h : decode wire = .error e) :
    decodeTo (α := U64) wire = .error e := by unfold decodeTo; rw [h]

private theorem raw_result (wire : ByteArray) (item : RlpItem)
    (h : decode wire = .ok item) :
    decodeTo (α := U64) wire = (toNatBounded 8 item).map U64.ofNat := by
  unfold decodeTo
  rw [h]
  rfl

-- 7. Leading zero wins over any width, before the word constructor is reached.
private theorem leading_zero (b : ByteArray) (h : b[0]? = some 0) :
    RlpDecode.ofRlp (α := U64) (.bytes b) =
      .error (.nonCanonical "integer leading zero") := by
  rw [decoder, toNatBounded_leading_zero 8 b h]
  rfl

private theorem list_no_success (xs : List RlpItem) (x : U64) :
    RlpDecode.ofRlp (α := U64) (.list xs) ≠ .ok x := by
  intro h
  have hi := (success_iff (.list xs) x).mp h
  change RlpItem.list xs = RlpItem.bytes _ at hi
  contradiction
private theorem bounded_construction (item : RlpItem) (n : Nat)
    (h : toNatBounded 8 item = .ok n) : (U64.ofNat n).toNat = n := by
  exact U64.toNat_ofNat_of_lt ((toNatBounded_eq_ok_item_iff 8 item n).mp h).2

-- 8. Only the external observation erases the complete diagnostic.
private theorem error_observation (wire : ByteArray) (e : RlpError)
    (h : decodeTo (α := U64) wire = .error e) :
    (decodeTo (α := U64) wire).mapError (fun (_ : RlpError) => ()) = .error () := by
  rw [h]; rfl
private theorem success_observation (wire : ByteArray) (x : U64)
    (h : decodeTo wire = .ok x) :
    (decodeTo (α := U64) wire).mapError (fun (_ : RlpError) => ()) = .ok x := by
  rw [h]; rfl
end U64

namespace U32
-- 1. The adapter, complete wire model and complete size.
private theorem encoder (x : U32) : RlpEncode.toRlp x = ofNat x.toNat := rfl
private theorem bytes_model (x : U32) :
    (encodeOf x).data.toList = encodeModel (ofNat x.toNat) := toList_encode _
private theorem wire_size (x : U32) :
    (encodeOf x).size = encodedSize (ofNat x.toNat) := size_encode _

-- 2. Every value lies in the encoder domain, through public size/range laws.
private theorem domain (x : U32) : Encodable (RlpEncode.toRlp x) := by
  apply (encodable_bytes_iff _).mpr
  have h : (Uint.toBeBytes x.toNat).size ≤ 4 :=
    (Uint.size_toBeBytes_le_iff x.toNat 4).mpr (U32.toNat_lt x)
  change (Uint.toBeBytes x.toNat).toByteArray.size < 2 ^ 64
  rw [Bytes.size_toByteArray]
  exact Nat.lt_of_le_of_lt h (by decide)

-- 3. The model inverse composes bounded acceptance with reconstruction.
private theorem model_inverse (x : U32) :
    RlpDecode.ofRlp (RlpEncode.toRlp x) = .ok x := by
  change (toNatBounded 4 (ofNat x.toNat)).map U32.ofNat = .ok x
  rw [(toNatBounded_eq_ok_item_iff 4 _ x.toNat).mpr ⟨rfl, U32.toNat_lt x⟩]
  exact congrArg Except.ok (U32.ofNat_toNat x)

-- 4. The public inverse discharges its finite encoder domain privately.
private theorem inverse (x : U32) : decodeTo (encodeOf x) = .ok x :=
  decodeTo_encodeOf_u32 x

-- 5. Success recovers the exact model; bounded admission rules out wrapping.
private theorem success_iff (item : RlpItem) (x : U32) :
    RlpDecode.ofRlp (α := U32) item = .ok x ↔ item = ofNat x.toNat := by
  constructor
  · intro h
    change (toNatBounded 4 item).map U32.ofNat = .ok x at h
    cases hn : toNatBounded 4 item with
    | error e => rw [hn] at h; contradiction
    | ok n =>
      have hx : U32.ofNat n = x := by simpa only [hn, Except.map, Except.ok.injEq] using h
      obtain ⟨hi, hr⟩ := (toNatBounded_eq_ok_item_iff 4 item n).mp hn
      have he : x.toNat = n := by rw [← hx]; exact U32.toNat_ofNat_of_lt hr
      rw [he]; exact hi
  · intro h
    rw [h]
    exact model_inverse x

-- Successful wires recover the raw item, its domain and every original byte.
private theorem raw_success (wire : ByteArray) (x : U32) (h : decodeTo wire = .ok x) :
    decode wire = .ok (ofNat x.toNat) := by
  cases hd : decode wire with
  | error e => unfold decodeTo at h; rw [hd] at h; contradiction
  | ok item =>
    have ht : RlpDecode.ofRlp item = .ok x := by unfold decodeTo at h; rw [hd] at h; exact h
    rw [(success_iff item x).mp ht]
private theorem success_domain (wire : ByteArray) (x : U32) (h : decodeTo wire = .ok x) :
    Encodable (ofNat x.toNat) := decode_success_encodable wire _ (raw_success wire x h)
private theorem reencode (wire : ByteArray) (x : U32) (h : decodeTo wire = .ok x) :
    encodeOf x = wire := encode_eq_of_decode_eq_ok wire _ (raw_success wire x h)

-- 6. Complete decoder equation and raw failure forwarding.
private theorem decoder (item : RlpItem) :
    RlpDecode.ofRlp (α := U32) item = (toNatBounded 4 item).map U32.ofNat := rfl
private theorem raw_error (wire : ByteArray) (e : RlpError) (h : decode wire = .error e) :
    decodeTo (α := U32) wire = .error e := by unfold decodeTo; rw [h]

private theorem raw_result (wire : ByteArray) (item : RlpItem)
    (h : decode wire = .ok item) :
    decodeTo (α := U32) wire = (toNatBounded 4 item).map U32.ofNat := by
  unfold decodeTo
  rw [h]
  rfl

-- 7. Leading zero wins over any width, before the word constructor is reached.
private theorem leading_zero (b : ByteArray) (h : b[0]? = some 0) :
    RlpDecode.ofRlp (α := U32) (.bytes b) =
      .error (.nonCanonical "integer leading zero") := by
  rw [decoder, toNatBounded_leading_zero 4 b h]
  rfl

private theorem list_no_success (xs : List RlpItem) (x : U32) :
    RlpDecode.ofRlp (α := U32) (.list xs) ≠ .ok x := by
  intro h
  have hi := (success_iff (.list xs) x).mp h
  change RlpItem.list xs = RlpItem.bytes _ at hi
  contradiction
private theorem bounded_construction (item : RlpItem) (n : Nat)
    (h : toNatBounded 4 item = .ok n) : (U32.ofNat n).toNat = n := by
  exact U32.toNat_ofNat_of_lt ((toNatBounded_eq_ok_item_iff 4 item n).mp h).2

-- 8. Only the external observation erases the complete diagnostic.
private theorem error_observation (wire : ByteArray) (e : RlpError)
    (h : decodeTo (α := U32) wire = .error e) :
    (decodeTo (α := U32) wire).mapError (fun (_ : RlpError) => ()) = .error () := by
  rw [h]; rfl
private theorem success_observation (wire : ByteArray) (x : U32)
    (h : decodeTo wire = .ok x) :
    (decodeTo (α := U32) wire).mapError (fun (_ : RlpError) => ()) = .ok x := by
  rw [h]; rfl
end U32

namespace U8
-- 1. The adapter, complete wire model and complete size.
private theorem encoder (x : U8) : RlpEncode.toRlp x = ofNat x.toNat := rfl
private theorem bytes_model (x : U8) :
    (encodeOf x).data.toList = encodeModel (ofNat x.toNat) := toList_encode _
private theorem wire_size (x : U8) :
    (encodeOf x).size = encodedSize (ofNat x.toNat) := size_encode _

-- 2. Every value lies in the encoder domain, through public size/range laws.
private theorem domain (x : U8) : Encodable (RlpEncode.toRlp x) := by
  apply (encodable_bytes_iff _).mpr
  have h : (Uint.toBeBytes x.toNat).size ≤ 1 :=
    (Uint.size_toBeBytes_le_iff x.toNat 1).mpr (U8.toNat_lt x)
  change (Uint.toBeBytes x.toNat).toByteArray.size < 2 ^ 64
  rw [Bytes.size_toByteArray]
  exact Nat.lt_of_le_of_lt h (by decide)

-- 3. The model inverse composes bounded acceptance with reconstruction.
private theorem model_inverse (x : U8) :
    RlpDecode.ofRlp (RlpEncode.toRlp x) = .ok x := by
  change (toNatBounded 1 (ofNat x.toNat)).map U8.ofNat = .ok x
  rw [(toNatBounded_eq_ok_item_iff 1 _ x.toNat).mpr ⟨rfl, U8.toNat_lt x⟩]
  exact congrArg Except.ok (U8.ofNat_toNat x)

-- 4. The public inverse discharges its finite encoder domain privately.
private theorem inverse (x : U8) : decodeTo (encodeOf x) = .ok x :=
  decodeTo_encodeOf_u8 x

-- 5. Success recovers the exact model; bounded admission rules out wrapping.
private theorem success_iff (item : RlpItem) (x : U8) :
    RlpDecode.ofRlp (α := U8) item = .ok x ↔ item = ofNat x.toNat := by
  constructor
  · intro h
    change (toNatBounded 1 item).map U8.ofNat = .ok x at h
    cases hn : toNatBounded 1 item with
    | error e => rw [hn] at h; contradiction
    | ok n =>
      have hx : U8.ofNat n = x := by simpa only [hn, Except.map, Except.ok.injEq] using h
      obtain ⟨hi, hr⟩ := (toNatBounded_eq_ok_item_iff 1 item n).mp hn
      have he : x.toNat = n := by rw [← hx]; exact U8.toNat_ofNat_of_lt hr
      rw [he]; exact hi
  · intro h
    rw [h]
    exact model_inverse x

-- Successful wires recover the raw item, its domain and every original byte.
private theorem raw_success (wire : ByteArray) (x : U8) (h : decodeTo wire = .ok x) :
    decode wire = .ok (ofNat x.toNat) := by
  cases hd : decode wire with
  | error e => unfold decodeTo at h; rw [hd] at h; contradiction
  | ok item =>
    have ht : RlpDecode.ofRlp item = .ok x := by unfold decodeTo at h; rw [hd] at h; exact h
    rw [(success_iff item x).mp ht]
private theorem success_domain (wire : ByteArray) (x : U8) (h : decodeTo wire = .ok x) :
    Encodable (ofNat x.toNat) := decode_success_encodable wire _ (raw_success wire x h)
private theorem reencode (wire : ByteArray) (x : U8) (h : decodeTo wire = .ok x) :
    encodeOf x = wire := encode_eq_of_decode_eq_ok wire _ (raw_success wire x h)

-- 6. Complete decoder equation and raw failure forwarding.
private theorem decoder (item : RlpItem) :
    RlpDecode.ofRlp (α := U8) item = (toNatBounded 1 item).map U8.ofNat := rfl
private theorem raw_error (wire : ByteArray) (e : RlpError) (h : decode wire = .error e) :
    decodeTo (α := U8) wire = .error e := by unfold decodeTo; rw [h]

private theorem raw_result (wire : ByteArray) (item : RlpItem)
    (h : decode wire = .ok item) :
    decodeTo (α := U8) wire = (toNatBounded 1 item).map U8.ofNat := by
  unfold decodeTo
  rw [h]
  rfl

-- 7. Leading zero wins over any width, before the word constructor is reached.
private theorem leading_zero (b : ByteArray) (h : b[0]? = some 0) :
    RlpDecode.ofRlp (α := U8) (.bytes b) =
      .error (.nonCanonical "integer leading zero") := by
  rw [decoder, toNatBounded_leading_zero 1 b h]
  rfl

private theorem list_no_success (xs : List RlpItem) (x : U8) :
    RlpDecode.ofRlp (α := U8) (.list xs) ≠ .ok x := by
  intro h
  have hi := (success_iff (.list xs) x).mp h
  change RlpItem.list xs = RlpItem.bytes _ at hi
  contradiction
private theorem bounded_construction (item : RlpItem) (n : Nat)
    (h : toNatBounded 1 item = .ok n) : (U8.ofNat n).toNat = n := by
  exact U8.toNat_ofNat_of_lt ((toNatBounded_eq_ok_item_iff 1 item n).mp h).2

-- 8. Only the external observation erases the complete diagnostic.
private theorem error_observation (wire : ByteArray) (e : RlpError)
    (h : decodeTo (α := U8) wire = .error e) :
    (decodeTo (α := U8) wire).mapError (fun (_ : RlpError) => ()) = .error () := by
  rw [h]; rfl
private theorem success_observation (wire : ByteArray) (x : U8)
    (h : decodeTo wire = .ok x) :
    (decodeTo (α := U8) wire).mapError (fun (_ : RlpError) => ()) = .ok x := by
  rw [h]; rfl
end U8

end STFSpec.Conformance.Codec.RlpNarrowUnsignedCallerProofs
