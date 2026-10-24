/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Codec

/-!
# U256 RLP public-law callers

Library `EthConformance`. Eight private groups preserve exact words, models,
wires and diagnostics through the public Codec facade.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/
namespace STFSpec.Conformance.Codec.RlpU256CallerProofs
open STFSpec.Codec STFSpec.Codec.Rlp STFSpec.Base

-- 1. The adapter, complete wire model and complete size.
private theorem encoder (x : U256) : RlpEncode.toRlp x = ofNat x.toNat := rfl
private theorem bytes_model (x : U256) :
    (encodeOf x).data.toList = encodeModel (ofNat x.toNat) := toList_encode _
private theorem wire_size (x : U256) :
    (encodeOf x).size = encodedSize (ofNat x.toNat) := size_encode _

-- 2. The complete decoder equation and raw failure forwarding.
private theorem decoder (item : RlpItem) :
    RlpDecode.ofRlp (α := U256) item = (toNatBounded 32 item).map U256.ofNat := rfl
private theorem raw_error (wire : ByteArray) (e : RlpError) (h : decode wire = .error e) :
    decodeTo (α := U256) wire = .error e := by unfold decodeTo; rw [h]

-- 3. The model inverse composes bounded acceptance with reconstruction.
private theorem model_inverse (x : U256) :
    RlpDecode.ofRlp (RlpEncode.toRlp x) = .ok x := by
  change (toNatBounded 32 (ofNat x.toNat)).map U256.ofNat = .ok x
  rw [(toNatBounded_eq_ok_item_iff 32 _ x.toNat).mpr ⟨rfl, U256.toNat_lt x⟩]
  exact congrArg Except.ok (U256.ofNat_toNat x)

-- 4. The public inverse discharges its finite encoder domain privately.
private theorem inverse (x : U256) : decodeTo (encodeOf x) = .ok x :=
  decodeTo_encodeOf_u256 x

-- 5. Success recovers the exact model; bounded admission rules out wrapping.
private theorem success_iff (item : RlpItem) (x : U256) :
    RlpDecode.ofRlp (α := U256) item = .ok x ↔ item = ofNat x.toNat := by
  constructor
  · intro h
    change (toNatBounded 32 item).map U256.ofNat = .ok x at h
    cases hn : toNatBounded 32 item with
    | error e => rw [hn] at h; contradiction
    | ok n =>
      have hx : U256.ofNat n = x := by simpa only [hn, Except.map, Except.ok.injEq] using h
      obtain ⟨hi, hr⟩ := (toNatBounded_eq_ok_item_iff 32 item n).mp hn
      have he : x.toNat = n := by rw [← hx]; exact U256.toNat_ofNat_of_lt hr
      rw [he]; exact hi
  · intro h
    rw [h]
    exact model_inverse x

-- 6. Typed success recovers raw success, its domain and every original wire byte.
private theorem raw_success (wire : ByteArray) (x : U256) (h : decodeTo wire = .ok x) :
    decode wire = .ok (ofNat x.toNat) := by
  cases hd : decode wire with
  | error e => unfold decodeTo at h; rw [hd] at h; contradiction
  | ok item =>
    have ht : RlpDecode.ofRlp item = .ok x := by unfold decodeTo at h; rw [hd] at h; exact h
    rw [(success_iff item x).mp ht]
private theorem success_domain (wire : ByteArray) (x : U256) (h : decodeTo wire = .ok x) :
    Encodable (ofNat x.toNat) := decode_success_encodable wire _ (raw_success wire x h)
private theorem reencode (wire : ByteArray) (x : U256) (h : decodeTo wire = .ok x) :
    encodeOf x = wire := encode_eq_of_decode_eq_ok wire _ (raw_success wire x h)

-- 7. Leading zero wins over any width, before the word constructor is reached.
private theorem leading_zero (b : ByteArray) (h : b[0]? = some 0) :
    RlpDecode.ofRlp (α := U256) (.bytes b) =
      .error (.nonCanonical "integer leading zero") := by
  rw [decoder, toNatBounded_leading_zero 32 b h]
  rfl

-- 8. Only the external observation erases the complete diagnostic.
private theorem error_observation (wire : ByteArray) (e : RlpError)
    (h : decodeTo (α := U256) wire = .error e) :
    (decodeTo (α := U256) wire).mapError (fun (_ : RlpError) => ()) = .error () := by
  rw [h]; rfl
private theorem success_observation (wire : ByteArray) (x : U256)
    (h : decodeTo wire = .ok x) :
    (decodeTo (α := U256) wire).mapError (fun (_ : RlpError) => ()) = .ok x := by
  rw [h]; rfl

end STFSpec.Conformance.Codec.RlpU256CallerProofs
