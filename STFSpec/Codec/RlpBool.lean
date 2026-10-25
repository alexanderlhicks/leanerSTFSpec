/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.RlpDecodeOf

/-!
# Typed RLP booleans

Library `EthCodec`. False uses empty bytes and true uses singleton01.
Raw decoding precedes the existing Boolean adapter (Q68).
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§2–7.
-/

namespace STFSpec.Codec

/-- Boolean encoding; locked `ethereum_rlp/rlp.py:79–83` (0.1.6). -/
instance : RlpEncode Bool where
  toRlp b := if b then .bytes ⟨#[1]⟩ else .bytes ByteArray.empty

/-- Boolean decoding; locked `ethereum_rlp/rlp.py:208–209,245–251` (0.1.6). -/
instance : RlpDecode Bool where
  ofRlp := Rlp.toBool

private theorem bool_encodable (b : Bool) : Rlp.Encodable (RlpEncode.toRlp b) := by
  cases b <;> apply (Rlp.encodable_bytes_iff _).mpr <;> decide

/-- Every Boolean model lies in Q47, so its wire roundtrip is unconditional. -/
theorem Rlp.decodeTo_encodeOf_bool (b : Bool) :
    Rlp.decodeTo (α := Bool) (Rlp.encodeOf b) =
      (Except.ok b : Except RlpError Bool) := by
  unfold Rlp.decodeTo Rlp.encodeOf
  rw [Rlp.decode_encode _ (bool_encodable b)]
  apply (Rlp.toBool_eq_ok_iff _ b).mpr
  cases b
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

end STFSpec.Codec
