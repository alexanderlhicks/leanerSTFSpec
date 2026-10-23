/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.RlpDecodeOf

/-!
# Typed RLP byte strings

Library `EthCodec`. ByteArray adapters preserve every byte, including leading
zeros. Raw decoding precedes byte-shape checking (Q68); Q47 remains explicit.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§2–7.
-/

namespace STFSpec.Codec

/-- Byte-string encoding; locked `ethereum_rlp/rlp.py:70–72` (0.1.6). -/
instance : RlpEncode ByteArray where
  toRlp := RlpItem.bytes

/-- Original Bytes decoding; locked `ethereum_rlp/rlp.py:206–207,254–260` (0.1.6). -/
instance : RlpDecode ByteArray where
  ofRlp := Rlp.toBytes

/-- Byte-string wire roundtrip under the raw encoder's explicit Q47 premise. -/
theorem Rlp.decodeTo_encodeOf_byteArray (b : ByteArray)
    (h : Rlp.Encodable (.bytes b)) :
    Rlp.decodeTo (α := ByteArray) (Rlp.encodeOf b) =
      (Except.ok b : Except RlpError ByteArray) := by
  unfold Rlp.decodeTo Rlp.encodeOf
  dsimp only [RlpEncode.toRlp, RlpDecode.ofRlp]
  rw [Rlp.decode_encode _ h]
  exact (Rlp.toBytes_eq_ok_iff _ b).mpr rfl

end STFSpec.Codec
