/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.RlpDecodeOf

/-!
# Typed RLP nominal Hash32

Library `EthCodec`. Preserve the complete 32 bytes of the existing nominal hash.
The finite payload size privately discharges the standard RLP domain premise.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§2–7.
-/

namespace STFSpec.Codec

/-- Preserve all hash bytes; locked `ethereum_rlp/rlp.py:70–72,101` (0.1.6).
EELS `src/ethereum/crypto/hash.py:19` aliases Hash32 to Bytes32. -/
instance : RlpEncode Base.Hash32 where
  toRlp x := .bytes x.toBytes.toByteArray

/-- Decode exactly 32 bytes, then restore the nominal domain; locked
`ethereum_rlp/rlp.py:206–207,255–262` and `ethereum_types/bytes.py:29–37` (0.4.1). -/
instance : RlpDecode Base.Hash32 where
  ofRlp item := (Rlp.toFixed 32 item).map Base.Hash32.ofBytes32

/-- Every Hash32 encoding decodes to the same nominal value and complete bytes. -/
theorem Rlp.decodeTo_encodeOf_hash32 (x : Base.Hash32) :
    Rlp.decodeTo (α := Base.Hash32) (Rlp.encodeOf x) =
      (Except.ok x : Except RlpError Base.Hash32) := by
  have hd : Rlp.Encodable (.bytes x.toBytes.toByteArray) := by
    rw [Rlp.encodable_bytes_iff, Base.Bytes.size_toByteArray, Base.Hash32.size_toBytes]
    decide
  have hi : Rlp.toFixed 32 (.bytes x.toBytes.toByteArray) = .ok x.toBytes32 := by
    apply (Rlp.toFixed_eq_ok_item_iff 32 _ x.toBytes32).mpr
    rw [Base.Hash32.toBytes_toBytes32]
  unfold Rlp.decodeTo Rlp.encodeOf
  have hm : Rlp.Encodable (RlpEncode.toRlp x) := hd
  rw [Rlp.decode_encode _ hm]
  change (Rlp.toFixed 32 (.bytes x.toBytes.toByteArray)).map Base.Hash32.ofBytes32 = .ok x
  rw [hi]
  exact congrArg Except.ok (Base.Hash32.ofBytes32_toBytes32 x)

end STFSpec.Codec
