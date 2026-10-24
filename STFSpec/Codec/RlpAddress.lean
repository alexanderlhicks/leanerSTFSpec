/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.RlpDecodeOf

/-!
# Typed RLP nominal Address

Library `EthCodec`. Preserve all 20 bytes of the existing nominal address.
The finite payload size privately discharges the standard RLP domain premise.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§2–7.
-/

namespace STFSpec.Codec

/-- Preserve every address byte; locked `ethereum_rlp/rlp.py:70–72,101` (0.1.6).
EELS `src/ethereum/state.py:33` aliases Address to Bytes20. -/
instance : RlpEncode Base.Address where
  toRlp x := .bytes x.toBytes.toByteArray

/-- Require a byte leaf, then exactly 20 bytes through the public checked constructor;
locked `ethereum_rlp/rlp.py:206–207,255–262` and `ethereum_types/bytes.py:29–37` (0.4.1). -/
instance : RlpDecode Base.Address where
  ofRlp item := (Rlp.toBytes item).bind
    (fun b => (Base.Address.ofBytes? (Base.Bytes.ofByteArray b)).elim
      (.error (.shape "fixed bytes length")) Except.ok)

/-- Every Address encoding decodes to the same nominal value and complete bytes. -/
theorem Rlp.decodeTo_encodeOf_address (x : Base.Address) :
    Rlp.decodeTo (α := Base.Address) (Rlp.encodeOf x) =
      (Except.ok x : Except RlpError Base.Address) := by
  have hi : RlpDecode.ofRlp (RlpEncode.toRlp x) = .ok x := by
    simp only [RlpEncode.toRlp, RlpDecode.ofRlp, Rlp.toBytes, Except.bind,
      Base.Bytes.ofByteArray_toByteArray, Base.Address.ofBytes?_toBytes, Option.elim]
  have hd : Rlp.Encodable (RlpEncode.toRlp x) := by
    change Rlp.Encodable (.bytes x.toBytes.toByteArray)
    rw [Rlp.encodable_bytes_iff, Base.Bytes.size_toByteArray, Base.Address.size_toBytes]
    decide
  unfold Rlp.decodeTo Rlp.encodeOf
  rw [Rlp.decode_encode _ hd]
  exact hi

end STFSpec.Codec
