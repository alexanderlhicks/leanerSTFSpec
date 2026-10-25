/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.RlpDecodeOf

/-!
# Typed RLP U256 words

Library `EthCodec`. Words use minimal unsigned bytes, including empty zero.
The existing bounded integer adapter rejects leading zero before excess width.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§2–7.
-/

namespace STFSpec.Codec

/-- Minimal word encoding; locked `ethereum_rlp/rlp.py:77–78` (0.1.6) and
`ethereum_types/numeric.py:477–484` (0.4.1). -/
instance : RlpEncode Base.U256 where
  toRlp x := Rlp.ofNat x.toNat

/-- Word decoding; locked `ethereum_rlp/rlp.py:263–275` (0.1.6) and
`ethereum_types/numeric.py:566–577` (0.4.1). Width admission precedes construction. -/
instance : RlpDecode Base.U256 where
  ofRlp item := (Rlp.toNatBounded 32 item).map Base.U256.ofNat

private theorem u256_encodable (x : Base.U256) : Rlp.Encodable (RlpEncode.toRlp x) := by
  apply (Rlp.encodable_bytes_iff _).mpr
  have h : (Base.Uint.toBeBytes x.toNat).size ≤ 32 :=
    (Base.Uint.size_toBeBytes_le_iff x.toNat 32).mpr (Base.U256.toNat_lt x)
  change (Base.Uint.toBeBytes x.toNat).toByteArray.size < 2 ^ 64
  rw [Base.Bytes.size_toByteArray]
  exact Nat.lt_of_le_of_lt h (by decide)

/-- Every U256 model lies in Q47, so its wire roundtrip is unconditional. -/
theorem Rlp.decodeTo_encodeOf_u256 (x : Base.U256) :
    Rlp.decodeTo (α := Base.U256) (Rlp.encodeOf x) =
      (Except.ok x : Except RlpError Base.U256) := by
  unfold Rlp.decodeTo Rlp.encodeOf
  rw [Rlp.decode_encode _ (u256_encodable x)]
  change (Rlp.toNatBounded 32 (Rlp.ofNat x.toNat)).map Base.U256.ofNat = .ok x
  rw [(Rlp.toNatBounded_eq_ok_item_iff 32 _ x.toNat).mpr ⟨rfl, Base.U256.toNat_lt x⟩]
  exact congrArg Except.ok (Base.U256.ofNat_toNat x)

end STFSpec.Codec
