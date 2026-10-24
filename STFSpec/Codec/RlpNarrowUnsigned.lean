/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.RlpDecodeOf

/-!
# Typed RLP narrow unsigned words

Library `EthCodec`. Words use minimal unsigned bytes, including empty zero.
The existing bounded integer adapter rejects leading zero before excess width.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§2–7.
-/

namespace STFSpec.Codec

/-- Minimal word encoding; locked `ethereum_rlp/rlp.py:77–78` (0.1.6) and
`ethereum_types/numeric.py:477–484` (0.4.1). -/
instance : RlpEncode Base.U64 where
  toRlp x := Rlp.ofNat x.toNat

/-- Word decoding; locked `ethereum_rlp/rlp.py:263–275` (0.1.6) and
`ethereum_types/numeric.py:566–577` (0.4.1). Width admission precedes construction. -/
instance : RlpDecode Base.U64 where
  ofRlp item := (Rlp.toNatBounded 8 item).map Base.U64.ofNat

private theorem u64_encodable (x : Base.U64) : Rlp.Encodable (RlpEncode.toRlp x) := by
  apply (Rlp.encodable_bytes_iff _).mpr
  have h : (Base.Uint.toBeBytes x.toNat).size ≤ 8 :=
    (Base.Uint.size_toBeBytes_le_iff x.toNat 8).mpr (Base.U64.toNat_lt x)
  change (Base.Uint.toBeBytes x.toNat).toByteArray.size < 2 ^ 64
  rw [Base.Bytes.size_toByteArray]
  exact Nat.lt_of_le_of_lt h (by decide)

/-- Every U64 model lies in Q47, so its wire roundtrip is unconditional. -/
theorem Rlp.decodeTo_encodeOf_u64 (x : Base.U64) :
    Rlp.decodeTo (α := Base.U64) (Rlp.encodeOf x) =
      (Except.ok x : Except RlpError Base.U64) := by
  unfold Rlp.decodeTo Rlp.encodeOf
  rw [Rlp.decode_encode _ (u64_encodable x)]
  change (Rlp.toNatBounded 8 (Rlp.ofNat x.toNat)).map Base.U64.ofNat = .ok x
  rw [(Rlp.toNatBounded_eq_ok_item_iff 8 _ x.toNat).mpr ⟨rfl, Base.U64.toNat_lt x⟩]
  exact congrArg Except.ok (Base.U64.ofNat_toNat x)

/-- Minimal word encoding; locked `ethereum_rlp/rlp.py:77–78` (0.1.6) and
`ethereum_types/numeric.py:477–484` (0.4.1). -/
instance : RlpEncode Base.U32 where
  toRlp x := Rlp.ofNat x.toNat

/-- Word decoding; locked `ethereum_rlp/rlp.py:263–275` (0.1.6) and
`ethereum_types/numeric.py:566–577` (0.4.1). Width admission precedes construction. -/
instance : RlpDecode Base.U32 where
  ofRlp item := (Rlp.toNatBounded 4 item).map Base.U32.ofNat

private theorem u32_encodable (x : Base.U32) : Rlp.Encodable (RlpEncode.toRlp x) := by
  apply (Rlp.encodable_bytes_iff _).mpr
  have h : (Base.Uint.toBeBytes x.toNat).size ≤ 4 :=
    (Base.Uint.size_toBeBytes_le_iff x.toNat 4).mpr (Base.U32.toNat_lt x)
  change (Base.Uint.toBeBytes x.toNat).toByteArray.size < 2 ^ 64
  rw [Base.Bytes.size_toByteArray]
  exact Nat.lt_of_le_of_lt h (by decide)

/-- Every U32 model lies in Q47, so its wire roundtrip is unconditional. -/
theorem Rlp.decodeTo_encodeOf_u32 (x : Base.U32) :
    Rlp.decodeTo (α := Base.U32) (Rlp.encodeOf x) =
      (Except.ok x : Except RlpError Base.U32) := by
  unfold Rlp.decodeTo Rlp.encodeOf
  rw [Rlp.decode_encode _ (u32_encodable x)]
  change (Rlp.toNatBounded 4 (Rlp.ofNat x.toNat)).map Base.U32.ofNat = .ok x
  rw [(Rlp.toNatBounded_eq_ok_item_iff 4 _ x.toNat).mpr ⟨rfl, Base.U32.toNat_lt x⟩]
  exact congrArg Except.ok (Base.U32.ofNat_toNat x)

/-- Minimal word encoding; locked `ethereum_rlp/rlp.py:77–78` (0.1.6) and
`ethereum_types/numeric.py:477–484` (0.4.1). -/
instance : RlpEncode Base.U8 where
  toRlp x := Rlp.ofNat x.toNat

/-- Word decoding; locked `ethereum_rlp/rlp.py:263–275` (0.1.6) and
`ethereum_types/numeric.py:566–577` (0.4.1). Width admission precedes construction. -/
instance : RlpDecode Base.U8 where
  ofRlp item := (Rlp.toNatBounded 1 item).map Base.U8.ofNat

private theorem u8_encodable (x : Base.U8) : Rlp.Encodable (RlpEncode.toRlp x) := by
  apply (Rlp.encodable_bytes_iff _).mpr
  have h : (Base.Uint.toBeBytes x.toNat).size ≤ 1 :=
    (Base.Uint.size_toBeBytes_le_iff x.toNat 1).mpr (Base.U8.toNat_lt x)
  change (Base.Uint.toBeBytes x.toNat).toByteArray.size < 2 ^ 64
  rw [Base.Bytes.size_toByteArray]
  exact Nat.lt_of_le_of_lt h (by decide)

/-- Every U8 model lies in Q47, so its wire roundtrip is unconditional. -/
theorem Rlp.decodeTo_encodeOf_u8 (x : Base.U8) :
    Rlp.decodeTo (α := Base.U8) (Rlp.encodeOf x) =
      (Except.ok x : Except RlpError Base.U8) := by
  unfold Rlp.decodeTo Rlp.encodeOf
  rw [Rlp.decode_encode _ (u8_encodable x)]
  change (Rlp.toNatBounded 1 (Rlp.ofNat x.toNat)).map Base.U8.ofNat = .ok x
  rw [(Rlp.toNatBounded_eq_ok_item_iff 1 _ x.toNat).mpr ⟨rfl, Base.U8.toNat_lt x⟩]
  exact congrArg Except.ok (Base.U8.ofNat_toNat x)

end STFSpec.Codec
