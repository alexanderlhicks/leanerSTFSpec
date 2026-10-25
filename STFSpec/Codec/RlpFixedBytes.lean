/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.RlpDecodeOf

/-!
# Typed RLP fixed bytes

Library `EthCodec`. Exact-width bytes retain every zero; widths are arbitrary Nat,
including zero. The wire inverse retains the explicit Q47 domain premise.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§2–7.
-/

namespace STFSpec.Codec

variable {n : Nat}

/-- Preserve complete fixed bytes; locked `ethereum_rlp/rlp.py:70–72,99–108` (0.1.6). -/
instance : RlpEncode (Base.FixedBytes n) where
  toRlp x := .bytes x.toBytes.toByteArray

/-- Exact-length decoding; locked `ethereum_rlp/rlp.py:206–207,255–262` (0.1.6)
and `ethereum_types/bytes.py:29–37` (0.4.1). Lists fail before checked construction. -/
instance : RlpDecode (Base.FixedBytes n) where
  ofRlp := Rlp.toFixed n

/-- Fixed-byte wire inversion under the explicit standard RLP payload domain. -/
theorem Rlp.decodeTo_encodeOf_fixedBytes (x : Base.FixedBytes n)
    (h : Rlp.Encodable (.bytes x.toBytes.toByteArray)) :
    Rlp.decodeTo (α := Base.FixedBytes n) (Rlp.encodeOf x) =
      (Except.ok x : Except RlpError (Base.FixedBytes n)) := by
  unfold Rlp.decodeTo Rlp.encodeOf
  have hi : Rlp.Encodable (RlpEncode.toRlp x) := h
  rw [Rlp.decode_encode _ hi]
  exact (Rlp.toFixed_eq_ok_item_iff n _ x).mpr rfl

end STFSpec.Codec
