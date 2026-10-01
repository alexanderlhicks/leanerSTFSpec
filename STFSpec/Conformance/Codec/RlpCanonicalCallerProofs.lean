/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Codec

/-!
# Universal raw RLP public-law callers

Library `EthConformance`. Consumers compose inverse and binding laws using
Q47's explicit `Encodable` domain.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3,7.
-/

namespace STFSpec.Conformance.Codec.RlpCanonicalCallerProofs
open STFSpec.Codec STFSpec.Codec.Rlp

example (x : RlpItem) (hx : Encodable x) : decode (encode x) = .ok x :=
  decode_encode x hx

example (b : ByteArray) (x : RlpItem) (h : decode b = .ok x) :
    Encodable x ∧ encode x = b :=
  ⟨decode_success_encodable b x h, encode_eq_of_decode_eq_ok b x h⟩

example (b : ByteArray) (x : RlpItem) :
    decode b = .ok x ↔ Encodable x ∧ encode x = b := decode_eq_ok_iff b x

example (b : ByteArray) :
    (∃ x, decode b = .ok x) ↔ ∃ x, Encodable x ∧ encode x = b := exists_decode_eq_ok_iff b

example (x y : RlpItem) (hx : Encodable x) (hy : Encodable y)
    (h : encode x = encode y) : x = y := eq_of_encode_eq x y hx hy h

example (x y : RlpItem) (hx : Encodable x) (hy : Encodable y)
    (r s : ByteArray) (h : encode x ++ r = encode y ++ s) : x = y ∧ r = s :=
  encode_prefix_free x y hx hy r s h

example (x y : RlpItem) (hx : Encodable x) (hy : Encodable y) :
    encode x = encode y ↔ x = y := encode_inj x y hx hy

example (x : RlpItem) (hx : Encodable x) (tail : List UInt8) :
    itemLengthModel (encodeModel x ++ tail) = .ok (encodeModel x).length :=
  itemLengthModel_encodeModel x hx tail

/-- Canonicality composes with round trip to preserve an accepted decoded tree exactly. -/
example (b : ByteArray) (x : RlpItem) (h : decode b = .ok x) :
    decode (encode x) = .ok x := decode_encode x (decode_success_encodable b x h)

end STFSpec.Conformance.Codec.RlpCanonicalCallerProofs
