/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.RlpDecode
import STFSpec.Codec.RlpEncodeOf

/-!
# Typed RLP wire decoding

Library `EthCodec`. Raw decoding precedes the supplied total model adapter.
Both phases preserve their complete results (Q68). Source correspondence retains
class/callback, reflection, host and first-consuming-handler premises.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§2–7.
-/

namespace STFSpec.Codec

/-- A typed model decoder; locked `ethereum_rlp/rlp.py:162–171` (0.1.6).
Instance owners supply separate schema and inverse laws. -/
class RlpDecode (α : Type) where
  /-- Preserve the complete typed result, including every supplied diagnostic. -/
  ofRlp : RlpItem → Except RlpError α

/-- Raw-first typed decoding; `ethereum_rlp/rlp.py:167–171` (0.1.6). -/
def Rlp.decodeTo {α : Type} [RlpDecode α] (b : ByteArray) : Except RlpError α :=
  match Rlp.decode b with
  | .error e => .error e
  | .ok x => RlpDecode.ofRlp (α := α) x

/-- Unbounded source Uint adapter; `ethereum_rlp/rlp.py:263–273` (0.1.6). -/
instance : RlpDecode Nat where
  ofRlp := Rlp.toNat

/-- Nat wire roundtrip under the raw encoder's explicit item-domain premise. -/
theorem Rlp.decodeTo_encodeOf_nat (n : Nat)
    (h : Rlp.Encodable (Rlp.ofNat n)) :
    Rlp.decodeTo (α := Nat) (Rlp.encodeOf n) =
      (Except.ok n : Except RlpError Nat) := by
  unfold Rlp.decodeTo Rlp.encodeOf
  change (match Rlp.decode (Rlp.encode (Rlp.ofNat n)) with
    | .error e => .error e
    | .ok x => Rlp.toNat x) = (Except.ok n : Except RlpError Nat)
  rw [Rlp.decode_encode _ h]
  exact Rlp.toNat_ofNat n

end STFSpec.Codec
