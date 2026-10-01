/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Raw RLP public-law callers

Library `EthConformance`. Consumers use the public model/ordered-case equations
and the Base window laws. `RlpCanonicalCallerProofs.lean` composes the separate
wire canonicality and inverse laws.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3,7.
-/

namespace STFSpec.Conformance.Codec.RlpDecodeCallerProofs

open STFSpec.Codec STFSpec.Codec.Rlp STFSpec.Base

example (b : ByteArray) : decode b = decodeModel b.data.toList := decode_eq_model b

example (b : ByteArray) (start stop : Nat) :
    decode ((Bytes.ofByteArray b).extract start stop).toByteArray =
      decodeModel ((b.data.toList.drop start).take (stop - start)) :=
  decode_window_model b start stop

example (tag : UInt8) (body : List UInt8) (h : tag.toNat < 128) (hne : body ≠ []) :
    decodeModel (tag :: body) = .error (.nonCanonical "negative length") := by
  rw [decodeModel_single tag body h, ite_eq_right hne]

example (tag : UInt8) (body : List UInt8) (lo : 128 ≤ tag.toNat) (hi : tag.toNat ≤ 183)
    (ht : tag.toNat - 128 > body.length) :
    decodeModel (tag :: body) = .error .truncated := by
  rw [decodeModel_short_bytes tag body lo hi, ite_eq_left ht]

example (tag : UInt8) (body : List UInt8) (lo : 128 ≤ tag.toNat) (hi : tag.toNat ≤ 183)
    (ht : tag.toNat - 128 < body.length) :
    decodeModel (tag :: body) = .error .trailing := by
  rw [decodeModel_short_bytes tag body lo hi, ite_eq_right (by omega), ite_eq_left ht]

example (b : ByteArray) (x : RlpItem) (h : decode b = .ok x) : 0 < b.size :=
  decode_success_nonempty b x h

example (tag : UInt8) (body : List UInt8) (lo : 192 ≤ tag.toNat) (hi : tag.toNat ≤ 247)
    (he : tag.toNat - 192 < body.length) :
    decodeModel (tag :: body) = .error .trailing :=
  decodeModel_short_list_trailing tag body lo hi he

end STFSpec.Conformance.Codec.RlpDecodeCallerProofs
