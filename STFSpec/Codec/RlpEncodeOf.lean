/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.RlpEncode

/-!
# Typed RLP encoding

Library `EthCodec`. The reference wrapper composes the supplied model adapter
with the raw encoder. Nat uses minimal unsigned bytes, including empty zero.
No decoder, inverse or instance-domain law is supplied by this class.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§2–7.
-/

namespace STFSpec.Codec

/-- A typed value's RLP model adapter; locked `ethereum_rlp/rlp.py:66–88` (0.1.6).
Instance owners supply their schema and its separate laws. -/
class RlpEncode (α : Type) where
  /-- Preserve the value's complete RLP model. -/
  toRlp : α → RlpItem

/-- Encode through the supplied adapter; `ethereum_rlp/rlp.py:66–135` (0.1.6).
Standard/source correspondence retains `Rlp.Encodable` and source/host premises. -/
def Rlp.encodeOf {α : Type} [RlpEncode α] (a : α) : ByteArray :=
  Rlp.encode (RlpEncode.toRlp a)

/-- Unbounded unsigned encoding; `ethereum_rlp/rlp.py:77–78` (0.1.6) and
`ethereum_types/numeric.py:477–484` (0.4.1). Zero has an empty payload. -/
instance : RlpEncode Nat where
  toRlp := Rlp.ofNat

end STFSpec.Codec
