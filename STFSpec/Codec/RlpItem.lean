/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base

/-!
# RLP model items and diagnostic errors

Library `EthCodec`. `RlpItem` is the public nested byte/list model of
`ethereum_rlp/rlp.py` (locked ethereum-rlp 0.1.6). No nested instances are derived.
Typed diagnostics do not introduce distinct protocol outcomes; the future
`decodeTo` wrapper must map them to the source's single DecodingError channel.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§2–7.
-/

namespace STFSpec.Codec

/-- Untyped RLP values: byte strings and ordered lists; no wire decoder is implied. -/
inductive RlpItem where
  | bytes (b : ByteArray)
  | list (items : List RlpItem)

/-- Diagnostic context only; pinned `ethereum_rlp/exceptions.py` has DecodingError.
The wire constructors are retained from the stated interface, without wire APIs. -/
inductive RlpError where
  | empty
  | truncated
  | trailing
  | nonCanonical (why : String)
  | shape (ctx : String)
  deriving DecidableEq

end STFSpec.Codec
