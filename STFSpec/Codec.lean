/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.RlpEncode
import STFSpec.Codec.RlpHeader
import STFSpec.Codec.RlpDecode
import STFSpec.Codec.Address

/-!
# STFSpec.Codec

RLP and SSZ codecs, SSZ `hash_tree_root`, and CREATE/CREATE2 address derivation.

Library `EthCodec`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). RLP encoding and typed model leaf
adapters, raw decoding and derived addresses are implemented; SSZ remains scaffolding.
Spec guidance: `STFSpec/informal/modules/EthCodec.md`.
-/
