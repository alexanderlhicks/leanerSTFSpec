/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.RlpEncode
import STFSpec.Codec.RlpHeader
import STFSpec.Codec.RlpDecode
import STFSpec.Codec.Address

/-!
# STFSpec.Codec

RLP and SSZ codecs, and SSZ `hash_tree_root`.

Library `EthCodec`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). RLP encoding and typed model leaf
adapters and raw decoding are implemented; SSZ remains scaffolding.
Spec guidance: `STFSpec/informal/modules/EthCodec.md`.
-/
