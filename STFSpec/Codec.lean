/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.RlpTyped

/-!
# STFSpec.Codec

RLP and SSZ codecs, and SSZ `hash_tree_root`.

Library `EthCodec`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). Typed RLP leaf adapters are implemented; wire and SSZ APIs remain scaffolding.
Spec guidance: `STFSpec/informal/modules/EthCodec.md`.
-/
