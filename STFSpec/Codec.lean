/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.RlpEncode
import STFSpec.Codec.RlpEncodeOf
import STFSpec.Codec.RlpDecodeOf
import STFSpec.Codec.RlpByteArray
import STFSpec.Codec.RlpBool
import STFSpec.Codec.RlpU256
import STFSpec.Codec.RlpHeader
import STFSpec.Codec.RlpDecode
import STFSpec.Codec.RlpCanonical
import STFSpec.Codec.Address
import STFSpec.Codec.SszModel
import STFSpec.Codec.SszWellTyped
import STFSpec.Codec.SszWellFormed
import STFSpec.Codec.SszPack
import STFSpec.Codec.SszFixedSize

import STFSpec.Codec.RlpNarrowUnsigned
import STFSpec.Codec.RlpFixedBytes
import STFSpec.Codec.RlpAddress
import STFSpec.Codec.RlpList
import STFSpec.Codec.RlpHash32

/-!
# STFSpec.Codec

RLP and SSZ codecs, SSZ `hash_tree_root`, and CREATE/CREATE2 address derivation.

Library `EthCodec`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). RLP encoding and typed model leaf
adapters, raw decoding, derived addresses and the raw SSZ vocabulary are implemented;
structural SSZ sizing and schema well-formedness are supplied; SSZ codecs and roots remain unimplemented.
Spec guidance: `STFSpec/informal/modules/EthCodec.md`.
-/
