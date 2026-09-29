/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.U256
import STFSpec.Base.U256Arithmetic

/-!
# STFSpec.Base

Primitive types and conversions: the `U256` API, fixed-width words, `Bytes`, `Address`,
`Hash32`, `Bytes32`, big-endian conversions, and the `Envelope` record. No fork policy.

Library `EthBase`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). The U256 value, constructor, order and unsigned
arithmetic slices are implemented; the remaining API is scaffolding.
Spec guidance: `STFSpec/informal/modules/EthBase.md`.
-/
