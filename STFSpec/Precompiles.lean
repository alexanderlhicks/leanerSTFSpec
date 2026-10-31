/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Precompiles.KzgVersionedHash

/-!
# STFSpec.Precompiles

Precompiled contracts: input parsing, gas and output encoding over named crypto primitives.

Library `EthPrecompiles`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3).
The KZG versioned-hash byte helper is implemented; other precompiles remain scaffolding.
Spec guidance: `STFSpec/informal/modules/EthPrecompiles.md`.
-/
