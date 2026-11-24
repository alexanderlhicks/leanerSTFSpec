/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Precompiles.Identity
import STFSpec.Precompiles.KzgVersionedHash
import STFSpec.Precompiles.Ripemd160
import STFSpec.Precompiles.Sha256

/-!
# STFSpec.Precompiles

Precompiled contracts: input parsing, gas and output encoding over named crypto primitives.

Library `EthPrecompiles`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3).
The standalone SHA256, RIPEMD160 and IDENTITY entries and KZG versioned-hash helper are supplied.
Table installation and the remaining precompile entries are open.
Spec guidance: `STFSpec/informal/modules/EthPrecompiles.md`.
-/
