/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Hash.KeccakPermutation
import STFSpec.Hash.Sha256Compression

/-!
# STFSpec.Hash

keccak-f[1600] and keccak256, SHA-256, RIPEMD-160, BLAKE2 F, and the `KeccakQuery` class.

Library `EthHash`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). Implementation status is owned by
the spec guidance document.
Spec guidance: `STFSpec/informal/modules/EthHash.md`.
-/
