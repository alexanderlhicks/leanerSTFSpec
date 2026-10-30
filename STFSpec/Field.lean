/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Field.Reference
import STFSpec.Field.ReferencePower
import STFSpec.Field.Moduli

/-!
# STFSpec.Field

Prime fields and extension towers for the precompiles.

Library `EthField`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). The canonical natural reference carrier,
basic residue arithmetic, natural powers and eight exact natural moduli are supplied;
other field operations, executable Montgomery arithmetic and towers remain open.
Spec guidance: `STFSpec/informal/modules/EthField.md`.
-/
