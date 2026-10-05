/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.Account
import STFSpec.State.WriteOrder

/-!
# STFSpec.State

State semantics: `Account`, the `PreState` record and its lookup contract
`ModelsLookups` (the full `Models` is defined in `EthStateCommit`), transaction/block
overlays, lifetimes, `BlockDiff`, and their laws. Independent of commitments.

Library `EthState`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). Account values and internal WriteOrder
support are supplied. Lookup providers, model mutation/application, state overlays,
tracker effects and lifecycle laws remain scaffolding.
Spec guidance: `STFSpec/informal/modules/EthState.md`.
-/
