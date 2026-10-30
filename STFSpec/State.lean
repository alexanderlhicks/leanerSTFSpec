/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.Account
import STFSpec.State.WriteOrder
import STFSpec.State.MathState
import STFSpec.State.BlockDiff
import STFSpec.State.Apply
import STFSpec.State.PreState
import STFSpec.State.StateError
import STFSpec.State.Structural
import STFSpec.State.TxObs
import STFSpec.State.BlockState
import STFSpec.State.BlockInitialization
import STFSpec.State.BlockExtraction
import STFSpec.State.BlockView
import STFSpec.State.ModelsLookups

/-!
# STFSpec.State

State semantics: `Account`, the `PreState` record and its lookup contract
`ModelsLookups` (the full `Models` is defined in `EthStateCommit`), transaction/block
overlays, lifetimes, `BlockDiff`, and their laws. Independent of commitments.

Library `EthState`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). Account values, internal WriteOrder
support, raw MathState observers, raw BlockDiff values, raw mathematical diff
application, the raw PreState carrier with coarse witness-error values and the nominal
StateError, raw TxObs and raw BlockState carriers, block initialization with its F20 law,
raw block-diff extraction with seven complete field equations,
the mathematical block view with its ordinary application equation,
bounded structural preservation and
supplied-record success-only `ModelsLookups`.
Lookup providers, model mutation, combined transaction state, tracker effects and lifecycle laws
remain scaffolding.
Spec guidance: `STFSpec/informal/modules/EthState.md`.
-/
