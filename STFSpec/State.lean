/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.Account
import STFSpec.State.WriteOrder
import STFSpec.State.TxRevertible
import STFSpec.State.MathState
import STFSpec.State.BlockDiff
import STFSpec.State.Apply
import STFSpec.State.PreState
import STFSpec.State.StateError
import STFSpec.State.Structural
import STFSpec.State.TxObs
import STFSpec.State.BlockState
import STFSpec.State.TxState
import STFSpec.State.PreStateAccount
import STFSpec.State.BlockInitialization
import STFSpec.State.ReadSets
import STFSpec.State.BlockExtraction
import STFSpec.State.BlockView
import STFSpec.State.ModelsLookups
import STFSpec.State.WitnessAncestors

/-!
# STFSpec.State

State semantics: `Account`, the `PreState` record and its lookup contract
`ModelsLookups` (the full `Models` is defined in `EthStateCommit`), transaction/block
overlays, lifetimes, `BlockDiff`, and their laws. Independent of commitments.

Library `EthState`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). Account values, internal WriteOrder
support, raw MathState observers, raw BlockDiff values, raw mathematical diff
application, the raw PreState carrier with coarse witness-error values, the nominal
StateError carrier, the raw eight-field TxRevertible carrier, the raw TxObs,
BlockState and three-field TxState carriers, the StateM transformer alias,
block initialization with its F20 law, logical account/storage read
views and membership laws, raw block-diff extraction with seven complete field
equations, the mathematical block view with its ordinary application equation, bounded
structural preservation, supplied-record success-only `ModelsLookups` and opaque witness
ancestor selection are supplied. TxState assembles the complete providers with hash-only
code observations; it supplies no current-pin full-state refinement. The Monad-only optional pre-transaction account read and defaulted wrapper, with
their bounded action/error/framing/membership/model laws, are supplied. Lookup providers, model
mutation, other tracker effects and lifecycle laws remain scaffolding.
Spec guidance: `STFSpec/informal/modules/EthState.md`.
-/
