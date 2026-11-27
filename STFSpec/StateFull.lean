/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateCommit

/-!
# STFSpec.StateFull

The full-state carrier stores a mathematical state with the supplied structural
well-formedness and code authenticity proofs.

Library `EthStateFull`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3).
Spec guidance: `STFSpec/informal/modules/EthStateFull.md`.
-/

namespace STFSpec.StateFull

open STFSpec.State STFSpec.StateCommit

/-- Mathematical carrier for the account, storage and code maps of EELS
`src/ethereum/state_mpt.py:34–47`, with the supplied invariant proofs. -/
structure FullState where
  /-- The complete supplied mathematical state. -/
  σ : MathState
  /-- Structural well-formedness of the supplied state. -/
  wf : MathState.WF σ
  /-- Authenticity of every entry in the supplied raw code table. -/
  codeAuthentic : CodeAuthentic σ

/-- Package the supplied state and its two invariant proofs (FS1). -/
def FullState.ofMath (σ : MathState) (hwf : MathState.WF σ) (hc : CodeAuthentic σ) :
    FullState :=
  {
    σ := σ
    wf := hwf
    codeAuthentic := hc
  }

end STFSpec.StateFull
