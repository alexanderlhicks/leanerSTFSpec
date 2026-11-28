/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Hash.KeccakQuery
import STFSpec.State.BlockDiff
import STFSpec.State.MathState
import STFSpec.State.PreState

/-!
# Code-hash agreement

Library `EthStateCommit`. Raw code tables authenticate every stored entry.
Provider agreement requires the empty-code answer and authenticates successful reads.
Spec guidance: `STFSpec/informal/modules/EthStateCommit.md` §§5, 7.3.
-/

namespace STFSpec.StateCommit

open STFSpec.Base STFSpec.Hash STFSpec.State

/-- Each raw code entry is keyed by its digest, including entries hidden by the
reserved-hash lookup bypass. EELS `src/ethereum/state_mpt.py:49–57` and `:164–170`. -/
def CodeAuthentic (σ : MathState) : Prop :=
  ∀ h code, σ.code[h]? = some code → Id.run (KeccakQuery.keccak (m := Id) code) = h

/-- Each raw code change is keyed by its digest. EELS `src/ethereum/state_mpt.py:161`
applies every supplied entry. -/
def CodeChangesAuthentic (d : BlockDiff) : Prop :=
  ∀ h code, d.codeChanges[h]? = some code → Id.run (KeccakQuery.keccak (m := Id) code) = h

/-- The provider returns empty code at the concrete reserved hash and authentic
bytes on every success. EELS `src/ethereum/state_mpt.py:49–57` and
`src/ethereum/forks/amsterdam/witness_state.py:129–137`. -/
def ModelsCode (ps : PreState Id) : Prop :=
  ps.getCode (Id.run (HashConsts.query (m := Id))).emptyCodeHash = .ok ByteArray.empty ∧
    ∀ h code, ps.getCode h = .ok code → Id.run (KeccakQuery.keccak (m := Id) code) = h

end STFSpec.StateCommit
