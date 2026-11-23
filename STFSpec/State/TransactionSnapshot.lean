/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.TxState

/-!
# Transaction snapshots and rollback

Library `EthState`. A snapshot contains the complete revertible record from D22/D23.
Spec guidance: `STFSpec/informal/modules/EthState.md` R24 and §5.
-/

namespace STFSpec.State

/-- Save the revertible fields, including the B1 write-order indexes.
See EELS `src/ethereum/forks/amsterdam/state_tracker.py:744–777` at the pin. -/
def copyTxState {m : Type → Type} (t : TxState m) : TxRevertible :=
  t.rev

/-- Install the saved revertible record while keeping the current block and observations.
See EELS `src/ethereum/forks/amsterdam/state_tracker.py:780–798` at the pin. -/
def restoreTxState {m : Type → Type} [Monad m] (snap : TxRevertible) : StateM m Unit :=
  fun t ↦ ExceptT.mk (pure (.ok ((), { t with rev := snap })))

end STFSpec.State
