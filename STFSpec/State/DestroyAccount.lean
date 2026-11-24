/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.DestroyStorage
import STFSpec.State.SetAccount

/-!
# Transaction account destruction

Library `EthState`. Spec guidance `STFSpec/informal/modules/EthState.md` R17.
-/

namespace STFSpec.State

open Base

/-- Clear the target's storage, then record an account tombstone in write order.
Implements EELS `src/ethereum/forks/amsterdam/state_tracker.py:484–501`. -/
def destroyAccount {m : Type → Type} [Monad m] (a : Address) : StateM m Unit := do
  destroyStorage a
  setAccount a none

end STFSpec.State
