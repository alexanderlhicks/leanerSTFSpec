/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.TxState

/-!
# Transient storage reads

Library `EthState`. Spec guidance: `STFSpec/informal/modules/EthState.md` §§2.4/7.1.
-/

namespace STFSpec.State

open Base

/-- Read the transaction's transient word with a zero default.
Implements `src/ethereum/forks/amsterdam/state_tracker.py:327–349` at the pin. -/
def getTransientStorage {m : Type → Type} [Monad m]
    (a : Address) (k : Bytes32) : StateM m U256 := fun t ↦
  ExceptT.mk (pure (.ok ((t.rev.transient[(a, k)]?).getD U256.zero, t)))

/-- The underlying action returns the lookup and the whole original transaction state. -/
theorem getTransientStorage_action {m : Type → Type} [Monad m]
    (t : TxState m) (a : Address) (k : Bytes32) :
    ((getTransientStorage a k).run t).run =
      pure (.ok ((t.rev.transient[(a, k)]?).getD U256.zero, t)) := rfl

end STFSpec.State
