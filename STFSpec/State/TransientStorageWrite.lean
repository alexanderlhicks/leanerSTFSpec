/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.TxState

/-!
# Transient storage writes

Library `EthState`. Update one entry in the transaction's revertible transient map.
Spec guidance: `STFSpec/informal/modules/EthState.md` R23 and §7.1.
-/

namespace STFSpec.State

open Base

/-- Write the full address and slot pair, erasing the entry when the word is zero.
Implements `src/ethereum/forks/amsterdam/state_tracker.py:574–598` at the pin. -/
def setTransientStorage {m : Type → Type} [Monad m]
    (a : Address) (k : Bytes32) (v : U256) : StateM m Unit := fun t ↦
  let map := t.rev.transient
  let updated := if v = U256.zero then map.erase (a, k) else map.insert (a, k) v
  ExceptT.mk (pure (.ok ((), { t with rev.transient := updated })))

end STFSpec.State
