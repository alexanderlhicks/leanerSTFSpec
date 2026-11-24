/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.ModifyState

/-!
# Account balance and nonce updates

Library `EthState`. Spec guidance `STFSpec/informal/modules/EthState.md` R20.
-/

namespace STFSpec.State
open Base

/-- Replace the balance through R18, preserving the nonce and code hash.
EELS `src/ethereum/forks/amsterdam/state_tracker.py:673–693` at the pin. -/
def setAccountBalance {m : Type → Type} [Monad m] (a : Address) (amount : U256) : StateM m Unit :=
  modifyState a (fun account ↦ .ok { account with balance := amount })

/-- Increase the unbounded nonce through R18, retaining the balance and code hash.
EELS `src/ethereum/forks/amsterdam/state_tracker.py:696–712` at the pin. -/
def incrementNonce {m : Type → Type} [Monad m] (a : Address) : StateM m Unit :=
  modifyState a (fun account ↦ .ok { account with nonce := account.nonce + 1 })

end STFSpec.State
