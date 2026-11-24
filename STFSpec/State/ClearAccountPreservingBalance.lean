/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.DestroyStorage
import STFSpec.State.ModifyState

/-!
# Clear an account while preserving its balance

Library `EthState`. See `STFSpec/informal/modules/EthState.md` R17.
-/

namespace STFSpec.State
open Base

/-- Clear storage first, then reset the nonce and code hash through R18.
EELS `src/ethereum/forks/amsterdam/state_tracker.py:504–525` at the pin. -/
def clearAccountPreservingBalance {m : Type → Type} [Monad m] (a : Address) : StateM m Unit :=
  fun t ↦
    let emptyHash := t.block.consts.emptyCodeHash
    (do
      destroyStorage a
      modifyState a (fun account ↦ .ok { account with nonce := 0, codeHash := emptyHash })
      : StateM m Unit).run t

end STFSpec.State
