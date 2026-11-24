/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.ModifyState

/-!
# Install transaction code

Library `EthState`. Spec guidance `STFSpec/informal/modules/EthState.md` R21.
-/

namespace STFSpec.State

open Base

/-- Stage code under its supplied hash, then update the account through R18.
The block's supplied empty-code hash suppresses the code-table write.
The caller computes the hash through `KeccakQuery` (D5).
EELS `src/ethereum/forks/amsterdam/state_tracker.py:715–738` at the pin. -/
def setCode {m : Type → Type} [Monad m] (a : Address) (code : ByteArray)
    (codeHash : Hash32) : StateM m Unit := fun t ↦
  let input := if codeHash = t.block.consts.emptyCodeHash then t
    else { t with rev.codeWrites := t.rev.codeWrites.insert codeHash code }
  (modifyState a (fun account ↦ .ok { account with codeHash })).run input

end STFSpec.State
