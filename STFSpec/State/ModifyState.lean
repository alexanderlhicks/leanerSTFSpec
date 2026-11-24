/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.AccountDefault
import STFSpec.State.AccountEmptiness
import STFSpec.State.DestroyAccount

/-!
# Transaction account modification

Library `EthState`. Spec guidance `STFSpec/informal/modules/EthState.md` R18.
-/

namespace STFSpec.State
open Base

private def writeUpdatedAccount {m : Type → Type} [Monad m]
    (a : Address) (updated : Account) : StateM m Unit := do
  setAccount a (some updated)
  if ← accountExistsAndIsEmpty a then
    destroyAccount a

/-- Read the defaulted account, apply the update, and write the result. A second
current read tests for emptiness before destroying the account.
Implements EELS `src/ethereum/forks/amsterdam/state_tracker.py:601–613`. -/
def modifyState {m : Type → Type} [Monad m]
    (a : Address) (f : Account → Except StateError Account) : StateM m Unit := fun t ↦
  ExceptT.mk do
    match ← ((getAccount a).run t).run with
    | .error error => pure (.error error)
    | .ok (account, next) =>
      match f account with
      | .error error => pure (.error error)
      | .ok updated => ((writeUpdatedAccount a updated).run next).run

end STFSpec.State
