/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.AccountOptional

/-!
# Current account emptiness and liveness

Library `EthState`. Classify present accounts against the empty account from
the lookup's returned block context.
Spec guidance is in `STFSpec/informal/modules/EthState.md` §§2.4/7.1.
-/

namespace STFSpec.State

open Base

private def testCurrentAccount {m : Type → Type} [Monad m]
    (a : Address) (test : Account → Account → Bool) : StateM m Bool := fun t ↦ ExceptT.mk do
  match ← ((getAccountOptional a).run t).run with
  | .error error => pure (.error error)
  | .ok (none, next) => pure (.ok (false, next))
  | .ok (some account, next) => pure (.ok (test account (emptyAccount next.block.consts), next))

/-- Check whether the current account is present and empty.
Follows `src/ethereum/forks/amsterdam/state_tracker.py:383–410` at the pin. -/
def accountExistsAndIsEmpty {m : Type → Type} [Monad m] (a : Address) : StateM m Bool :=
  testCurrentAccount a fun account empty ↦ decide (account = empty)

/-- Check whether the current account is present and nonempty.
Follows `src/ethereum/forks/amsterdam/state_tracker.py:413–431` at the pin. -/
def isAccountAlive {m : Type → Type} [Monad m] (a : Address) : StateM m Bool :=
  testCurrentAccount a fun account empty ↦ decide (account ≠ empty)

end STFSpec.State
