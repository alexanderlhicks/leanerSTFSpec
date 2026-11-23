/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.AccountOptional

/-!
# Current account existence

Library `EthState`. Test the presence of the current optional account.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§2.4/3/5/7.1.
-/

namespace STFSpec.State

open Base

/-- Read the current optional account once and test its presence.
EELS `src/ethereum/forks/amsterdam/state_tracker.py:352–369` at the pin.
A present empty account counts as present. The read supplies the returned state or error. -/
def accountExists {m : Type → Type} [Monad m]
    (a : Address) : StateM m Bool := fun t ↦ ExceptT.mk do
  match ← ((getAccountOptional a).run t).run with
  | .ok (account, next) => pure (.ok (account.isSome, next))
  | .error error => pure (.error error)

private theorem accountExists_action {m : Type → Type} [Monad m]
    (a : Address) (t : TxState m) :
    ((accountExists a).run t).run = (do
      match ← ((getAccountOptional a).run t).run with
      | .ok (account, next) => pure (.ok (account.isSome, next))
      | .error error => pure (.error error)) := rfl

private theorem accountExists_result (a : Address) (t : TxState Id) :
    ((accountExists a).run t).run =
      (((getAccountOptional a).run t).run : Except StateError (Option Account × TxState Id)).map
        (fun (account, next) ↦ (account.isSome, next)) := by
  rw [accountExists_action]
  cases ((getAccountOptional a).run t).run with
  | error error => rfl
  | ok pair =>
    rcases pair with ⟨account, next⟩
    rfl

private theorem accountExists_model (a : Address) (t : TxState Id) (σ₀ : MathState)
    (hwf : MathState.WF σ₀) (hm : ModelsLookups t.block.consts t.block.preState σ₀)
    (account : Option Account) (next : TxState Id)
    (h : ((getAccountOptional a).run t).run = .ok (account, next)) :
    ((accountExists a).run t).run = .ok (((t.view σ₀).account? a).isSome, next) := by
  rw [accountExists_result, h, ← getAccountOptional_model t σ₀ hwf hm a account next h]
  rfl

end STFSpec.State
