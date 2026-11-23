/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.AccountDefault

/-!
# Account deployability

Library `EthState`. Test the nonce and code hash of the current defaulted account.
Spec guidance is in `STFSpec/informal/modules/EthState.md` R13 and §7.1.
-/

namespace STFSpec.State

open Base

section

variable (consts : HashConsts)
local notation "EMPTY_CODE_HASH" => consts.emptyCodeHash

private def deployableFields (account : Account) : Bool :=
  account.nonce == 0 && account.codeHash == EMPTY_CODE_HASH

end

/-- Read the current defaulted account once and test its nonce and code hash.
Implements `src/ethereum/forks/amsterdam/state_tracker.py:372–380` at the pin. -/
def accountDeployable {m : Type → Type} [Monad m] (a : Address) :
    StateM m Bool := fun t ↦ ExceptT.mk do
  match ← ((getAccount a).run t).run with
  | .ok (account, next) => pure (.ok (deployableFields t.block.consts account, next))
  | .error error => pure (.error error)

private theorem deployableFields_iff (consts : HashConsts) (account : Account) :
    deployableFields consts account = true ↔
      account.nonce = 0 ∧ account.codeHash = consts.emptyCodeHash := by
  simp [deployableFields, beq_iff_eq]

private theorem accountDeployable_action {m : Type → Type} [Monad m]
    (t : TxState m) (a : Address) :
    ((accountDeployable a).run t).run = (do
      match ← ((getAccount a).run t).run with
      | .ok (account, next) => pure (.ok (deployableFields t.block.consts account, next))
      | .error error => pure (.error error)) := rfl

private theorem accountDeployable_success (t next : TxState Id) (a : Address)
    (account : Account) (read : ((getAccount a).run t).run = .ok (account, next)) :
    ((accountDeployable a).run t).run = .ok (deployableFields t.block.consts account, next) := by
  rw [accountDeployable_action, read]
  rfl

private theorem accountDeployable_error (t : TxState Id) (a : Address) (error : StateError)
    (read : ((getAccount a).run t).run = .error error) :
    ((accountDeployable a).run t).run = .error error := by
  rw [accountDeployable_action, read]
  rfl

private theorem accountDeployable_model (t next : TxState Id) (initial : MathState)
    (a : Address) (account : Account) (wf : MathState.WF initial)
    (models : ModelsLookups t.block.consts t.block.preState initial)
    (read : ((getAccount a).run t).run = .ok (account, next)) :
    ((accountDeployable a).run t).run = .ok
      (deployableFields t.block.consts
        (((t.view initial).account? a).getD (emptyAccount t.block.consts)), next) := by
  rw [accountDeployable_success t next a account read,
    getAccount_model t initial wf models a account next read]

end STFSpec.State
