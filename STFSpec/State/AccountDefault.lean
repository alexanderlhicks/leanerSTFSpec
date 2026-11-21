/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.AccountOptional

/-!
# Defaulted current account reads

Library `EthState`: default only successful current-account absence using the initial
retained constants. Present accounts, complete success state and exact errors survive.
Spec guidance: `STFSpec/informal/modules/EthState.md` R29/R30/§7.1.
-/

namespace STFSpec.State

open Base

/-- Read the current account, defaulting only absence to the retained constants.
Implements `src/ethereum/forks/amsterdam/state_tracker.py:200–225` at the pin.
The optional action runs once; its exact state and errors are retained. -/
def getAccount {m : Type → Type} [Monad m]
    (a : Address) : StateM m Account := fun t ↦ ExceptT.mk do
  match ← ((getAccountOptional a).run t).run with
  | .ok (account, next) => pure (.ok (account.getD (emptyAccount t.block.consts), next))
  | .error error => pure (.error error)

/-- Complete literal wrapper action, with no laws assumed of the base Monad. -/
theorem getAccount_action {m : Type → Type} [Monad m]
    (t : TxState m) (a : Address) :
    ((getAccount a).run t).run = (do
      match ← ((getAccountOptional a).run t).run with
      | .ok (account, next) => pure (.ok (account.getD (emptyAccount t.block.consts), next))
      | .error error => pure (.error error)) := rfl

/-- Both overlay misses and provider failure return the exact wrapped error at Id. -/
theorem getAccount_error (t : TxState Id) (a : Address)
    (error : WitnessError) (ht : t.rev.accountWrites[a]? = none)
    (hb : t.block.accountWrites[a]? = none)
    (hp : t.block.preState.getAccount? a = .error error) :
    ((getAccount a).run t).run = .error (.witness error) := by
  rw [getAccount_action, getAccountOptional_error t a error ht hb hp]
  rfl

private theorem default_success (t : TxState Id) (a : Address) (account : Account)
    (next : TxState Id)
    (h : ((getAccount a).run t).run = .ok (account, next)) :
    ∃ optional, ((getAccountOptional a).run t).run = .ok (optional, next) ∧
      account = optional.getD (emptyAccount t.block.consts) := by
  rw [getAccount_action] at h
  cases ho : ((getAccountOptional a).run t).run with
  | error error => simp [ho] at h
  | ok pair =>
    rcases pair with ⟨optional, state⟩
    simp only [ho] at h
    change Except.ok (optional.getD (emptyAccount t.block.consts), state) =
      Except.ok (account, next) at h
    obtain ⟨ha, hs⟩ := Prod.mk.inj (Except.ok.inj h)
    exact ⟨optional, hs ▸ rfl, ha.symm⟩

/-- Id success retains the whole block and revertible data and unrelated observations. -/
theorem getAccount_frames (t : TxState Id) (a : Address)
    (account : Account) (next : TxState Id)
    (h : ((getAccount a).run t).run = .ok (account, next)) :
    next.block = t.block ∧ next.rev = t.rev ∧
      next.obs.storageReads = t.obs.storageReads ∧
      next.obs.codeReads = t.obs.codeReads ∧
      next.obs.createdAccounts = t.obs.createdAccounts := by
  obtain ⟨optional, ho, _⟩ := default_success t a account next h
  exact getAccountOptional_frames t a optional next ho

/-- Id success adds precisely the queried semantic account-read membership. -/
theorem getAccount_mem (t : TxState Id) (a b : Address)
    (account : Account) (next : TxState Id)
    (h : ((getAccount a).run t).run = .ok (account, next)) :
    b ∈ next.obs.accountReads ↔ b = a ∨ b ∈ t.obs.accountReads := by
  obtain ⟨optional, ho, _⟩ := default_success t a account next h
  exact getAccountOptional_mem t a b optional next ho

/-- Under the existing initial WF/lookup/success domain, default the transaction-view account. -/
theorem getAccount_model (t : TxState Id) (σ₀ : MathState)
    (hwf : MathState.WF σ₀)
    (hm : ModelsLookups t.block.consts t.block.preState σ₀)
    (a : Address) (account : Account) (next : TxState Id)
    (h : ((getAccount a).run t).run = .ok (account, next)) :
    account = ((t.view σ₀).account? a).getD (emptyAccount t.block.consts) := by
  obtain ⟨optional, ho, ha⟩ := default_success t a account next h
  rw [ha, getAccountOptional_model t σ₀ hwf hm a optional next ho]

end STFSpec.State
