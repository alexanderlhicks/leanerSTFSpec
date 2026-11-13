/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.TxState
import STFSpec.State.BlockView
import STFSpec.State.ModelsLookups

/-!
# Optional account before the transaction

Library `EthState`: record an account read, then use the block write or its retained
provider. Transaction writes are skipped and provider failures retain their payload.
Spec guidance: `STFSpec/informal/modules/EthState.md` R29/R30/§7.1.
-/

namespace STFSpec.State

open Base

/-- Read the optional account before the transaction, preserving absence and tombstones.
Implements `src/ethereum/forks/amsterdam/state_tracker.py:107–137` at the pin.
Every fall-through invokes the retained provider, even after an earlier observation.
Failure returns no transaction state, following the existing `StateM` wiring. -/
def getPreStateAccountOptional {m : Type → Type} [Monad m]
    (a : Address) : StateM m (Option Account) := fun t ↦ ExceptT.mk do
  let next := { t with obs.accountReads := t.obs.accountReads.insert a }
  match t.block.accountWrites[a]? with
  | some account => pure (.ok (account, next))
  | none =>
    match ← t.block.preState.getAccount? a with
    | .ok account => pure (.ok (account, next))
    | .error error => pure (.error (.witness error))

/-- A stored block value, including a tombstone, suppresses every provider action. -/
theorem getPreStateAccountOptional_of_block {m : Type → Type} [Monad m]
    (t : TxState m) (a : Address) (account : Option Account)
    (h : t.block.accountWrites[a]? = some account) :
    ((getPreStateAccountOptional a).run t).run =
      pure (.ok (account, { t with obs.accountReads := t.obs.accountReads.insert a })) := by
  change (match t.block.accountWrites[a]? with
    | some value => _
    | none => _) = _
  simp only [h]

/-- A missing block entry invokes exactly the supplied account action once.
This action equation interprets no arbitrary base-monad effects. -/
theorem getPreStateAccountOptional_of_missing {m : Type → Type} [Monad m]
    (t : TxState m) (a : Address) (h : t.block.accountWrites[a]? = none) :
    ((getPreStateAccountOptional a).run t).run = (do
      match ← t.block.preState.getAccount? a with
      | .ok account => pure (.ok
          (account, { t with obs.accountReads := t.obs.accountReads.insert a }))
      | .error error => pure (.error (.witness error))) := by
  change (match t.block.accountWrites[a]? with
    | some value => _
    | none => _) = _
  simp only [h]

/-- At `Id`, a provider failure retains its exact typed payload and returns no state. -/
theorem getPreStateAccountOptional_error (t : TxState Id) (a : Address)
    (error : WitnessError) (hb : t.block.accountWrites[a]? = none)
    (hp : t.block.preState.getAccount? a = .error error) :
    ((getPreStateAccountOptional a).run t).run = .error (.witness error) := by
  rw [getPreStateAccountOptional_of_missing t a hb]
  simp only [hp]
  rfl

private theorem success_state (t : TxState Id) (a : Address) (account : Option Account)
    (next : TxState Id)
    (h : ((getPreStateAccountOptional a).run t).run = .ok (account, next)) :
    next = { t with obs.accountReads := t.obs.accountReads.insert a } := by
  cases hb : t.block.accountWrites[a]? with
  | some value =>
    rw [getPreStateAccountOptional_of_block t a value hb] at h
    exact (Prod.mk.inj (Except.ok.inj h)).2.symm
  | none =>
    rw [getPreStateAccountOptional_of_missing t a hb] at h
    cases hp : t.block.preState.getAccount? a with
    | error e => simp [hp] at h
    | ok value =>
      simp only [hp] at h
      change Except.ok (value, _) = Except.ok (account, next) at h
      exact (Prod.mk.inj (Except.ok.inj h)).2.symm

/-- Successful reads retain the complete block and revertible data and all unrelated
observations. No well-formedness or provider-model premise is needed. -/
theorem getPreStateAccountOptional_frames (t : TxState Id) (a : Address)
    (account : Option Account) (next : TxState Id)
    (h : ((getPreStateAccountOptional a).run t).run = .ok (account, next)) :
    next.block = t.block ∧ next.rev = t.rev ∧
      next.obs.storageReads = t.obs.storageReads ∧
      next.obs.codeReads = t.obs.codeReads ∧
      next.obs.createdAccounts = t.obs.createdAccounts := by
  rw [success_state t a account next h]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Successful account-read membership is precisely the queried address or old membership.
The statement asserts semantic membership rather than raw HashSet equality. -/
theorem getPreStateAccountOptional_mem (t : TxState Id) (a b : Address)
    (account : Option Account) (next : TxState Id)
    (h : ((getPreStateAccountOptional a).run t).run = .ok (account, next)) :
    b ∈ next.obs.accountReads ↔ b = a ∨ b ∈ t.obs.accountReads := by
  rw [success_state t a account next h]
  rw [Std.HashSet.mem_insert]
  exact or_congr (by simp only [beq_iff_eq]; exact eq_comm) Iff.rfl

/-- On the §7.1 domain, a successful read returns the mathematical block view's account.
Only the account-success conjunct of the retained provider agreement is used. -/
theorem getPreStateAccountOptional_model (t : TxState Id) (σ₀ : MathState)
    (_hwf : MathState.WF σ₀)
    (hm : ModelsLookups t.block.consts t.block.preState σ₀)
    (a : Address) (account : Option Account) (next : TxState Id)
    (h : ((getPreStateAccountOptional a).run t).run = .ok (account, next)) :
    account = (t.block.view σ₀).account? a := by
  rw [← BlockState.apply_extractBlockDiff, MathState.apply_account?_eq,
    extractBlockDiff_accountChanges]
  cases hb : t.block.accountWrites[a]? with
  | some value =>
    rw [getPreStateAccountOptional_of_block t a value hb] at h
    exact (Prod.mk.inj (Except.ok.inj h)).1.symm
  | none =>
    rw [getPreStateAccountOptional_of_missing t a hb] at h
    cases hp : t.block.preState.getAccount? a with
    | error e => simp [hp] at h
    | ok value =>
      simp only [hp] at h
      change Except.ok (value, _) = Except.ok (account, next) at h
      have he := (Prod.mk.inj (Except.ok.inj h)).1
      exact he ▸ (hm.1 a value hp).symm

end STFSpec.State
