/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.PreStateAccount
import STFSpec.State.TransactionView

/-!
# Current optional account reads

Library `EthState`: record the account read, select a transaction entry including a
tombstone, or delegate to the pre-transaction read on the marked state.
Spec guidance: `STFSpec/informal/modules/EthState.md` R29/R30/§7.1.
-/

namespace STFSpec.State

open Base

/-- Read the current optional account, retaining transaction tombstones and absence.
Implements `src/ethereum/forks/amsterdam/state_tracker.py:174–197` at the pin.
Transaction misses retain the pre-transaction action's second read insertion and
provider sequencing. Failure returns no transaction state through `StateM`. -/
def getAccountOptional {m : Type → Type} [Monad m]
    (a : Address) : StateM m (Option Account) := fun t ↦ ExceptT.mk <|
  let next := { t with obs.accountReads := t.obs.accountReads.insert a }
  match t.rev.accountWrites[a]? with
  | some account => pure (.ok (account, next))
  | none => ((getPreStateAccountOptional a).run next).run

/-- A transaction entry, including a tombstone, suppresses the block/provider read. -/
theorem getAccountOptional_of_tx {m : Type → Type} [Monad m]
    (t : TxState m) (a : Address) (account : Option Account)
    (h : t.rev.accountWrites[a]? = some account) :
    ((getAccountOptional a).run t).run =
      pure (.ok (account, { t with obs.accountReads := t.obs.accountReads.insert a })) := by
  change (match t.rev.accountWrites[a]? with
    | some value => _
    | none => _) = _
  simp only [h]

/-- A transaction miss delegates the complete action on the once-marked state.
Only `Monad` is assumed; no duplicate-insert or base-effect equation is used. -/
theorem getAccountOptional_of_missing {m : Type → Type} [Monad m]
    (t : TxState m) (a : Address) (h : t.rev.accountWrites[a]? = none) :
    ((getAccountOptional a).run t).run =
      ((getPreStateAccountOptional a).run
        { t with obs.accountReads := t.obs.accountReads.insert a }).run := by
  change (match t.rev.accountWrites[a]? with
    | some value => _
    | none => _) = _
  simp only [h]

/-- At `Id`, both overlay misses preserve the complete provider error without state. -/
theorem getAccountOptional_error (t : TxState Id) (a : Address)
    (error : WitnessError) (ht : t.rev.accountWrites[a]? = none)
    (hb : t.block.accountWrites[a]? = none)
    (hp : t.block.preState.getAccount? a = .error error) :
    ((getAccountOptional a).run t).run = .error (.witness error) := by
  rw [getAccountOptional_of_missing t a ht]
  exact getPreStateAccountOptional_error _ a error hb hp

private theorem success_cases (t : TxState Id) (a : Address) (account : Option Account)
    (next : TxState Id)
    (h : ((getAccountOptional a).run t).run = .ok (account, next)) :
    (t.rev.accountWrites[a]? = some account ∧
      next = { t with obs.accountReads := t.obs.accountReads.insert a }) ∨
    (t.rev.accountWrites[a]? = none ∧
      ((getPreStateAccountOptional a).run
        { t with obs.accountReads := t.obs.accountReads.insert a }).run =
        .ok (account, next)) := by
  cases ht : t.rev.accountWrites[a]? with
  | some value =>
    rw [getAccountOptional_of_tx t a value ht] at h
    obtain ⟨ha, hs⟩ := Prod.mk.inj (Except.ok.inj h)
    exact Or.inl ⟨congrArg some ha, hs.symm⟩
  | none =>
    exact Or.inr ⟨rfl, (getAccountOptional_of_missing t a ht) ▸ h⟩

/-- Id success retains the complete block, revertible data and unrelated observations. -/
theorem getAccountOptional_frames (t : TxState Id) (a : Address)
    (account : Option Account) (next : TxState Id)
    (h : ((getAccountOptional a).run t).run = .ok (account, next)) :
    next.block = t.block ∧ next.rev = t.rev ∧
      next.obs.storageReads = t.obs.storageReads ∧
      next.obs.codeReads = t.obs.codeReads ∧
      next.obs.createdAccounts = t.obs.createdAccounts := by
  rcases success_cases t a account next h with ⟨_, hs⟩ | ⟨_, hs⟩
  · rw [hs]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact getPreStateAccountOptional_frames
      { t with obs.accountReads := t.obs.accountReads.insert a } a account next hs

/-- Successful read membership is precisely the queried address or old membership.
The contract does not identify raw duplicate-insert HashSet representations. -/
theorem getAccountOptional_mem (t : TxState Id) (a b : Address)
    (account : Option Account) (next : TxState Id)
    (h : ((getAccountOptional a).run t).run = .ok (account, next)) :
    b ∈ next.obs.accountReads ↔ b = a ∨ b ∈ t.obs.accountReads := by
  have inserted : b ∈ t.obs.accountReads.insert a ↔ b = a ∨ b ∈ t.obs.accountReads := by
    rw [Std.HashSet.mem_insert]
    exact or_congr (by simp only [beq_iff_eq]; exact eq_comm) Iff.rfl
  rcases success_cases t a account next h with ⟨_, hs⟩ | ⟨_, hs⟩
  · rw [hs]
    exact inserted
  · rw [getPreStateAccountOptional_mem _ a b account next hs]
    change (b = a ∨ b ∈ t.obs.accountReads.insert a) ↔ _
    rw [inserted]
    exact ⟨fun h ↦ h.elim Or.inl id, fun h ↦ Or.inr h⟩

/-- Under the existing initial WF/lookup/success domain, return the transaction-view account.
Only the public account-view equation and pre-transaction model law are consumed. -/
theorem getAccountOptional_model (t : TxState Id) (σ₀ : MathState)
    (hwf : MathState.WF σ₀)
    (hm : ModelsLookups t.block.consts t.block.preState σ₀)
    (a : Address) (account : Option Account) (next : TxState Id)
    (h : ((getAccountOptional a).run t).run = .ok (account, next)) :
    account = (t.view σ₀).account? a := by
  rw [TxState.view_account?_eq]
  rcases success_cases t a account next h with ⟨ht, _⟩ | ⟨ht, hs⟩
  · rw [ht]
  · rw [ht]
    exact getPreStateAccountOptional_model
      { t with obs.accountReads := t.obs.accountReads.insert a } σ₀ hwf hm a account next hs

end STFSpec.State
