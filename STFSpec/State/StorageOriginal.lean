/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.BlockView
import STFSpec.State.ModelsLookups
import STFSpec.State.TxState

/-!
# Original storage reads

The `EthState` action reads an original slot according to R12 in
`STFSpec/informal/modules/EthState.md`.
-/

namespace STFSpec.State

open Base

/-- Read an original slot. A created account returns zero. Otherwise a block slot write
wins over a block clear, and a miss in both uses the retained pre-state provider.
Success retains the whole transaction. Implements
`src/ethereum/forks/amsterdam/state_tracker.py:298–324` at the pin. -/
def getStorageOriginal {m : Type → Type} [Monad m]
    (a : Address) (k : Bytes32) : StateM m U256 := fun t ↦ ExceptT.mk <|
  if a ∈ t.obs.createdAccounts then pure (.ok (U256.zero, t))
  else
    match (t.block.storageWrites[a]?).bind (fun writes ↦ writes[k]?) with
    | some value => pure (.ok (value, t))
    | none =>
      if a ∈ t.block.storageClears then pure (.ok (U256.zero, t))
      else do
        match ← t.block.preState.getStorage a k with
        | .ok value => pure (.ok (value, t))
        | .error error => pure (.error (.witness error))

private theorem original_of_created {m : Type → Type} [Monad m] (t : TxState m)
    (a : Address) (k : Bytes32) (created : a ∈ t.obs.createdAccounts) :
    ((getStorageOriginal a k).run t).run = pure (.ok (U256.zero, t)) := by
  simp only [StateT.run, ExceptT.run, ExceptT.mk, getStorageOriginal, created, ite_true]

private theorem original_of_write {m : Type → Type} [Monad m] (t : TxState m)
    (a : Address) (k : Bytes32) (value : U256) (created : a ∉ t.obs.createdAccounts)
    (hit : (t.block.storageWrites[a]?).bind (fun writes ↦ writes[k]?) = some value) :
    ((getStorageOriginal a k).run t).run = pure (.ok (value, t)) := by
  simp only [StateT.run, ExceptT.run, ExceptT.mk, getStorageOriginal, created, ite_false, hit]

private theorem original_of_clear {m : Type → Type} [Monad m] (t : TxState m)
    (a : Address) (k : Bytes32) (created : a ∉ t.obs.createdAccounts)
    (miss : (t.block.storageWrites[a]?).bind (fun writes ↦ writes[k]?) = none)
    (cleared : a ∈ t.block.storageClears) :
    ((getStorageOriginal a k).run t).run = pure (.ok (U256.zero, t)) := by
  simp only [StateT.run, ExceptT.run, ExceptT.mk, getStorageOriginal, created, ite_false, miss,
    cleared, ite_true]

private theorem original_of_provider {m : Type → Type} [Monad m] (t : TxState m)
    (a : Address) (k : Bytes32) (created : a ∉ t.obs.createdAccounts)
    (miss : (t.block.storageWrites[a]?).bind (fun writes ↦ writes[k]?) = none)
    (cleared : a ∉ t.block.storageClears) :
    ((getStorageOriginal a k).run t).run = (do
      match ← t.block.preState.getStorage a k with
      | .ok value => pure (.ok (value, t))
      | .error error => pure (.error (.witness error))) := by
  simp only [StateT.run, ExceptT.run, ExceptT.mk, getStorageOriginal, created, ite_false, miss,
    cleared]

private theorem original_model (t next : TxState Id) (σ₀ : MathState)
    (_wf : MathState.WF σ₀) (agreement : ModelsLookups t.block.consts t.block.preState σ₀)
    (a : Address) (k : Bytes32) (value : U256)
    (success : ((getStorageOriginal a k).run t).run = .ok (value, next)) :
    value = (if a ∈ t.obs.createdAccounts then U256.zero else (t.block.view σ₀).storageAt a k) ∧
      next = t := by
  rw [← t.block.apply_extractBlockDiff σ₀, MathState.apply_storageAt_eq,
    extractBlockDiff_storageChanges, extractBlockDiff_storageClears]
  by_cases created : a ∈ t.obs.createdAccounts
  · rw [original_of_created t a k created] at success
    rw [ite_eq_left created]
    exact Prod.mk.inj (Except.ok.inj success.symm)
  · rw [ite_eq_right created]
    cases slot : (t.block.storageWrites[a]?).bind (fun writes ↦ writes[k]?) with
    | some written =>
      rw [original_of_write t a k written created slot] at success
      exact Prod.mk.inj (Except.ok.inj success.symm)
    | none =>
      by_cases cleared : a ∈ t.block.storageClears
      · rw [original_of_clear t a k created slot cleared] at success
        rw [ite_eq_left cleared]
        exact Prod.mk.inj (Except.ok.inj success.symm)
      · rw [original_of_provider t a k created slot cleared] at success
        rw [ite_eq_right cleared]
        change (match t.block.preState.getStorage a k with
          | .ok written => Except.ok (written, t)
          | .error error => Except.error (StateError.witness error)) = Except.ok (value, next) at success
        cases answer : t.block.preState.getStorage a k with
        | error error => simp [answer] at success
        | ok returned =>
          rw [answer] at success
          obtain ⟨sameValue, sameState⟩ := Prod.mk.inj (Except.ok.inj success.symm)
          exact ⟨sameValue.trans (agreement.2.1 a k returned answer).symm, sameState⟩

end STFSpec.State
