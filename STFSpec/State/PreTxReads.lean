/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.BlockView
import STFSpec.State.TxState
import STFSpec.State.StateError

/-!
# Pre-transaction values for the block access list

Library `EthState`. Read the cumulative block overlay or its retained provider
without changing the tracker. Spec guidance: `STFSpec/informal/modules/EthState.md`
§§3/5/7/8.
-/

namespace STFSpec.State

open Base

/-- Return the block account entry, including a tombstone, or bind the retained
optional account action. EELS `src/ethereum/forks/amsterdam/block_access_lists.py:690–705`
at the pin. -/
def preTxAccount {m : Type → Type} [Monad m] (t : TxState m) (a : Address) :
    m (Except StateError (Option Account)) :=
  match t.block.accountWrites[a]? with
  | some account => pure (.ok account)
  | none => do
    match ← t.block.preState.getAccount? a with
    | .ok account => pure (.ok account)
    | .error err => pure (.error (.witness err))

/-- Return a block slot, including zero, or zero after a block clear. A remaining
miss binds the retained storage action. EELS
`src/ethereum/forks/amsterdam/block_access_lists.py:708–724` at the pin. -/
def preTxStorage {m : Type → Type} [Monad m] (t : TxState m) (a : Address) (k : Bytes32) :
    m (Except StateError U256) :=
  match (t.block.storageWrites[a]?).bind (fun slots ↦ slots[k]?) with
  | some value => pure (.ok value)
  | none =>
    if a ∈ t.block.storageClears then pure (.ok U256.zero)
    else do
      match ← t.block.preState.getStorage a k with
      | .ok value => pure (.ok value)
      | .error err => pure (.error (.witness err))

private theorem preTxAccount_action {m : Type → Type} [Monad m] (t : TxState m)
    (a : Address) :
    preTxAccount t a = (match t.block.accountWrites[a]? with
      | some account => pure (.ok account)
      | none => do
        match ← t.block.preState.getAccount? a with
        | .ok account => pure (.ok account)
        | .error err => pure (.error (.witness err))) := rfl

private theorem preTxStorage_action {m : Type → Type} [Monad m] (t : TxState m)
    (a : Address) (k : Bytes32) :
    preTxStorage t a k = (match (t.block.storageWrites[a]?).bind (fun slots ↦ slots[k]?) with
      | some value => pure (.ok value)
      | none =>
        if a ∈ t.block.storageClears then pure (.ok U256.zero)
        else do
          match ← t.block.preState.getStorage a k with
          | .ok value => pure (.ok value)
          | .error err => pure (.error (.witness err))) := rfl

private theorem accountFramed {m : Type → Type} [Monad m] (t u : TxState m) (a : Address)
    (writes : t.block.accountWrites[a]? = u.block.accountWrites[a]?)
    (provider : t.block.preState.getAccount? a = u.block.preState.getAccount? a) :
    preTxAccount t a = preTxAccount u a := by
  simp only [preTxAccount_action, writes, provider]

private theorem storageFramed {m : Type → Type} [Monad m] (t u : TxState m) (a : Address)
    (k : Bytes32)
    (slot : (t.block.storageWrites[a]?).bind (fun slots ↦ slots[k]?) =
      (u.block.storageWrites[a]?).bind (fun slots ↦ slots[k]?))
    (clear : a ∈ t.block.storageClears ↔ a ∈ u.block.storageClears)
    (provider : t.block.preState.getStorage a k = u.block.preState.getStorage a k) :
    preTxStorage t a k = preTxStorage u a k := by
  simp only [preTxStorage_action, slot, clear, provider]

private theorem accountView (t : TxState Id) (σ : MathState) (a : Address)
    (account : Option Account)
    (agreement : ∀ result, t.block.preState.getAccount? a = .ok result → σ.account? a = result)
    (found : preTxAccount t a = .ok account) :
    (t.block.view σ).account? a = account := by
  rw [← t.block.apply_extractBlockDiff σ, MathState.apply_account?_eq,
    extractBlockDiff_accountChanges]
  cases slot : t.block.accountWrites[a]? with
  | some stored =>
    simp only [preTxAccount, slot] at found
    exact Except.ok.inj found
  | none =>
    cases result : t.block.preState.getAccount? a with
    | error err =>
      simp only [preTxAccount, slot, result] at found
      cases found
    | ok raw =>
      simp only [preTxAccount, slot, result] at found
      exact (agreement _ result).trans (Except.ok.inj found)

private theorem storageView (t : TxState Id) (σ : MathState) (a : Address) (k : Bytes32)
    (value : U256)
    (agreement : ∀ result, t.block.preState.getStorage a k = .ok result → σ.storageAt a k = result)
    (found : preTxStorage t a k = .ok value) :
    (t.block.view σ).storageAt a k = value := by
  rw [← t.block.apply_extractBlockDiff σ, MathState.apply_storageAt_eq,
    extractBlockDiff_storageChanges, extractBlockDiff_storageClears]
  cases slot : (t.block.storageWrites[a]?).bind (fun slots ↦ slots[k]?) with
  | some written =>
    simp only [preTxStorage, slot] at found
    exact Except.ok.inj found
  | none =>
    by_cases clear : a ∈ t.block.storageClears
    · simp only [preTxStorage, slot, clear, ite_true] at found
      simp only [clear, ite_true]
      exact Except.ok.inj found
    · cases result : t.block.preState.getStorage a k with
      | error err =>
        simp only [preTxStorage, slot, clear, ite_false, result] at found
        cases found
      | ok raw =>
        simp only [preTxStorage, slot, clear, ite_false, result] at found
        simp only [clear, ite_false]
        exact (agreement _ result).trans (Except.ok.inj found)

end STFSpec.State
