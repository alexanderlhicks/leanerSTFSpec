/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.TransactionView
import STFSpec.State.ModelsLookups

/-!
# Current storage reads

Library `EthState`. Record a storage read before selecting a slot write, clear
or provider answer. Spec guidance: `STFSpec/informal/modules/EthState.md`
R11/R29/R30 and §7.1.
-/

namespace STFSpec.State
open Base

private def writtenSlot? (writes : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256))
    (a : Address) (k : Bytes32) : Option U256 :=
  (writes[a]?).bind (fun patch ↦ patch[k]?)

private def markStorageRead {m : Type → Type} (t : TxState m) (a : Address) (k : Bytes32) :
    TxState m :=
  { t with obs.storageReads := t.obs.storageReads.insert (a, k) }

/-- Read the current storage slot and record its address and key.
Implements `src/ethereum/forks/amsterdam/state_tracker.py:262–295` at the pin.
Each layer's slot write takes priority over its clear. If both layers lack the slot
and an address clear, call the retained provider once. On failure, return the wrapped
provider error without a transaction state. -/
def getStorage {m : Type → Type} [Monad m] (a : Address) (k : Bytes32) :
    StateM m U256 := fun t ↦ ExceptT.mk <|
  let next := markStorageRead t a k
  match writtenSlot? t.rev.storageWrites a k with
  | some value => pure (.ok (value, next))
  | none =>
    if a ∈ t.rev.storageClears then pure (.ok (U256.zero, next))
    else
      match writtenSlot? t.block.storageWrites a k with
      | some value => pure (.ok (value, next))
      | none =>
        if a ∈ t.block.storageClears then pure (.ok (U256.zero, next))
        else do
          match ← t.block.preState.getStorage a k with
          | .ok value => pure (.ok (value, next))
          | .error error => pure (.error (.witness error))

private theorem getStorage_of_tx_slot {m : Type → Type} [Monad m] (t : TxState m) (a : Address)
    (k : Bytes32) (v : U256) (h : writtenSlot? t.rev.storageWrites a k = some v) :
    ((getStorage a k).run t).run = pure (.ok (v, markStorageRead t a k)) := by
  simp only [getStorage, StateT.run, ExceptT.run, ExceptT.mk, h]

private theorem getStorage_of_tx_clear {m : Type → Type} [Monad m] (t : TxState m) (a : Address)
    (k : Bytes32) (miss : writtenSlot? t.rev.storageWrites a k = none)
    (h : a ∈ t.rev.storageClears) :
    ((getStorage a k).run t).run = pure (.ok (U256.zero, markStorageRead t a k)) := by
  simp only [getStorage, StateT.run, ExceptT.run, ExceptT.mk, miss, h, ite_true]

private theorem getStorage_of_block_slot {m : Type → Type} [Monad m] (t : TxState m) (a : Address)
    (k : Bytes32) (v : U256) (txMiss : writtenSlot? t.rev.storageWrites a k = none)
    (txKeep : a ∉ t.rev.storageClears) (h : writtenSlot? t.block.storageWrites a k = some v) :
    ((getStorage a k).run t).run = pure (.ok (v, markStorageRead t a k)) := by
  simp only [getStorage, StateT.run, ExceptT.run, ExceptT.mk, txMiss, txKeep, ite_false, h]

private theorem getStorage_of_block_clear {m : Type → Type} [Monad m] (t : TxState m) (a : Address)
    (k : Bytes32) (txMiss : writtenSlot? t.rev.storageWrites a k = none)
    (txKeep : a ∉ t.rev.storageClears) (blockMiss : writtenSlot? t.block.storageWrites a k = none)
    (h : a ∈ t.block.storageClears) :
    ((getStorage a k).run t).run = pure (.ok (U256.zero, markStorageRead t a k)) := by
  simp only [getStorage, StateT.run, ExceptT.run, ExceptT.mk, txMiss, txKeep, ite_false,
    blockMiss, h, ite_true]

private theorem getStorage_of_provider {m : Type → Type} [Monad m] (t : TxState m) (a : Address)
    (k : Bytes32) (txMiss : writtenSlot? t.rev.storageWrites a k = none)
    (txKeep : a ∉ t.rev.storageClears) (blockMiss : writtenSlot? t.block.storageWrites a k = none)
    (blockKeep : a ∉ t.block.storageClears) :
    ((getStorage a k).run t).run = (do
      match ← t.block.preState.getStorage a k with
      | .ok value => pure (.ok (value, markStorageRead t a k))
      | .error error => pure (.error (.witness error))) := by
  simp only [getStorage, StateT.run, ExceptT.run, ExceptT.mk, txMiss, txKeep, ite_false,
    blockMiss, blockKeep]

private theorem viewStorage {m : Type → Type} (t : TxState m) (a : Address)
    (k : Bytes32) (σ : MathState) :
    (t.view σ).storageAt a k = match writtenSlot? t.rev.storageWrites a k with
    | none => if a ∈ t.rev.storageClears then U256.zero else (t.block.view σ).storageAt a k
    | some value => value := by
  rw [TxState.view, MathState.apply_storageAt_eq]
  rfl

private theorem blockViewStorage {m : Type → Type} (t : TxState m) (a : Address)
    (k : Bytes32) (σ : MathState) :
    (t.block.view σ).storageAt a k = match writtenSlot? t.block.storageWrites a k with
    | none => if a ∈ t.block.storageClears then U256.zero else σ.storageAt a k
    | some value => value := by
  rw [← t.block.apply_extractBlockDiff σ, MathState.apply_storageAt_eq,
    extractBlockDiff_storageChanges, extractBlockDiff_storageClears]
  rfl

private theorem pureSuccess (t : TxState Id) (a : Address) (k : Bytes32)
    (expected value : U256) (next : TxState Id)
    (h : Except.ok (expected, markStorageRead t a k) =
      (Except.ok (value, next) : Except StateError (U256 × TxState Id))) :
    value = expected ∧ next = markStorageRead t a k :=
  Prod.mk.inj (Except.ok.inj h.symm)

private theorem getStorage_model (t next : TxState Id) (σ : MathState)
    (_hwf : MathState.WF σ)
    (agreement : ModelsLookups t.block.consts t.block.preState σ)
    (a : Address) (k : Bytes32) (value : U256)
    (h : ((getStorage a k).run t).run = .ok (value, next)) :
    value = (t.view σ).storageAt a k ∧ next = markStorageRead t a k := by
  rw [viewStorage, blockViewStorage]
  cases wt : writtenSlot? t.rev.storageWrites a k with
  | some v =>
    rw [getStorage_of_tx_slot t a k v wt] at h
    exact pureSuccess t a k v value next h
  | none =>
    by_cases ct : a ∈ t.rev.storageClears
    · rw [getStorage_of_tx_clear t a k wt ct] at h
      simp only [ct, ite_true]
      exact pureSuccess t a k U256.zero value next h
    · simp only [ct, ite_false]
      cases wb : writtenSlot? t.block.storageWrites a k with
      | some v =>
        rw [getStorage_of_block_slot t a k v wt ct wb] at h
        exact pureSuccess t a k v value next h
      | none =>
        by_cases cb : a ∈ t.block.storageClears
        · rw [getStorage_of_block_clear t a k wt ct wb cb] at h
          simp only [cb, ite_true]
          exact pureSuccess t a k U256.zero value next h
        · rw [getStorage_of_provider t a k wt ct wb cb] at h
          simp only [cb, ite_false]
          change (match t.block.preState.getStorage a k with
            | .ok v => .ok (v, markStorageRead t a k)
            | .error e => .error (StateError.witness e)) =
            (Except.ok (value, next) : Except StateError (U256 × TxState Id)) at h
          cases answer : t.block.preState.getStorage a k with
          | error error => simp [answer] at h
          | ok v =>
            rw [answer] at h
            obtain ⟨hv, hn⟩ := pureSuccess t a k v value next h
            exact ⟨hv.trans (agreement.2.1 a k v answer).symm, hn⟩

private theorem markedStorageRead_mem {m : Type → Type} (t : TxState m) (a : Address) (k : Bytes32)
    (pair : Address × Bytes32) :
    pair ∈ (markStorageRead t a k).obs.storageReads ↔ pair = (a, k) ∨ pair ∈ t.obs.storageReads := by
  rw [markStorageRead, Std.HashSet.mem_insert]
  simp only [beq_iff_eq, @eq_comm _ (a, k) pair]

private theorem getStorage_error (t : TxState Id) (a : Address) (k : Bytes32)
    (txMiss : writtenSlot? t.rev.storageWrites a k = none) (txKeep : a ∉ t.rev.storageClears)
    (blockMiss : writtenSlot? t.block.storageWrites a k = none)
    (blockKeep : a ∉ t.block.storageClears) (error : WitnessError)
    (answer : t.block.preState.getStorage a k = .error error) :
    ((getStorage a k).run t).run = .error (.witness error) := by
  rw [getStorage_of_provider t a k txMiss txKeep blockMiss blockKeep]
  change (match t.block.preState.getStorage a k with
    | .ok v => Except.ok (v, markStorageRead t a k)
    | .error e => Except.error (StateError.witness e)) = _
  rw [answer]

private theorem getStorage_frame (t next : TxState Id) (a : Address) (k : Bytes32)
    (value : U256) (h : ((getStorage a k).run t).run = .ok (value, next)) :
    next = markStorageRead t a k := by
  simp only [getStorage, StateT.run, ExceptT.run, ExceptT.mk, pure, bind] at h
  repeat' first | split at h | exact (pureSuccess t a k _ value next h).2 | contradiction

private theorem getStorage_mem (t next : TxState Id) (a : Address) (k : Bytes32)
    (value : U256) (h : ((getStorage a k).run t).run = .ok (value, next))
    (pair : Address × Bytes32) :
    pair ∈ next.obs.storageReads ↔ pair = (a, k) ∨ pair ∈ t.obs.storageReads := by
  rw [getStorage_frame t next a k value h, markedStorageRead_mem]

end STFSpec.State
