/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.TxState

/-!
# Code reads

Library `EthState`. Read by hash and record only provider lookups.
Spec guidance: `STFSpec/informal/modules/EthState.md` §7.1.
-/

namespace STFSpec.State

open Base

/-- Read code by hash in the order of EELS
`src/ethereum/forks/amsterdam/state_tracker.py:228–259` at the pin.
The supplied reserved hash and both overlay hits bypass the provider.
On a miss, mark the hash and call the provider even if the hash was already marked. -/
def getCode {m : Type → Type} [Monad m] (h : Hash32) : StateM m ByteArray :=
  fun t ↦ ExceptT.mk <|
    if h = t.block.consts.emptyCodeHash then
      pure (.ok (ByteArray.empty, t))
    else
      match t.rev.codeWrites[h]? with
      | some code => pure (.ok (code, t))
      | none =>
        match t.block.codeWrites[h]? with
        | some code => pure (.ok (code, t))
        | none => do
          let next := { t with obs.codeReads := t.obs.codeReads.insert h }
          match ← t.block.preState.getCode h with
          | .ok code => pure (.ok (code, next))
          | .error error => pure (.error (.witness error))

/-- The complete action uses only `Monad`, with no equations about its effects. -/
theorem getCode_action {m : Type → Type} [Monad m]
    (t : TxState m) (h : Hash32) :
    ((getCode h).run t).run =
      (if h = t.block.consts.emptyCodeHash then
        pure (.ok (ByteArray.empty, t))
      else
        match t.rev.codeWrites[h]? with
        | some code => pure (.ok (code, t))
        | none =>
          match t.block.codeWrites[h]? with
          | some code => pure (.ok (code, t))
          | none => do
            let next := { t with obs.codeReads := t.obs.codeReads.insert h }
            match ← t.block.preState.getCode h with
            | .ok code => pure (.ok (code, next))
            | .error error => pure (.error (.witness error))) := rfl

/-- A provider failure at `Id` returns the exact wrapped error. -/
theorem getCode_error (t : TxState Id) (h : Hash32)
    (error : WitnessError) (hh : h ≠ t.block.consts.emptyCodeHash)
    (ht : t.rev.codeWrites[h]? = none) (hb : t.block.codeWrites[h]? = none)
    (hp : t.block.preState.getCode h = .error error) :
    ((getCode h).run t).run = .error (.witness error) := by
  rw [getCode_action, ite_eq_right hh, ht, hb]
  change (match t.block.preState.getCode h with | .ok _ => _ | .error _ => _) = _
  rw [hp]
  rfl

private theorem success_state (t : TxState Id) (h : Hash32)
    (code : ByteArray) (next : TxState Id)
    (hs : ((getCode h).run t).run = .ok (code, next)) :
    next = if h ≠ t.block.consts.emptyCodeHash ∧
        t.rev.codeWrites[h]? = none ∧ t.block.codeWrites[h]? = none then
      { t with obs.codeReads := t.obs.codeReads.insert h }
    else t := by
  rw [getCode_action] at hs
  by_cases hh : h = t.block.consts.emptyCodeHash
  · rw [ite_eq_left hh] at hs
    rw [ite_eq_right (fun miss ↦ miss.1 hh)]
    exact (Prod.mk.inj (Except.ok.inj hs)).2.symm
  · rw [ite_eq_right hh] at hs
    cases ht : t.rev.codeWrites[h]? with
    | some value =>
      rw [ht] at hs
      rw [ite_eq_right (fun miss ↦ Option.some_ne_none _ miss.2.1)]
      exact (Prod.mk.inj (Except.ok.inj hs)).2.symm
    | none =>
      rw [ht] at hs
      cases hb : t.block.codeWrites[h]? with
      | some value =>
        rw [hb] at hs
        rw [ite_eq_right (fun miss ↦ Option.some_ne_none _ miss.2.2)]
        exact (Prod.mk.inj (Except.ok.inj hs)).2.symm
      | none =>
        rw [hb] at hs
        change (match t.block.preState.getCode h with | .ok _ => _ | .error _ => _) = _ at hs
        cases hp : t.block.preState.getCode h with
        | ok value =>
          rw [hp] at hs
          rw [ite_eq_left ⟨hh, rfl, rfl⟩]
          exact (Prod.mk.inj (Except.ok.inj hs)).2.symm
        | error error =>
          rw [hp] at hs
          contradiction

/-- A successful read at `Id` preserves the complete state outside code reads. -/
theorem getCode_frames (t : TxState Id) (h : Hash32)
    (code : ByteArray) (next : TxState Id)
    (hs : ((getCode h).run t).run = .ok (code, next)) :
    next.block = t.block ∧ next.rev = t.rev ∧
      next.obs.accountReads = t.obs.accountReads ∧
      next.obs.storageReads = t.obs.storageReads ∧
      next.obs.createdAccounts = t.obs.createdAccounts := by
  rw [success_state t h code next hs]
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A successful read at `Id` adds membership only for a nonreserved provider miss
and retains every old member. -/
theorem getCode_mem (t : TxState Id) (h k : Hash32)
    (code : ByteArray) (next : TxState Id)
    (hs : ((getCode h).run t).run = .ok (code, next)) :
    k ∈ next.obs.codeReads ↔ k ∈ t.obs.codeReads ∨
      (k = h ∧ h ≠ t.block.consts.emptyCodeHash ∧
        t.rev.codeWrites[h]? = none ∧ t.block.codeWrites[h]? = none) := by
  rw [success_state t h code next hs]
  split
  · rename_i miss
    change k ∈ t.obs.codeReads.insert h ↔ _
    rw [Std.HashSet.mem_insert]
    rw [beq_iff_eq]
    exact ⟨fun found ↦ found.elim (fun eq ↦ Or.inr ⟨eq.symm, miss⟩) Or.inl,
      fun found ↦ found.elim Or.inr (fun hit ↦ Or.inl hit.1.symm)⟩
  · rename_i bypass
    exact ⟨Or.inl, fun found ↦ found.elim id (fun hit ↦ (bypass hit.2).elim)⟩

end STFSpec.State
