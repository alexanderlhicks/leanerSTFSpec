/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.TransactionView

/-!
# Ordered transaction account writes

Library `EthState`: the complete account option and its first-write position.
Spec guidance: `STFSpec/informal/modules/EthState.md` R14/§7.1/§7.5.
-/

namespace STFSpec.State

open Base

/-- Store an account option and record its address in the transaction write order.
Setting `none` stores a tombstone. Implements EELS
`src/ethereum/forks/amsterdam/state_tracker.py:434–454`, with B1 order metadata.
The action does not read the account or change its storage. -/
def setAccount {m : Type → Type} [Monad m] (a : Address) (account : Option Account) :
    StateM m Unit := fun t ↦ ExceptT.mk <| pure (.ok ((), { t with
      rev.accountWrites := t.rev.accountWrites.insert a account
      rev.accountOrder := t.rev.accountOrder.record a }))

private theorem setAccount_run {m : Type → Type} [Monad m]
    (t : TxState m) (a : Address) (account : Option Account) :
    ((setAccount a account).run t).run = pure (.ok ((), { t with
      rev.accountWrites := t.rev.accountWrites.insert a account
      rev.accountOrder := t.rev.accountOrder.record a })) := rfl

private theorem setAccount_success (t next : TxState Id) (a : Address)
    (account : Option Account)
    (h : ((setAccount a account).run t).run = .ok ((), next)) :
    next = { t with
      rev.accountWrites := t.rev.accountWrites.insert a account
      rev.accountOrder := t.rev.accountOrder.record a } :=
  (congrArg Prod.snd (Except.ok.inj h)).symm

private theorem setAccount_frames (t next : TxState Id) (a : Address)
    (account : Option Account)
    (h : ((setAccount a account).run t).run = .ok ((), next)) :
    next.block = t.block ∧ next.obs = t.obs ∧
      next.rev.storageWrites = t.rev.storageWrites ∧
      next.rev.storageAddressOrder = t.rev.storageAddressOrder ∧
      next.rev.storageSlotOrder = t.rev.storageSlotOrder ∧
      next.rev.codeWrites = t.rev.codeWrites ∧
      next.rev.storageClears = t.rev.storageClears ∧
      next.rev.transient = t.rev.transient := by
  rw [setAccount_success t next a account h]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem setAccount_lookup (t next : TxState Id) (a b : Address)
    (account : Option Account)
    (h : ((setAccount a account).run t).run = .ok ((), next)) :
    next.rev.accountWrites[b]? = if a = b then some account else t.rev.accountWrites[b]? := by
  rw [setAccount_success t next a account h]
  simp [Std.ExtTreeMap.getElem?_insert]

private theorem setAccount_order_of_present (t next : TxState Id) (a : Address)
    (account : Option Account) (p : Nat)
    (h : ((setAccount a account).run t).run = .ok ((), next))
    (hp : t.rev.accountOrder.positions[a]? = some p) :
    next.rev.accountOrder = t.rev.accountOrder := by
  rw [setAccount_success t next a account h]
  exact t.rev.accountOrder.record_of_present a p hp

private theorem setAccount_order_wf (t next : TxState Id) (a : Address)
    (account : Option Account)
    (h : ((setAccount a account).run t).run = .ok ((), next))
    (hwf : t.rev.accountOrder.WF) : next.rev.accountOrder.WF := by
  rw [setAccount_success t next a account h]
  exact t.rev.accountOrder.wf_record a hwf

private theorem setAccount_order_agrees (t next : TxState Id) (a : Address)
    (account : Option Account)
    (h : ((setAccount a account).run t).run = .ok ((), next))
    (ha : t.rev.accountOrder.Agrees t.rev.accountWrites) :
    next.rev.accountOrder.Agrees next.rev.accountWrites := by
  rw [setAccount_success t next a account h]
  exact t.rev.accountOrder.agrees_record_insert t.rev.accountWrites a account ha

private theorem setAccount_order_list (t next : TxState Id) (a : Address)
    (account : Option Account)
    (h : ((setAccount a account).run t).run = .ok ((), next))
    (hwf : t.rev.accountOrder.WF) (ha : t.rev.accountOrder.Agrees t.rev.accountWrites) :
    next.rev.accountOrder.toList =
      if t.rev.accountWrites[a]?.isSome then t.rev.accountOrder.toList
      else t.rev.accountOrder.toList ++ [a] := by
  rw [setAccount_success t next a account h]
  exact (t.rev.accountOrder.toList_record a hwf).trans (by rw [ha a])

private theorem view_setAccount (σ₀ : MathState) (t next : TxState Id)
    (a : Address) (account : Option Account)
    (h : ((setAccount a account).run t).run = .ok ((), next)) :
    next.view σ₀ = { t.view σ₀ with accounts :=
      match account with
      | none => (t.view σ₀).accounts.erase a
      | some value => (t.view σ₀).accounts.insert a value } := by
  have hnext := setAccount_success t next a account h
  subst next
  refine MathState.ext_lookup (fun b ↦ ?_) (fun b ↦ ?_) (fun k ↦ ?_)
  · change (({ t with
        rev.accountWrites := t.rev.accountWrites.insert a account
        rev.accountOrder := t.rev.accountOrder.record a } : TxState Id).view σ₀).account? b = _
    rw [TxState.view_account?_eq]
    simp only [Std.ExtTreeMap.getElem?_insert, Std.compare_eq_iff_eq]
    by_cases hab : a = b <;> cases account <;>
      simp [hab, ← MathState.account?_eq_lookup, TxState.view_account?_eq,
        Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_erase]
  · rw [TxState.view, TxState.view, MathState.apply_storage_lookup, MathState.apply_storage_lookup]
    rfl
  · rw [TxState.view, TxState.view, MathState.apply_code_lookup, MathState.apply_code_lookup]
    rfl

end STFSpec.State
