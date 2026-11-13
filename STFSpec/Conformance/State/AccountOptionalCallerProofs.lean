/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Current optional account read clients

Library `EthConformance`: private clients consume only the public action equations,
model law and framing laws. Whole function retention is ordinary equality at Id;
no arbitrary Monad observer, failed-state projection or rollback is introduced.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/4/7.1.
-/

namespace STFSpec.Conformance.State.AccountOptionalCallerProofs

open STFSpec.State STFSpec.Base

private def exact_type : {m : Type → Type} → [Monad m] →
    Address → STFSpec.State.StateM m (Option Account) := @getAccountOptional

private theorem transaction_suppression {m : Type → Type} [Monad m]
    (t : TxState m) (a : Address) (o : Option Account)
    (h : t.rev.accountWrites[a]? = some o) :
    ((getAccountOptional a).run t).run =
      pure (.ok (o, { t with obs.accountReads := t.obs.accountReads.insert a })) :=
  getAccountOptional_of_tx t a o h

private theorem fall_through {m : Type → Type} [Monad m]
    (t : TxState m) (a : Address) (h : t.rev.accountWrites[a]? = none) :
    ((getAccountOptional a).run t).run =
      ((getPreStateAccountOptional a).run
        { t with obs.accountReads := t.obs.accountReads.insert a }).run :=
  getAccountOptional_of_missing t a h

private theorem complete_retention (t next : TxState Id) (a : Address) (o : Option Account)
    (h : ((getAccountOptional a).run t).run = .ok (o, next)) :
    next.block = t.block ∧ next.rev = t.rev ∧
      next.block.preState = t.block.preState ∧
      next.block.preState.getAccount? = t.block.preState.getAccount? ∧
      next.block.preState.getStorage = t.block.preState.getStorage ∧
      next.block.preState.getCode = t.block.preState.getCode ∧
      next.block.preState.stateRoot = t.block.preState.stateRoot ∧
      next.block.consts = t.block.consts ∧
      next.obs.storageReads = t.obs.storageReads ∧
      next.obs.codeReads = t.obs.codeReads ∧
      next.obs.createdAccounts = t.obs.createdAccounts := by
  obtain ⟨hb, hr, hs, hc, hcreated⟩ := getAccountOptional_frames t a o next h
  exact ⟨hb, hr, congrArg BlockState.preState hb,
    congrArg (fun b ↦ b.preState.getAccount?) hb,
    congrArg (fun b ↦ b.preState.getStorage) hb,
    congrArg (fun b ↦ b.preState.getCode) hb,
    congrArg (fun b ↦ b.preState.stateRoot) hb,
    congrArg BlockState.consts hb, hs, hc, hcreated⟩

private theorem queried_member (t next : TxState Id) (a : Address) (o : Option Account)
    (h : ((getAccountOptional a).run t).run = .ok (o, next)) :
    a ∈ next.obs.accountReads :=
  (getAccountOptional_mem t a a o next h).mpr (Or.inl rfl)

private theorem old_member (t next : TxState Id) (a b : Address) (o : Option Account)
    (h : ((getAccountOptional a).run t).run = .ok (o, next))
    (hb : b ∈ t.obs.accountReads) : b ∈ next.obs.accountReads :=
  (getAccountOptional_mem t a b o next h).mpr (Or.inr hb)

private theorem only_members (t next : TxState Id) (a b : Address) (o : Option Account)
    (h : ((getAccountOptional a).run t).run = .ok (o, next))
    (hb : b ∈ next.obs.accountReads) : b = a ∨ b ∈ t.obs.accountReads :=
  (getAccountOptional_mem t a b o next h).mp hb

private theorem exact_error (t : TxState Id) (a : Address) (e : WitnessError)
    (ht : t.rev.accountWrites[a]? = none)
    (hb : t.block.accountWrites[a]? = none)
    (hp : t.block.preState.getAccount? a = .error e) :
    ((getAccountOptional a).run t).run = .error (.witness e) :=
  getAccountOptional_error t a e ht hb hp

private theorem model_client (t next : TxState Id) (σ₀ : MathState)
    (hwf : MathState.WF σ₀) (hm : ModelsLookups t.block.consts t.block.preState σ₀)
    (a : Address) (o : Option Account)
    (h : ((getAccountOptional a).run t).run = .ok (o, next)) :
    o = (t.view σ₀).account? a :=
  getAccountOptional_model t σ₀ hwf hm a o next h

end STFSpec.Conformance.State.AccountOptionalCallerProofs
