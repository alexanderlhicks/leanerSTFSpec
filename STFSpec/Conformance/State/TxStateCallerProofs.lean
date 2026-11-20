/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Raw transaction-state clients

Library `EthConformance`: private facade clients check complete raw fields and the
exact state/error transformer order. Arbitrary provider values need no class premise;
the sequencing controls use `Id`. These clients establish no tracker or source refinement.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/4/5/7/10.
-/

namespace STFSpec.Conformance.State.TxStateCallerProofs

open STFSpec.State

variable {m : Type → Type} {α : Type}

private def exact_type : (Type → Type) → Type := @TxState

private def exact_constructor : BlockState m → TxRevertible → TxObs → TxState m :=
  @TxState.mk m

private def exact_block : TxState m → BlockState m := @TxState.block m

private def exact_rev : TxState m → TxRevertible := @TxState.rev m

private def exact_obs : TxState m → TxObs := @TxState.obs m

private def exact_alias : (Type → Type) → Type → Type := @STFSpec.State.StateM

private theorem supplied_constructor (block : BlockState m) (rev : TxRevertible) (obs : TxObs) :
    let t := TxState.mk block rev obs
    (t.block, t.rev, t.obs) = (block, rev, obs) := rfl

private theorem reconstruct (t : TxState m) : TxState.mk t.block t.rev t.obs = t := rfl

private theorem whole_components (t u : TxState m)
    (hBlock : t.block = u.block) (hRev : t.rev = u.rev) (hObs : t.obs = u.obs) : t = u := by
  cases t
  cases u
  cases hBlock
  cases hRev
  cases hObs
  rfl

private theorem replace_block (t : TxState m) (block : BlockState m) :
    ({ t with block := block } : TxState m) = TxState.mk block t.rev t.obs := rfl

private theorem replace_rev (t : TxState m) (rev : TxRevertible) :
    ({ t with rev := rev } : TxState m) = TxState.mk t.block rev t.obs := rfl

private theorem replace_obs (t : TxState m) (obs : TxObs) :
    ({ t with obs := obs } : TxState m) = TxState.mk t.block t.rev obs := rfl

private theorem replace_block_rev_commute (t : TxState m) (block : BlockState m)
    (rev : TxRevertible) :
    { { t with block := block } with rev := rev } =
      ({ { t with rev := rev } with block := block } : TxState m) := rfl

private theorem replace_block_obs_commute (t : TxState m) (block : BlockState m) (obs : TxObs) :
    { { t with block := block } with obs := obs } =
      ({ { t with obs := obs } with block := block } : TxState m) := rfl

private theorem replace_rev_obs_commute (t : TxState m) (rev : TxRevertible) (obs : TxObs) :
    { { t with rev := rev } with obs := obs } =
      ({ { t with obs := obs } with rev := rev } : TxState m) := rfl

private def contravariant_constructor :
    BlockState (fun β ↦ β → Nat) → TxRevertible → TxObs → TxState (fun β ↦ β → Nat) :=
  TxState.mk

private theorem alias_shape :
    STFSpec.State.StateM m α = (TxState m → m (Except StateError (α × TxState m))) := rfl

private def exact_run :
    STFSpec.State.StateM m α → TxState m → m (Except StateError (α × TxState m)) :=
  fun action t ↦ (action.run t).run

private theorem run_preserves_action (action : m (Except StateError (α × TxState m)))
    (t : TxState m) :
    (StateT.run (σ := TxState m) (m := ExceptT StateError m)
      ((fun _ ↦ action) : STFSpec.State.StateM m α) t).run = action := rfl

private def contravariant_run :
    STFSpec.State.StateM (fun β ↦ β → Nat) α →
      TxState (fun β ↦ β → Nat) → (Except StateError
        (α × TxState (fun β ↦ β → Nat)) → Nat) := exact_run

private theorem pure_run (value : α) (t : TxState Id) :
    ((pure value : STFSpec.State.StateM Id α).run t).run = .ok (value, t) := rfl

private theorem get_run (t : TxState Id) :
    ((get : STFSpec.State.StateM Id (TxState Id)).run t).run = .ok (t, t) := rfl

private theorem put_get_run (initial next : TxState Id) :
    ((do
      set next
      get : STFSpec.State.StateM Id (TxState Id)).run initial).run = .ok (next, next) := rfl

private theorem replace_and_read_run (initial : TxState Id) (block : BlockState Id)
    (rev : TxRevertible) (obs : TxObs) :
    ((do
      set { initial with block := block, rev := rev, obs := obs }
      let t ← get
      pure (t.block, t.rev, t.obs) :
        STFSpec.State.StateM Id (BlockState Id × TxRevertible × TxObs)).run initial).run =
      .ok ((block, rev, obs), TxState.mk block rev obs) := rfl

private theorem error_run (initial : TxState Id) (error : StateError) :
    ((throw error : STFSpec.State.StateM Id α).run initial).run = .error error := rfl

private theorem put_then_error_run (initial next : TxState Id) (error : StateError) (value : α) :
    ((do
      set next
      throw error
      pure value : STFSpec.State.StateM Id α).run initial).run = .error error := rfl

private theorem witness_error_run (initial next : TxState Id) (error : WitnessError) :
    ((do
      set next
      throw (StateError.witness error) : STFSpec.State.StateM Id Unit).run initial).run =
      .error (.witness error) := rfl

end STFSpec.Conformance.State.TxStateCallerProofs
