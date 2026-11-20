/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Runner

/-!
# Public checked VM adapter clients

Library `EthConformance`. Private clients check exact F14 signatures, complete
routing, world retention/erasure and base effects through the public Runner facade.
The supplied bind/pure equation also holds for a deliberately nonlawful Monad.
Spec guidance: `STFSpec/informal/modules/EthVmRunner.md` §§3/4/5/7.
-/

namespace STFSpec.Conformance.Vm.Runner.RunCheckedCallerProofs
open STFSpec.State STFSpec.Vm.Core STFSpec.Vm.Runner

private def aliasSignature : (Type → Type) → Type → Type := RunM

private theorem alias_unfolding (m : Type → Type) :
    RunM m = ExceptT InternalError (VmM m) := rfl

private def contravariantAlias {α : Type} :
    RunM (fun β ↦ β → Nat) α → VmWorld (fun β ↦ β → Nat) →
      (Except VmFault (Except InternalError α × VmWorld (fun β ↦ β → Nat)) → Nat) :=
  fun action world ↦ (action.run.run world).run

private def adapterSignature {m : Type → Type} [Monad m] {α : Type} :
    VmM m (Except InternalError α) → VmWorld m →
      m (CheckedResult VmFault (α × VmWorld m)) := runVmChecked

private theorem public_equation {m : Type → Type} [Monad m] {α : Type}
    (action : VmM m (Except InternalError α)) (world : VmWorld m) :
    runVmChecked action world = (do
      match ← (action.run world).run with
      | .error vf => pure (.ok (.error vf))
      | .ok (.error i, _) => pure (.error i)
      | .ok (.ok a, after) => pure (.ok (.ok (a, after)))) :=
  runVmChecked_eq action world

private theorem id_fault {α : Type} (initial after : VmWorld Id) (fault : VmFault) :
    runVmChecked (do
      set after
      throw fault : VmM Id (Except InternalError α)) initial = .ok (.error fault) := by
  simp only [runVmChecked_eq]
  rfl

private theorem id_nested_state_fault (initial after : VmWorld Id) (error : StateError) :
    runVmChecked (do
      set after
      throw (VmFault.state error) : VmM Id (Except InternalError Unit)) initial =
      .ok (.error (.state error)) := by
  simp only [runVmChecked_eq]
  rfl

private theorem id_nested_witness_fault (initial after : VmWorld Id) (error : WitnessError) :
    runVmChecked (do
      set after
      throw (VmFault.state (.witness error)) : VmM Id (Except InternalError Unit)) initial =
      .ok (.error (.state (.witness error))) := by
  simp only [runVmChecked_eq]
  rfl

private theorem id_internal {α : Type} (initial after : VmWorld Id) (error : InternalError) :
    runVmChecked (do
      set after
      pure (.error error) : VmM Id (Except InternalError α)) initial = .error error := by
  simp only [runVmChecked_eq]
  rfl

private theorem id_internal_world_erasure {α : Type} (initial left right : VmWorld Id)
    (error : InternalError) :
    runVmChecked (do
      set left
      pure (.error error) : VmM Id (Except InternalError α)) initial =
    runVmChecked (do
      set right
      pure (.error error) : VmM Id (Except InternalError α)) initial := by
  simp only [runVmChecked_eq]
  rfl

private theorem id_updated_success {α : Type} (initial after : VmWorld Id) (value : α) :
    runVmChecked (do
      set after
      pure (.ok value) : VmM Id (Except InternalError α)) initial =
      .ok (.ok (value, after)) := by
  simp only [runVmChecked_eq]
  rfl

private theorem id_changed_success {α : Type} (initial after : VmWorld Id) (value : α)
    (changed : after ≠ initial) :
    runVmChecked (do
      set after
      pure (.ok value) : VmM Id (Except InternalError α)) initial ≠
      .ok (.ok (value, initial)) := by
  intro equal
  rw [runVmChecked_eq] at equal
  exact changed (congrArg Prod.snd (Except.ok.inj (Except.ok.inj equal)))

private abbrev Logged := StateT (List Nat) Id

private def logEvent (event : Nat) : VmM Logged Unit := fun world ↦ ExceptT.mk do
  modify (fun events ↦ events ++ [event])
  pure (.ok ((), world))

-- These controls execute actual VM binds and world changes over a lawful effectful base.
private theorem effect_order {α : Type} (initial after : VmWorld Logged) (value : α)
    (events : List Nat) :
    (runVmChecked (do
      logEvent 11
      set after
      logEvent 23
      pure (.ok value)) initial).run events =
      (.ok (.ok (value, after)), events ++ [11, 23]) := by
  rw [runVmChecked_eq]
  change ((.ok (.ok (value, after)) : CheckedResult VmFault (α × VmWorld Logged)),
    (events ++ [11]) ++ [23]) = _
  rw [List.append_assoc]
  rfl

private theorem effect_fault (initial after : VmWorld Logged) (fault : VmFault)
    (events : List Nat) :
    (runVmChecked (do
      logEvent 11
      set after
      throw fault
      logEvent 23
      pure (.ok ())) initial).run events =
      (.ok (.error fault), events ++ [11]) := by
  simp only [runVmChecked_eq]
  rfl

private theorem effect_internal (initial after : VmWorld Logged) (error : InternalError)
    (events : List Nat) :
    (runVmChecked (do
      logEvent 11
      set after
      pure (.error error) : VmM Logged (Except InternalError Unit)) initial).run events =
      (.error error, events ++ [11]) := by
  simp only [runVmChecked_eq]
  rfl

private theorem base_no_result {α : Type} (world : VmWorld Option) :
    runVmChecked (fun _ ↦ ExceptT.mk none : VmM Option (Except InternalError α)) world =
      none := by
  simp only [runVmChecked_eq]
  rfl

private theorem base_failure {α : Type} (world : VmWorld (Except (String × List Nat)))
    (failure : String × List Nat) :
    runVmChecked (fun _ ↦ ExceptT.mk (.error failure) :
      VmM (Except (String × List Nat)) (Except InternalError α)) world =
      .error failure := by
  simp only [runVmChecked_eq]
  rfl

-- An incoherent map must not replace the literal supplied bind and pure.
private structure Marked (α : Type) where
  value : α
  marks : Nat

private instance : Monad Marked where
  pure value := ⟨value, 1⟩
  bind action next :=
    let result := next action.value
    ⟨result.value, action.marks + result.marks + 10⟩
  map f action := ⟨f action.value, action.marks + 100⟩

private theorem nonlawful_literal {α : Type} (initial after : VmWorld Marked) (value : α) :
    runVmChecked (fun _ ↦ ExceptT.mk ⟨.ok (.ok value, after), 7⟩) initial =
      (⟨.ok (.ok (value, after)), 18⟩ : Marked _) := by
  simp only [runVmChecked_eq]
  rfl

private theorem nonlawful_map_differs {α : Type} (initial after : VmWorld Marked)
    (value : α) :
    runVmChecked (fun _ ↦ ExceptT.mk ⟨.ok (.ok value, after), 7⟩) initial ≠
      Functor.map (fun result : Except VmFault (Except InternalError α × VmWorld Marked) ↦
        match result with
        | .error vf => .ok (.error vf)
        | .ok (.error i, _) => .error i
        | .ok (.ok a, world) => .ok (.ok (a, world)))
        (⟨.ok (.ok value, after), 7⟩ : Marked _) := by
  intro equal
  rw [runVmChecked_eq] at equal
  have impossible : (18 : Nat) = 107 := congrArg Marked.marks equal
  cases impossible

end STFSpec.Conformance.Vm.Runner.RunCheckedCallerProofs
