/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Raw VM world clients

Library `EthConformance`: private public-facade clients check complete transaction
retention and exact state/error wiring, including a non-Monad type constructor.
The sequencing controls use `Id`; they claim no rollback of underlying effects.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/5/7/10.
-/

namespace STFSpec.Conformance.Vm.Core.WorldCallerProofs

open STFSpec.State STFSpec.Vm.Core

variable {m : Type → Type} {α : Type}

private def exact_type : (Type → Type) → Type := @VmWorld

private def exact_constructor : TxState m → VmWorld m := @VmWorld.mk m

private def exact_projection : VmWorld m → TxState m := @VmWorld.tx m

private def exact_alias : (Type → Type) → Type → Type := @VmM

private theorem whole_transaction (tx : TxState m) : (VmWorld.mk tx).tx = tx := rfl

private theorem reconstruct (w : VmWorld m) : VmWorld.mk w.tx = w := rfl

private theorem whole_world (w v : VmWorld m) (h : w.tx = v.tx) : w = v := by
  cases w
  cases v
  cases h
  rfl

private theorem replace_transaction (w : VmWorld m) (tx : TxState m) :
    ({ w with tx := tx } : VmWorld m) = VmWorld.mk tx := rfl

private def contravariant_constructor :
    TxState (fun β ↦ β → Nat) → VmWorld (fun β ↦ β → Nat) := VmWorld.mk

private theorem alias_shape :
    VmM m α = (VmWorld m → m (Except VmFault (α × VmWorld m))) := rfl

private def exact_run : VmM m α → VmWorld m → m (Except VmFault (α × VmWorld m)) :=
  fun action w ↦ (action.run w).run

private theorem run_preserves_action (action : m (Except VmFault (α × VmWorld m)))
    (w : VmWorld m) :
    (StateT.run (σ := VmWorld m) (m := ExceptT VmFault m)
      ((fun _ ↦ action) : VmM m α) w).run = action := rfl

private def contravariant_run :
    VmM (fun β ↦ β → Nat) α → VmWorld (fun β ↦ β → Nat) →
      (Except VmFault (α × VmWorld (fun β ↦ β → Nat)) → Nat) := exact_run

private theorem pure_run (value : α) (w : VmWorld Id) :
    ((pure value : VmM Id α).run w).run = .ok (value, w) := rfl

private theorem get_run (w : VmWorld Id) :
    ((get : VmM Id (VmWorld Id)).run w).run = .ok (w, w) := rfl

private theorem put_get_run (initial next : VmWorld Id) :
    ((do
      set next
      get : VmM Id (VmWorld Id)).run initial).run = .ok (next, next) := rfl

private theorem replace_and_read_run (initial : VmWorld Id) (tx : TxState Id) :
    ((do
      set { initial with tx := tx }
      let w ← get
      pure w.tx : VmM Id (TxState Id)).run initial).run = .ok (tx, VmWorld.mk tx) := rfl

private theorem error_run (initial : VmWorld Id) (error : VmFault) :
    ((throw error : VmM Id α).run initial).run = .error error := rfl

private theorem put_then_error_run (initial next : VmWorld Id) (error : VmFault) (value : α) :
    ((do
      set next
      throw error
      pure value : VmM Id α).run initial).run = .error error := rfl

private theorem nested_witness_error_run (initial next : VmWorld Id) (error : WitnessError) :
    ((do
      set next
      throw (VmFault.state (.witness error)) : VmM Id Unit).run initial).run =
      .error (.state (.witness error)) := rfl

end STFSpec.Conformance.Vm.Core.WorldCallerProofs
