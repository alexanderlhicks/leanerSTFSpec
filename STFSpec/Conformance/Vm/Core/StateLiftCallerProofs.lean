/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# State lift clients

Library `EthConformance`: private facade clients retain complete arbitrary values,
transactions and errors. Concrete lawful traces check ordered underlying effects;
an underlying failure stays outside the VM error layer. These are Lean-only checks.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/5/7/10.
-/

namespace STFSpec.Conformance.Vm.Core.StateLiftCallerProofs

open STFSpec.State STFSpec.Vm.Core

variable {m : Type → Type} {α : Type}

private def exact_type [Monad m] : StateM m α → VmM m α := liftState

private theorem literal_run [Monad m] (action : StateM m α) (world : VmWorld m) :
    ((liftState action).run world).run =
      ((action.run world.tx).run >>= fun result ↦
        pure (match result with
          | .ok (value, tx) => .ok (value, { world with tx := tx })
          | .error error => .error (.state error))) := liftState_run action world

private theorem lawful_result [Monad m] [LawfulMonad m] (world : VmWorld m)
    (value : α) (tx : TxState m) :
    ((liftState (fun _ ↦
      (pure (.ok (value, tx)) : m (Except StateError (α × TxState m))))).run world).run =
      pure (.ok (value, VmWorld.mk tx)) := by
  rw [liftState_run]
  simp only [StateT.run, ExceptT.run, pure_bind]

private theorem whole_result (world : VmWorld Id) (value : α) (tx : TxState Id) :
    ((liftState (fun _ ↦ .ok (value, tx))).run world).run =
      .ok (value, VmWorld.mk tx) := by
  rw [liftState_run]
  rfl

private theorem read (world : VmWorld Id) :
    ((liftState (get : StateM Id (TxState Id))).run world).run =
      .ok (world.tx, world) := by
  rw [liftState_run]
  rfl

private theorem read_replace_read (world : VmWorld Id) (next : TxState Id) :
    ((liftState (do
      let before ← get
      set next
      let after ← get
      pure (before, after) : StateM Id (TxState Id × TxState Id))).run world).run =
      .ok ((world.tx, next), VmWorld.mk next) := by
  rw [liftState_run]
  rfl

private theorem pure_result (world : VmWorld Id) (value : α) :
    ((liftState (pure value : StateM Id α)).run world).run = .ok (value, world) := by
  rw [liftState_run]
  rfl

private theorem whole_error (world : VmWorld Id) (error : StateError) :
    ((liftState (throw error : StateM Id α)).run world).run =
      .error (.state error) := by
  rw [liftState_run]
  rfl

private theorem put_failure_skips (world : VmWorld Id) (next : TxState Id)
    (error : StateError) (continuation : StateM Id α) :
    ((liftState (do
      set next
      throw error
      continuation)).run world).run = .error (.state error) := by
  rw [liftState_run]
  rfl

private abbrev Trace := StateT (List Nat) Id

private def mark (event : Nat) : Trace Unit := modify (· ++ [event])

private theorem ordered_success (world : VmWorld Trace) (next : TxState Trace) (value : α) :
    (((liftState (do
      let before ← get
      liftM (mark 11)
      set next
      liftM (mark 22)
      pure (value, before) : StateM Trace (α × TxState Trace))).run world).run).run [] =
      (.ok ((value, world.tx), VmWorld.mk next), [11, 22]) := by
  rw [liftState_run]
  rfl

private theorem ordered_failure (world : VmWorld Trace) (next : TxState Trace)
    (error : StateError) (value : α) :
    (((do
      let result ← liftState (do
        liftM (mark 11)
        set next
        liftM (mark 22)
        throw error
        liftM (mark 33)
        pure value : StateM Trace α)
      liftM (mark 44)
      pure result : VmM Trace α).run world).run).run [] =
      (.error (.state error), [11, 22]) := by
  let action : StateM Trace α := do
    liftM (mark 11)
    set next
    liftM (mark 22)
    throw error
    liftM (mark 33)
    pure value
  have routed : liftState action =
      (fun _ events ↦
        (.error (.state error), (events ++ [11]) ++ [22]) : VmM Trace α) := by
    funext initial
    change ((liftState action).run initial).run = _
    rw [liftState_run]
    rfl
  rw [routed]
  rfl

private theorem outer_failure (world : VmWorld Option) :
    ((liftState (fun _ ↦ none : StateM Option α)).run world).run = none := by
  rw [liftState_run]
  rfl

end STFSpec.Conformance.Vm.Core.StateLiftCallerProofs
