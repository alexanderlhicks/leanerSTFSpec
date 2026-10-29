/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Action-factorization clients

Library `EthConformance`. Private clients use the public Core facade and exact Id law.
The local six-field success relation tests the guided consequence without implementing
`MeterOk` or the precompile carrier. State and Except witnesses are local examples;
the nonlawful `CountMap` control shows that a Monad need not admit even safe pure actions.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Vm.Core.SatisfiesMCallerProofs
open STFSpec.Vm.Core

private theorem id_elimination {α : Type} (P : α → Prop) (x : Id α)
    (h : SatisfiesM (m := Id) P x) : P x :=
  (satisfiesM_id_iff P x).mp h

private theorem id_introduction {α : Type} (P : α → Prop) (x : Id α)
    (h : P x) : SatisfiesM (m := Id) P x :=
  (satisfiesM_id_iff P x).mpr h

private theorem true_id : SatisfiesM (m := Id) (fun n : Nat => n = 7) (7 : Id Nat) :=
  (satisfiesM_id_iff _ _).mpr rfl

private theorem false_id : ¬ SatisfiesM (m := Id) (fun n : Nat => n = 8) (7 : Id Nat) := by
  intro h
  have := (satisfiesM_id_iff _ _).mp h
  contradiction

-- The complete guided successful relation, on arbitrary raw meters.
private def successRelation (g g' : GasMeter) : Prop :=
  g'.gasLeft ≤ g.gasLeft ∧ { g' with gasLeft := g.gasLeft } = g

private theorem id_success_fields (g : GasMeter) (x : Id GasMeter)
    (h : SatisfiesM (m := Id) (successRelation g) x) :
    x.gasLeft ≤ g.gasLeft ∧ x.stateGasLeft = g.stateGasLeft ∧
      x.stateGasBaseline = g.stateGasBaseline ∧ x.refundCounter = g.refundCounter ∧
      x.stateGasSpilled = g.stateGasSpilled ∧
      x.stateGasCommittedSpill = g.stateGasCommittedSpill := by
  obtain ⟨hle, heq⟩ := (satisfiesM_id_iff _ _).mp h
  have hState := congrArg GasMeter.stateGasLeft heq
  have hBaseline := congrArg GasMeter.stateGasBaseline heq
  have hRefund := congrArg GasMeter.refundCounter heq
  have hSpill := congrArg GasMeter.stateGasSpilled heq
  have hCommitted := congrArg GasMeter.stateGasCommittedSpill heq
  exact ⟨hle, hState, hBaseline, hRefund, hSpill, hCommitted⟩

private theorem charged_id (g : GasMeter) (cost : Nat) :
    SatisfiesM (m := Id) (successRelation g)
      ({ g with gasLeft := g.gasLeft - cost } : Id GasMeter) :=
  (satisfiesM_id_iff _ _).mpr ⟨Nat.sub_le _ _, rfl⟩

private theorem spill_change_rejected (g : GasMeter) :
    ¬ SatisfiesM (m := Id) (successRelation g)
      ({ g with stateGasCommittedSpill := g.stateGasCommittedSpill + 1 } : Id GasMeter) := by
  intro h
  have heq := ((satisfiesM_id_iff _ _).mp h).2
  have hSpill := congrArg GasMeter.stateGasCommittedSpill heq
  change g.stateGasCommittedSpill + 1 = g.stateGasCommittedSpill at hSpill
  omega

private def traceAction : StateM Nat Nat := fun s => (7, s + 1)

private theorem state_witness : SatisfiesM (fun n => n = 7) traceAction := by
  refine ⟨(fun s => (⟨7, rfl⟩, s + 1)), ?_⟩
  rfl

private theorem state_trace (s : Nat) : traceAction.run s = (7, s + 1) := rfl

private theorem except_error_witness :
    SatisfiesM (fun _ : Nat => False) (Except.error "query" : Except String Nat) := by
  exact ⟨Except.error "query", rfl⟩

-- Ordinary logged bind, but map adds a tick. Monad carries no law forcing agreement.
private structure CountMap (α : Type) where
  ticks : Nat
  value : α

private instance : Monad CountMap where
  pure a := ⟨0, a⟩
  bind x f := let y := f x.value; ⟨x.ticks + y.ticks, y.value⟩
  map f x := ⟨x.ticks + 1, f x.value⟩

private theorem countMap_safe_pure_rejected :
    ¬ SatisfiesM (fun n : Nat => n = 7) (pure 7 : CountMap Nat) := by
  rintro ⟨y, h⟩
  have hticks := congrArg CountMap.ticks h
  change y.ticks + 1 = 0 at hticks
  omega

private theorem countMap_map_pure_fails :
    Subtype.val <$> (pure (⟨7, rfl⟩ : {n : Nat // n = 7}) : CountMap _) ≠
      (pure 7 : CountMap Nat) := by
  intro h
  have hticks := congrArg CountMap.ticks h
  contradiction

private theorem countMap_map_composition_fails :
    ((fun n : Nat => n + 1) <$> ((fun n : Nat => n + 2) <$> (pure 7 : CountMap Nat))) ≠
      ((fun n : Nat => (n + 2) + 1) <$> (pure 7 : CountMap Nat)) := by
  intro h
  have hticks := congrArg CountMap.ticks h
  contradiction

end STFSpec.Conformance.Vm.Core.SatisfiesMCallerProofs
