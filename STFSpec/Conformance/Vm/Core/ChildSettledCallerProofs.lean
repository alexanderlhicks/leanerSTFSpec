/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Private child settlement clause clients

Library `EthConformance`. Complete logical and constructive-decision clients use
only the public facade, raw record projections and public rollback equations.
All unused Frame fields remain arbitrary; none of these inputs asserts execution
reachability or supplies the runner's missing non-top committed-spill proof.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/5/7.
-/

namespace STFSpec.Conformance.Vm.Core.ChildSettledCallerProofs
open STFSpec.Vm.Core STFSpec.Base

private def predicateSignature : Frame → Bool → Prop := ChildSettled

private def deciderSignature (f : Frame) (failed : Bool) :
    Decidable (ChildSettled f failed) := instDecidableChildSettled f failed

private def settledDecision (f : Frame) (failed : Bool) : Bool :=
  decide (ChildSettled f failed)

private theorem decision_correct (f : Frame) (failed : Bool) :
    settledDecision f failed = true ↔ ChildSettled f failed := by
  simp only [settledDecision, decide_eq_true_eq]

private theorem all_clauses (f : Frame) (failed : Bool) :
    ChildSettled f failed ↔
      f.gasMeter.stateGasCommittedSpill = 0 ∧
      (if failed then f.gasMeter.stateGasSpilled = 0 ∧
        f.gasMeter.refundCounter = 0 ∧
        f.gasMeter.stateGasLeft = f.gasMeter.stateGasBaseline else True) := by
  rfl

private theorem success_iff (f : Frame) :
    ChildSettled f false ↔ f.gasMeter.stateGasCommittedSpill = 0 := by
  simp only [ChildSettled, Bool.false_eq_true, ↓reduceIte, and_true]

private theorem failure_iff (f : Frame) :
    ChildSettled f true ↔
      f.gasMeter.stateGasCommittedSpill = 0 ∧
      f.gasMeter.stateGasSpilled = 0 ∧ f.gasMeter.refundCounter = 0 ∧
      f.gasMeter.stateGasLeft = f.gasMeter.stateGasBaseline := by
  rfl

private theorem decompose (f : Frame) (failed : Bool) (h : ChildSettled f failed) :
    f.gasMeter.stateGasCommittedSpill = 0 ∧
      (failed = true → f.gasMeter.stateGasSpilled = 0 ∧
        f.gasMeter.refundCounter = 0 ∧
        f.gasMeter.stateGasLeft = f.gasMeter.stateGasBaseline) := by
  refine ⟨h.1, ?_⟩
  intro hf
  subst failed
  exact h.2

private theorem reconstruct (f : Frame) (failed : Bool)
    (hC : f.gasMeter.stateGasCommittedSpill = 0)
    (hFailed : failed = true → f.gasMeter.stateGasSpilled = 0 ∧
      f.gasMeter.refundCounter = 0 ∧
      f.gasMeter.stateGasLeft = f.gasMeter.stateGasBaseline) : ChildSettled f failed := by
  cases failed
  · exact ⟨hC, True.intro⟩
  · exact ⟨hC, hFailed rfl⟩

private theorem other_fields_irrelevant (f : Frame) (failed : Bool)
    (pc : Nat) (stack : Stack) (memory : Memory) (logs : LogRope)
    (deleted : AddrSet) (returned : Bytes) (warm : AddrSet) (slots : SlotSet) :
    ChildSettled (Frame.mk pc stack memory f.gasMeter logs deleted returned warm slots) failed ↔
      ChildSettled f failed := by
  rfl

private theorem execution_gas_irrelevant (f : Frame) (failed : Bool) (gas : Nat) :
    ChildSettled { f with gasMeter := { f.gasMeter with gasLeft := gas } } failed ↔
      ChildSettled f failed := by
  rfl

-- Each clause is necessary independently, for every choice of unused Frame fields.
private theorem reject_committed (f : Frame) (failed : Bool) :
    ¬ ChildSettled { f with gasMeter := ⟨3, 7, 7, 0, 0, 1⟩ } failed := by
  intro h
  exact Nat.noConfusion h.1

private theorem reject_pending (f : Frame) :
    ¬ ChildSettled { f with gasMeter := ⟨3, 7, 7, 0, 1, 0⟩ } true := by
  simp [ChildSettled]

private theorem reject_negative_refund (f : Frame) :
    ¬ ChildSettled { f with gasMeter := ⟨3, 7, 7, -1, 0, 0⟩ } true := by
  simp [ChildSettled]

private theorem reject_positive_refund (f : Frame) :
    ¬ ChildSettled { f with gasMeter := ⟨3, 7, 7, 1, 0, 0⟩ } true := by
  simp [ChildSettled]

private theorem reject_reservoir (f : Frame) :
    ¬ ChildSettled { f with gasMeter := ⟨3, 8, 7, 0, 0, 0⟩ } true := by
  simp [ChildSettled]

-- Success has only C=0: both signed refund directions and positive pools are admitted.
private theorem accept_raw_success (f : Frame) :
    ChildSettled { f with gasMeter := ⟨4, 9, 2, -5, 3, 0⟩ } false ∧
    ChildSettled { f with gasMeter := ⟨4, 9, 2, 5, 3, 0⟩ } false := by
  exact ⟨⟨rfl, True.intro⟩, ⟨rfl, True.intro⟩⟩

-- Failure is shared by revert and halt; arbitrary gas and return data stay admitted.
private theorem accept_raw_failure (f : Frame) (gas baseline : Nat) (returned : Bytes) :
    ChildSettled { f with
      gasMeter := ⟨gas, baseline, baseline, 0, 0, 0⟩
      returnData := returned } true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem nonempty_revert_control (f : Frame) :
    ChildSettled { f with
      gasMeter := ⟨17, 7, 7, 0, 0, 0⟩
      returnData := Bytes.ofList [0, 255, 128] } true := by
  exact accept_raw_failure f 17 7 _

private theorem restore_with_separate_committed_proof (f : Frame)
    (hC : f.gasMeter.stateGasCommittedSpill = 0) :
    { f with gasMeter := restoreStateGas f.gasMeter } =
      Frame.mk f.pc f.stack f.memory (restoreStateGas f.gasMeter) f.logs
        f.accountsToDelete f.returnData f.accessedAddresses f.accessedStorageKeys ∧
    ChildSettled { f with gasMeter := restoreStateGas f.gasMeter } true := by
  refine ⟨rfl, ?_⟩
  exact ⟨(congrArg GasMeter.stateGasCommittedSpill (restoreStateGas_eq _)).trans hC,
    restoreStateGas_post _⟩

private theorem restore_forfeit_with_separate_committed_proof (f : Frame)
    (hC : f.gasMeter.stateGasCommittedSpill = 0) :
    let restored := restoreStateGas f.gasMeter
    let halted := forfeitRemainingGas restored (restoreStateGas_post _).1
    { f with gasMeter := halted } =
      Frame.mk f.pc f.stack f.memory halted f.logs f.accountsToDelete f.returnData
        f.accessedAddresses f.accessedStorageKeys ∧
    ChildSettled { f with gasMeter := halted } true := by
  dsimp only
  rw [forfeitRemainingGas_eq]
  refine ⟨rfl, ?_⟩
  exact ⟨(congrArg GasMeter.stateGasCommittedSpill (restoreStateGas_eq _)).trans hC,
    restoreStateGas_post _⟩

-- Preserve the complete C=7 counterexample through actual ordinary rollback/forfeit.
private theorem committed_counterexample (f : Frame) :
    let original : GasMeter := ⟨3, 10, 1, -2, 4, 7⟩
    let restored := restoreStateGas original
    let halted := forfeitRemainingGas restored (restoreStateGas_post _).1
    restored = (⟨7, 1, 1, 0, 0, 7⟩ : GasMeter) ∧
    halted = (⟨0, 1, 1, 0, 0, 7⟩ : GasMeter) ∧
    { f with gasMeter := restored } =
      Frame.mk f.pc f.stack f.memory ⟨7, 1, 1, 0, 0, 7⟩ f.logs
        f.accountsToDelete f.returnData f.accessedAddresses f.accessedStorageKeys ∧
    { f with gasMeter := halted } =
      Frame.mk f.pc f.stack f.memory ⟨0, 1, 1, 0, 0, 7⟩ f.logs
        f.accountsToDelete f.returnData f.accessedAddresses f.accessedStorageKeys ∧
    ¬ ChildSettled { f with gasMeter := restored } true ∧
    ¬ ChildSettled { f with gasMeter := halted } true := by
  dsimp only
  rw [forfeitRemainingGas_eq, restoreStateGas_eq]
  exact ⟨rfl, rfl, rfl, rfl, by simp [ChildSettled], by simp [ChildSettled]⟩

-- Executable decisions reduce with arbitrary untouched data, without Frame equality.
private theorem decision_controls (f : Frame) :
    settledDecision { f with gasMeter := ⟨4, 9, 2, -5, 3, 0⟩ } false = true ∧
    settledDecision { f with gasMeter := ⟨4, 9, 2, -5, 3, 0⟩ } true = false ∧
    settledDecision { f with gasMeter := ⟨17, 7, 7, 0, 0, 0⟩ } true = true ∧
    settledDecision { f with gasMeter := ⟨17, 7, 7, 0, 0, 7⟩ } false = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end STFSpec.Conformance.Vm.Core.ChildSettledCallerProofs
