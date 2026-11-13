/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions

/-!
# Settled child outcome clients

Library `EthConformance`. Private public-facade clients retain complete arbitrary
provider values and check the dependent local proof boundary. These clients do
not establish execution reachability, rollback correctness or proof production.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Vm.Instructions.ChildOutcomeCallerProofs
open STFSpec.Base STFSpec.Vm.Core STFSpec.Vm.Instructions

private def construct (f : Frame) (output : Bytes) (error : Option FrameError)
    (h : ChildSettled f error.isSome) : ChildOutcome :=
  ChildOutcome.mk f output error h

private def fields (c : ChildOutcome) : Frame × Bytes × Option FrameError :=
  (c.frame, c.output, c.error)

private theorem constructor_fields (f : Frame) (output : Bytes) (error : Option FrameError)
    (h : ChildSettled f error.isSome) :
    fields (construct f output error h) = (f, output, error) := rfl

private theorem constructor_proof (f : Frame) (output : Bytes) (error : Option FrameError)
    (h : ChildSettled f error.isSome) :
    (construct f output error h).settled = h := rfl

private theorem reconstruction (c : ChildOutcome) :
    ChildOutcome.mk c.frame c.output c.error c.settled = c := rfl

private theorem all_fields_determine (c d : ChildOutcome) (h : fields c = fields d) :
    c = d := by
  cases c
  cases d
  cases h
  rfl

private theorem dependent_elimination (c : ChildOutcome)
    (P : (f : Frame) → (output : Bytes) → (error : Option FrameError) →
      ChildSettled f error.isSome → Prop)
    (h : ∀ f output error settled, P f output error settled) :
    P c.frame c.output c.error c.settled := by
  cases c with
  | mk f output error settled => exact h f output error settled

private theorem replacements (c : ChildOutcome) (f : Frame) (output : Bytes)
    (error : Option FrameError) (hf : ChildSettled f c.error.isSome)
    (he : ChildSettled c.frame error.isSome) :
    fields { c with frame := f, settled := hf } = (f, c.output, c.error) ∧
    fields { c with output := output } = (c.frame, output, c.error) ∧
    fields { c with error := error, settled := he } = (c.frame, c.output, error) :=
  ⟨rfl, rfl, rfl⟩

private theorem replacement_proofs (c : ChildOutcome) (f : Frame) (output : Bytes)
    (error : Option FrameError) (hf : ChildSettled f c.error.isSome)
    (he : ChildSettled c.frame error.isSome) :
    ({ c with frame := f, settled := hf } : ChildOutcome).settled = hf ∧
    ({ c with output := output } : ChildOutcome).settled = c.settled ∧
    ({ c with error := error, settled := he } : ChildOutcome).settled = he :=
  ⟨rfl, rfl, rfl⟩

private theorem success_clauses (c : ChildOutcome) (h : c.error = none) :
    c.frame.gasMeter.stateGasCommittedSpill = 0 := by
  have hs := c.settled
  rw [h] at hs
  exact hs.1

private theorem failure_clauses (c : ChildOutcome) (e : FrameError)
    (h : c.error = some e) :
    c.frame.gasMeter.stateGasCommittedSpill = 0 ∧
    c.frame.gasMeter.stateGasSpilled = 0 ∧
    c.frame.gasMeter.refundCounter = 0 ∧
    c.frame.gasMeter.stateGasLeft = c.frame.gasMeter.stateGasBaseline := by
  have hs := c.settled
  rw [h] at hs
  exact hs

private theorem success_constructible (f : Frame) (output : Bytes)
    (h : f.gasMeter.stateGasCommittedSpill = 0) :
    fields (construct f output none ⟨h, True.intro⟩) = (f, output, none) := rfl

private theorem failure_constructible (f : Frame) (output : Bytes) (e : FrameError)
    (hC : f.gasMeter.stateGasCommittedSpill = 0)
    (hS : f.gasMeter.stateGasSpilled = 0) (hR : f.gasMeter.refundCounter = 0)
    (hB : f.gasMeter.stateGasLeft = f.gasMeter.stateGasBaseline) :
    fields (construct f output (some e) ⟨hC, hS, hR, hB⟩) =
      (f, output, some e) := rfl

-- These boundary witnesses retain every unused field of the supplied Frame.
-- Success admits both signed refunds, pending spill and unequal reservoir/baseline.
private theorem success_boundaries (f : Frame) (output : Bytes) :
    let negative := { f with gasMeter := ⟨2 ^ 300, 9, 2, -5, 3, 0⟩ }
    let positive := { f with gasMeter := ⟨0, 9, 2, 5, 3, 0⟩ }
    fields (construct negative output none ⟨rfl, True.intro⟩) =
      (negative, output, none) ∧
    fields (construct positive output none ⟨rfl, True.intro⟩) =
      (positive, output, none) := ⟨rfl, rfl⟩

-- Halt and revert share the failed flag without identifying their payloads.
-- In particular a raw halt can retain nonempty output and arbitrary execution gas.
private theorem failure_boundaries (f : Frame) (output : Bytes) (e : ExceptionalHalt)
    (gas baseline : Nat) :
    let child := { f with gasMeter := ⟨gas, baseline, baseline, 0, 0, 0⟩ }
    fields (construct child output (some (.halt e)) ⟨rfl, rfl, rfl, rfl⟩) =
      (child, output, some (.halt e)) ∧
    fields (construct child output (some .revert) ⟨rfl, rfl, rfl, rfl⟩) =
      (child, output, some .revert) := ⟨rfl, rfl⟩

private theorem error_payloads (f : Frame) (output : Bytes) (opcode : UInt8) (reason : String) :
    let child := { f with gasMeter := ⟨17, 7, 7, 0, 0, 0⟩ }
    (construct child output (some (.halt (.invalidOpcode opcode)))
      ⟨rfl, rfl, rfl, rfl⟩).error = some (.halt (.invalidOpcode opcode)) ∧
    (construct child output (some (.halt (.precompileHalt reason)))
      ⟨rfl, rfl, rfl, rfl⟩).error = some (.halt (.precompileHalt reason)) ∧
    (construct child output (some .revert) ⟨rfl, rfl, rfl, rfl⟩).error ≠
      some (.halt (.precompileHalt reason)) := by
  exact ⟨rfl, rfl, by intro h; cases h⟩

private theorem complete_bytes (c : ChildOutcome) (bytes : List UInt8) :
    ({ c with output := Bytes.ofList bytes } : ChildOutcome).output.toList = bytes :=
  Bytes.toList_ofList bytes

private theorem nonempty_outputs (f : Frame) :
    let child := { f with gasMeter := ⟨2 ^ 300 + 1, 0, 0, 0, 0, 0⟩ }
    (construct child (Bytes.ofList [0, 255, 0, 128]) none
      ⟨rfl, True.intro⟩).output.toList = [0, 255, 0, 128] ∧
    (construct child (Bytes.ofList [255, 0, 1, 255]) (some .revert)
      ⟨rfl, rfl, rfl, rfl⟩).output.toList = [255, 0, 1, 255] ∧
    (construct child (Bytes.ofList [128, 0, 128]) (some (.halt .outOfGas))
      ⟨rfl, rfl, rfl, rfl⟩).output.toList = [128, 0, 128] :=
  ⟨Bytes.toList_ofList _, Bytes.toList_ofList _, Bytes.toList_ofList _⟩

-- Each bad meter lacks the required local proof, regardless of retained payloads.
private theorem bad_meters (f : Frame) :
    ¬ ChildSettled { f with gasMeter := ⟨17, 7, 7, 0, 0, 1⟩ } false ∧
    ¬ ChildSettled { f with gasMeter := ⟨17, 7, 7, 0, 1, 0⟩ } true ∧
    ¬ ChildSettled { f with gasMeter := ⟨17, 7, 7, -1, 0, 0⟩ } true ∧
    ¬ ChildSettled { f with gasMeter := ⟨17, 7, 7, 1, 0, 0⟩ } true ∧
    ¬ ChildSettled { f with gasMeter := ⟨17, 8, 7, 0, 0, 0⟩ } true := by
  simp [ChildSettled]

private theorem decision_boundary (f : Frame) :
    decide (ChildSettled { f with gasMeter := ⟨17, 8, 7, -1, 1, 0⟩ } false) = true ∧
    decide (ChildSettled { f with gasMeter := ⟨17, 8, 7, -1, 1, 0⟩ } true) = false ∧
    decide (ChildSettled { f with gasMeter := ⟨17, 7, 7, 0, 0, 0⟩ } true) = true :=
  ⟨rfl, rfl, rfl⟩

-- The missing-field diagnostic requires the supplied proof, rather than a default.
/-- error: Fields missing: `settled` -/
#guard_msgs (substring := true) in
example (f : Frame) (output : Bytes) (error : Option FrameError) : ChildOutcome :=
  { frame := f, output := output, error := error }

-- A success proof does not prove the additional failed-child reset clauses.
/--
error: Application type mismatch: The argument
  h
has type
  ChildSettled f false
but is expected to have type
  ChildSettled f (some FrameError.revert).isSome
in the application
  { frame := f, output := output, error := some FrameError.revert, settled := h }
-/
#guard_msgs in
example (f : Frame) (output : Bytes) (h : ChildSettled f false) : ChildOutcome :=
  ChildOutcome.mk f output (some .revert) h

-- A different Frame requires its own proof even when the failure flag is unchanged.
/--
error: Application type mismatch: The argument
  h
has type
  ChildSettled f error.isSome
but is expected to have type
  ChildSettled g error.isSome
in the application
  { frame := g, output := output, error := error, settled := h }
-/
#guard_msgs in
example (f g : Frame) (output : Bytes) (error : Option FrameError)
    (h : ChildSettled f error.isSome) : ChildOutcome :=
  ChildOutcome.mk g output error h

end STFSpec.Conformance.Vm.Instructions.ChildOutcomeCallerProofs
