/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Raw frame error callers

Library `EthConformance`. Private ordinary clients use the public constructors and
eliminators, retaining arbitrary complete halt payloads and the separate revert branch.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/5.
-/

namespace STFSpec.Conformance.Vm.Core.FrameErrorCallerProofs
open STFSpec.Vm.Core

private theorem reconstruct (e : FrameError) :
    (match e with
     | .halt payload => FrameError.halt payload
     | .revert => .revert) = e := by
  cases e <;> rfl

private theorem extract_halt (e : ExceptionalHalt) :
    (match FrameError.halt e with
     | .halt payload => some payload
     | .revert => none) = some e := rfl

private theorem extract_revert :
    (match FrameError.revert with
     | .halt payload => some payload
     | .revert => none) = (none : Option ExceptionalHalt) := rfl

private theorem halt_injective (a b : ExceptionalHalt)
    (h : FrameError.halt a = .halt b) : a = b := by
  cases h
  rfl

private theorem halt_ne_revert (e : ExceptionalHalt) : FrameError.halt e ≠ .revert := by
  intro h
  cases h

private theorem revert_ne_halt (e : ExceptionalHalt) : FrameError.revert ≠ .halt e := by
  intro h
  cases h

private theorem exhaustive (e : FrameError) :
    (∃ payload, e = .halt payload) ∨ e = .revert := by
  cases e with
  | halt payload => exact .inl ⟨payload, rfl⟩
  | revert => exact .inr rfl

private theorem eliminate (P : FrameError → Prop)
    (onHalt : ∀ payload, P (.halt payload)) (onRevert : P .revert)
    (e : FrameError) : P e := by
  cases e with
  | halt payload => exact onHalt payload
  | revert => exact onRevert

private theorem opcode_payload (code : UInt8) :
    (match FrameError.halt (.invalidOpcode code) with
     | .halt (.invalidOpcode payload) => some payload
     | _ => none) = some code := rfl

private theorem bare_payload (reason : String) :
    (match FrameError.halt (.precompileHalt reason) with
     | .halt (.precompileHalt payload) => some payload
     | _ => none) = some reason := rfl

end STFSpec.Conformance.Vm.Core.FrameErrorCallerProofs
