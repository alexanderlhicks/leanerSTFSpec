/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core.Frame

/-!
# Child settlement assertion boundary

Library `EthVmCore`. The raw logical predicate records the four incorporation
assertions, without choosing how the runner produces their proof (F11).
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7.
-/

namespace STFSpec.Vm.Core

/-- Incorporation requires zero committed spill on every child and the three
reset clauses on failure; EELS
`src/ethereum/forks/amsterdam/vm/__init__.py:227,232–234`. -/
def ChildSettled (child : Frame) (failed : Bool) : Prop :=
  child.gasMeter.stateGasCommittedSpill = 0 ∧
    (if failed then
      child.gasMeter.stateGasSpilled = 0 ∧
      child.gasMeter.refundCounter = 0 ∧
      child.gasMeter.stateGasLeft = child.gasMeter.stateGasBaseline
     else True)

/-- Constructive logical decidability; this supplies no runtime caller or proof producer. -/
instance instDecidableChildSettled (child : Frame) (failed : Bool) :
    Decidable (ChildSettled child failed) := by
  unfold ChildSettled
  infer_instance

end STFSpec.Vm.Core
