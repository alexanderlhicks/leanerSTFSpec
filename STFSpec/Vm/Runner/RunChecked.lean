/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core.World
import STFSpec.Vm.Runner.Checked

/-!
# Checked VM action adapter

Library `EthVmRunner`. The F14 adapter retains complete payloads while routing
VM faults and internal failures into their separate checked-result channels.
This project adapter has no corresponding EELS function.
Spec guidance: `STFSpec/informal/modules/EthVmRunner.md` §§3/5/7.
-/

namespace STFSpec.Vm.Runner
open STFSpec.Vm.Core

/-- Internal-error transformer over the state/error VM monad (F14).
Forming the alias requires no class premise. -/
abbrev RunM (m : Type → Type) := ExceptT InternalError (VmM m)

/-- Route a VM action through the supplied base bind and pure (F14).
A VM fault retains its complete payload; internal failure discards its returned
world; success retains the complete payload and updated world. -/
def runVmChecked {m : Type → Type} [Monad m] {α : Type}
    (action : VmM m (Except InternalError α)) (world : VmWorld m) :
    m (CheckedResult VmFault (α × VmWorld m)) := do
  match ← (action.run world).run with
  | .error vf => pure (.ok (.error vf))
  | .ok (.error i, _) => pure (.error i)
  | .ok (.ok a, after) => pure (.ok (.ok (a, after)))

/-- Complete literal base-action routing equation, without a lawful-monad premise. -/
theorem runVmChecked_eq {m : Type → Type} [Monad m] {α : Type}
    (action : VmM m (Except InternalError α)) (world : VmWorld m) :
    runVmChecked action world = (do
      match ← (action.run world).run with
      | .error vf => pure (.ok (.error vf))
      | .ok (.error i, _) => pure (.error i)
      | .ok (.ok a, after) => pure (.ok (.ok (a, after)))) := rfl

end STFSpec.Vm.Runner
