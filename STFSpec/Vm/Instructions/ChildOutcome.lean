/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core.ChildSettled
import STFSpec.Vm.Core.Exceptions

/-!
# Settled child outcome data

Library `EthVmInstructions`. This carrier retains a complete child frame, output
and optional frame error with a supplied local settlement proof. It selects no
runner proof-production route (F11).
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md` §§3/5/7.
-/

namespace STFSpec.Vm.Instructions
open STFSpec.Base STFSpec.Vm.Core

/-- Child return data with the incorporation assertions from pinned EELS
`src/ethereum/forks/amsterdam/vm/__init__.py:221,226–228`.
Actual child error handling at `vm/interpreter.py:449–465` remains a producer obligation. -/
structure ChildOutcome where
  frame : Frame
  output : Bytes
  error : Option FrameError
  settled : ChildSettled frame error.isSome

end STFSpec.Vm.Instructions
