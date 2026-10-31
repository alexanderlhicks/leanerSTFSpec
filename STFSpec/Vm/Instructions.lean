/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions.CreateRequest
import STFSpec.Vm.Instructions.Ops

/-!
# STFSpec.Vm.Instructions

One handler per opcode, producing a `StepResult`: a successor frame, a halt/revert/exceptional outcome, or a child call/create request.

Library `EthVmInstructions`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). The raw `CreateRequest` carrier and opcode
byte conversions are supplied; handlers, child construction and resume remain unimplemented.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md`.
-/
