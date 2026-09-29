/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

/-!
# STFSpec.Vm.Instructions

One handler per opcode, producing a `StepResult`: a successor frame, a halt/revert/exceptional outcome, or a child call/create request.

Library `EthVmInstructions`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). No definitions yet: scaffolding only.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md`.
-/
