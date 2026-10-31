/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import Init.Control.Except

/-!
# Checked runner carriers

Library `EthVmRunner`. Source-free internal-error and two-layer checked-result
carriers. Execution, propagation and fuel adequacy remain separate obligations.
Spec guidance: `STFSpec/informal/modules/EthVmRunner.md` §§3/5/7.
-/

namespace STFSpec.Vm.Runner

/-- Spec-internal failure (O11), separate from frame exits and protocol rejections.
The optional invariant failure remains reserved by F11. -/
inductive InternalError where
  /-- Per-frame fuel exhaustion, retaining the complete supplied depth. -/
  | fuelExhausted (depth : Nat)

/-- An internal failure, an inner typed rejection, or a successful payload. -/
abbrev CheckedResult (ε α : Type) := Except InternalError (Except ε α)

/-- Checked transformer order (F14): `.run.run` retains the outer internal channel. -/
abbrev CheckedT (ε : Type) (m : Type → Type) := ExceptT ε (ExceptT InternalError m)

end STFSpec.Vm.Runner
