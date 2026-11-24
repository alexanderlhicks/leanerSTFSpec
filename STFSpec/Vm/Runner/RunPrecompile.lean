/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core.Precompile
import STFSpec.Vm.Runner.Output

/-!
# Precompile execution within a frame

Library `EthVmRunner`. This adapter consumes a supplied precompile action.
The caller owns selection and transaction snapshot restoration.
Spec guidance: `STFSpec/informal/modules/EthVmRunner.md` §§2.4/2.6/5/7.
-/

namespace STFSpec.Vm.Runner

open STFSpec.Base STFSpec.Vm.Core

/-- Run an installed action on the supplied input and frame meter.
Success installs the returned meter. A halt restores pending state gas and
forfeits execution gas. EELS `vm/interpreter.py:432–436,450–459` at the pin. -/
def runPrecompile {m : Type → Type} [Monad m]
    (p : PrecompileFn m) (f : Frame) (input : Bytes) : m FrameResult := do
  match ← p input f.gasMeter with
  | .ok paid output => pure ⟨{ f with gasMeter := paid }, output, none⟩
  | .halt error =>
    let restored := restoreStateGas f.gasMeter
    let meter := forfeitRemainingGas restored (restoreStateGas_post f.gasMeter).1
    pure ⟨{ f with gasMeter := meter }, Bytes.empty, some (.halt error)⟩

end STFSpec.Vm.Runner
