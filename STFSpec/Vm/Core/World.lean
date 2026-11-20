/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.TxState
import STFSpec.Vm.Core.VmFault

/-!
# Raw VM world and VM monad

Library `EthVmCore`: retain one complete supplied transaction state and the guided
state/error transformer order. This module supplies nominal wiring; `StateLift.lean`
supplies the state lift. Initialization, tracker operations, lifetimes and execution
semantics remain separate.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/5/7/10.
-/

namespace STFSpec.Vm.Core

/-- The raw world from EthVmCore §5 retains the complete supplied transaction state.
There is no class or validity premise. The State providers retain their code-read
discrepancy recorded in EthState §10 X16(b). -/
structure VmWorld (m : Type → Type) where
  /-- Single supplied owner of block context, revertible writes and observations. -/
  tx : STFSpec.State.TxState m

/-- State/error transformer wiring from EthVmCore §5.
Running yields `m (Except VmFault (α × VmWorld m))`: failure returns no world.
This alias alone supplies no state lift or rollback interpretation of underlying effects. -/
abbrev VmM (m : Type → Type) := StateT (VmWorld m) (ExceptT VmFault m)

end STFSpec.Vm.Core
