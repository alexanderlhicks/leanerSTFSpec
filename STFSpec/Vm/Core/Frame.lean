/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core.Stack
import STFSpec.Vm.Core.Memory
import STFSpec.Vm.Core.GasMeter
import STFSpec.Vm.Core.Logs
import STFSpec.Vm.Core.Sets

/-!
# Mutable frame data

Library `EthVmCore`. This raw record supplies exactly the mutable partition of
pinned EELS `src/ethereum/forks/amsterdam/vm/__init__.py:153–191` (R-ENV-3).
Immutable call context, control outcomes and parent execution have separate owners.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7.
-/

namespace STFSpec.Vm.Core
open STFSpec.Base

/-- The nine independent mutable fields of Evm, without extra admission conditions. -/
structure Frame where
  /-- Program counter, independent of code or host-width bounds. -/
  pc : Nat
  /-- Complete bounded operand stack. -/
  stack : Stack
  /-- Complete aligned memory. -/
  memory : Memory
  /-- Complete six-field gas meter, including its signed refund. -/
  gasMeter : GasMeter
  /-- Chronological log rope, retaining the supplied raw shape. -/
  logs : LogRope
  /-- Addresses marked for deletion. -/
  accountsToDelete : AddrSet
  /-- Complete most recent child return data. -/
  returnData : Bytes
  /-- Warm addresses, independent of the deletion set. -/
  accessedAddresses : AddrSet
  /-- Warm address/storage-slot pairs. -/
  accessedStorageKeys : SlotSet

end STFSpec.Vm.Core
