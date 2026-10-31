/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.FixedBytes
import Std.Data.ExtTreeSet

/-!
# Persistent address and storage-slot sets

Library `EthVmCore`. Reuse Base's nominal address and lexical address/slot ordering
and Std's public finite-set API for the mutable Evm fields at pinned EELS
`src/ethereum/forks/amsterdam/vm/__init__.py:187,190–191`.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7.
-/

namespace STFSpec.Vm.Core
open STFSpec.Base

/-- Persistent address set for deletion and warm-address bookkeeping. -/
abbrev AddrSet := Std.ExtTreeSet Address

/-- Persistent storage-slot set, ordered lexically by address and then slot. -/
abbrev SlotSet := Std.ExtTreeSet (Address × Bytes32)

end STFSpec.Vm.Core
