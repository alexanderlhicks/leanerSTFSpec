/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.U256
import STFSpec.Base.FixedBytes

/-!
# Raw creation requests

Library `EthVmInstructions`. The creation suspension interface retains the supplied
child grants, endowment, addresses, init code and account-charge flag.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md` §§3/5/7.
-/

namespace STFSpec.Vm.Instructions

/-- Raw creation suspension data. The split originates in pinned EELS
`src/ethereum/forks/amsterdam/vm/instructions/system.py:66–192`.
Producers establish preflight, gas withholding and destination effects separately. -/
structure CreateRequest where
  gas : Nat
  stateGasReservoir : Nat
  endowment : STFSpec.Base.U256
  caller : STFSpec.Base.Address
  contractAddress : STFSpec.Base.Address
  initCode : STFSpec.Base.Bytes
  newAccountCharged : Bool

end STFSpec.Vm.Instructions
