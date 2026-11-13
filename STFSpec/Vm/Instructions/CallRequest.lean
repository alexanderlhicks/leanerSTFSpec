/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.U256
import STFSpec.Base.FixedBytes

/-!
# Raw call requests

Library `EthVmInstructions`. The call suspension interface retains independent
child grants, value, addresses, flags, complete input/code bytes and output window.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md` §§3/5/7.
-/

namespace STFSpec.Vm.Instructions

/-- Raw call suspension data. The split originates in pinned EELS
`src/ethereum/forks/amsterdam/vm/instructions/system.py:369–462`.
Producers establish preflight, gas withholding and child-context policy separately. -/
structure CallRequest where
  gas : Nat
  stateGasReservoir : Nat
  value : STFSpec.Base.U256
  caller : STFSpec.Base.Address
  to : STFSpec.Base.Address
  codeAddress : STFSpec.Base.Address
  shouldTransferValue : Bool
  isStatic : Bool
  disablePrecompiles : Bool
  newAccountCharged : Bool
  callData : STFSpec.Base.Bytes
  code : STFSpec.Base.Bytes
  outOffset : STFSpec.Base.U256
  outSize : STFSpec.Base.U256

end STFSpec.Vm.Instructions
