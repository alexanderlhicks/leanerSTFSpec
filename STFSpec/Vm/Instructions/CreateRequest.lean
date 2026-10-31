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
  /-- Child execution grant after withholding, `create_message_gas` (system.py:120). -/
  gas : Nat
  /-- Parent reservoir drained into the child, `create_message_state_gas_reservoir` (:132). -/
  stateGasReservoir : Nat
  /-- Value transferred to the child, `value=endowment` (:149). -/
  endowment : STFSpec.Base.U256
  /-- The creating frame's target, `caller=evm.current_target` (:147). -/
  caller : STFSpec.Base.Address
  /-- The new contract's address, `current_target=contract_address` (:148). -/
  contractAddress : STFSpec.Base.Address
  /-- The child's code, `code=init_code` (:156, read at :89). -/
  initCode : STFSpec.Base.Bytes
  /-- Whether NEW_ACCOUNT was charged, refunded if the child fails (:114, :186). -/
  newAccountCharged : Bool

end STFSpec.Vm.Instructions
