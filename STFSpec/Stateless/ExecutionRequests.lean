/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless.RequestItems

/-!
# Raw execution requests

Library `EthStateless`. Five independent arrays retain complete nominal request items.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3–7.
-/

namespace STFSpec.Stateless

/-- Raw ordered request collections; EELS
`src/ethereum/forks/amsterdam/execution_engine/requests.py:99–121` at the pin.
Construction retains every array, including empty arrays and repeated items,
without validation or effects. -/
structure ExecutionRequests where
  deposits : Array DepositRequest
  withdrawals : Array WithdrawalRequest
  consolidations : Array ConsolidationRequest
  builderDeposits : Array BuilderDepositRequest
  builderExits : Array BuilderExitRequest

end STFSpec.Stateless
