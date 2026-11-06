/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.FixedBytes
import STFSpec.Base.U64

/-!
# Raw execution-request items

Library `EthStateless`. Five nominal carriers retain every supplied Base field.
Schema adapters, wire encoding and execution are separate from these raw values.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3–7.
-/

namespace STFSpec.Stateless

open STFSpec.Base

/-- Raw `DepositRequest` fields in source order; EELS
`src/ethereum/forks/amsterdam/execution_engine/requests.py:42` at the pin.
Construction adds no validation or effects. -/
structure DepositRequest where
  pubkey : Bytes48
  withdrawalCredentials : Bytes32
  amount : U64
  signature : Bytes96
  index : U64

/-- Raw `WithdrawalRequest` fields in source order; EELS
`src/ethereum/forks/amsterdam/execution_engine/requests.py:55` at the pin.
Construction adds no validation or effects. -/
structure WithdrawalRequest where
  sourceAddress : Address
  validatorPubkey : Bytes48
  amount : U64

/-- Raw `ConsolidationRequest` fields in source order; EELS
`src/ethereum/forks/amsterdam/execution_engine/requests.py:66` at the pin.
Construction adds no validation or effects. -/
structure ConsolidationRequest where
  sourceAddress : Address
  sourcePubkey : Bytes48
  targetPubkey : Bytes48

/-- Raw `BuilderDepositRequest` fields in source order; EELS
`src/ethereum/forks/amsterdam/execution_engine/requests.py:77` at the pin.
Construction adds no validation or effects. -/
structure BuilderDepositRequest where
  pubkey : Bytes48
  withdrawalCredentials : Bytes32
  amount : U64
  signature : Bytes96

/-- Raw `BuilderExitRequest` fields in source order; EELS
`src/ethereum/forks/amsterdam/execution_engine/requests.py:89` at the pin.
Construction adds no validation or effects. -/
structure BuilderExitRequest where
  sourceAddress : Address
  pubkey : Bytes48

end STFSpec.Stateless
