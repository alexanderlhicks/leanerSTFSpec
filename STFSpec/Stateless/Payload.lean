/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.U256
import STFSpec.Block.Withdrawal
import STFSpec.Stateless.ExecutionRequests

/-!
# Raw execution payload and new-payload request

Library `EthStateless`. Complete independent fields retain raw bytes and ordered collections.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3–7.
-/

namespace STFSpec.Stateless

/-- Raw ordered payload fields; EELS
`src/ethereum/forks/amsterdam/execution_engine/types.py:39–72` at the pin.
Construction retains all supplied values without validation or effects. -/
structure ExecutionPayload where
  parentHash : Base.Hash32
  feeRecipient : Base.Address
  stateRoot : Base.Hash32
  receiptsRoot : Base.Hash32
  logsBloom : Base.Bloom
  prevRandao : Base.Bytes32
  blockNumber : Base.U64
  gasLimit : Base.U64
  gasUsed : Base.U64
  timestamp : Base.U64
  extraData : ByteArray
  baseFeePerGas : Base.U256
  blockHash : Base.Hash32
  transactions : Array ByteArray
  withdrawals : Array Block.Withdrawal
  blobGasUsed : Base.U64
  excessBlobGas : Base.U64
  blockAccessList : ByteArray
  slotNumber : Base.U64

/-- Raw ordered request fields; EELS
`src/ethereum/forks/amsterdam/execution_engine/types.py:78–96` at the pin.
Construction retains all supplied values without validation or effects. -/
structure NewPayloadRequest where
  executionPayload : ExecutionPayload
  versionedHashes : Array Base.VersionedHash
  parentBeaconBlockRoot : Base.Hash32
  executionRequests : ExecutionRequests

end STFSpec.Stateless
