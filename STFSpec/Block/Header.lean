/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.Bytes
import STFSpec.Base.FixedBytes
import STFSpec.Base.U256
import STFSpec.Base.U64

/-!
# Raw block headers

Library `EthBlock`. Required fields retain their supplied values in source order.
These carriers provide storage and common parent projections.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§2.1, 3, 5 and 7.
-/

namespace STFSpec.Block

open STFSpec.Base

/-- Raw Amsterdam header; EELS `src/ethereum/forks/amsterdam/blocks.py:72`. -/
structure Header where
  parentHash : Hash32
  ommersHash : Hash32
  coinbase : Address
  stateRoot : Root
  transactionsRoot : Root
  receiptRoot : Root
  bloom : Bloom
  difficulty : Nat
  number : Nat
  gasLimit : Nat
  gasUsed : Nat
  timestamp : U256
  extraData : Bytes
  prevRandao : Bytes32
  nonce : Bytes8
  baseFeePerGas : Nat
  withdrawalsRoot : Root
  blobGasUsed : U64
  excessBlobGas : U64
  parentBeaconBlockRoot : Root
  requestsHash : Hash32
  blockAccessListHash : Hash32
  slotNumber : U64

/-- Raw bpo5 header; EELS `src/ethereum/forks/bpo5/blocks.py:71`. -/
structure PrevHeader where
  parentHash : Hash32
  ommersHash : Hash32
  coinbase : Address
  stateRoot : Root
  transactionsRoot : Root
  receiptRoot : Root
  bloom : Bloom
  difficulty : Nat
  number : Nat
  gasLimit : Nat
  gasUsed : Nat
  timestamp : U256
  extraData : Bytes
  prevRandao : Bytes32
  nonce : Bytes8
  baseFeePerGas : Nat
  withdrawalsRoot : Root
  blobGasUsed : U64
  excessBlobGas : U64
  parentBeaconBlockRoot : Root
  requestsHash : Hash32

/-- Preserve the parent variant of EELS `Header | PreviousHeader`;
`src/ethereum/forks/amsterdam/fork.py:149,425`. -/
inductive ParentHeader where
  | amsterdam (h : Header)
  | bpo5 (h : PrevHeader)

namespace ParentHeader

/-- The supplied `gasLimit` of either parent variant. -/
def gasLimit : ParentHeader → Nat
  | .amsterdam h => h.gasLimit
  | .bpo5 h => h.gasLimit

/-- The supplied `gasUsed` of either parent variant. -/
def gasUsed : ParentHeader → Nat
  | .amsterdam h => h.gasUsed
  | .bpo5 h => h.gasUsed

/-- The supplied `baseFeePerGas` of either parent variant. -/
def baseFeePerGas : ParentHeader → Nat
  | .amsterdam h => h.baseFeePerGas
  | .bpo5 h => h.baseFeePerGas

/-- The supplied `timestamp` of either parent variant. -/
def timestamp : ParentHeader → U256
  | .amsterdam h => h.timestamp
  | .bpo5 h => h.timestamp

/-- The supplied `number` of either parent variant. -/
def number : ParentHeader → Nat
  | .amsterdam h => h.number
  | .bpo5 h => h.number

/-- The supplied `stateRoot` of either parent variant. -/
def stateRoot : ParentHeader → Root
  | .amsterdam h => h.stateRoot
  | .bpo5 h => h.stateRoot

/-- The supplied `excessBlobGas` of either parent variant. -/
def excessBlobGas : ParentHeader → U64
  | .amsterdam h => h.excessBlobGas
  | .bpo5 h => h.excessBlobGas

/-- The supplied `blobGasUsed` of either parent variant. -/
def blobGasUsed : ParentHeader → U64
  | .amsterdam h => h.blobGasUsed
  | .bpo5 h => h.blobGasUsed

/-- The supplied `parentHash` of either parent variant. -/
def parentHash : ParentHeader → Hash32
  | .amsterdam h => h.parentHash
  | .bpo5 h => h.parentHash

end ParentHeader

end STFSpec.Block
