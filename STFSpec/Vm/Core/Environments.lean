/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.ValueRecords
import STFSpec.Vm.Core.Sets

/-!
# Raw block and transaction environments

Library `EthVmCore`. Immutable VM-visible data from pinned EELS
`src/ethereum/forks/amsterdam/vm/__init__.py:49–67,125–148` (R-ENV-1/R-ENV-2).
State, block builders/hints and paid-write bookkeeping retain their separate owners.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7.
-/

namespace STFSpec.Vm.Core
open STFSpec.Base

/-- The eleven VM-visible block fields; history guarantees belong to intended construction. -/
structure BlockEnvironment where
  /-- Supplied chain identifier. -/
  chainId : U64
  /-- Independent block gas limit. -/
  blockGasLimit : Nat
  /-- Complete ordered history array, without a raw length or ordering restriction. -/
  blockHashes : Array Hash32
  /-- Block beneficiary. -/
  coinbase : Address
  /-- Independent block number. -/
  number : Nat
  /-- Independent base fee. -/
  baseFeePerGas : Nat
  /-- Block timestamp as an EVM word. -/
  time : U256
  /-- Complete randomness bytes. -/
  prevRandao : Bytes32
  /-- Excess blob gas at its existing nominal width. -/
  excessBlobGas : U64
  /-- Complete parent beacon block root. -/
  parentBeaconBlockRoot : Hash32
  /-- Slot number at its existing nominal width. -/
  slotNumber : U64

/-- The sixteen VM-visible transaction fields, without extra admission conditions. -/
structure TransactionEnvironment where
  /-- Transaction origin, independent of recipient. -/
  origin : Address
  /-- Recipient, including the deployment address for creation. -/
  recipient : Address
  /-- Whether this transaction creates a contract. -/
  isCreate : Bool
  /-- Complete input bytes. -/
  data : Bytes
  /-- Supplied transaction value. -/
  value : U256
  /-- Independent transaction gas limit. -/
  gasLimit : Nat
  /-- Independent effective gas price. -/
  effectiveGasPrice : Nat
  /-- Independent execution gas grant. -/
  executionGasGrant : Nat
  /-- Independent state gas reservoir. -/
  stateGasReservoir : Nat
  /-- Independent calldata floor. -/
  calldataFloor : Nat
  /-- Supplied access-list address set. -/
  accessListAddresses : AddrSet
  /-- Supplied access-list address/storage-slot set. -/
  accessListStorageKeys : SlotSet
  /-- Complete ordered blob hash array, retaining duplicates. -/
  blobVersionedHashes : Array VersionedHash
  /-- Complete ordered authorization array, retaining every field and occurrence. -/
  authorizations : Array Authorization
  /-- Optional block index; absence differs from a present zero. -/
  indexInBlock : Option Nat
  /-- Optional transaction hash; absence differs from a present zero hash. -/
  txHash : Option Hash32

end STFSpec.Vm.Core
