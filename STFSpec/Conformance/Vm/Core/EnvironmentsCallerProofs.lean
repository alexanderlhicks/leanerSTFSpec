/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Complete raw environment clients

Library `EthConformance`. Private public-facade clients check complete constructor
signatures, every projection and reconstruction. Independent updates retain all
unrelated fields, without a context, admission, history or gas-policy premise.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7.
-/

namespace STFSpec.Conformance.Vm.Core.EnvironmentsCallerProofs
open STFSpec.Vm.Core STFSpec.Base

private theorem block_constructor (chainId : U64) (blockGasLimit : Nat)
    (blockHashes : Array Hash32) (coinbase : Address) (number baseFeePerGas : Nat)
    (time : U256) (prevRandao : Bytes32) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Hash32) (slotNumber : U64) :
    let e := BlockEnvironment.mk chainId blockGasLimit blockHashes coinbase number
      baseFeePerGas time prevRandao excessBlobGas parentBeaconBlockRoot slotNumber
    (e.chainId, e.blockGasLimit, e.blockHashes, e.coinbase, e.number, e.baseFeePerGas,
      e.time, e.prevRandao, e.excessBlobGas, e.parentBeaconBlockRoot, e.slotNumber) =
      (chainId, blockGasLimit, blockHashes, coinbase, number, baseFeePerGas,
        time, prevRandao, excessBlobGas, parentBeaconBlockRoot, slotNumber) := by
  rfl

private theorem block_reconstruct (e : BlockEnvironment) :
    BlockEnvironment.mk e.chainId e.blockGasLimit e.blockHashes e.coinbase e.number
      e.baseFeePerGas e.time e.prevRandao e.excessBlobGas e.parentBeaconBlockRoot e.slotNumber =
        e := by
  rfl

private theorem transaction_constructor (origin recipient : Address) (isCreate : Bool)
    (data : Bytes) (value : U256)
    (gasLimit effectiveGasPrice executionGasGrant stateGasReservoir calldataFloor : Nat)
    (accessListAddresses : AddrSet) (accessListStorageKeys : SlotSet)
    (blobVersionedHashes : Array VersionedHash) (authorizations : Array Authorization)
    (indexInBlock : Option Nat) (txHash : Option Hash32) :
    let e := TransactionEnvironment.mk origin recipient isCreate data value gasLimit
      effectiveGasPrice executionGasGrant stateGasReservoir calldataFloor accessListAddresses
      accessListStorageKeys blobVersionedHashes authorizations indexInBlock txHash
    (e.origin, e.recipient, e.isCreate, e.data, e.value, e.gasLimit, e.effectiveGasPrice,
      e.executionGasGrant, e.stateGasReservoir, e.calldataFloor, e.accessListAddresses,
      e.accessListStorageKeys, e.blobVersionedHashes, e.authorizations, e.indexInBlock, e.txHash) =
      (origin, recipient, isCreate, data, value, gasLimit, effectiveGasPrice,
        executionGasGrant, stateGasReservoir, calldataFloor, accessListAddresses,
        accessListStorageKeys, blobVersionedHashes, authorizations, indexInBlock, txHash) := by
  rfl

private theorem transaction_reconstruct (e : TransactionEnvironment) :
    TransactionEnvironment.mk e.origin e.recipient e.isCreate e.data e.value e.gasLimit
      e.effectiveGasPrice e.executionGasGrant e.stateGasReservoir e.calldataFloor
      e.accessListAddresses e.accessListStorageKeys e.blobVersionedHashes e.authorizations
      e.indexInBlock e.txHash = e := by
  rfl

private theorem replace_history (e : BlockEnvironment) (hashes : Array Hash32) :
    { e with blockHashes := hashes } =
      BlockEnvironment.mk e.chainId e.blockGasLimit hashes e.coinbase e.number
        e.baseFeePerGas e.time e.prevRandao e.excessBlobGas e.parentBeaconBlockRoot
        e.slotNumber := by
  rfl

private theorem replace_block_metadata (e : BlockEnvironment) (coinbase : Address)
    (number baseFee : Nat) (time : U256) (random : Bytes32) (excess slot : U64) (root : Hash32) :
    { e with
      coinbase := coinbase
      number := number
      baseFeePerGas := baseFee
      time := time
      prevRandao := random
      excessBlobGas := excess
      parentBeaconBlockRoot := root
      slotNumber := slot } =
      BlockEnvironment.mk e.chainId e.blockGasLimit e.blockHashes coinbase number baseFee
        time random excess root slot := by
  rfl

private theorem replace_gas_limit (e : TransactionEnvironment) (n : Nat) :
    { e with gasLimit := n } =
      TransactionEnvironment.mk e.origin e.recipient e.isCreate e.data e.value n
        e.effectiveGasPrice e.executionGasGrant e.stateGasReservoir e.calldataFloor
        e.accessListAddresses e.accessListStorageKeys e.blobVersionedHashes e.authorizations
        e.indexInBlock e.txHash := by
  rfl

private theorem replace_price (e : TransactionEnvironment) (n : Nat) :
    { e with effectiveGasPrice := n } =
      TransactionEnvironment.mk e.origin e.recipient e.isCreate e.data e.value e.gasLimit
        n e.executionGasGrant e.stateGasReservoir e.calldataFloor
        e.accessListAddresses e.accessListStorageKeys e.blobVersionedHashes e.authorizations
        e.indexInBlock e.txHash := by
  rfl

private theorem replace_execution_grant (e : TransactionEnvironment) (n : Nat) :
    { e with executionGasGrant := n } =
      TransactionEnvironment.mk e.origin e.recipient e.isCreate e.data e.value e.gasLimit
        e.effectiveGasPrice n e.stateGasReservoir e.calldataFloor
        e.accessListAddresses e.accessListStorageKeys e.blobVersionedHashes e.authorizations
        e.indexInBlock e.txHash := by
  rfl

private theorem replace_state_reservoir (e : TransactionEnvironment) (n : Nat) :
    { e with stateGasReservoir := n } =
      TransactionEnvironment.mk e.origin e.recipient e.isCreate e.data e.value e.gasLimit
        e.effectiveGasPrice e.executionGasGrant n e.calldataFloor
        e.accessListAddresses e.accessListStorageKeys e.blobVersionedHashes e.authorizations
        e.indexInBlock e.txHash := by
  rfl

private theorem replace_floor (e : TransactionEnvironment) (n : Nat) :
    { e with calldataFloor := n } =
      TransactionEnvironment.mk e.origin e.recipient e.isCreate e.data e.value e.gasLimit
        e.effectiveGasPrice e.executionGasGrant e.stateGasReservoir n
        e.accessListAddresses e.accessListStorageKeys e.blobVersionedHashes e.authorizations
        e.indexInBlock e.txHash := by
  rfl

private theorem replace_origin (e : TransactionEnvironment) (a : Address) :
    { e with origin := a } =
      TransactionEnvironment.mk a e.recipient e.isCreate e.data e.value e.gasLimit
        e.effectiveGasPrice e.executionGasGrant e.stateGasReservoir e.calldataFloor
        e.accessListAddresses e.accessListStorageKeys e.blobVersionedHashes e.authorizations
        e.indexInBlock e.txHash := by
  rfl

private theorem replace_recipient (e : TransactionEnvironment) (a : Address) :
    { e with recipient := a } =
      TransactionEnvironment.mk e.origin a e.isCreate e.data e.value e.gasLimit
        e.effectiveGasPrice e.executionGasGrant e.stateGasReservoir e.calldataFloor
        e.accessListAddresses e.accessListStorageKeys e.blobVersionedHashes e.authorizations
        e.indexInBlock e.txHash := by
  rfl

private theorem replace_transaction_metadata (e : TransactionEnvironment)
    (create : Bool) (data : Bytes) (value : U256) (addresses : AddrSet) (slots : SlotSet)
    (hashes : Array VersionedHash) (auths : Array Authorization)
    (index : Option Nat) (hash : Option Hash32) :
    { e with
      isCreate := create
      data := data
      value := value
      accessListAddresses := addresses
      accessListStorageKeys := slots
      blobVersionedHashes := hashes
      authorizations := auths
      indexInBlock := index
      txHash := hash } =
      TransactionEnvironment.mk e.origin e.recipient create data value e.gasLimit
        e.effectiveGasPrice e.executionGasGrant e.stateGasReservoir e.calldataFloor
        addresses slots hashes auths index hash := by
  rfl

end STFSpec.Conformance.Vm.Core.EnvironmentsCallerProofs
