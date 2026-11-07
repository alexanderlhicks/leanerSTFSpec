/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block

/-!
# Public raw header clients

Library `EthConformance`. Arbitrary complete construction, projection,
reconstruction and independent field updates use the public Block facade.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3–7.
-/

open STFSpec.Base STFSpec.Block

private def headerConstructorType :
    Hash32 → Hash32 → Address → Root → Root → Root → Bloom → Nat → Nat → Nat → Nat → U256 → Bytes →
      Bytes32 → Bytes8 → Nat → Root → U64 → U64 → Root → Hash32 → Hash32 → U64 → Header :=
      Header.mk

private def header_parentHash_type : Header → Hash32 := Header.parentHash
private def header_ommersHash_type : Header → Hash32 := Header.ommersHash
private def header_coinbase_type : Header → Address := Header.coinbase
private def header_stateRoot_type : Header → Root := Header.stateRoot
private def header_transactionsRoot_type : Header → Root := Header.transactionsRoot
private def header_receiptRoot_type : Header → Root := Header.receiptRoot
private def header_bloom_type : Header → Bloom := Header.bloom
private def header_difficulty_type : Header → Nat := Header.difficulty
private def header_number_type : Header → Nat := Header.number
private def header_gasLimit_type : Header → Nat := Header.gasLimit
private def header_gasUsed_type : Header → Nat := Header.gasUsed
private def header_timestamp_type : Header → U256 := Header.timestamp
private def header_extraData_type : Header → Bytes := Header.extraData
private def header_prevRandao_type : Header → Bytes32 := Header.prevRandao
private def header_nonce_type : Header → Bytes8 := Header.nonce
private def header_baseFeePerGas_type : Header → Nat := Header.baseFeePerGas
private def header_withdrawalsRoot_type : Header → Root := Header.withdrawalsRoot
private def header_blobGasUsed_type : Header → U64 := Header.blobGasUsed
private def header_excessBlobGas_type : Header → U64 := Header.excessBlobGas
private def header_parentBeaconBlockRoot_type : Header → Root := Header.parentBeaconBlockRoot
private def header_requestsHash_type : Header → Hash32 := Header.requestsHash
private def header_blockAccessListHash_type : Header → Hash32 := Header.blockAccessListHash
private def header_slotNumber_type : Header → U64 := Header.slotNumber

private theorem header_parentHash_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) (blockAccessListHash : Hash32)
    (slotNumber : U64) :
    (Header.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash
      blockAccessListHash slotNumber).parentHash = parentHash := rfl

private theorem header_ommersHash_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) (blockAccessListHash : Hash32)
    (slotNumber : U64) :
    (Header.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash
      blockAccessListHash slotNumber).ommersHash = ommersHash := rfl

private theorem header_coinbase_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) (blockAccessListHash : Hash32)
    (slotNumber : U64) :
    (Header.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash
      blockAccessListHash slotNumber).coinbase = coinbase := rfl

private theorem header_stateRoot_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) (blockAccessListHash : Hash32)
    (slotNumber : U64) :
    (Header.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash
      blockAccessListHash slotNumber).stateRoot = stateRoot := rfl

private theorem header_transactionsRoot_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) (blockAccessListHash : Hash32)
    (slotNumber : U64) :
    (Header.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash
      blockAccessListHash slotNumber).transactionsRoot = transactionsRoot := rfl

private theorem header_receiptRoot_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) (blockAccessListHash : Hash32)
    (slotNumber : U64) :
    (Header.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash
      blockAccessListHash slotNumber).receiptRoot = receiptRoot := rfl

private theorem header_bloom_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) (blockAccessListHash : Hash32)
    (slotNumber : U64) :
    (Header.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash
      blockAccessListHash slotNumber).bloom = bloom := rfl

private theorem header_difficulty_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) (blockAccessListHash : Hash32)
    (slotNumber : U64) :
    (Header.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash
      blockAccessListHash slotNumber).difficulty = difficulty := rfl

private theorem header_number_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) (blockAccessListHash : Hash32)
    (slotNumber : U64) :
    (Header.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash
      blockAccessListHash slotNumber).number = number := rfl

private theorem header_gasLimit_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) (blockAccessListHash : Hash32)
    (slotNumber : U64) :
    (Header.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash
      blockAccessListHash slotNumber).gasLimit = gasLimit := rfl

private theorem header_gasUsed_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) (blockAccessListHash : Hash32)
    (slotNumber : U64) :
    (Header.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash
      blockAccessListHash slotNumber).gasUsed = gasUsed := rfl

private theorem header_timestamp_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) (blockAccessListHash : Hash32)
    (slotNumber : U64) :
    (Header.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash
      blockAccessListHash slotNumber).timestamp = timestamp := rfl

private theorem header_extraData_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) (blockAccessListHash : Hash32)
    (slotNumber : U64) :
    (Header.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash
      blockAccessListHash slotNumber).extraData = extraData := rfl

private theorem header_prevRandao_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) (blockAccessListHash : Hash32)
    (slotNumber : U64) :
    (Header.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash
      blockAccessListHash slotNumber).prevRandao = prevRandao := rfl

private theorem header_nonce_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) (blockAccessListHash : Hash32)
    (slotNumber : U64) :
    (Header.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash
      blockAccessListHash slotNumber).nonce = nonce := rfl

private theorem header_baseFeePerGas_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) (blockAccessListHash : Hash32)
    (slotNumber : U64) :
    (Header.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash
      blockAccessListHash slotNumber).baseFeePerGas = baseFeePerGas := rfl

private theorem header_withdrawalsRoot_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) (blockAccessListHash : Hash32)
    (slotNumber : U64) :
    (Header.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash
      blockAccessListHash slotNumber).withdrawalsRoot = withdrawalsRoot := rfl

private theorem header_blobGasUsed_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) (blockAccessListHash : Hash32)
    (slotNumber : U64) :
    (Header.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash
      blockAccessListHash slotNumber).blobGasUsed = blobGasUsed := rfl

private theorem header_excessBlobGas_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) (blockAccessListHash : Hash32)
    (slotNumber : U64) :
    (Header.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash
      blockAccessListHash slotNumber).excessBlobGas = excessBlobGas := rfl

private theorem header_parentBeaconBlockRoot_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) (blockAccessListHash : Hash32)
    (slotNumber : U64) :
    (Header.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash
      blockAccessListHash slotNumber).parentBeaconBlockRoot = parentBeaconBlockRoot := rfl

private theorem header_requestsHash_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) (blockAccessListHash : Hash32)
    (slotNumber : U64) :
    (Header.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash
      blockAccessListHash slotNumber).requestsHash = requestsHash := rfl

private theorem header_blockAccessListHash_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) (blockAccessListHash : Hash32)
    (slotNumber : U64) :
    (Header.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash
      blockAccessListHash slotNumber).blockAccessListHash = blockAccessListHash := rfl

private theorem header_slotNumber_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) (blockAccessListHash : Hash32)
    (slotNumber : U64) :
    (Header.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash
      blockAccessListHash slotNumber).slotNumber = slotNumber := rfl

private theorem header_reconstruct (h : Header) :
    Header.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot h.receiptRoot
      h.bloom h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData h.prevRandao
      h.nonce h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas
      h.parentBeaconBlockRoot h.requestsHash h.blockAccessListHash h.slotNumber = h := rfl

private theorem header_update_parentHash (h : Header) (value : Hash32) :
    { h with parentHash := value } =
      Header.mk value h.ommersHash h.coinbase h.stateRoot h.transactionsRoot h.receiptRoot h.bloom
      h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData h.prevRandao h.nonce
      h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas h.parentBeaconBlockRoot
      h.requestsHash h.blockAccessListHash h.slotNumber := rfl

private theorem header_update_ommersHash (h : Header) (value : Hash32) :
    { h with ommersHash := value } =
      Header.mk h.parentHash value h.coinbase h.stateRoot h.transactionsRoot h.receiptRoot h.bloom
      h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData h.prevRandao h.nonce
      h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas h.parentBeaconBlockRoot
      h.requestsHash h.blockAccessListHash h.slotNumber := rfl

private theorem header_update_coinbase (h : Header) (value : Address) :
    { h with coinbase := value } =
      Header.mk h.parentHash h.ommersHash value h.stateRoot h.transactionsRoot h.receiptRoot
      h.bloom h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData h.prevRandao
      h.nonce h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas
      h.parentBeaconBlockRoot h.requestsHash h.blockAccessListHash h.slotNumber := rfl

private theorem header_update_stateRoot (h : Header) (value : Root) :
    { h with stateRoot := value } =
      Header.mk h.parentHash h.ommersHash h.coinbase value h.transactionsRoot h.receiptRoot h.bloom
      h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData h.prevRandao h.nonce
      h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas h.parentBeaconBlockRoot
      h.requestsHash h.blockAccessListHash h.slotNumber := rfl

private theorem header_update_transactionsRoot (h : Header) (value : Root) :
    { h with transactionsRoot := value } =
      Header.mk h.parentHash h.ommersHash h.coinbase h.stateRoot value h.receiptRoot h.bloom
      h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData h.prevRandao h.nonce
      h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas h.parentBeaconBlockRoot
      h.requestsHash h.blockAccessListHash h.slotNumber := rfl

private theorem header_update_receiptRoot (h : Header) (value : Root) :
    { h with receiptRoot := value } =
      Header.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot value h.bloom
      h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData h.prevRandao h.nonce
      h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas h.parentBeaconBlockRoot
      h.requestsHash h.blockAccessListHash h.slotNumber := rfl

private theorem header_update_bloom (h : Header) (value : Bloom) :
    { h with bloom := value } =
      Header.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot h.receiptRoot
      value h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData h.prevRandao h.nonce
      h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas h.parentBeaconBlockRoot
      h.requestsHash h.blockAccessListHash h.slotNumber := rfl

private theorem header_update_difficulty (h : Header) (value : Nat) :
    { h with difficulty := value } =
      Header.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot h.receiptRoot
      h.bloom value h.number h.gasLimit h.gasUsed h.timestamp h.extraData h.prevRandao h.nonce
      h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas h.parentBeaconBlockRoot
      h.requestsHash h.blockAccessListHash h.slotNumber := rfl

private theorem header_update_number (h : Header) (value : Nat) :
    { h with number := value } =
      Header.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot h.receiptRoot
      h.bloom h.difficulty value h.gasLimit h.gasUsed h.timestamp h.extraData h.prevRandao h.nonce
      h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas h.parentBeaconBlockRoot
      h.requestsHash h.blockAccessListHash h.slotNumber := rfl

private theorem header_update_gasLimit (h : Header) (value : Nat) :
    { h with gasLimit := value } =
      Header.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot h.receiptRoot
      h.bloom h.difficulty h.number value h.gasUsed h.timestamp h.extraData h.prevRandao h.nonce
      h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas h.parentBeaconBlockRoot
      h.requestsHash h.blockAccessListHash h.slotNumber := rfl

private theorem header_update_gasUsed (h : Header) (value : Nat) :
    { h with gasUsed := value } =
      Header.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot h.receiptRoot
      h.bloom h.difficulty h.number h.gasLimit value h.timestamp h.extraData h.prevRandao h.nonce
      h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas h.parentBeaconBlockRoot
      h.requestsHash h.blockAccessListHash h.slotNumber := rfl

private theorem header_update_timestamp (h : Header) (value : U256) :
    { h with timestamp := value } =
      Header.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot h.receiptRoot
      h.bloom h.difficulty h.number h.gasLimit h.gasUsed value h.extraData h.prevRandao h.nonce
      h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas h.parentBeaconBlockRoot
      h.requestsHash h.blockAccessListHash h.slotNumber := rfl

private theorem header_update_extraData (h : Header) (value : Bytes) :
    { h with extraData := value } =
      Header.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot h.receiptRoot
      h.bloom h.difficulty h.number h.gasLimit h.gasUsed h.timestamp value h.prevRandao h.nonce
      h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas h.parentBeaconBlockRoot
      h.requestsHash h.blockAccessListHash h.slotNumber := rfl

private theorem header_update_prevRandao (h : Header) (value : Bytes32) :
    { h with prevRandao := value } =
      Header.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot h.receiptRoot
      h.bloom h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData value h.nonce
      h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas h.parentBeaconBlockRoot
      h.requestsHash h.blockAccessListHash h.slotNumber := rfl

private theorem header_update_nonce (h : Header) (value : Bytes8) :
    { h with nonce := value } =
      Header.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot h.receiptRoot
      h.bloom h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData h.prevRandao value
      h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas h.parentBeaconBlockRoot
      h.requestsHash h.blockAccessListHash h.slotNumber := rfl

private theorem header_update_baseFeePerGas (h : Header) (value : Nat) :
    { h with baseFeePerGas := value } =
      Header.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot h.receiptRoot
      h.bloom h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData h.prevRandao
      h.nonce value h.withdrawalsRoot h.blobGasUsed h.excessBlobGas h.parentBeaconBlockRoot
      h.requestsHash h.blockAccessListHash h.slotNumber := rfl

private theorem header_update_withdrawalsRoot (h : Header) (value : Root) :
    { h with withdrawalsRoot := value } =
      Header.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot h.receiptRoot
      h.bloom h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData h.prevRandao
      h.nonce h.baseFeePerGas value h.blobGasUsed h.excessBlobGas h.parentBeaconBlockRoot
      h.requestsHash h.blockAccessListHash h.slotNumber := rfl

private theorem header_update_blobGasUsed (h : Header) (value : U64) :
    { h with blobGasUsed := value } =
      Header.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot h.receiptRoot
      h.bloom h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData h.prevRandao
      h.nonce h.baseFeePerGas h.withdrawalsRoot value h.excessBlobGas h.parentBeaconBlockRoot
      h.requestsHash h.blockAccessListHash h.slotNumber := rfl

private theorem header_update_excessBlobGas (h : Header) (value : U64) :
    { h with excessBlobGas := value } =
      Header.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot h.receiptRoot
      h.bloom h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData h.prevRandao
      h.nonce h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed value h.parentBeaconBlockRoot
      h.requestsHash h.blockAccessListHash h.slotNumber := rfl

private theorem header_update_parentBeaconBlockRoot (h : Header) (value : Root) :
    { h with parentBeaconBlockRoot := value } =
      Header.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot h.receiptRoot
      h.bloom h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData h.prevRandao
      h.nonce h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas value h.requestsHash
      h.blockAccessListHash h.slotNumber := rfl

private theorem header_update_requestsHash (h : Header) (value : Hash32) :
    { h with requestsHash := value } =
      Header.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot h.receiptRoot
      h.bloom h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData h.prevRandao
      h.nonce h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas
      h.parentBeaconBlockRoot value h.blockAccessListHash h.slotNumber := rfl

private theorem header_update_blockAccessListHash (h : Header) (value : Hash32) :
    { h with blockAccessListHash := value } =
      Header.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot h.receiptRoot
      h.bloom h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData h.prevRandao
      h.nonce h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas
      h.parentBeaconBlockRoot h.requestsHash value h.slotNumber := rfl

private theorem header_update_slotNumber (h : Header) (value : U64) :
    { h with slotNumber := value } =
      Header.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot h.receiptRoot
      h.bloom h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData h.prevRandao
      h.nonce h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas
      h.parentBeaconBlockRoot h.requestsHash h.blockAccessListHash value := rfl

private def prevHeaderConstructorType :
    Hash32 → Hash32 → Address → Root → Root → Root → Bloom → Nat → Nat → Nat → Nat → U256 → Bytes →
      Bytes32 → Bytes8 → Nat → Root → U64 → U64 → Root → Hash32 → PrevHeader := PrevHeader.mk

private def prevHeader_parentHash_type : PrevHeader → Hash32 := PrevHeader.parentHash
private def prevHeader_ommersHash_type : PrevHeader → Hash32 := PrevHeader.ommersHash
private def prevHeader_coinbase_type : PrevHeader → Address := PrevHeader.coinbase
private def prevHeader_stateRoot_type : PrevHeader → Root := PrevHeader.stateRoot
private def prevHeader_transactionsRoot_type : PrevHeader → Root := PrevHeader.transactionsRoot
private def prevHeader_receiptRoot_type : PrevHeader → Root := PrevHeader.receiptRoot
private def prevHeader_bloom_type : PrevHeader → Bloom := PrevHeader.bloom
private def prevHeader_difficulty_type : PrevHeader → Nat := PrevHeader.difficulty
private def prevHeader_number_type : PrevHeader → Nat := PrevHeader.number
private def prevHeader_gasLimit_type : PrevHeader → Nat := PrevHeader.gasLimit
private def prevHeader_gasUsed_type : PrevHeader → Nat := PrevHeader.gasUsed
private def prevHeader_timestamp_type : PrevHeader → U256 := PrevHeader.timestamp
private def prevHeader_extraData_type : PrevHeader → Bytes := PrevHeader.extraData
private def prevHeader_prevRandao_type : PrevHeader → Bytes32 := PrevHeader.prevRandao
private def prevHeader_nonce_type : PrevHeader → Bytes8 := PrevHeader.nonce
private def prevHeader_baseFeePerGas_type : PrevHeader → Nat := PrevHeader.baseFeePerGas
private def prevHeader_withdrawalsRoot_type : PrevHeader → Root := PrevHeader.withdrawalsRoot
private def prevHeader_blobGasUsed_type : PrevHeader → U64 := PrevHeader.blobGasUsed
private def prevHeader_excessBlobGas_type : PrevHeader → U64 := PrevHeader.excessBlobGas
private def prevHeader_parentBeaconBlockRoot_type : PrevHeader → Root :=
      PrevHeader.parentBeaconBlockRoot
private def prevHeader_requestsHash_type : PrevHeader → Hash32 := PrevHeader.requestsHash

private theorem prevHeader_parentHash_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) :
    (PrevHeader.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash).parentHash =
      parentHash := rfl

private theorem prevHeader_ommersHash_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) :
    (PrevHeader.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash).ommersHash =
      ommersHash := rfl

private theorem prevHeader_coinbase_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) :
    (PrevHeader.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash).coinbase =
      coinbase := rfl

private theorem prevHeader_stateRoot_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) :
    (PrevHeader.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash).stateRoot =
      stateRoot := rfl

private theorem prevHeader_transactionsRoot_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) :
    (PrevHeader.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot
      requestsHash).transactionsRoot = transactionsRoot := rfl

private theorem prevHeader_receiptRoot_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) :
    (PrevHeader.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash).receiptRoot =
      receiptRoot := rfl

private theorem prevHeader_bloom_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) :
    (PrevHeader.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash).bloom =
      bloom := rfl

private theorem prevHeader_difficulty_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) :
    (PrevHeader.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash).difficulty =
      difficulty := rfl

private theorem prevHeader_number_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) :
    (PrevHeader.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash).number =
      number := rfl

private theorem prevHeader_gasLimit_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) :
    (PrevHeader.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash).gasLimit =
      gasLimit := rfl

private theorem prevHeader_gasUsed_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) :
    (PrevHeader.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash).gasUsed =
      gasUsed := rfl

private theorem prevHeader_timestamp_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) :
    (PrevHeader.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash).timestamp =
      timestamp := rfl

private theorem prevHeader_extraData_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) :
    (PrevHeader.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash).extraData =
      extraData := rfl

private theorem prevHeader_prevRandao_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) :
    (PrevHeader.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash).prevRandao =
      prevRandao := rfl

private theorem prevHeader_nonce_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) :
    (PrevHeader.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash).nonce =
      nonce := rfl

private theorem prevHeader_baseFeePerGas_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) :
    (PrevHeader.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash).baseFeePerGas =
      baseFeePerGas := rfl

private theorem prevHeader_withdrawalsRoot_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) :
    (PrevHeader.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot
      requestsHash).withdrawalsRoot = withdrawalsRoot := rfl

private theorem prevHeader_blobGasUsed_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) :
    (PrevHeader.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash).blobGasUsed =
      blobGasUsed := rfl

private theorem prevHeader_excessBlobGas_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) :
    (PrevHeader.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash).excessBlobGas =
      excessBlobGas := rfl

private theorem prevHeader_parentBeaconBlockRoot_projection (parentHash : Hash32)
    (ommersHash : Hash32) (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root)
    (receiptRoot : Root) (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat)
    (gasUsed : Nat) (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) :
    (PrevHeader.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot
      requestsHash).parentBeaconBlockRoot = parentBeaconBlockRoot := rfl

private theorem prevHeader_requestsHash_projection (parentHash : Hash32) (ommersHash : Hash32)
    (coinbase : Address) (stateRoot : Root) (transactionsRoot : Root) (receiptRoot : Root)
    (bloom : Bloom) (difficulty : Nat) (number : Nat) (gasLimit : Nat) (gasUsed : Nat)
    (timestamp : U256) (extraData : Bytes) (prevRandao : Bytes32) (nonce : Bytes8)
    (baseFeePerGas : Nat) (withdrawalsRoot : Root) (blobGasUsed : U64) (excessBlobGas : U64)
    (parentBeaconBlockRoot : Root) (requestsHash : Hash32) :
    (PrevHeader.mk parentHash ommersHash coinbase stateRoot transactionsRoot receiptRoot bloom
      difficulty number gasLimit gasUsed timestamp extraData prevRandao nonce baseFeePerGas
      withdrawalsRoot blobGasUsed excessBlobGas parentBeaconBlockRoot requestsHash).requestsHash =
      requestsHash := rfl

private theorem prevHeader_reconstruct (h : PrevHeader) :
    PrevHeader.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot h.receiptRoot
      h.bloom h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData h.prevRandao
      h.nonce h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas
      h.parentBeaconBlockRoot h.requestsHash = h := rfl

private theorem prevHeader_update_parentHash (h : PrevHeader) (value : Hash32) :
    { h with parentHash := value } =
      PrevHeader.mk value h.ommersHash h.coinbase h.stateRoot h.transactionsRoot h.receiptRoot
      h.bloom h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData h.prevRandao
      h.nonce h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas
      h.parentBeaconBlockRoot h.requestsHash := rfl

private theorem prevHeader_update_ommersHash (h : PrevHeader) (value : Hash32) :
    { h with ommersHash := value } =
      PrevHeader.mk h.parentHash value h.coinbase h.stateRoot h.transactionsRoot h.receiptRoot
      h.bloom h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData h.prevRandao
      h.nonce h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas
      h.parentBeaconBlockRoot h.requestsHash := rfl

private theorem prevHeader_update_coinbase (h : PrevHeader) (value : Address) :
    { h with coinbase := value } =
      PrevHeader.mk h.parentHash h.ommersHash value h.stateRoot h.transactionsRoot h.receiptRoot
      h.bloom h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData h.prevRandao
      h.nonce h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas
      h.parentBeaconBlockRoot h.requestsHash := rfl

private theorem prevHeader_update_stateRoot (h : PrevHeader) (value : Root) :
    { h with stateRoot := value } =
      PrevHeader.mk h.parentHash h.ommersHash h.coinbase value h.transactionsRoot h.receiptRoot
      h.bloom h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData h.prevRandao
      h.nonce h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas
      h.parentBeaconBlockRoot h.requestsHash := rfl

private theorem prevHeader_update_transactionsRoot (h : PrevHeader) (value : Root) :
    { h with transactionsRoot := value } =
      PrevHeader.mk h.parentHash h.ommersHash h.coinbase h.stateRoot value h.receiptRoot h.bloom
      h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData h.prevRandao h.nonce
      h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas h.parentBeaconBlockRoot
      h.requestsHash := rfl

private theorem prevHeader_update_receiptRoot (h : PrevHeader) (value : Root) :
    { h with receiptRoot := value } =
      PrevHeader.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot value
      h.bloom h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData h.prevRandao
      h.nonce h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas
      h.parentBeaconBlockRoot h.requestsHash := rfl

private theorem prevHeader_update_bloom (h : PrevHeader) (value : Bloom) :
    { h with bloom := value } =
      PrevHeader.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot
      h.receiptRoot value h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData
      h.prevRandao h.nonce h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas
      h.parentBeaconBlockRoot h.requestsHash := rfl

private theorem prevHeader_update_difficulty (h : PrevHeader) (value : Nat) :
    { h with difficulty := value } =
      PrevHeader.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot
      h.receiptRoot h.bloom value h.number h.gasLimit h.gasUsed h.timestamp h.extraData
      h.prevRandao h.nonce h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas
      h.parentBeaconBlockRoot h.requestsHash := rfl

private theorem prevHeader_update_number (h : PrevHeader) (value : Nat) :
    { h with number := value } =
      PrevHeader.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot
      h.receiptRoot h.bloom h.difficulty value h.gasLimit h.gasUsed h.timestamp h.extraData
      h.prevRandao h.nonce h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas
      h.parentBeaconBlockRoot h.requestsHash := rfl

private theorem prevHeader_update_gasLimit (h : PrevHeader) (value : Nat) :
    { h with gasLimit := value } =
      PrevHeader.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot
      h.receiptRoot h.bloom h.difficulty h.number value h.gasUsed h.timestamp h.extraData
      h.prevRandao h.nonce h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas
      h.parentBeaconBlockRoot h.requestsHash := rfl

private theorem prevHeader_update_gasUsed (h : PrevHeader) (value : Nat) :
    { h with gasUsed := value } =
      PrevHeader.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot
      h.receiptRoot h.bloom h.difficulty h.number h.gasLimit value h.timestamp h.extraData
      h.prevRandao h.nonce h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas
      h.parentBeaconBlockRoot h.requestsHash := rfl

private theorem prevHeader_update_timestamp (h : PrevHeader) (value : U256) :
    { h with timestamp := value } =
      PrevHeader.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot
      h.receiptRoot h.bloom h.difficulty h.number h.gasLimit h.gasUsed value h.extraData
      h.prevRandao h.nonce h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas
      h.parentBeaconBlockRoot h.requestsHash := rfl

private theorem prevHeader_update_extraData (h : PrevHeader) (value : Bytes) :
    { h with extraData := value } =
      PrevHeader.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot
      h.receiptRoot h.bloom h.difficulty h.number h.gasLimit h.gasUsed h.timestamp value
      h.prevRandao h.nonce h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas
      h.parentBeaconBlockRoot h.requestsHash := rfl

private theorem prevHeader_update_prevRandao (h : PrevHeader) (value : Bytes32) :
    { h with prevRandao := value } =
      PrevHeader.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot
      h.receiptRoot h.bloom h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData
      value h.nonce h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas
      h.parentBeaconBlockRoot h.requestsHash := rfl

private theorem prevHeader_update_nonce (h : PrevHeader) (value : Bytes8) :
    { h with nonce := value } =
      PrevHeader.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot
      h.receiptRoot h.bloom h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData
      h.prevRandao value h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas
      h.parentBeaconBlockRoot h.requestsHash := rfl

private theorem prevHeader_update_baseFeePerGas (h : PrevHeader) (value : Nat) :
    { h with baseFeePerGas := value } =
      PrevHeader.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot
      h.receiptRoot h.bloom h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData
      h.prevRandao h.nonce value h.withdrawalsRoot h.blobGasUsed h.excessBlobGas
      h.parentBeaconBlockRoot h.requestsHash := rfl

private theorem prevHeader_update_withdrawalsRoot (h : PrevHeader) (value : Root) :
    { h with withdrawalsRoot := value } =
      PrevHeader.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot
      h.receiptRoot h.bloom h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData
      h.prevRandao h.nonce h.baseFeePerGas value h.blobGasUsed h.excessBlobGas
      h.parentBeaconBlockRoot h.requestsHash := rfl

private theorem prevHeader_update_blobGasUsed (h : PrevHeader) (value : U64) :
    { h with blobGasUsed := value } =
      PrevHeader.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot
      h.receiptRoot h.bloom h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData
      h.prevRandao h.nonce h.baseFeePerGas h.withdrawalsRoot value h.excessBlobGas
      h.parentBeaconBlockRoot h.requestsHash := rfl

private theorem prevHeader_update_excessBlobGas (h : PrevHeader) (value : U64) :
    { h with excessBlobGas := value } =
      PrevHeader.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot
      h.receiptRoot h.bloom h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData
      h.prevRandao h.nonce h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed value
      h.parentBeaconBlockRoot h.requestsHash := rfl

private theorem prevHeader_update_parentBeaconBlockRoot (h : PrevHeader) (value : Root) :
    { h with parentBeaconBlockRoot := value } =
      PrevHeader.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot
      h.receiptRoot h.bloom h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData
      h.prevRandao h.nonce h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas value
      h.requestsHash := rfl

private theorem prevHeader_update_requestsHash (h : PrevHeader) (value : Hash32) :
    { h with requestsHash := value } =
      PrevHeader.mk h.parentHash h.ommersHash h.coinbase h.stateRoot h.transactionsRoot
      h.receiptRoot h.bloom h.difficulty h.number h.gasLimit h.gasUsed h.timestamp h.extraData
      h.prevRandao h.nonce h.baseFeePerGas h.withdrawalsRoot h.blobGasUsed h.excessBlobGas
      h.parentBeaconBlockRoot value := rfl

private def amsterdamConstructorType : Header → ParentHeader := ParentHeader.amsterdam
private def bpo5ConstructorType : PrevHeader → ParentHeader := ParentHeader.bpo5

private def parent_gasLimit_type : ParentHeader → Nat := ParentHeader.gasLimit
private theorem parent_gasLimit_amsterdam (h : Header) :
    ParentHeader.gasLimit (.amsterdam h) = h.gasLimit := rfl

private theorem parent_gasLimit_bpo5 (h : PrevHeader) :
    ParentHeader.gasLimit (.bpo5 h) = h.gasLimit := rfl

private def parent_gasUsed_type : ParentHeader → Nat := ParentHeader.gasUsed
private theorem parent_gasUsed_amsterdam (h : Header) :
    ParentHeader.gasUsed (.amsterdam h) = h.gasUsed := rfl

private theorem parent_gasUsed_bpo5 (h : PrevHeader) :
    ParentHeader.gasUsed (.bpo5 h) = h.gasUsed := rfl

private def parent_baseFeePerGas_type : ParentHeader → Nat := ParentHeader.baseFeePerGas
private theorem parent_baseFeePerGas_amsterdam (h : Header) :
    ParentHeader.baseFeePerGas (.amsterdam h) = h.baseFeePerGas := rfl

private theorem parent_baseFeePerGas_bpo5 (h : PrevHeader) :
    ParentHeader.baseFeePerGas (.bpo5 h) = h.baseFeePerGas := rfl

private def parent_timestamp_type : ParentHeader → U256 := ParentHeader.timestamp
private theorem parent_timestamp_amsterdam (h : Header) :
    ParentHeader.timestamp (.amsterdam h) = h.timestamp := rfl

private theorem parent_timestamp_bpo5 (h : PrevHeader) :
    ParentHeader.timestamp (.bpo5 h) = h.timestamp := rfl

private def parent_number_type : ParentHeader → Nat := ParentHeader.number
private theorem parent_number_amsterdam (h : Header) :
    ParentHeader.number (.amsterdam h) = h.number := rfl

private theorem parent_number_bpo5 (h : PrevHeader) :
    ParentHeader.number (.bpo5 h) = h.number := rfl

private def parent_stateRoot_type : ParentHeader → Root := ParentHeader.stateRoot
private theorem parent_stateRoot_amsterdam (h : Header) :
    ParentHeader.stateRoot (.amsterdam h) = h.stateRoot := rfl

private theorem parent_stateRoot_bpo5 (h : PrevHeader) :
    ParentHeader.stateRoot (.bpo5 h) = h.stateRoot := rfl

private def parent_excessBlobGas_type : ParentHeader → U64 := ParentHeader.excessBlobGas
private theorem parent_excessBlobGas_amsterdam (h : Header) :
    ParentHeader.excessBlobGas (.amsterdam h) = h.excessBlobGas := rfl

private theorem parent_excessBlobGas_bpo5 (h : PrevHeader) :
    ParentHeader.excessBlobGas (.bpo5 h) = h.excessBlobGas := rfl

private def parent_blobGasUsed_type : ParentHeader → U64 := ParentHeader.blobGasUsed
private theorem parent_blobGasUsed_amsterdam (h : Header) :
    ParentHeader.blobGasUsed (.amsterdam h) = h.blobGasUsed := rfl

private theorem parent_blobGasUsed_bpo5 (h : PrevHeader) :
    ParentHeader.blobGasUsed (.bpo5 h) = h.blobGasUsed := rfl

private def parent_parentHash_type : ParentHeader → Hash32 := ParentHeader.parentHash
private theorem parent_parentHash_amsterdam (h : Header) :
    ParentHeader.parentHash (.amsterdam h) = h.parentHash := rfl

private theorem parent_parentHash_bpo5 (h : PrevHeader) :
    ParentHeader.parentHash (.bpo5 h) = h.parentHash := rfl

private theorem parent_reconstruct (h : ParentHeader) :
    (match h with
      | .amsterdam value => ParentHeader.amsterdam value
      | .bpo5 value => ParentHeader.bpo5 value) = h := by
  cases h <;> rfl

private theorem variants_distinct (a : Header) (b : PrevHeader) :
    ParentHeader.amsterdam a ≠ ParentHeader.bpo5 b := by
  intro h
  cases h
