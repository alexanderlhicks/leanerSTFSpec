/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block.Header
import STFSpec.Codec.RlpEncodeOf

/-!
# Header RLP models

Library `EthBlock`. These intentionally public models preserve every raw field
in source order. Numeric fields use minimal unsigned bytes; fixed byte fields
keep their full widths. Encoding adds no validation or hashing.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3–7.
-/

namespace STFSpec.Block

open STFSpec.Codec

/-- Ordered raw header model; EELS `src/ethereum/forks/amsterdam/blocks.py:72–270`
and locked `ethereum_rlp/rlp.py:66–135` (0.1.6). All raw fields are admitted. -/
instance Header.instRlpEncode : RlpEncode Header where
  toRlp h := .list [
    .bytes h.parentHash.toBytes.toByteArray,
    .bytes h.ommersHash.toBytes.toByteArray,
    .bytes h.coinbase.toBytes.toByteArray,
    .bytes h.stateRoot.toBytes.toByteArray,
    .bytes h.transactionsRoot.toBytes.toByteArray,
    .bytes h.receiptRoot.toBytes.toByteArray,
    .bytes h.bloom.toBytes.toByteArray,
    Rlp.ofNat h.difficulty,
    Rlp.ofNat h.number,
    Rlp.ofNat h.gasLimit,
    Rlp.ofNat h.gasUsed,
    Rlp.ofNat h.timestamp.toNat,
    .bytes h.extraData.toByteArray,
    .bytes h.prevRandao.toBytes.toByteArray,
    .bytes h.nonce.toBytes.toByteArray,
    Rlp.ofNat h.baseFeePerGas,
    .bytes h.withdrawalsRoot.toBytes.toByteArray,
    Rlp.ofNat h.blobGasUsed.toNat,
    Rlp.ofNat h.excessBlobGas.toNat,
    .bytes h.parentBeaconBlockRoot.toBytes.toByteArray,
    .bytes h.requestsHash.toBytes.toByteArray,
    .bytes h.blockAccessListHash.toBytes.toByteArray,
    Rlp.ofNat h.slotNumber.toNat]

/-- Ordered raw header model; EELS `src/ethereum/forks/bpo5/blocks.py:71–247`
and locked `ethereum_rlp/rlp.py:66–135` (0.1.6). All raw fields are admitted. -/
instance PrevHeader.instRlpEncode : RlpEncode PrevHeader where
  toRlp h := .list [
    .bytes h.parentHash.toBytes.toByteArray,
    .bytes h.ommersHash.toBytes.toByteArray,
    .bytes h.coinbase.toBytes.toByteArray,
    .bytes h.stateRoot.toBytes.toByteArray,
    .bytes h.transactionsRoot.toBytes.toByteArray,
    .bytes h.receiptRoot.toBytes.toByteArray,
    .bytes h.bloom.toBytes.toByteArray,
    Rlp.ofNat h.difficulty,
    Rlp.ofNat h.number,
    Rlp.ofNat h.gasLimit,
    Rlp.ofNat h.gasUsed,
    Rlp.ofNat h.timestamp.toNat,
    .bytes h.extraData.toByteArray,
    .bytes h.prevRandao.toBytes.toByteArray,
    .bytes h.nonce.toBytes.toByteArray,
    Rlp.ofNat h.baseFeePerGas,
    .bytes h.withdrawalsRoot.toBytes.toByteArray,
    Rlp.ofNat h.blobGasUsed.toNat,
    Rlp.ofNat h.excessBlobGas.toNat,
    .bytes h.parentBeaconBlockRoot.toBytes.toByteArray,
    .bytes h.requestsHash.toBytes.toByteArray]

/-- Re-encode the supplied parent variant; EELS
`src/ethereum/forks/amsterdam/fork.py:149,425,476`. No variant tag is emitted. -/
instance ParentHeader.instRlpEncode : RlpEncode ParentHeader where
  toRlp
    | .amsterdam h => RlpEncode.toRlp h
    | .bpo5 h => RlpEncode.toRlp h

end STFSpec.Block
