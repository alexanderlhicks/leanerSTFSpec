/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block.BlockAccessList
import STFSpec.Codec.RlpAddress
import STFSpec.Codec.RlpByteArray
import STFSpec.Codec.RlpList
import STFSpec.Codec.RlpNarrowUnsigned
import STFSpec.Codec.RlpU256

/-!
# Block access list RLP models

Library `EthBlock`. The six nominal models preserve the source field order and
all supplied entries. The outer array uses the existing ordered List model via
`toList`. Q47 governs standard wire correspondence.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§2.11, 3 and 5.
-/

namespace STFSpec.Block

open STFSpec.Codec

/-- Encode the index and new storage value in source order.
EELS `src/ethereum/forks/amsterdam/block_access_lists.py:34–55`. -/
instance StorageChange.instRlpEncode : RlpEncode StorageChange where
  toRlp change := .list [RlpEncode.toRlp change.blockAccessIndex, RlpEncode.toRlp change.newValue]

/-- Encode the index and post-change balance in source order.
EELS `src/ethereum/forks/amsterdam/block_access_lists.py:61–82`. -/
instance BalanceChange.instRlpEncode : RlpEncode BalanceChange where
  toRlp change := .list [RlpEncode.toRlp change.blockAccessIndex, RlpEncode.toRlp change.postBalance]

/-- Encode the index and new nonce in source order.
EELS `src/ethereum/forks/amsterdam/block_access_lists.py:88–109`. -/
instance NonceChange.instRlpEncode : RlpEncode NonceChange where
  toRlp change := .list [RlpEncode.toRlp change.blockAccessIndex, RlpEncode.toRlp change.newNonce]

/-- Encode the index and complete code byte string in source order.
EELS `src/ethereum/forks/amsterdam/block_access_lists.py:115–136`. -/
instance CodeChange.instRlpEncode : RlpEncode CodeChange where
  toRlp change := .list [RlpEncode.toRlp change.blockAccessIndex, RlpEncode.toRlp change.newCode]

/-- Encode the slot and the complete ordered storage changes.
EELS `src/ethereum/forks/amsterdam/block_access_lists.py:142–161`. -/
instance SlotChanges.instRlpEncode : RlpEncode SlotChanges where
  toRlp entry := .list [RlpEncode.toRlp entry.slot, RlpEncode.toRlp entry.changes]

/-- Encode all six account fields in source order.
EELS `src/ethereum/forks/amsterdam/block_access_lists.py:167–214`. -/
instance AccountChanges.instRlpEncode : RlpEncode AccountChanges where
  toRlp entry := .list [
    RlpEncode.toRlp entry.address,
    RlpEncode.toRlp entry.storageChanges,
    RlpEncode.toRlp entry.storageReads,
    RlpEncode.toRlp entry.balanceChanges,
    RlpEncode.toRlp entry.nonceChanges,
    RlpEncode.toRlp entry.codeChanges]

end STFSpec.Block
