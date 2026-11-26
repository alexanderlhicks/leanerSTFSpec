/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.FixedBytes
import STFSpec.Base.U32
import STFSpec.Base.U64
import STFSpec.Base.U256

/-!
# Raw block access list

Library `EthBlock`. The six records retain the supplied fields in source order,
including every nested entry and byte.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§2.11, 3 and 5.
-/

namespace STFSpec.Block

/-- Storage value at a block access index.
EELS `src/ethereum/forks/amsterdam/block_access_lists.py:34–59`. -/
structure StorageChange where
  blockAccessIndex : Base.U32
  newValue : Base.U256

/-- Balance at a block access index.
EELS `src/ethereum/forks/amsterdam/block_access_lists.py:61–86`. -/
structure BalanceChange where
  blockAccessIndex : Base.U32
  postBalance : Base.U256

/-- Nonce at a block access index.
EELS `src/ethereum/forks/amsterdam/block_access_lists.py:88–113`. -/
structure NonceChange where
  blockAccessIndex : Base.U32
  newNonce : Base.U64

/-- Code bytes at a block access index.
EELS `src/ethereum/forks/amsterdam/block_access_lists.py:115–140`. -/
structure CodeChange where
  blockAccessIndex : Base.U32
  newCode : ByteArray

/-- Supplied storage changes at a slot.
EELS `src/ethereum/forks/amsterdam/block_access_lists.py:142–165`. -/
structure SlotChanges where
  slot : Base.U256
  changes : List StorageChange

/-- Supplied account changes in source field order.
EELS `src/ethereum/forks/amsterdam/block_access_lists.py:167–214`. -/
structure AccountChanges where
  address : Base.Address
  storageChanges : List SlotChanges
  storageReads : List Base.U256
  balanceChanges : List BalanceChange
  nonceChanges : List NonceChange
  codeChanges : List CodeChange

/-- Ordered raw account entries.
EELS `src/ethereum/forks/amsterdam/block_access_lists.py:216`. -/
abbrev BlockAccessList := Array AccountChanges

end STFSpec.Block
