/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.BlockState

/-!
# Raw block-diff extraction

Library `EthState`: retain all four effect fields and transport the three B1
indexes through their existing ordered observer, preserving the slot-map domain.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/5/7 (Q85).
-/

namespace STFSpec.State

variable {m : Type → Type}

/-- Extract the complete raw effects without calling the provider.
EELS `src/ethereum/forks/amsterdam/state_tracker.py:880–900` copies the four
effect fields. Q85 transports supplied B1 metadata through `WriteOrder.toList`,
including malformed occurrences and extra or present-empty slot metadata.
No WF, history, constants coherence or class premise is required. -/
def extractBlockDiff (b : BlockState m) : BlockDiff where
  accountChanges := b.accountWrites
  accountOrder := WriteOrder.toList b.accountOrder
  storageChanges := b.storageWrites
  storageAddressOrder := WriteOrder.toList b.storageAddressOrder
  storageSlotOrder := b.storageSlotOrder.map (fun _ r ↦ WriteOrder.toList r)
  codeChanges := b.codeWrites
  storageClears := b.storageClears

/-- Extraction preserves the complete account write map, including tombstones. -/
theorem extractBlockDiff_accountChanges (b : BlockState m) :
    (extractBlockDiff b).accountChanges = b.accountWrites := rfl

/-- Extraction preserves complete storage writes, including zeros and empty patches. -/
theorem extractBlockDiff_storageChanges (b : BlockState m) :
    (extractBlockDiff b).storageChanges = b.storageWrites := rfl

/-- Extraction preserves the complete code map without checking hashes or payloads. -/
theorem extractBlockDiff_codeChanges (b : BlockState m) :
    (extractBlockDiff b).codeChanges = b.codeWrites := rfl

/-- Extraction preserves storage-clear membership without choosing a traversal order. -/
theorem extractBlockDiff_storageClears (b : BlockState m) :
    (extractBlockDiff b).storageClears = b.storageClears := rfl

/-- Account metadata is exactly the existing raw ordered observer. -/
theorem extractBlockDiff_accountOrder (b : BlockState m) :
    (extractBlockDiff b).accountOrder = WriteOrder.toList b.accountOrder := rfl

/-- Storage-address metadata is exactly the existing raw ordered observer. -/
theorem extractBlockDiff_storageAddressOrder (b : BlockState m) :
    (extractBlockDiff b).storageAddressOrder = WriteOrder.toList b.storageAddressOrder := rfl

/-- Map every supplied slot index, retaining missing, empty and extra map entries. -/
theorem extractBlockDiff_storageSlotOrder (b : BlockState m) :
    (extractBlockDiff b).storageSlotOrder =
      b.storageSlotOrder.map (fun _ r ↦ WriteOrder.toList r) := rfl

end STFSpec.State
