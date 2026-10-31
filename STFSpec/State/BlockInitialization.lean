/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.BlockState

/-!
# Block-state initialization

Library `EthState`: retain the supplied provider and F20 constants, with empty
writes, observations and B1 indexes. Whole-result verification stays in this owner.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/5/7/8.
-/

namespace STFSpec.State.BlockState

variable {m : Type → Type}

/-- Initialize a block over the complete supplied provider and constants.
EELS `src/ethereum/forks/amsterdam/state_tracker.py:57–86`, used at `fork.py:325`.
F20 adds the supplied constants; B1 adds empty first-write indexes. No provider
operation or constants acquisition is performed. -/
def new (ps : PreState m) (consts : Base.HashConsts) : BlockState m where
  preState := ps
  consts := consts
  accountWrites := ∅
  accountOrder := WriteOrder.empty
  storageWrites := ∅
  storageAddressOrder := WriteOrder.empty
  storageSlotOrder := ∅
  codeWrites := ∅
  storageClears := ∅
  accountReads := ∅
  storageReads := ∅
  codeReads := ∅
  oldestAncestorOffset := none

/-- Initialization preserves the whole caller-supplied F20 constants record. -/
theorem new_consts (ps : PreState m) (consts : Base.HashConsts) :
    (new ps consts).consts = consts := rfl

-- This owner-local reduction verifies all defaults and whole arbitrary provider
-- retention. It supplies no extra public consumer equation or reachability law.
private theorem new_complete (ps : PreState m) (consts : Base.HashConsts) :
    new ps consts =
      ⟨ps, consts, ∅, WriteOrder.empty, ∅, WriteOrder.empty, ∅, ∅, ∅, ∅, ∅, ∅, none⟩ := rfl

private theorem provider_retained (ps : PreState m) (consts : Base.HashConsts) :
    (new ps consts).preState = ps := rfl

end STFSpec.State.BlockState
