/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.BlockState

/-!
# Logical block read sets

Library `EthState`: predicate views of the supplied block observation fields.
These views expose complete-key membership without enumeration or tracker effects.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/5/7/8.
-/

namespace STFSpec.State.BlockState

variable {m : Type → Type}

/-- Logical account-read membership of an arbitrary supplied block.
EELS `src/ethereum/forks/amsterdam/state_tracker.py:75`; consumed by
`src/ethereum/forks/amsterdam/block_access_lists.py:847–849`. -/
def accountReadSet (b : BlockState m) : Base.Address → Prop :=
  fun a ↦ a ∈ b.accountReads

/-- Logical storage-read membership, retaining both complete key components.
EELS `src/ethereum/forks/amsterdam/state_tracker.py:79`; consumed by
`src/ethereum/forks/amsterdam/block_access_lists.py:843–845`. -/
def storageReadSet (b : BlockState m) : (Base.Address × Base.Bytes32) → Prop :=
  fun pair ↦ pair ∈ b.storageReads

/-- The logical account view is exactly the supplied raw field's membership. -/
theorem accountReadSet_iff (b : BlockState m) (a : Base.Address) :
    accountReadSet b a ↔ a ∈ b.accountReads := Iff.rfl

/-- The logical storage view is exactly the supplied raw field's whole-key membership. -/
theorem storageReadSet_iff (b : BlockState m) (pair : Base.Address × Base.Bytes32) :
    storageReadSet b pair ↔ pair ∈ b.storageReads := Iff.rfl

end STFSpec.State.BlockState
