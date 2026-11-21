/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.TxState

/-!
# Transaction-state initialization

Library `EthState`. Initialize the transaction over its supplied block with
empty revertible fields, observations and B1 write-order indexes.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/5/7.
-/

namespace STFSpec.State.TxState

variable {m : Type → Type}

/-- Construct fresh transaction data over the supplied block.
See EELS `src/ethereum/forks/amsterdam/state_tracker.py:78–104` at the pin. -/
def new (block : BlockState m) : TxState m where
  block := block
  rev := ⟨∅, WriteOrder.empty, ∅, WriteOrder.empty, ∅, ∅, ∅, ∅⟩
  obs := ⟨∅, ∅, ∅, ∅⟩

private theorem new_complete (block : BlockState m) :
    new block =
      ⟨block, ⟨∅, WriteOrder.empty, ∅, WriteOrder.empty, ∅, ∅, ∅, ∅⟩, ⟨∅, ∅, ∅, ∅⟩⟩ := rfl

end STFSpec.State.TxState
