/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.BlockExtraction
import STFSpec.State.Apply

/-!
# Mathematical block-state view

Library `EthState`: apply the extracted raw effects to a supplied mathematical state.
This model composition has no corresponding standalone Python operation.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§5/7.2.
-/

namespace STFSpec.State.BlockState

variable {m : Type → Type}

/-- The complete mathematical block view, for arbitrary raw inputs without class premises.
Composition of extraction (`src/ethereum/forks/amsterdam/state_tracker.py:880–900`)
and mathematical application (`src/ethereum/state_mpt.py:133–161`) at the pin.
Provider actions, constants, observations and replay metadata add no effects. -/
def view (σ₀ : MathState) (b : BlockState m) : MathState :=
  σ₀.apply (extractBlockDiff b)

/-- Applying the extracted effects is exactly the mathematical block view.
This equation supplies no reachable WF, history or witness replay agreement. -/
theorem apply_extractBlockDiff (σ₀ : MathState) (b : BlockState m) :
    σ₀.apply (extractBlockDiff b) = b.view σ₀ := rfl

end STFSpec.State.BlockState
