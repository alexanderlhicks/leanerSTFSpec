/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.PreState
import STFSpec.State.MathState

/-!
# Supplied-record lookup agreement

Library `EthState`: successful provider answers agree with raw mathematical observers
at the caller's constants. Errors impose no constraint; progress is a separate obligation.
Spec guidance: `STFSpec/informal/modules/EthState.md` R8/§5 (Q57).
-/

namespace STFSpec.State

open Base

/-- Success-only account, storage and code agreement at supplied constants (Q57).
The provider shape is EELS `src/ethereum/state.py:100–122`; mathematical observers
follow `src/ethereum/state_mpt.py:49–80`. This proposition adds no root, WF,
authentication, availability or constants-coherence premise. -/
def ModelsLookups (consts : HashConsts) (ps : PreState Id) (σ : MathState) : Prop :=
  (∀ a o, ps.getAccount? a = .ok o → σ.account? a = o) ∧
  (∀ a k v, ps.getStorage a k = .ok v → σ.storageAt a k = v) ∧
  (∀ h code, ps.getCode h = .ok code → σ.code? consts h = some code)

end STFSpec.State
