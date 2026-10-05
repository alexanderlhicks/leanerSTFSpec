/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.WitnessError
import STFSpec.State.BlockDiff

/-!
# Raw pre-state provider record

Library `EthState`: four arbitrary supplied actions and their ordinary record laws.
The carrier has no monad premise and implements no lookup, hashing or root semantics.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§2.3/5/7.
-/

namespace STFSpec.State

open Base

/-- Four supplied provider operations; EELS `src/ethereum/state.py:92–139`.
Record equality preserves complete actions, without asserting an equivalence of their effects. -/
structure PreState (m : Type → Type) where
  /-- Supplied optional account action; EELS `src/ethereum/state.py:100–106`. -/
  getAccount? : Address → m (Except WitnessError (Option Account))
  /-- Supplied storage action; EELS `src/ethereum/state.py:108–114`. -/
  getStorage : Address → Bytes32 → m (Except WitnessError U256)
  /-- Supplied code action, without an optional result; EELS `src/ethereum/state.py:116–122`. -/
  getCode : Hash32 → m (Except WitnessError ByteArray)
  /-- Supplied root action on the complete raw diff; EELS `src/ethereum/state.py:124–139`. -/
  stateRoot : BlockDiff → m (Except WitnessError Hash32)

namespace PreState

variable {m : Type → Type}
variable (ga : Address → m (Except WitnessError (Option Account)))
variable (gs : Address → Bytes32 → m (Except WitnessError U256))
variable (gc : Hash32 → m (Except WitnessError ByteArray))
variable (sr : BlockDiff → m (Except WitnessError Hash32))

/-- Construction preserves the complete supplied account function. -/
theorem getAccount?_mk : (PreState.mk ga gs gc sr).getAccount? = ga := rfl

/-- Construction preserves the complete supplied storage function. -/
theorem getStorage_mk : (PreState.mk ga gs gc sr).getStorage = gs := rfl

/-- Construction preserves the complete supplied code function. -/
theorem getCode_mk : (PreState.mk ga gs gc sr).getCode = gc := rfl

/-- Construction preserves the complete supplied root function. -/
theorem stateRoot_mk : (PreState.mk ga gs gc sr).stateRoot = sr := rfl

/-- Reconstruction from the four public fields returns the provider record. -/
theorem eta (ps : PreState m) :
    PreState.mk ps.getAccount? ps.getStorage ps.getCode ps.stateRoot = ps := by
  cases ps
  rfl

/-- Equality of the four complete supplied functions determines the record. -/
theorem ext {ps qs : PreState m}
    (ha : ps.getAccount? = qs.getAccount?) (hs : ps.getStorage = qs.getStorage)
    (hc : ps.getCode = qs.getCode) (hr : ps.stateRoot = qs.stateRoot) : ps = qs := by
  cases ps
  cases qs
  cases ha
  cases hs
  cases hc
  cases hr
  rfl

/-- Pointwise equality of complete actions determines the provider record. -/
theorem ext_apply {ps qs : PreState m}
    (ha : ∀ a, ps.getAccount? a = qs.getAccount? a)
    (hs : ∀ a k, ps.getStorage a k = qs.getStorage a k)
    (hc : ∀ h, ps.getCode h = qs.getCode h)
    (hr : ∀ d, ps.stateRoot d = qs.stateRoot d) : ps = qs :=
  ext (funext ha) (funext fun a ↦ funext (hs a)) (funext hc) (funext hr)

end PreState

end STFSpec.State
