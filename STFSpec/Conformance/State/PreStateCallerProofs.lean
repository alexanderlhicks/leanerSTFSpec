/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.PreState

/-!
# Public-only raw provider clients

Library `EthConformance`: arbitrary type constructors consume all seven public laws.
No monad instance, backend interpretation or generated provider equation is used.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§5/7.
-/

namespace STFSpec.Conformance.State.PreStateCallerProofs

open STFSpec.Base STFSpec.State

variable {m : Type → Type}
variable (ga : Address → m (Except WitnessError (Option Account)))
variable (gs : Address → Bytes32 → m (Except WitnessError U256))
variable (gc : Hash32 → m (Except WitnessError ByteArray))
variable (sr : BlockDiff → m (Except WitnessError Hash32))

/-- A symbolic account action is retained under an arbitrary type constructor. -/
theorem account (a : Address) : (PreState.mk ga gs gc sr).getAccount? a = ga a :=
  congrFun (PreState.getAccount?_mk ga gs gc sr) a

/-- A symbolic storage action retains both inputs without a monad premise. -/
theorem storage (a : Address) (k : Bytes32) :
    (PreState.mk ga gs gc sr).getStorage a k = gs a k :=
  congrFun (congrFun (PreState.getStorage_mk ga gs gc sr) a) k

/-- A symbolic code action keeps the exact nonoptional result type. -/
theorem code (h : Hash32) : (PreState.mk ga gs gc sr).getCode h = gc h :=
  congrFun (PreState.getCode_mk ga gs gc sr) h

/-- A symbolic root action receives the entire arbitrary raw diff. -/
theorem root (d : BlockDiff) : (PreState.mk ga gs gc sr).stateRoot d = sr d :=
  congrFun (PreState.stateRoot_mk ga gs gc sr) d

/-- The public eta law reconstructs a generic carrier. -/
theorem rebuild (ps : PreState m) :
    PreState.mk ps.getAccount? ps.getStorage ps.getCode ps.stateRoot = ps :=
  PreState.eta ps

/-- Consumers can determine equality from complete public functions. -/
theorem functions {ps qs : PreState m}
    (ha : ps.getAccount? = qs.getAccount?) (hs : ps.getStorage = qs.getStorage)
    (hc : ps.getCode = qs.getCode) (hr : ps.stateRoot = qs.stateRoot) : ps = qs :=
  PreState.ext ha hs hc hr

/-- Consumers can determine equality from arbitrary pointwise complete actions. -/
theorem actions {ps qs : PreState m}
    (ha : ∀ a, ps.getAccount? a = qs.getAccount? a)
    (hs : ∀ a k, ps.getStorage a k = qs.getStorage a k)
    (hc : ∀ h, ps.getCode h = qs.getCode h)
    (hr : ∀ d, ps.stateRoot d = qs.stateRoot d) : ps = qs :=
  PreState.ext_apply ha hs hc hr

end STFSpec.Conformance.State.PreStateCallerProofs
