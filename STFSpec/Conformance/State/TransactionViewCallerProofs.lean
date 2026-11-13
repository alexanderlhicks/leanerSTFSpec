/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Public mathematical transaction-view callers

Library `EthConformance`: private class-free clients use only the public account law.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/4/7.1/7.2.
-/

namespace STFSpec.Conformance.State.TransactionViewCallerProofs

open STFSpec.State STFSpec.Base

private def signature : {m : Type → Type} → MathState → TxState m → MathState :=
  @TxState.view

private theorem account {m : Type → Type} (σ : MathState) (t : TxState m) (a : Address) :
    (t.view σ).account? a =
      match t.rev.accountWrites[a]? with
      | some replacement => replacement
      | none => (t.block.view σ).account? a := TxState.view_account?_eq σ t a

private theorem tombstone {m : Type → Type} (σ : MathState) (t : TxState m) (a : Address)
    (ha : t.rev.accountWrites[a]? = some none) : (t.view σ).account? a = none := by
  rw [TxState.view_account?_eq, ha]

private theorem missing {m : Type → Type} (σ : MathState) (t : TxState m) (a : Address)
    (ha : t.rev.accountWrites[a]? = none) :
    (t.view σ).account? a = (t.block.view σ).account? a := by
  rw [TxState.view_account?_eq, ha]

private def Contravariant (α : Type) : Type := α → Nat
#check_failure (inferInstance : Monad Contravariant)

private def noMonadSignature : MathState → TxState Contravariant → MathState := signature

private theorem noMonadLaw (σ : MathState) (t : TxState Contravariant) (a : Address) :
    (noMonadSignature σ t).account? a =
      match t.rev.accountWrites[a]? with
      | some replacement => replacement
      | none => (t.block.view σ).account? a := TxState.view_account?_eq σ t a

end STFSpec.Conformance.State.TransactionViewCallerProofs
