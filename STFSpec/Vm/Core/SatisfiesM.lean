/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

/-!
# Logical action factorization

Library `EthVmCore`. A monadic action factors through results carrying a proof.
This logical predicate supplies no arbitrary-monad result observation or progress guarantee.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7 (Q83).
-/

namespace STFSpec.Vm.Core

/-- The action is the map-erasure of an action carrying certified results.
The `Monad` binder is the shared carrier contract; no monad laws are assumed. -/
def SatisfiesM {m : Type → Type} [Monad m] {α : Type}
    (P : α → Prop) (x : m α) : Prop :=
  ∃ y : m {r : α // P r}, Subtype.val <$> y = x

/-- At `Id`, action factorization is exactly the result predicate. -/
theorem satisfiesM_id_iff {α : Type} (P : α → Prop) (x : Id α) :
    SatisfiesM P x ↔ P x := by
  constructor
  · rintro ⟨y, h⟩
    change y.val = x at h
    exact h ▸ y.property
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

end STFSpec.Vm.Core
