/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.TxState

/-!
# Account creation marker

Library `EthState`. Spec guidance: `STFSpec/informal/modules/EthState.md` R22.
-/

namespace STFSpec.State

open Base

/-- Insert the complete address into this transaction's created-account set.
Implements EELS `src/ethereum/forks/amsterdam/state_tracker.py:552–571`. -/
def markAccountCreated {m : Type → Type} [Monad m] (a : Address) : StateM m Unit :=
  fun t ↦ ExceptT.mk (pure (.ok ((), { t with
    obs.createdAccounts := t.obs.createdAccounts.insert a })))

private theorem markAccountCreated_run {m : Type → Type} [Monad m]
    (t : TxState m) (a : Address) :
    ((markAccountCreated a).run t).run =
      pure (.ok ((), { t with obs.createdAccounts := t.obs.createdAccounts.insert a })) := rfl

private theorem markAccountCreated_frame (t next : TxState Id) (a : Address)
    (h : ((markAccountCreated a).run t).run = .ok ((), next)) :
    { next with obs.createdAccounts := t.obs.createdAccounts } = t := by
  rw [markAccountCreated_run] at h
  cases h
  rfl

private theorem createdAccounts_mem (s : Std.HashSet Address) (a b : Address) :
    b ∈ s.insert a ↔ a = b ∨ b ∈ s := by
  rw [Std.HashSet.mem_insert, beq_iff_eq]

private theorem createdAccounts_insert_idempotent (s : Std.HashSet Address) (a b : Address) :
    b ∈ (s.insert a).insert a ↔ b ∈ s.insert a := by
  simp only [createdAccounts_mem, ← or_assoc, or_self]

end STFSpec.State
