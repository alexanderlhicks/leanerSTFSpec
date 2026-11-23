/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.TxState

/-!
# Ancestor access recording

Library `EthState`. Record a new maximum offset in the block held by the
current transaction.
Spec guidance: `STFSpec/informal/modules/EthState.md` R27 and §§5/7.
-/

namespace STFSpec.State

private def recordOffset {m : Type → Type} (t : TxState m) (offset : Nat) : TxState m :=
  if t.block.oldestAncestorOffset.isNone || t.block.oldestAncestorOffset.any (· < offset) then
    { t with block.oldestAncestorOffset := some offset }
  else t

/-- Record the first offset or a strictly older ancestor.
See EELS `src/ethereum/forks/amsterdam/state_tracker.py:884–905` at the pin. -/
def trackAncestorAccess {m : Type → Type} [Monad m] (offset : Nat) : StateM m Unit := fun t ↦
  ExceptT.mk (pure (.ok ((), recordOffset t offset)))

private theorem track_action {m : Type → Type} [Monad m] (t : TxState m) (offset : Nat) :
    ((trackAncestorAccess offset).run t).run = pure (.ok ((), recordOffset t offset)) := rfl

private theorem record_offset {m : Type → Type} (t : TxState m) (offset : Nat) :
    (recordOffset t offset).block.oldestAncestorOffset = some
      (match t.block.oldestAncestorOffset with
       | none => offset
       | some previous => max previous offset) := by
  cases h : t.block.oldestAncestorOffset with
  | none => simp [recordOffset, h]
  | some previous =>
    by_cases older : previous < offset
    · simp [recordOffset, h, older, Nat.max_eq_right (Nat.le_of_lt older)]
    · simp [recordOffset, h, older, Nat.max_eq_left (Nat.le_of_not_gt older)]

private theorem retained_fields {m : Type → Type} (t : TxState m) (offset : Nat) :
    let next := recordOffset t offset
    { next with block.oldestAncestorOffset := t.block.oldestAncestorOffset } = t := by
  cases t with
  | mk block rev obs =>
    cases block
    simp only [recordOffset]
    split <;> rfl

end STFSpec.State
