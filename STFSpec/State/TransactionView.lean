/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.TxState
import STFSpec.State.BlockView

/-!
# Mathematical transaction-state view

Library `EthState`: apply complete revertible effects to the mathematical block view.
The internal conversion transports existing order observers without repairing raw indexes.
There is no standalone Python mathematical-view operation.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/5/7.1/7.2.
-/

namespace STFSpec.State

open Base

private def TxRevertible.asDiff (r : TxRevertible) : BlockDiff where
  accountChanges := r.accountWrites
  accountOrder := WriteOrder.toList r.accountOrder
  storageChanges := r.storageWrites
  storageAddressOrder := WriteOrder.toList r.storageAddressOrder
  storageSlotOrder := r.storageSlotOrder.map (fun _ index ↦ WriteOrder.toList index)
  codeChanges := r.codeWrites
  storageClears := r.storageClears

private theorem TxRevertible.asDiff_eq (r : TxRevertible) :
    r.asDiff = BlockDiff.mk r.accountWrites (WriteOrder.toList r.accountOrder)
      r.storageWrites (WriteOrder.toList r.storageAddressOrder)
      (r.storageSlotOrder.map (fun _ index ↦ WriteOrder.toList index))
      r.codeWrites r.storageClears := rfl

private theorem TxRevertible.asDiff_slot_lookup (r : TxRevertible) (a : Address) :
    r.asDiff.storageSlotOrder[a]? = (r.storageSlotOrder[a]?).map WriteOrder.toList := by
  simp only [asDiff_eq, Std.ExtTreeMap.getElem?_map]

namespace TxState

variable {m : Type → Type}

/-- Complete raw mathematical transaction view, without class or validity premises.
Composes the transaction effects of EELS `src/ethereum/forks/amsterdam/state_tracker.py:78–104`
with block extraction (`:861–881`) and application (`src/ethereum/state_mpt.py:133–161`).
Transient data, observations, providers, constants and replay metadata add no effects. -/
def view (σ₀ : MathState) (t : TxState m) : MathState :=
  (t.block.view σ₀).apply t.rev.asDiff

private theorem view_eq_apply (σ₀ : MathState) (t : TxState m) :
    t.view σ₀ = (t.block.view σ₀).apply t.rev.asDiff := rfl

private theorem view_eq_effects (σ₀ : MathState) (t : TxState m) :
    t.view σ₀ = (t.block.view σ₀).apply
      ⟨t.rev.accountWrites, [], t.rev.storageWrites, [], ∅,
        t.rev.codeWrites, t.rev.storageClears⟩ := by
  rw [view_eq_apply]
  exact MathState.apply_congr_effects _ _ _ rfl rfl rfl rfl

/-- Transaction account entries, including tombstones, override the block view.
The future `getAccountOptional_model` consumer needs this unconditional equation;
it requires no Monad, WF, provider agreement or history premise. -/
theorem view_account?_eq (σ₀ : MathState) (t : TxState m) (a : Address) :
    (t.view σ₀).account? a =
      match t.rev.accountWrites[a]? with
      | some account => account
      | none => (t.block.view σ₀).account? a := by
  rw [view_eq_apply, MathState.apply_account?_eq, TxRevertible.asDiff_eq]
  cases t.rev.accountWrites[a]? <;> rfl

private theorem view_accounts (σ₀ : MathState) (t : TxState m) (a : Address) :
    (t.view σ₀).accounts[a]? =
      match t.rev.accountWrites[a]? with
      | none => (t.block.view σ₀).accounts[a]?
      | some account => account := by
  rw [view_eq_apply, MathState.apply_accounts_lookup]
  rfl

private theorem view_storage (σ₀ : MathState) (t : TxState m) (a : Address) :
    (t.view σ₀).storage[a]? =
      match t.rev.storageWrites[a]? with
      | none => if a ∈ t.rev.storageClears then none else (t.block.view σ₀).storage[a]?
      | some writes =>
        let out := writes.foldl (fun out k v ↦
          if v = U256.zero then out.erase k else out.insert k v)
          ((if a ∈ t.rev.storageClears then none else (t.block.view σ₀).storage[a]?).getD ∅)
        if out.isEmpty then none else some out := by
  rw [view_eq_apply, MathState.apply_storage_lookup]
  rfl

private theorem view_code (σ₀ : MathState) (t : TxState m) (h : Hash32) :
    (t.view σ₀).code[h]? =
      match t.rev.codeWrites[h]? with
      | none => (t.block.view σ₀).code[h]?
      | some bytes => some bytes := by
  rw [view_eq_apply, MathState.apply_code_lookup]
  rfl

private theorem view_congr_revertible (σ₀ : MathState) (t u : TxState m)
    (hb : t.block = u.block) (ha : t.rev.accountWrites = u.rev.accountWrites)
    (hs : t.rev.storageWrites = u.rev.storageWrites)
    (hc : t.rev.codeWrites = u.rev.codeWrites)
    (hcl : t.rev.storageClears = u.rev.storageClears) : t.view σ₀ = u.view σ₀ := by
  rw [view_eq_effects, view_eq_effects, hb, ha, hs, hc, hcl]

end TxState

end STFSpec.State
