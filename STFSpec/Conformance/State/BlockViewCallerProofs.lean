/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Public mathematical block-view callers

Library `EthConformance`: private arbitrary-input clients compose the public view,
extraction, application and observer laws without unfolding semantic definitions.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/4/7/8.
-/

namespace STFSpec.Conformance.State.BlockViewCallerProofs

open STFSpec.State STFSpec.Base

private def signature : {m : Type → Type} → MathState → BlockState m → MathState :=
  @BlockState.view
private def Contravariant (α : Type) : Type := α → Nat
#check_failure (inferInstance : Monad Contravariant)
private def noMonadSignature : MathState → BlockState Contravariant → MathState := signature

private theorem complete {m : Type → Type} (σ : MathState) (b : BlockState m) :
    b.view σ = σ.apply
      ⟨b.accountWrites, [], b.storageWrites, [], ∅, b.codeWrites, b.storageClears⟩ := by
  rw [← BlockState.apply_extractBlockDiff]
  apply MathState.apply_congr_effects
  · exact extractBlockDiff_accountChanges b
  · exact extractBlockDiff_storageChanges b
  · exact extractBlockDiff_codeChanges b
  · exact extractBlockDiff_storageClears b

private theorem accounts {m : Type → Type} (σ : MathState) (b : BlockState m) (a : Address) :
    (b.view σ).accounts[a]? =
      match b.accountWrites[a]? with
      | none => σ.accounts[a]?
      | some replacement => replacement := by
  rw [← BlockState.apply_extractBlockDiff, MathState.apply_accounts_lookup,
    extractBlockDiff_accountChanges]
  rfl

private theorem storage {m : Type → Type} (σ : MathState) (b : BlockState m) (a : Address) :
    (b.view σ).storage[a]? =
      match b.storageWrites[a]? with
      | none => if a ∈ b.storageClears then none else σ.storage[a]?
      | some writes =>
        let out := writes.foldl (fun out k v ↦
          if v = U256.zero then out.erase k else out.insert k v)
          ((if a ∈ b.storageClears then none else σ.storage[a]?).getD ∅)
        if out.isEmpty then none else some out := by
  rw [← BlockState.apply_extractBlockDiff, MathState.apply_storage_lookup,
    extractBlockDiff_storageChanges, extractBlockDiff_storageClears]
  rfl

private theorem code {m : Type → Type} (σ : MathState) (b : BlockState m) (h : Hash32) :
    (b.view σ).code[h]? =
      match b.codeWrites[h]? with
      | none => σ.code[h]?
      | some bytes => some bytes := by
  rw [← BlockState.apply_extractBlockDiff, MathState.apply_code_lookup,
    extractBlockDiff_codeChanges]
  rfl

private theorem accountObservation {m : Type → Type}
    (σ : MathState) (b : BlockState m) (a : Address) :
    (b.view σ).account? a =
      match b.accountWrites[a]? with
      | none => σ.account? a
      | some replacement => replacement := by
  rw [← BlockState.apply_extractBlockDiff, MathState.apply_account?_eq,
    extractBlockDiff_accountChanges]
  rfl

private theorem storageObservation {m : Type → Type}
    (σ : MathState) (b : BlockState m) (a : Address) (k : Bytes32) :
    (b.view σ).storageAt a k =
      match (b.storageWrites[a]?).bind (fun slots ↦ slots[k]?) with
      | none => if a ∈ b.storageClears then U256.zero else σ.storageAt a k
      | some v => v := by
  rw [← BlockState.apply_extractBlockDiff, MathState.apply_storageAt_eq,
    extractBlockDiff_storageChanges, extractBlockDiff_storageClears]
  rfl

private theorem codeObservation {m : Type → Type}
    (σ : MathState) (b : BlockState m) (consts : HashConsts) (h : Hash32) :
    (b.view σ).code? consts h =
      if h = consts.emptyCodeHash then some ByteArray.empty else
        match b.codeWrites[h]? with
        | none => σ.code[h]?
        | some bytes => some bytes := by
  rw [← BlockState.apply_extractBlockDiff, MathState.apply_code?_eq,
    extractBlockDiff_codeChanges]
  rfl

-- All effects agree; arbitrary type constructors and every other field may differ.
private theorem effects {m n : Type → Type} (σ : MathState)
    (b : BlockState m) (c : BlockState n)
    (ha : b.accountWrites = c.accountWrites) (hs : b.storageWrites = c.storageWrites)
    (hc : b.codeWrites = c.codeWrites) (hcl : b.storageClears = c.storageClears) :
    b.view σ = c.view σ := by
  rw [← BlockState.apply_extractBlockDiff, ← BlockState.apply_extractBlockDiff]
  apply MathState.apply_congr_effects
  · rw [extractBlockDiff_accountChanges, extractBlockDiff_accountChanges, ha]
  · rw [extractBlockDiff_storageChanges, extractBlockDiff_storageChanges, hs]
  · rw [extractBlockDiff_codeChanges, extractBlockDiff_codeChanges, hc]
  · rw [extractBlockDiff_storageClears, extractBlockDiff_storageClears, hcl]

private theorem discarded {m : Type → Type} (σ : MathState) (b : BlockState m)
    (ps : PreState m) (consts : HashConsts) (ar : Std.HashSet Address)
    (sr : Std.HashSet (Address × Bytes32)) (cr : Std.HashSet (Address × Hash32))
    (offset : Option Nat) (ao sa : WriteOrder Address)
    (so : Std.ExtTreeMap Address (WriteOrder Bytes32)) :
    ({ b with
      preState := ps
      consts := consts
      accountReads := ar
      storageReads := sr
      codeReads := cr
      oldestAncestorOffset := offset
      accountOrder := ao
      storageAddressOrder := sa
      storageSlotOrder := so }).view σ =
      b.view σ := effects σ _ _ rfl rfl rfl rfl

private theorem contravariant (σ : MathState) (b : BlockState Contravariant) :
    noMonadSignature σ b = σ.apply (extractBlockDiff b) :=
  (BlockState.apply_extractBlockDiff σ b).symm

end STFSpec.Conformance.State.BlockViewCallerProofs
