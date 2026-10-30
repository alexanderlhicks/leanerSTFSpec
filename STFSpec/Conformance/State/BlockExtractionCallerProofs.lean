/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Public block-extraction callers

Library `EthConformance`: private clients use only the seven extraction laws,
BlockDiff extensionality, mathematical application and public Std/order laws.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/4/7/8.
-/

namespace STFSpec.Conformance.State.BlockExtractionCallerProofs

open STFSpec.State STFSpec.Base

private def signature : {m : Type → Type} → BlockState m → BlockDiff := @extractBlockDiff
private def Contravariant (α : Type) : Type := α → Nat
#check_failure (inferInstance : Monad Contravariant)
private def noMonadSignature : BlockState Contravariant → BlockDiff := signature

private theorem complete {m : Type → Type} (b : BlockState m) :
    extractBlockDiff b =
      ⟨b.accountWrites, b.accountOrder.toList, b.storageWrites, b.storageAddressOrder.toList,
        b.storageSlotOrder.map (fun _ r ↦ r.toList), b.codeWrites, b.storageClears⟩ := by
  apply BlockDiff.ext
  · exact extractBlockDiff_accountChanges b
  · exact extractBlockDiff_accountOrder b
  · exact extractBlockDiff_storageChanges b
  · exact extractBlockDiff_storageAddressOrder b
  · exact extractBlockDiff_storageSlotOrder b
  · exact extractBlockDiff_codeChanges b
  · exact extractBlockDiff_storageClears b

private theorem optionalSlots {m : Type → Type} (b : BlockState m) (a : Address) :
    (extractBlockDiff b).storageSlotOrder[a]? =
      (b.storageSlotOrder[a]?).map WriteOrder.toList := by
  rw [extractBlockDiff_storageSlotOrder, Std.ExtTreeMap.getElem?_map]

-- This varies every discarded field by arbitrary complete values, not membership equivalence.
private theorem discarded {m : Type → Type} (b : BlockState m) (ps : PreState m)
    (consts : HashConsts) (ar : Std.HashSet Address)
    (sr : Std.HashSet (Address × Bytes32)) (cr : Std.HashSet (Address × Hash32))
    (offset : Option Nat) :
    extractBlockDiff { b with
      preState := ps
      consts := consts
      accountReads := ar
      storageReads := sr
      codeReads := cr
      oldestAncestorOffset := offset } =
      extractBlockDiff b := by
  apply BlockDiff.ext <;>
    simp only [extractBlockDiff_accountChanges, extractBlockDiff_accountOrder,
      extractBlockDiff_storageChanges, extractBlockDiff_storageAddressOrder,
      extractBlockDiff_storageSlotOrder, extractBlockDiff_codeChanges,
      extractBlockDiff_storageClears]

private theorem arbitraryMonadFree (b : BlockState Contravariant) :
    (noMonadSignature b).accountChanges = b.accountWrites := extractBlockDiff_accountChanges b

-- Equal ordered observers suffice: the discarded next/forward maps need not be equal.
private theorem observers {m n : Type → Type} (b : BlockState m) (c : BlockState n)
    (ha : b.accountWrites = c.accountWrites)
    (hs : b.storageWrites = c.storageWrites) (hc : b.codeWrites = c.codeWrites)
    (hcl : b.storageClears = c.storageClears)
    (hao : b.accountOrder.toList = c.accountOrder.toList)
    (hsa : b.storageAddressOrder.toList = c.storageAddressOrder.toList)
    (hso : b.storageSlotOrder.map (fun _ r ↦ r.toList) =
      c.storageSlotOrder.map (fun _ r ↦ r.toList)) :
    extractBlockDiff b = extractBlockDiff c := by
  apply BlockDiff.ext <;>
    simp only [extractBlockDiff_accountChanges, extractBlockDiff_accountOrder,
      extractBlockDiff_storageChanges, extractBlockDiff_storageAddressOrder,
      extractBlockDiff_storageSlotOrder, extractBlockDiff_codeChanges,
      extractBlockDiff_storageClears]
  all_goals assumption

private theorem metadataApplication {m : Type → Type} (σ : MathState) (b : BlockState m)
    (ao : WriteOrder Address) (sa : WriteOrder Address)
    (so : Std.ExtTreeMap Address (WriteOrder Bytes32)) :
    σ.apply (extractBlockDiff { b with
      accountOrder := ao
      storageAddressOrder := sa
      storageSlotOrder := so }) = σ.apply (extractBlockDiff b) := by
  apply MathState.apply_congr_effects <;>
    simp only [extractBlockDiff_accountChanges, extractBlockDiff_storageChanges,
      extractBlockDiff_codeChanges, extractBlockDiff_storageClears]

end STFSpec.Conformance.State.BlockExtractionCallerProofs
