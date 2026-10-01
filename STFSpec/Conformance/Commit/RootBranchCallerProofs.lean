/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Conformance.Commit.RootBranchGuards

/-!
# Universal clients of bounded branch support

Library `EthConformance`. These consumers use existing public domain, Nibbles,
Std, Vector and InternalNode laws. Private branch law clients live in Root; no
private names or provider representation are used here. No recursive constructor,
root or witness canonicality theorem is supplied.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/4/7.1.
-/

namespace STFSpec.Conformance.Commit.RootBranchCallerProofs

open STFSpec.Commit STFSpec.Codec STFSpec.Hash
open RootBranchGuards

/-! Reusable public-only provider clients. -/

/-- Every numeric child retains the next-depth domain through its public law. -/
theorem child_domain {obj : Std.ExtTreeMap Nibbles ByteArray} {level : Nat}
    (hd : PatricializeDomain obj level) (digit : Fin 16) :
    PatricializeDomain (obj.filter (fun key _ ↦
      if h : level < key.size then decide (key.get ⟨level, h⟩ = digit) else false))
      (level + 1) := hd.child digit

/-- Ending keys are excluded before a numeric child reads any digit. -/
theorem ending_exclusion {obj : Std.ExtTreeMap Nibbles ByteArray} {level : Nat}
    (digit : Fin 16) (key : Nibbles) (h : key.size = level) :
    key ∉ obj.filter (fun key _ ↦
      if h : level < key.size then decide (key.get ⟨level, h⟩ = digit) else false) :=
  PatricializeDomain.ending_not_mem_child digit h

/-- The unique ending key retains its original bytes, including an empty value. -/
theorem ending_value {obj : Std.ExtTreeMap Nibbles ByteArray} {level : Nat}
    (hd : PatricializeDomain obj level) (a key : Nibbles)
    (ha : a ∈ obj) (hk : key ∈ obj) (hl : key.size = level) :
    obj[a.take level]? = some (obj[key]'hk) := by
  rw [hd.ending_prefix_key ha hk hl]
  exact Std.ExtTreeMap.getElem?_eq_some_getElem hk

/-- Optional ending lookup is independent of the selected actual member. -/
theorem ending_choice {obj : Std.ExtTreeMap Nibbles ByteArray} {level : Nat}
    (hd : PatricializeDomain obj level) (a b : Nibbles) (ha : a ∈ obj) (hb : b ∈ obj) :
    obj[a.take level]? = obj[b.take level]? := hd.branch_value_representative_eq ha hb

/-- The fixed sixteen-reference assembly preserves each numeric child position. -/
theorem fixed_reference_position (reference : Fin 16 → RlpItem) (value : ByteArray)
    (digit : Fin 16) :
    ((Vector.ofFn reference).toList ++ [RlpItem.bytes value])[digit.val]'(by simp; omega) =
      reference digit := by
  rw [branch_items_get]
  simp

/-- The branch value occupies the final position after all sixteen references. -/
theorem fixed_value_position (reference : Fin 16 → RlpItem) (value : ByteArray) :
    ((Vector.ofFn reference).toList ++ [RlpItem.bytes value])[16]'(by simp) = .bytes value :=
  branch_items_value _ _

end STFSpec.Conformance.Commit.RootBranchCallerProofs
