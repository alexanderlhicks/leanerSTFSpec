/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit.Root

/-!
# Root-domain consumers through public contracts

Library `EthConformance`. These proofs consume actual packed `Nibbles`, finite
map contracts and the domain laws without unfolding path storage or map internals.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/7.1.
-/

namespace STFSpec.Conformance.Commit.RootDomainCallerProofs

open STFSpec.Commit

/-- Every numeric root child starts in the reachable domain, for arbitrary maps. -/
theorem root_child (obj : Std.ExtTreeMap Nibbles ByteArray) (digit : Fin 16) :
    PatricializeDomain
      (obj.filter (fun k _ ↦
        if h : 0 < k.size then decide (k.get ⟨0, h⟩ = digit) else false)) 1 :=
  (PatricializeDomain.zero obj).child digit

/-- Advancing any shared prefix has an explicit full-key depth premise. -/
theorem extension_client (obj : Std.ExtTreeMap Nibbles ByteArray) (level amount : Nat)
    (depth : ∀ k : Nibbles, k ∈ obj → level + amount ≤ k.size)
    (shared : ∀ k : Nibbles, k ∈ obj → ∀ j : Nibbles, j ∈ obj →
      k.take (level + amount) = j.take (level + amount)) :
    PatricializeDomain obj (level + amount) := PatricializeDomain.extension depth shared

/-- A present ending value, even empty, is found from every representative. -/
theorem ending_value (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (hd : PatricializeDomain obj level) (representative k : Nibbles)
    (hr : representative ∈ obj) (hk : k ∈ obj) (hl : k.size = level) :
    obj[representative.take level]? = some (obj[k]'hk) := by
  rw [hd.ending_prefix_key hr hk hl]
  exact Std.ExtTreeMap.getElem?_eq_some_getElem hk

/-- The branch lookup remains optional: the domain does not invent a missing key. -/
theorem absent_branch_value (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (hd : PatricializeDomain obj level) (a b : Nibbles) (ha : a ∈ obj) (hb : b ∈ obj)
    (habsent : obj[a.take level]? = none) : obj[b.take level]? = none := by
  rw [← hd.branch_value_representative_eq ha hb]
  exact habsent

/-- Ending-key exclusion needs only the size equation, and covers all children. -/
theorem ending_exclusion (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (k : Nibbles) (hk : k.size = level) (digit : Fin 16) :
    k ∉ obj.filter (fun key _ ↦
      if h : level < key.size then decide (key.get ⟨level, h⟩ = digit) else false) :=
  PatricializeDomain.ending_not_mem_child digit hk

/-- Distinct full keys inserted in either order have identical optional lookups. -/
theorem insert_permutation (obj : Std.ExtTreeMap Nibbles ByteArray)
    (a b k : Nibbles) (va vb : ByteArray) (hne : a ≠ b) :
    ((obj.insert a va).insert b vb)[k]? = ((obj.insert b vb).insert a va)[k]? := by
  simp only [Std.ExtTreeMap.getElem?_insert, Nibbles.compare_eq_eq_iff]
  by_cases ha : a = k <;> by_cases hb : b = k <;> simp_all

/-- Zero-domain does not depend on key order or duplicate-key replacement. -/
theorem inserted_zero (obj : Std.ExtTreeMap Nibbles ByteArray) (a : Nibbles) (v : ByteArray) :
    PatricializeDomain (obj.insert a v) 0 := PatricializeDomain.zero _

end STFSpec.Conformance.Commit.RootDomainCallerProofs
