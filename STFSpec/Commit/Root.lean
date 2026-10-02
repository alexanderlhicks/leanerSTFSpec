/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit.Nibbles
import Std.Data.ExtTreeMap.Lemmas
import STFSpec.Commit.InternalNode
import Init.Data.Vector.OfFn

/-!
# Mathematical trie construction, roots and domain support

Library `EthCommit`. Support for pinned EELS
`src/ethereum/merkle_patricia_trie.py:478–581`, on Q50's reachable domain.
Keys retain complete paths and values may be empty. `patricialize` implements C7
with well-founded recursion and minimum-key selection. The private branch stage
sequences actual child construction then C6 encoding in numeric order, without
hashing the returned parent. Ordinary public dispatch equations retain literal
monadic association; a private recursive proof permits arbitrary valid member
selectors at every descendant. C8 supplies the supplied-empty branch and one
final complete top query. Witness acceptance remains separate.
Partition, sum, prefix and branch helpers stay private to this owner; callers use
public domain and construction laws.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§2.2/5/7.1.
-/

namespace STFSpec.Commit

open STFSpec.Base STFSpec.Codec STFSpec.Hash

/-- Reachable depth of a finite full-key map: keys are long enough and have the
same consumed prefix. Every finite map has this domain at depth zero. -/
structure PatricializeDomain (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat) : Prop where
  /-- No key ends before the consumed depth. -/
  depth : ∀ k, k ∈ obj → level ≤ k.size
  /-- Every pair of keys has the same consumed prefix. -/
  consumedPrefix : ∀ k, k ∈ obj → ∀ j, j ∈ obj → k.take level = j.take level

namespace PatricializeDomain

/-- Construction starts at zero for every finite map, without value/length restrictions. -/
theorem zero (obj : Std.ExtTreeMap Nibbles ByteArray) : PatricializeDomain obj 0 := by
  constructor
  · intro k hk
    omega
  · intro k hk j hj
    rw [Nibbles.take_zero, Nibbles.take_zero]

/-- At most one full key can end at the consumed depth. -/
theorem ending_unique {obj : Std.ExtTreeMap Nibbles ByteArray} {level : Nat}
    (hd : PatricializeDomain obj level) {k j : Nibbles}
    (hk : k ∈ obj) (hj : j ∈ obj) (hkl : k.size = level) (hjl : j.size = level) :
    k = j := by
  have hp := hd.consumedPrefix k hk j hj
  rwa [Nibbles.take_of_size_le k level (by omega),
    Nibbles.take_of_size_le j level (by omega)] at hp

/-- An ending key equals the consumed prefix of any representative. -/
theorem ending_prefix_key {obj : Std.ExtTreeMap Nibbles ByteArray} {level : Nat}
    (hd : PatricializeDomain obj level) {representative k : Nibbles}
    (hr : representative ∈ obj) (hk : k ∈ obj) (hl : k.size = level) :
    representative.take level = k := by
  have hp := hd.consumedPrefix representative hr k hk
  rwa [Nibbles.take_of_size_le k level (by omega)] at hp

/-- Optional branch-value lookup is independent of the representative, including
absent and empty byte values. This is not whole-constructor choice independence on its own. -/
theorem branch_value_representative_eq {obj : Std.ExtTreeMap Nibbles ByteArray} {level : Nat}
    (hd : PatricializeDomain obj level) {a b : Nibbles} (ha : a ∈ obj) (hb : b ∈ obj) :
    obj[a.take level]? = obj[b.take level]? := by
  rw [hd.consumedPrefix a ha b hb]

/-- A shared extension preserves the domain when all full keys reach and agree
through the advanced depth. Strict descent additionally needs positive advancement. -/
theorem extension {obj : Std.ExtTreeMap Nibbles ByteArray} {level amount : Nat}
    (hd : ∀ k : Nibbles, k ∈ obj → level + amount ≤ k.size)
    (hp : ∀ k : Nibbles, k ∈ obj → ∀ j : Nibbles, j ∈ obj →
      k.take (level + amount) = j.take (level + amount)) :
    PatricializeDomain obj (level + amount) := ⟨hd, hp⟩

end PatricializeDomain

/-! Private support uses packed bounded digit access, guarded before reading.
The list model occurs only in proofs; keys are never shortened by partitioning. -/

private def inChild (level : Nat) (digit : Fin 16) (k : Nibbles) : Bool :=
  if h : level < k.size then decide (k.get ⟨level, h⟩ = digit) else false

private def childPartition (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (digit : Fin 16) : Std.ExtTreeMap Nibbles ByteArray :=
  obj.filter fun k _ ↦ inChild level digit k

private theorem inChild_model (level : Nat) (digit : Fin 16) (k : Nibbles) :
    inChild level digit k = true ↔ k.toList[level]? = some digit := by
  unfold inChild
  by_cases h : level < k.size
  · rw [dite_eq_left h, decide_eq_true_eq,
      List.getElem?_eq_getElem (by rw [Nibbles.length_toList]; exact h),
      Nibbles.getElem_toList _ _ h]
    simp
  · rw [dite_eq_right h, List.getElem?_eq_none (by rw [Nibbles.length_toList]; omega)]
    simp

private theorem child_keys (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (digit : Fin 16) :
    (childPartition obj level digit).keys = obj.keys.filter (inChild level digit) :=
  Std.ExtTreeMap.keys_filter_key

private theorem mem_child {obj : Std.ExtTreeMap Nibbles ByteArray} {level : Nat}
    {digit : Fin 16} {k : Nibbles} :
    k ∈ childPartition obj level digit ↔ k ∈ obj ∧ k.toList[level]? = some digit := by
  rw [← Std.ExtTreeMap.mem_keys, child_keys, List.mem_filter, Std.ExtTreeMap.mem_keys,
    inChild_model]

private theorem child_lookup (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (digit : Fin 16) (k : Nibbles) :
    (childPartition obj level digit)[k]? = obj[k]?.filter (fun _ ↦ inChild level digit k) :=
  Std.ExtTreeMap.getElem?_filter'

/-- An ending key is excluded from every numeric child, without an out-of-range read. -/
theorem PatricializeDomain.ending_not_mem_child
    {obj : Std.ExtTreeMap Nibbles ByteArray} {level : Nat} (digit : Fin 16) {k : Nibbles}
    (hk : k.size = level) :
    k ∉ obj.filter (fun key _ ↦
      if h : level < key.size then decide (key.get ⟨level, h⟩ = digit) else false) := by
  change k ∉ childPartition obj level digit
  intro hc
  have h := (mem_child.mp hc).2
  rw [List.getElem?_eq_none (by rw [Nibbles.length_toList]; omega)] at h
  contradiction

/-- Each of the sixteen guarded numeric partitions preserves the domain at the
next depth. Empty partitions need no exceptional premise. -/
theorem PatricializeDomain.child {obj : Std.ExtTreeMap Nibbles ByteArray} {level : Nat}
    (hd : PatricializeDomain obj level) (digit : Fin 16) :
    PatricializeDomain
      (obj.filter (fun k _ ↦
        if h : level < k.size then decide (k.get ⟨level, h⟩ = digit) else false))
      (level + 1) := by
  change PatricializeDomain (childPartition obj level digit) (level + 1)
  constructor
  · intro k hk
    have h := (mem_child.mp hk).2
    obtain ⟨hb, _⟩ := List.getElem?_eq_some_iff.mp h
    rw [Nibbles.length_toList] at hb
    omega
  · intro k hk j hj
    obtain ⟨hk, hkd⟩ := mem_child.mp hk
    obtain ⟨hj, hjd⟩ := mem_child.mp hj
    obtain ⟨hkb, hkg⟩ := List.getElem?_eq_some_iff.mp hkd
    obtain ⟨hjb, hjg⟩ := List.getElem?_eq_some_iff.mp hjd
    apply Nibbles.ext
    rw [Nibbles.toList_take, Nibbles.toList_take,
      List.take_succ_eq_append_getElem hkb, List.take_succ_eq_append_getElem hjb,
      hkg, hjg]
    have hp := congrArg Nibbles.toList (hd.consumedPrefix k hk j hj)
    rw [Nibbles.toList_take, Nibbles.toList_take] at hp
    rw [hp]

/-! Strict sum descent. The sum is a termination measure, not a cost claim.
It enumerates the actual finite map's unique full keys through public Std laws. -/

private def remainingSum (keys : List Nibbles) (level : Nat) : Nat :=
  (keys.map fun key ↦ key.size - level).sum

private def remainingMeasure (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat) : Nat :=
  remainingSum obj.keys level

private theorem remainingSum_nil (level : Nat) : remainingSum [] level = 0 := rfl

private theorem remainingSum_cons (key : Nibbles) (keys : List Nibbles) (level : Nat) :
    remainingSum (key :: keys) level = (key.size - level) + remainingSum keys level := rfl

private theorem remainingSum_zero_mem {keys : List Nibbles} {level : Nat}
    (hz : remainingSum keys level = 0) {k : Nibbles} (hk : k ∈ keys) : k.size ≤ level := by
  induction keys with
  | nil => simp at hk
  | cons a keys ih =>
    rw [remainingSum_cons] at hz
    simp only [List.mem_cons] at hk
    rcases hk with rfl | hk
    · omega
    · exact ih (by omega) hk

private theorem multikey_measure_pos {obj : Std.ExtTreeMap Nibbles ByteArray} {level : Nat}
    (hd : PatricializeDomain obj level) (hm : 1 < obj.size) : 0 < remainingMeasure obj level := by
  have hn := Std.ExtTreeMap.nodup_keys (t := obj)
  have hl := Std.ExtTreeMap.length_keys (t := obj)
  cases he : obj.keys with
  | nil => simp [he] at hl; omega
  | cons k ks =>
    cases hs : ks with
    | nil => simp [he, hs] at hl; omega
    | cons j js =>
      apply Nat.pos_of_ne_zero
      intro hzero
      have hz : remainingSum obj.keys level = 0 := hzero
      have hk : k ∈ obj := Std.ExtTreeMap.mem_keys.mp (by simp [he])
      have hj : j ∈ obj := Std.ExtTreeMap.mem_keys.mp (by simp [he, hs])
      have hkl := remainingSum_zero_mem hz (k := k) (by simp [he])
      have hjl := remainingSum_zero_mem hz (k := j) (by simp [he, hs])
      have eq := hd.ending_unique hk hj (by have := hd.depth k hk; omega)
        (by have := hd.depth j hj; omega)
      simp only [he, hs, List.nodup_cons] at hn
      exact hn.1 (by simp [eq])

private theorem remainingSum_extension_lt {keys : List Nibbles} {level amount : Nat}
    (hne : keys ≠ []) (ha : 0 < amount)
    (hd : ∀ k, k ∈ keys → level + amount ≤ k.size) :
    remainingSum keys (level + amount) < remainingSum keys level := by
  induction keys with
  | nil => contradiction
  | cons k ks ih =>
    have hk := hd k (by simp)
    have hks : remainingSum ks (level + amount) ≤ remainingSum ks level := by
      cases he : ks with
      | nil => simp [remainingSum]
      | cons j js =>
        have hh := ih (by simp [he]) (fun a h ↦ hd a (by simp [h]))
        rw [he] at *
        omega
    rw [remainingSum_cons, remainingSum_cons]
    omega

private theorem extension_measure_lt {obj : Std.ExtTreeMap Nibbles ByteArray}
    {level amount : Nat} (hm : 0 < obj.size) (ha : 0 < amount)
    (hd : PatricializeDomain obj (level + amount)) :
    remainingMeasure obj (level + amount) < remainingMeasure obj level := by
  apply remainingSum_extension_lt
  · intro he
    have hl := Std.ExtTreeMap.length_keys (t := obj)
    simp [he] at hl
    omega
  · exact ha
  · intro k hk
    exact hd.depth k (Std.ExtTreeMap.mem_keys.mp hk)

private theorem remainingSum_child_le (keys : List Nibbles) (level : Nat) (digit : Fin 16) :
    remainingSum (keys.filter (inChild level digit)) (level + 1) ≤ remainingSum keys level := by
  induction keys with
  | nil => simp [remainingSum]
  | cons k ks ih =>
    simp only [List.filter_cons]
    split <;> simp only [remainingSum_cons] <;> omega

private theorem remainingSum_child_lt {keys : List Nibbles} {level : Nat} {digit : Fin 16}
    (hp : 0 < remainingSum keys level) :
    remainingSum (keys.filter (inChild level digit)) (level + 1) < remainingSum keys level := by
  induction keys with
  | nil => simp [remainingSum] at hp
  | cons k ks ih =>
    simp only [List.filter_cons]
    split
    · rename_i hc
      have hget := (inChild_model level digit k).mp hc
      obtain ⟨hb, _⟩ := List.getElem?_eq_some_iff.mp hget
      rw [Nibbles.length_toList] at hb
      have htail := remainingSum_child_le ks level digit
      simp only [remainingSum_cons]
      omega
    · have htail := remainingSum_child_le ks level digit
      by_cases ht : 0 < remainingSum ks level
      · have hh := ih ht
        simp only [remainingSum_cons]
        omega
      · simp only [remainingSum_cons] at hp ⊢
        omega

private theorem child_measure_lt {obj : Std.ExtTreeMap Nibbles ByteArray} {level : Nat}
    (hd : PatricializeDomain obj level) (hm : 1 < obj.size) (digit : Fin 16) :
    remainingMeasure (childPartition obj level digit) (level + 1) <
      remainingMeasure obj level := by
  unfold remainingMeasure
  rw [child_keys]
  exact remainingSum_child_lt (multikey_measure_pos hd hm)

/-! Longest shared-prefix support. Only the proof model copies suffixes.
The executable scan reads bounded full-key indices and stops at its current cap. -/

private def sharedPrefixScan (a b : Nibbles) : Nat → Nat → Nat
  | 0, _ => 0
  | remaining + 1, i =>
    if ha : i < a.size then
      if hb : i < b.size then
        if a.get ⟨i, ha⟩ = b.get ⟨i, hb⟩ then
          1 + sharedPrefixScan a b remaining (i + 1)
        else 0
      else 0
    else 0

private theorem sharedPrefixScan_model (a b : Nibbles) (remaining i : Nat)
    (ha : i + remaining ≤ a.size) (hb : i + remaining ≤ b.size) :
    sharedPrefixScan a b remaining i =
      min remaining (commonPrefixLengthModel (a.toList.drop i) (b.toList.drop i)) := by
  induction remaining generalizing i with
  | zero => simp [sharedPrefixScan]
  | succ remaining ih =>
    have hia : i < a.size := by omega
    have hib : i < b.size := by omega
    have ea : a.toList.drop i = a.get ⟨i, hia⟩ :: a.toList.drop (i + 1) := by
      rw [← List.getElem_cons_drop (by rw [Nibbles.length_toList]; exact hia),
        Nibbles.getElem_toList]
    have eb : b.toList.drop i = b.get ⟨i, hib⟩ :: b.toList.drop (i + 1) := by
      rw [← List.getElem_cons_drop (by rw [Nibbles.length_toList]; exact hib),
        Nibbles.getElem_toList]
    rw [sharedPrefixScan, dite_eq_left hia, dite_eq_left hib, ea, eb, commonPrefixLengthModel]
    split
    · rw [ih (i + 1) (by omega) (by omega)]
      omega
    · simp

private def pairSharedPrefix (a b : Nibbles) (level cap : Nat) : Nat :=
  sharedPrefixScan a b (min cap (min (a.size - level) (b.size - level))) level

private theorem pairSharedPrefix_model (a b : Nibbles) (level cap : Nat) :
    pairSharedPrefix a b level cap =
      min cap (commonPrefixLength (a.drop level) (b.drop level)) := by
  by_cases ha : level ≤ a.size
  · by_cases hb : level ≤ b.size
    · rw [pairSharedPrefix, sharedPrefixScan_model _ _ _ _ (by omega) (by omega)]
      rw [← Nibbles.toList_drop, ← Nibbles.toList_drop, ← commonPrefixLength_eq_model]
      have hleft := commonPrefixLength_le_left (a.drop level) (b.drop level)
      have hright := commonPrefixLength_le_right (a.drop level) (b.drop level)
      rw [Nibbles.size_drop] at hleft hright
      omega
    · have hz : b.size - level = 0 := by omega
      simp only [pairSharedPrefix, hz, Nat.min_zero, sharedPrefixScan]
      have h := commonPrefixLength_le_right (a.drop level) (b.drop level)
      rw [Nibbles.size_drop, hz] at h
      simp [Nat.eq_zero_of_le_zero h]
  · have hz : a.size - level = 0 := by omega
    simp only [pairSharedPrefix, hz, Nat.zero_min, Nat.min_zero, sharedPrefixScan]
    have h := commonPrefixLength_le_left (a.drop level) (b.drop level)
    rw [Nibbles.size_drop, hz] at h
    simp [Nat.eq_zero_of_le_zero h]

private def sharedPrefixFold (representative : Nibbles) (level : Nat) :
    List Nibbles → Nat → Nat
  | [], cap => cap
  | key :: keys, cap =>
    if cap = 0 then 0
    else sharedPrefixFold representative level keys
      (pairSharedPrefix representative key level cap)

private def sharedPrefixFoldModel (representative : List (Fin 16)) (level : Nat) :
    List (List (Fin 16)) → Nat → Nat
  | [], cap => cap
  | key :: keys, cap => sharedPrefixFoldModel representative level keys
      (min cap (commonPrefixLengthModel (representative.drop level) (key.drop level)))

private theorem sharedPrefixFoldModel_zero (representative : List (Fin 16)) (level : Nat)
    (keys : List (List (Fin 16))) : sharedPrefixFoldModel representative level keys 0 = 0 := by
  induction keys with
  | nil => rfl
  | cons key keys ih => simpa only [sharedPrefixFoldModel, Nat.zero_min] using ih

private theorem sharedPrefixFold_model (representative : Nibbles) (level : Nat)
    (keys : List Nibbles) (cap : Nat) :
    sharedPrefixFold representative level keys cap =
      sharedPrefixFoldModel representative.toList level (keys.map Nibbles.toList) cap := by
  induction keys generalizing cap with
  | nil => rfl
  | cons key keys ih =>
    rw [sharedPrefixFold]
    by_cases hz : cap = 0
    · rw [ite_eq_left hz, hz, sharedPrefixFoldModel_zero]
    · rw [ite_eq_right hz, ih, pairSharedPrefix_model, commonPrefixLength_eq_model,
        Nibbles.toList_drop, Nibbles.toList_drop]
      rfl

private def sharedPrefixFrom (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (representative : Nibbles) : Nat :=
  sharedPrefixFold representative level obj.keys (representative.size - level)

private def selectSharedPrefix (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat) :
    Option (Nibbles × Nat) :=
  match obj.keys with
  | [] => none
  | representative :: keys => some (representative,
      sharedPrefixFold representative level (representative :: keys) (representative.size - level))

private theorem sharedPrefixFold_le_iff (representative : Nibbles) (level : Nat)
    (keys : List Nibbles) (cap amount : Nat) :
    amount ≤ sharedPrefixFold representative level keys cap ↔
      amount ≤ cap ∧ ∀ key, key ∈ keys →
        amount ≤ commonPrefixLength (representative.drop level) (key.drop level) := by
  induction keys generalizing cap with
  | nil => simp [sharedPrefixFold]
  | cons key keys ih =>
    rw [sharedPrefixFold]
    by_cases hz : cap = 0
    · simp only [hz, ite_true, Nat.le_zero_eq]
      constructor
      · intro h
        subst amount
        simp
      · exact fun h ↦ h.1
    · rw [ite_eq_right hz, ih, pairSharedPrefix_model]
      simp only [Nat.le_min, List.mem_cons, forall_eq_or_imp, and_assoc]

private theorem take_advance_iff (a b : Nibbles) (level amount : Nat)
    (hp : a.take level = b.take level) :
    a.take (level + amount) = b.take (level + amount) ↔
      (a.drop level).take amount = (b.drop level).take amount := by
  constructor
  · intro h
    have hh := congrArg (fun key : Nibbles ↦ key.drop level) h
    simpa only [Nibbles.drop_take, Nibbles.take_drop] using hh
  · intro h
    apply Nibbles.ext
    have hp' := congrArg Nibbles.toList hp
    have h' := congrArg Nibbles.toList h
    simp only [Nibbles.toList_take, Nibbles.toList_drop] at hp' h' ⊢
    have ea := List.take_append_drop level (a.toList.take (level + amount))
    have eb := List.take_append_drop level (b.toList.take (level + amount))
    rw [List.take_take, Nat.min_eq_left (by omega), List.drop_take] at ea eb
    rw [← ea, ← eb, hp']
    rw [Nat.add_sub_cancel_left, h']

private theorem pairSharedPrefix_le_iff (a b : Nibbles) (level cap amount : Nat)
    (ha : level ≤ a.size) (hb : level ≤ b.size) (hp : a.take level = b.take level) :
    amount ≤ pairSharedPrefix a b level cap ↔
      amount ≤ cap ∧ level + amount ≤ a.size ∧ level + amount ≤ b.size ∧
        a.take (level + amount) = b.take (level + amount) := by
  rw [pairSharedPrefix_model, Nat.le_min]
  constructor
  · rintro ⟨hc, h⟩
    have hla := commonPrefixLength_le_left (a.drop level) (b.drop level)
    have hlb := commonPrefixLength_le_right (a.drop level) (b.drop level)
    rw [Nibbles.size_drop] at hla hlb
    have hsa : amount ≤ (a.drop level).size := by rw [Nibbles.size_drop]; omega
    have hsb : amount ≤ (b.drop level).size := by rw [Nibbles.size_drop]; omega
    exact ⟨hc, by omega, by omega, (take_advance_iff a b level amount hp).mpr
      ((Nibbles.take_eq_iff_le_commonPrefixLength _ _ amount hsa hsb).mpr h)⟩
  · rintro ⟨hc, hla, hlb, he⟩
    exact ⟨hc, (Nibbles.take_eq_iff_le_commonPrefixLength _ _ amount
      (by rw [Nibbles.size_drop]; omega) (by rw [Nibbles.size_drop]; omega)).mp
      ((take_advance_iff a b level amount hp).mp he)⟩

/-- The fold is characterized by the actual advanced full-key domain. This is
proof support for the C7 constructor, not a public selection operation. -/
private theorem sharedPrefixFrom_le_iff {obj : Std.ExtTreeMap Nibbles ByteArray}
    {level : Nat} (hd : PatricializeDomain obj level) (representative : Nibbles)
    (hr : representative ∈ obj) (amount : Nat) :
    amount ≤ sharedPrefixFrom obj level representative ↔
      PatricializeDomain obj (level + amount) := by
  rw [sharedPrefixFrom, sharedPrefixFold_le_iff]
  constructor
  · rintro ⟨hc, hkeys⟩
    have hra := hd.depth representative hr
    have pair : ∀ key, key ∈ obj → level + amount ≤ key.size ∧
        representative.take (level + amount) = key.take (level + amount) := by
      intro key hk
      have hcp := hkeys key (Std.ExtTreeMap.mem_keys.mpr hk)
      have hp : amount ≤ pairSharedPrefix representative key level
          (representative.size - level) := by
        rw [pairSharedPrefix_model, Nat.le_min]
        exact ⟨hc, hcp⟩
      have hh := (pairSharedPrefix_le_iff representative key level
        (representative.size - level) amount hra (hd.depth key hk)
        (hd.consumedPrefix representative hr key hk)).mp hp
      exact ⟨hh.2.2.1, hh.2.2.2⟩
    constructor
    · exact fun key hk ↦ (pair key hk).1
    · intro key hk other ho
      exact (pair key hk).2.symm.trans (pair other ho).2
  · intro h
    have hc : amount ≤ representative.size - level := by
      have hh := h.depth representative hr
      omega
    refine ⟨hc, ?_⟩
    intro key hk
    have hk' := Std.ExtTreeMap.mem_keys.mp hk
    have hp := (pairSharedPrefix_le_iff representative key level
      (representative.size - level) amount (hd.depth representative hr)
      (hd.depth key hk') (hd.consumedPrefix representative hr key hk')).mpr
      ⟨hc, h.depth representative hr, h.depth key hk',
        h.consumedPrefix representative hr key hk'⟩
    rw [pairSharedPrefix_model, Nat.le_min] at hp
    exact hp.2

private theorem sharedPrefixFrom_domain {obj : Std.ExtTreeMap Nibbles ByteArray}
    {level : Nat} (hd : PatricializeDomain obj level) (representative : Nibbles)
    (hr : representative ∈ obj) :
    PatricializeDomain obj (level + sharedPrefixFrom obj level representative) :=
  (sharedPrefixFrom_le_iff hd representative hr _).mp (Nat.le_refl _)

private theorem sharedPrefixFrom_bound {obj : Std.ExtTreeMap Nibbles ByteArray}
    {level : Nat} (hd : PatricializeDomain obj level) (representative : Nibbles)
    (hr : representative ∈ obj) (key : Nibbles) (hk : key ∈ obj) :
    sharedPrefixFrom obj level representative ≤ key.size - level := by
  have hh := (sharedPrefixFrom_domain hd representative hr).depth key hk
  omega

private theorem sharedPrefixFrom_maximal {obj : Std.ExtTreeMap Nibbles ByteArray}
    {level amount : Nat} (hd : PatricializeDomain obj level) (representative : Nibbles)
    (hr : representative ∈ obj) (ha : PatricializeDomain obj (level + amount)) :
    amount ≤ sharedPrefixFrom obj level representative :=
  (sharedPrefixFrom_le_iff hd representative hr amount).mpr ha

private theorem sharedPrefixFrom_representative_eq {obj : Std.ExtTreeMap Nibbles ByteArray}
    {level : Nat} (hd : PatricializeDomain obj level) (a b : Nibbles)
    (ha : a ∈ obj) (hb : b ∈ obj) :
    sharedPrefixFrom obj level a = sharedPrefixFrom obj level b := by
  apply Nat.le_antisymm
  · exact sharedPrefixFrom_maximal hd b hb (sharedPrefixFrom_domain hd a ha)
  · exact sharedPrefixFrom_maximal hd a ha (sharedPrefixFrom_domain hd b hb)

private theorem sharedPrefixFrom_keys_eq
    {obj other : Std.ExtTreeMap Nibbles ByteArray} {level : Nat}
    (hd : PatricializeDomain obj level) (ho : PatricializeDomain other level)
    (same : ∀ key : Nibbles, key ∈ obj ↔ key ∈ other)
    (a b : Nibbles) (ha : a ∈ obj) (hb : b ∈ other) :
    sharedPrefixFrom obj level a = sharedPrefixFrom other level b := by
  have transfer : ∀ amount, PatricializeDomain obj (level + amount) ↔
      PatricializeDomain other (level + amount) := by
    intro amount
    constructor
    · intro h
      exact ⟨fun key hk ↦ h.depth key ((same key).mpr hk),
        fun key hk other ho ↦ h.consumedPrefix key ((same key).mpr hk)
          other ((same other).mpr ho)⟩
    · intro h
      exact ⟨fun key hk ↦ h.depth key ((same key).mp hk),
        fun key hk other ho ↦ h.consumedPrefix key ((same key).mp hk)
          other ((same other).mp ho)⟩
  apply Nat.le_antisymm
  · exact sharedPrefixFrom_maximal ho b hb
      ((transfer _).mp (sharedPrefixFrom_domain hd a ha))
  · exact sharedPrefixFrom_maximal hd a ha
      ((transfer _).mpr (sharedPrefixFrom_domain ho b hb))

private theorem sharedPrefixFrom_prefix_representative_eq
    {obj : Std.ExtTreeMap Nibbles ByteArray} {level : Nat}
    (hd : PatricializeDomain obj level) (a b : Nibbles) (ha : a ∈ obj) (hb : b ∈ obj) :
    a.extract level (level + sharedPrefixFrom obj level a) =
      b.extract level (level + sharedPrefixFrom obj level b) := by
  rw [← sharedPrefixFrom_representative_eq hd a b ha hb]
  have hh := (sharedPrefixFrom_domain hd a ha).consumedPrefix a ha b hb
  have he := congrArg (fun key : Nibbles ↦ key.drop level) hh
  simpa only [Nibbles.drop_take] using he

private theorem sharedPrefixFrom_positive_descent
    {obj : Std.ExtTreeMap Nibbles ByteArray} {level : Nat}
    (hd : PatricializeDomain obj level) (representative : Nibbles)
    (hr : representative ∈ obj) (hp : 0 < sharedPrefixFrom obj level representative) :
    PatricializeDomain obj (level + sharedPrefixFrom obj level representative) ∧
      remainingMeasure obj (level + sharedPrefixFrom obj level representative) <
        remainingMeasure obj level := by
  have he := sharedPrefixFrom_domain hd representative hr
  refine ⟨he, extension_measure_lt ?_ hp he⟩
  have hm := Std.ExtTreeMap.length_keys (t := obj)
  have hmem := Std.ExtTreeMap.mem_keys.mpr hr
  have hh : 0 < obj.keys.length := List.length_pos_of_mem hmem
  omega

private theorem sharedPrefixFrom_zero_iff
    {obj : Std.ExtTreeMap Nibbles ByteArray} {level : Nat}
    (hd : PatricializeDomain obj level) (representative : Nibbles)
    (hr : representative ∈ obj) :
    sharedPrefixFrom obj level representative = 0 ↔
      ¬ PatricializeDomain obj (level + 1) := by
  have hh := sharedPrefixFrom_le_iff hd representative hr 1
  constructor
  · intro hz hn
    have hp := hh.mpr hn
    omega
  · intro hn
    by_cases hz : sharedPrefixFrom obj level representative = 0
    · exact hz
    · exact False.elim (hn (hh.mp (by omega)))

private theorem selectSharedPrefix_none_iff (obj : Std.ExtTreeMap Nibbles ByteArray)
    (level : Nat) : selectSharedPrefix obj level = none ↔ obj.keys = [] := by
  cases he : obj.keys <;> simp [selectSharedPrefix, he]

private theorem selectSharedPrefix_member
    {obj : Std.ExtTreeMap Nibbles ByteArray} {level : Nat} {representative : Nibbles}
    {amount : Nat} (h : selectSharedPrefix obj level = some (representative, amount)) :
    representative ∈ obj ∧ amount = sharedPrefixFrom obj level representative := by
  unfold selectSharedPrefix at h
  cases he : obj.keys with
  | nil => simp [he] at h
  | cons key keys =>
    simp only [he, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Std.ExtTreeMap.mem_keys.mp (by simp [he]), by rw [sharedPrefixFrom, he]⟩

private theorem selectSharedPrefix_domain
    {obj : Std.ExtTreeMap Nibbles ByteArray} {level : Nat}
    (hd : PatricializeDomain obj level) {representative : Nibbles} {amount : Nat}
    (h : selectSharedPrefix obj level = some (representative, amount)) :
    PatricializeDomain obj (level + amount) := by
  obtain ⟨hr, rfl⟩ := selectSharedPrefix_member h
  exact sharedPrefixFrom_domain hd representative hr

/-! Bounded sixteen-child branch support for EELS `:564–581`.
Whole-key filters and optional ending lookup preserve Q50 empty values.
The callback is supplied, not recursive construction. Its erased equality
witness identifies the actual partition for Root-local descent proofs.
Sequencing equations state LawfulMonad premises exactly where monad laws are used. -/

private theorem inChild_reference (level : Nat) (digit : Fin 16) (key : Nibbles) :
    inChild level digit key = decide (key.toList[level]? = some digit) := by
  unfold inChild
  by_cases h : level < key.size
  · rw [dite_eq_left h,
      List.getElem?_eq_getElem (by rw [Nibbles.length_toList]; exact h),
      Nibbles.getElem_toList _ _ h]
    simp
  · rw [dite_eq_right h, List.getElem?_eq_none (by rw [Nibbles.length_toList]; omega)]
    simp

private theorem childPartition_model (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (digit : Fin 16) : childPartition obj level digit =
      obj.filter (fun key _ ↦ decide (key.toList[level]? = some digit)) := by
  apply Std.ExtTreeMap.ext_getElem?
  intro key
  rw [childPartition, Std.ExtTreeMap.getElem?_filter', Std.ExtTreeMap.getElem?_filter',
    inChild_reference]

private theorem child_lookup_model (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (digit : Fin 16) (key : Nibbles) :
    (childPartition obj level digit)[key]? =
      obj[key]?.filter (fun _ ↦ decide (key.toList[level]? = some digit)) := by
  rw [childPartition, Std.ExtTreeMap.getElem?_filter', inChild_reference]

private theorem child_disjoint {obj : Std.ExtTreeMap Nibbles ByteArray} {level : Nat}
    {a b : Fin 16} (hne : a ≠ b) (key : Nibbles) :
    ¬ (key ∈ childPartition obj level a ∧ key ∈ childPartition obj level b) := by
  rintro ⟨ha, hb⟩
  have ea := (mem_child.mp ha).2
  have eb := (mem_child.mp hb).2
  exact hne (Option.some.inj (ea.symm.trans eb))

private theorem child_coverage {obj : Std.ExtTreeMap Nibbles ByteArray} {level : Nat}
    {key : Nibbles} :
    (∃ digit : Fin 16, key ∈ childPartition obj level digit) ↔ key ∈ obj ∧ level < key.size := by
  constructor
  · rintro ⟨digit, hk⟩
    obtain ⟨hk, hd⟩ := mem_child.mp hk
    obtain ⟨hl, _⟩ := List.getElem?_eq_some_iff.mp hd
    rw [Nibbles.length_toList] at hl
    exact ⟨hk, hl⟩
  · rintro ⟨hk, hl⟩
    refine ⟨key.get ⟨level, hl⟩, mem_child.mpr ⟨hk, ?_⟩⟩
    rw [List.getElem?_eq_getElem (by rw [Nibbles.length_toList]; exact hl),
      Nibbles.getElem_toList]

private theorem ending_excluded (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (digit : Fin 16) (key : Nibbles) (h : key.size = level) :
    key ∉ childPartition obj level digit :=
  PatricializeDomain.ending_not_mem_child digit h

private theorem childPartition_domain {obj : Std.ExtTreeMap Nibbles ByteArray} {level : Nat}
    (hd : PatricializeDomain obj level) (digit : Fin 16) :
    PatricializeDomain (childPartition obj level digit) (level + 1) := hd.child digit

private structure BranchParts where
  children : Vector (Std.ExtTreeMap Nibbles ByteArray) 16
  ending : Option ByteArray

private def branchParts (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (representative : Nibbles) : BranchParts :=
  ⟨Vector.ofFn (childPartition obj level), obj[representative.take level]?⟩

private theorem branchParts_get (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (representative : Nibbles) (digit : Fin 16) :
    (branchParts obj level representative).children[digit.val] =
      childPartition obj level digit := by
  simp only [branchParts, Vector.getElem_ofFn]

private theorem branchParts_ending_present {obj : Std.ExtTreeMap Nibbles ByteArray}
    {level : Nat} (hd : PatricializeDomain obj level) (a key : Nibbles)
    (ha : a ∈ obj) (hk : key ∈ obj) (hl : key.size = level) :
    (branchParts obj level a).ending = some (obj[key]'hk) := by
  change obj[a.take level]? = _
  rw [hd.ending_prefix_key ha hk hl]
  exact Std.ExtTreeMap.getElem?_eq_some_getElem hk

private theorem branchParts_ending_representative {obj : Std.ExtTreeMap Nibbles ByteArray}
    {level : Nat} (hd : PatricializeDomain obj level) (a b : Nibbles)
    (ha : a ∈ obj) (hb : b ∈ obj) : branchParts obj level a = branchParts obj level b := by
  unfold branchParts
  rw [hd.branch_value_representative_eq ha hb]

private theorem ending_default_representative {obj : Std.ExtTreeMap Nibbles ByteArray}
    {level : Nat} (hd : PatricializeDomain obj level) (a b : Nibbles)
    (ha : a ∈ obj) (hb : b ∈ obj) :
    (branchParts obj level a).ending.getD ByteArray.empty =
      (branchParts obj level b).ending.getD ByteArray.empty := by
  rw [branchParts_ending_representative hd a b ha hb]

private theorem branchParts_ending_none_iff {obj : Std.ExtTreeMap Nibbles ByteArray}
    {level : Nat} (hd : PatricializeDomain obj level) (a : Nibbles) (ha : a ∈ obj) :
    (branchParts obj level a).ending = none ↔
      ¬ ∃ key : Nibbles, key ∈ obj ∧ key.size = level := by
  constructor
  · intro hn
    rintro ⟨key, hk, hl⟩
    have hp := branchParts_ending_present hd a key ha hk hl
    rw [hn] at hp
    contradiction
  · intro hn
    apply Std.ExtTreeMap.getElem?_eq_none
    intro hk
    have hl : (a.take level).size = level := by
      rw [Nibbles.size_take, Nat.min_eq_left (hd.depth a ha)]
    exact hn ⟨a.take level, hk, hl⟩

private def childAction {m : Type → Type} [Monad m] [KeccakQuery m]
    (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (hd : PatricializeDomain obj level)
    (construct : (digit : Fin 16) → (child : Std.ExtTreeMap Nibbles ByteArray) →
      child = childPartition obj level digit →
      PatricializeDomain child (level + 1) → m (Option InternalNode))
    (digit : Fin 16) : m RlpItem := do
  let child ← construct digit (childPartition obj level digit) rfl (childPartition_domain hd digit)
  encodeInternalNode child

private def childReferences {m : Type → Type} [Monad m] [KeccakQuery m]
    (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (hd : PatricializeDomain obj level)
    (construct : (digit : Fin 16) → (child : Std.ExtTreeMap Nibbles ByteArray) →
      child = childPartition obj level digit →
      PatricializeDomain child (level + 1) → m (Option InternalNode)) :
    m (Vector RlpItem 16) :=
  Vector.ofFnM (childAction obj level hd construct)

private def branchStage {m : Type → Type} [Monad m] [KeccakQuery m]
    (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (hd : PatricializeDomain obj level) (representative : Nibbles)
    (construct : (digit : Fin 16) → (child : Std.ExtTreeMap Nibbles ByteArray) →
      child = childPartition obj level digit →
      PatricializeDomain child (level + 1) → m (Option InternalNode)) :
    m InternalNode := do
  let children ← childReferences obj level hd construct
  pure (.branch children (.bytes (obj[representative.take level]?.getD ByteArray.empty)))

private theorem childReferences_first {m : Type → Type} [Monad m] [LawfulMonad m]
    [KeccakQuery m] (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (hd : PatricializeDomain obj level)
    (construct : (digit : Fin 16) → (child : Std.ExtTreeMap Nibbles ByteArray) →
      child = childPartition obj level digit →
      PatricializeDomain child (level + 1) → m (Option InternalNode)) :
    childReferences obj level hd construct = (do
      let first ← childAction obj level hd construct 0
      let rest ← Vector.ofFnM (fun digit : Fin 15 ↦
        childAction obj level hd construct digit.succ)
      pure ((#v[first] ++ rest).cast (by omega))) :=
  by
    unfold childReferences
    simpa using (Vector.ofFnM_succ' (f := childAction obj level hd construct))

private theorem childReferences_list {m : Type → Type} [Monad m] [LawfulMonad m]
    [KeccakQuery m] (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (hd : PatricializeDomain obj level)
    (construct : (digit : Fin 16) → (child : Std.ExtTreeMap Nibbles ByteArray) →
      child = childPartition obj level digit →
      PatricializeDomain child (level + 1) → m (Option InternalNode)) :
    Vector.toList <$> childReferences obj level hd construct =
      List.ofFnM (childAction obj level hd construct) := Vector.toList_ofFnM

private theorem branchStage_assembled {m : Type → Type} [Monad m] [LawfulMonad m]
    [KeccakQuery m] (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (hd : PatricializeDomain obj level) (representative : Nibbles)
    (construct : (digit : Fin 16) → (child : Std.ExtTreeMap Nibbles ByteArray) →
      child = childPartition obj level digit →
      PatricializeDomain child (level + 1) → m (Option InternalNode)) :
    (fun node ↦ assembleInternalNode (some node)) <$>
      branchStage obj level hd representative construct = (do
      let items ← List.ofFnM (childAction obj level hd construct)
      pure (RlpItem.list (items ++
        [RlpItem.bytes ((branchParts obj level representative).ending.getD ByteArray.empty)]))) := by
  unfold branchStage
  simp only [map_bind, map_pure, assembleInternalNode_branch]
  rw [← childReferences_list obj level hd construct]
  simp only [bind_map_left, bind_pure, branchParts]

private theorem branchStage_representative {m : Type → Type} [Monad m] [KeccakQuery m]
    (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (hd : PatricializeDomain obj level) (a b : Nibbles) (ha : a ∈ obj) (hb : b ∈ obj)
    (construct : (digit : Fin 16) → (child : Std.ExtTreeMap Nibbles ByteArray) →
      child = childPartition obj level digit →
      PatricializeDomain child (level + 1) → m (Option InternalNode)) :
    branchStage obj level hd a construct = branchStage obj level hd b construct := by
  unfold branchStage
  rw [hd.branch_value_representative_eq ha hb]

private theorem childAction_construct_error {m : Type → Type} [Monad m] [LawfulMonad m]
    {ε : Type} [KeccakQuery (ExceptT ε m)] (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (hd : PatricializeDomain obj level)
    (construct : (digit : Fin 16) → (child : Std.ExtTreeMap Nibbles ByteArray) →
      child = childPartition obj level digit →
      PatricializeDomain child (level + 1) → ExceptT ε m (Option InternalNode))
    (digit : Fin 16) (error : ε)
    (failed : (construct digit (childPartition obj level digit) rfl
      (childPartition_domain hd digit)).run =
      pure (.error error)) :
    (childAction (m := ExceptT ε m) obj level hd construct digit).run = pure (.error error) := by
  rw [childAction, ExceptT.run_bind, failed]
  simp

/-- Digit-zero failure with callback run equal to pure error. This states no
arbitrary effectful or later-digit error law; those finite cases are tested separately. -/
private theorem branchStage_first_error {m : Type → Type} [Monad m] [LawfulMonad m]
    {ε : Type} [KeccakQuery (ExceptT ε m)] (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (hd : PatricializeDomain obj level) (representative : Nibbles)
    (construct : (digit : Fin 16) → (child : Std.ExtTreeMap Nibbles ByteArray) →
      child = childPartition obj level digit →
      PatricializeDomain child (level + 1) → ExceptT ε m (Option InternalNode))
    (error : ε)
    (failed : (construct 0 (childPartition obj level 0) rfl (childPartition_domain hd 0)).run =
      pure (.error error)) :
    (branchStage (m := ExceptT ε m) obj level hd representative construct).run =
      pure (.error error) := by
  have hc := childAction_construct_error obj level hd construct 0 error failed
  rw [branchStage, childReferences_first, ExceptT.run_bind, ExceptT.run_bind, hc]
  simp

private theorem childReferences_pure {m : Type → Type} [Monad m] [LawfulMonad m]
    [KeccakQuery m] (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (hd : PatricializeDomain obj level)
    (construct : (digit : Fin 16) → (child : Std.ExtTreeMap Nibbles ByteArray) →
      child = childPartition obj level digit →
      PatricializeDomain child (level + 1) → m (Option InternalNode))
    (reference : Fin 16 → RlpItem)
    (pureActions : ∀ digit, childAction obj level hd construct digit = pure (reference digit)) :
    childReferences obj level hd construct = pure (Vector.ofFn reference) := by
  unfold childReferences
  have he : childAction obj level hd construct = fun digit ↦ pure (reference digit) :=
    funext pureActions
  rw [he, Vector.ofFnM_pure]

private theorem branch_reference_position (reference : Fin 16 → RlpItem) (value : ByteArray)
    (digit : Fin 16) :
    ((Vector.ofFn reference).toList ++ [RlpItem.bytes value])[digit.val]'(by simp; omega) =
      reference digit := by
  rw [branch_items_get]
  simp

private theorem branch_value_position (reference : Fin 16 → RlpItem) (value : ByteArray) :
    ((Vector.ofFn reference).toList ++ [RlpItem.bytes value])[16]'(by simp) = .bytes value :=
  branch_items_value _ _

/-! Owner reference bridges and private law clients. Conformance observes these
List/drop expressions; all-input equalities connect them to the packed owner. -/

private def sharedPrefixFromModel (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (representative : Nibbles) : Nat :=
  sharedPrefixFoldModel representative.toList level (obj.keys.map Nibbles.toList)
    (representative.size - level)

private theorem sharedPrefixFrom_model (obj : Std.ExtTreeMap Nibbles ByteArray)
    (level : Nat) (representative : Nibbles) :
    sharedPrefixFrom obj level representative = sharedPrefixFromModel obj level representative :=
  sharedPrefixFold_model representative level obj.keys (representative.size - level)

private def selectSharedPrefixModel (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat) :
    Option (Nibbles × Nat) :=
  obj.keys.head?.map fun representative ↦
    (representative, sharedPrefixFromModel obj level representative)

private theorem selectSharedPrefix_model (obj : Std.ExtTreeMap Nibbles ByteArray)
    (level : Nat) : selectSharedPrefix obj level = selectSharedPrefixModel obj level := by
  cases he : obj.keys with
  | nil => simp [selectSharedPrefix, selectSharedPrefixModel, he]
  | cons representative keys =>
    simp only [selectSharedPrefix, selectSharedPrefixModel, he, List.head?_cons,
      Option.map_some]
    rw [← sharedPrefixFrom_model, sharedPrefixFrom, he]

/- The actual packed pair scan equals the legible suffix reference for every
level and cap, including bounded exhaustion beyond a key's end. -/
example (a b : Nibbles) (level cap : Nat) :
    pairSharedPrefix a b level cap = min cap (commonPrefixLength (a.drop level) (b.drop level)) :=
  pairSharedPrefix_model a b level cap

/- Arbitrary capped folds have an ordinary List/drop reference equality. -/
example (a : Nibbles) (level : Nat) (keys : List Nibbles) (cap : Nat) :
    sharedPrefixFold a level keys cap =
      sharedPrefixFoldModel a.toList level (keys.map Nibbles.toList) cap :=
  sharedPrefixFold_model a level keys cap

/- Exactly the reachable advanced domains are bounded by the selected amount. -/
example (obj : Std.ExtTreeMap Nibbles ByteArray) (level amount : Nat)
    (hd : PatricializeDomain obj level) (a : Nibbles) (ha : a ∈ obj) :
    amount ≤ sharedPrefixFrom obj level a ↔ PatricializeDomain obj (level + amount) :=
  sharedPrefixFrom_le_iff hd a ha amount

/- Each full key reaches the selected depth; values carry no extra premise. -/
example (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (hd : PatricializeDomain obj level) (a : Nibbles) (ha : a ∈ obj)
    (key : Nibbles) (hk : key ∈ obj) : sharedPrefixFrom obj level a ≤ key.size - level :=
  sharedPrefixFrom_bound hd a ha key hk

/- A universally shared additional prefix cannot exceed this amount. -/
example (obj : Std.ExtTreeMap Nibbles ByteArray) (level amount : Nat)
    (hd : PatricializeDomain obj level) (a : Nibbles) (ha : a ∈ obj)
    (advanced : PatricializeDomain obj (level + amount)) : amount ≤ sharedPrefixFrom obj level a :=
  sharedPrefixFrom_maximal hd a ha advanced

/- Both the amount and complete additional path are independent of the member. -/
example (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (hd : PatricializeDomain obj level) (a b : Nibbles) (ha : a ∈ obj) (hb : b ∈ obj) :
    sharedPrefixFrom obj level a = sharedPrefixFrom obj level b ∧
      a.extract level (level + sharedPrefixFrom obj level a) =
        b.extract level (level + sharedPrefixFrom obj level b) :=
  ⟨sharedPrefixFrom_representative_eq hd a b ha hb,
    sharedPrefixFrom_prefix_representative_eq hd a b ha hb⟩

/- Zero excludes a common positive next prefix only with a real member and domain. -/
example (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (hd : PatricializeDomain obj level) (a : Nibbles) (ha : a ∈ obj) :
    sharedPrefixFrom obj level a = 0 ↔ ¬ PatricializeDomain obj (level + 1) :=
  sharedPrefixFrom_zero_iff hd a ha

/- Selection handles an empty map separately and records an actual member otherwise. -/
example (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (a : Nibbles) (amount : Nat)
    (h : selectSharedPrefix obj level = some (a, amount)) :
    a ∈ obj ∧ amount = sharedPrefixFrom obj level a :=
  selectSharedPrefix_member h

/- The selected result supplies the existing public domain-extension contract. -/
example (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (hd : PatricializeDomain obj level) (a : Nibbles) (amount : Nat)
    (h : selectSharedPrefix obj level = some (a, amount)) :
    PatricializeDomain obj (level + amount) :=
  selectSharedPrefix_domain hd h

/- A positive selection supplies actual strict sum descent with no value restriction. -/
example (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (hd : PatricializeDomain obj level) (a : Nibbles) (ha : a ∈ obj)
    (hp : 0 < sharedPrefixFrom obj level a) :
    PatricializeDomain obj (level + sharedPrefixFrom obj level a) ∧
      remainingMeasure obj (level + sharedPrefixFrom obj level a) <
        remainingMeasure obj level :=
  sharedPrefixFrom_positive_descent hd a ha hp

/- Empty is explicitly distinguished from the nonempty zero-prefix case. -/
example (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat) :
    selectSharedPrefix obj level = none ↔ obj.keys = [] :=
  selectSharedPrefix_none_iff obj level

/- Changing values, including empties, or the insertion history cannot change
selection length when the actual maps have the same full keys. -/
example (obj other : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (hd : PatricializeDomain obj level) (ho : PatricializeDomain other level)
    (same : ∀ key : Nibbles, key ∈ obj ↔ key ∈ other)
    (a b : Nibbles) (ha : a ∈ obj) (hb : b ∈ other) :
    sharedPrefixFrom obj level a = sharedPrefixFrom other level b :=
  sharedPrefixFrom_keys_eq hd ho same a b ha hb

/-! Finite owner checks execute the private packed scan without exporting it. -/

#guard pairSharedPrefix (Nibbles.ofList [1, 2, 3, 4])
  (Nibbles.ofList [1, 2, 3, 5, 6, 7]) 0 99 = 3
#guard pairSharedPrefix (Nibbles.ofList [1, 2, 3, 4])
  (Nibbles.ofList [1, 2, 3, 5, 6, 7]) 0 2 = 2
#guard pairSharedPrefix (Nibbles.ofList [1, 2])
  (Nibbles.ofList [1, 2, 3]) 1 99 = 1
#guard pairSharedPrefix (Nibbles.ofList [1]) (Nibbles.ofList [1]) (2 ^ 80) (2 ^ 80) = 0
#guard selectSharedPrefix (∅ : Std.ExtTreeMap Nibbles ByteArray) 999 = none

/-! Owner-local clients of private branch laws. No private names cross the consumer seam. -/

example (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (digit : Fin 16) : childPartition obj level digit =
      obj.filter (fun key _ ↦ decide (key.toList[level]? = some digit)) :=
  childPartition_model obj level digit

example {obj : Std.ExtTreeMap Nibbles ByteArray} {level : Nat}
    {digit : Fin 16} {key : Nibbles} :
    key ∈ childPartition obj level digit ↔ key ∈ obj ∧ key.toList[level]? = some digit :=
  mem_child

example (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (digit : Fin 16) (key : Nibbles) :
    (childPartition obj level digit)[key]? =
      obj[key]?.filter (fun _ ↦ decide (key.toList[level]? = some digit)) :=
  child_lookup_model obj level digit key

example {obj : Std.ExtTreeMap Nibbles ByteArray} {level : Nat}
    {a b : Fin 16} (hne : a ≠ b) (key : Nibbles) :
    ¬ (key ∈ childPartition obj level a ∧ key ∈ childPartition obj level b) :=
  child_disjoint hne key

example {obj : Std.ExtTreeMap Nibbles ByteArray} {level : Nat}
    {key : Nibbles} :
    (∃ digit : Fin 16, key ∈ childPartition obj level digit) ↔ key ∈ obj ∧ level < key.size :=
  child_coverage

example {obj : Std.ExtTreeMap Nibbles ByteArray} {level : Nat}
    (hd : PatricializeDomain obj level) (a key : Nibbles)
    (ha : a ∈ obj) (hk : key ∈ obj) (hl : key.size = level) :
    (branchParts obj level a).ending = some (obj[key]'hk) :=
  branchParts_ending_present hd a key ha hk hl

example {obj : Std.ExtTreeMap Nibbles ByteArray} {level : Nat}
    (hd : PatricializeDomain obj level) (a : Nibbles) (ha : a ∈ obj) :
    (branchParts obj level a).ending = none ↔ ¬ ∃ key : Nibbles, key ∈ obj ∧ key.size = level :=
  branchParts_ending_none_iff hd a ha

example (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (a : Nibbles) (digit : Fin 16) :
    (BranchParts.children (branchParts obj level a))[digit.val] = childPartition obj level digit :=
  branchParts_get obj level a digit

example {obj : Std.ExtTreeMap Nibbles ByteArray} {level : Nat}
    (hd : PatricializeDomain obj level) (a b : Nibbles) (ha : a ∈ obj) (hb : b ∈ obj) :
    (BranchParts.children (branchParts obj level a)) =
      (BranchParts.children (branchParts obj level b)) ∧
      (branchParts obj level a).ending = (branchParts obj level b).ending := by
  have h := branchParts_ending_representative hd a b ha hb
  exact ⟨congrArg BranchParts.children h,
    congrArg BranchParts.ending h⟩

example {m : Type → Type} [Monad m] [KeccakQuery m]
    (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (hd : PatricializeDomain obj level) (a b : Nibbles) (ha : a ∈ obj) (hb : b ∈ obj)
    (construct : (digit : Fin 16) → (child : Std.ExtTreeMap Nibbles ByteArray) →
      child = childPartition obj level digit →
      PatricializeDomain child (level + 1) → m (Option InternalNode)) :
    branchStage obj level hd a construct = branchStage obj level hd b construct :=
  branchStage_representative obj level hd a b ha hb construct

example {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (hd : PatricializeDomain obj level) (a : Nibbles)
    (construct : (digit : Fin 16) → (child : Std.ExtTreeMap Nibbles ByteArray) →
      child = childPartition obj level digit →
      PatricializeDomain child (level + 1) → m (Option InternalNode)) :
    (fun node ↦ assembleInternalNode (some node)) <$> branchStage obj level hd a construct = (do
      let items ← List.ofFnM (childAction obj level hd construct)
      pure (RlpItem.list (items ++ [RlpItem.bytes (((branchParts obj level a).ending).getD
        ByteArray.empty)]))) :=
  branchStage_assembled obj level hd a construct

example {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (hd : PatricializeDomain obj level)
    (construct : (digit : Fin 16) → (child : Std.ExtTreeMap Nibbles ByteArray) →
      child = childPartition obj level digit →
      PatricializeDomain child (level + 1) → m (Option InternalNode)) :
    childReferences obj level hd construct = (do
      let first ← childAction obj level hd construct 0
      let rest ← Vector.ofFnM (fun digit : Fin 15 ↦
        childAction obj level hd construct digit.succ)
      pure ((#v[first] ++ rest).cast (by omega))) :=
  childReferences_first obj level hd construct

example {m : Type → Type} [Monad m] [LawfulMonad m]
    {ε : Type} [KeccakQuery (ExceptT ε m)] (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (hd : PatricializeDomain obj level) (a : Nibbles)
    (construct : (digit : Fin 16) → (child : Std.ExtTreeMap Nibbles ByteArray) →
      child = childPartition obj level digit →
      PatricializeDomain child (level + 1) → ExceptT ε m (Option InternalNode))
    (error : ε)
    (failed : (construct 0 (childPartition obj level 0) rfl (childPartition_domain
      hd 0)).run = pure (.error error)) :
    (branchStage (m := ExceptT ε m) obj level hd a construct).run = pure (.error error) :=
  branchStage_first_error obj level hd a construct error failed


/-! Recursive construction follows empty, singleton, extension, branch dispatch.
A private selector parameter supports the every-node choice-independence proof.
The public constructor supplies the lawful minimum key. -/

private abbrev RepresentativeSelector :=
  (obj : Std.ExtTreeMap Nibbles ByteArray) → Nat → obj.size ≠ 0 →
    {key : Nibbles // key ∈ obj}

private def minimumKeySelector : RepresentativeSelector := fun obj _ hn ↦
  ⟨obj.minKey (fun he ↦ hn (Std.ExtTreeMap.eq_empty_iff_size_eq_zero.mp he)),
    Std.ExtTreeMap.minKey_mem⟩

private theorem singleton_member_eq {obj : Std.ExtTreeMap Nibbles ByteArray}
    (hs : obj.size = 1) (a b : Nibbles) (ha : a ∈ obj) (hb : b ∈ obj) : a = b := by
  have hl := Std.ExtTreeMap.length_keys (t := obj)
  have hka := Std.ExtTreeMap.mem_keys.mpr ha
  have hkb := Std.ExtTreeMap.mem_keys.mpr hb
  obtain ⟨key, he⟩ := List.length_eq_one_iff.mp (hl.trans hs)
  rw [he] at hka hkb
  simp only [List.mem_singleton] at hka hkb
  exact hka.trans hkb.symm

private def patricializeWith {m : Type → Type} [Monad m] [KeccakQuery m]
    (select : RepresentativeSelector) (obj : Std.ExtTreeMap Nibbles ByteArray)
    (level : Nat) (domain : PatricializeDomain obj level) : m (Option InternalNode) :=
  if empty : obj.size = 0 then pure none
  else
    let representative := select obj level empty
    if _singleton : obj.size = 1 then
      pure (some (.leaf (representative.val.drop level)
        (.bytes (obj[representative.val]'representative.property))))
    else
      let amount := sharedPrefixFrom obj level representative.val
      if _positive : 0 < amount then do
        let child ← patricializeWith select obj (level + amount)
          (sharedPrefixFrom_domain domain representative.val representative.property)
        let reference ← encodeInternalNode child
        pure (some (.extension (representative.val.extract level (level + amount)) reference))
      else do
        let branch ← branchStage obj level domain representative.val
          (fun digit child _actual childDomain ↦ patricializeWith select child (level + 1)
            childDomain)
        pure (some branch)
termination_by remainingMeasure obj level
decreasing_by
  · exact (sharedPrefixFrom_positive_descent domain representative.val
      representative.property _positive).2
  · subst child
    exact child_measure_lt domain (by omega) digit

private theorem patricializeWith_independent {m : Type → Type} [Monad m] [KeccakQuery m]
    (left right : RepresentativeSelector) (obj : Std.ExtTreeMap Nibbles ByteArray)
    (level : Nat) (domain : PatricializeDomain obj level) :
    patricializeWith (m := m) left obj level domain =
      patricializeWith right obj level domain := by
  rw [patricializeWith, patricializeWith]
  by_cases empty : obj.size = 0
  · simp only [dite_eq_left empty]
  · simp only [dite_eq_right empty]
    let a := left obj level empty
    let b := right obj level empty
    by_cases singleton : obj.size = 1
    · simp only [dite_eq_left singleton]
      have same := singleton_member_eq singleton a.val b.val a.property b.property
      simp only [a, b] at same
      simp only [same]
    · simp only [dite_eq_right singleton]
      have amount := sharedPrefixFrom_representative_eq domain a.val b.val
        a.property b.property
      change sharedPrefixFrom obj level (left obj level empty).val =
        sharedPrefixFrom obj level (right obj level empty).val at amount
      simp only [← amount]
      by_cases positive : 0 < sharedPrefixFrom obj level a.val
      · simp only [a] at positive
        simp only [dite_eq_left positive]
        rw [patricializeWith_independent left right obj _]
        have path := sharedPrefixFrom_prefix_representative_eq domain a.val b.val
          a.property b.property
        simp only [a, b, ← amount] at path
        rw [path]
      · simp only [a] at positive
        simp only [dite_eq_right positive]
        have callbacks :
            (fun digit child (_actual : child = childPartition obj level digit) childDomain ↦
              patricializeWith (m := m) left child (level + 1) childDomain) =
            (fun digit child (_actual : child = childPartition obj level digit) childDomain ↦
              patricializeWith right child (level + 1) childDomain) := by
          funext digit child actual childDomain
          exact patricializeWith_independent left right child (level + 1) childDomain
        rw [callbacks, branchStage_representative obj level domain _ _
          (left obj level empty).property (right obj level empty).property]
termination_by remainingMeasure obj level
decreasing_by
  · exact (sharedPrefixFrom_positive_descent domain a.val a.property positive).2
  · subst child
    exact child_measure_lt domain (by omega) digit

/-- Recursively construct the mathematical internal trie on the reachable full-map
 domain. Empty values, ending keys and arbitrary finite lengths are retained.
 Every nonempty node selects the minimum full key. Pinned EELS
 `src/ethereum/merkle_patricia_trie.py:507–581` at the reference pin. -/
def patricialize {m : Type → Type} [Monad m] [KeccakQuery m]
    (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (domain : PatricializeDomain obj level) : m (Option InternalNode) :=
  patricializeWith minimumKeySelector obj level domain

/-- The reachable-domain proof is erased and cannot affect construction. -/
theorem patricialize_domain_irrel {m : Type → Type} [Monad m] [KeccakQuery m]
    (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (left right : PatricializeDomain obj level) :
    patricialize (m := m) obj level left = patricialize obj level right := rfl

/-- Equality of every optional full-key lookup determines the complete construction,
including query effects. Different-value writes must yield equal final maps. -/
theorem patricialize_ext {m : Type → Type} [Monad m] [KeccakQuery m]
    (obj other : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (domain : PatricializeDomain obj level) (otherDomain : PatricializeDomain other level)
    (same : ∀ key : Nibbles, obj[key]? = other[key]?) :
    patricialize (m := m) obj level domain = patricialize other level otherDomain := by
  have equal : obj = other := Std.ExtTreeMap.ext_getElem? same
  subst other
  rfl

/-- Empty dispatch returns absence at every depth without selecting a key or querying. -/
theorem patricialize_empty {m : Type → Type} [Monad m] [KeccakQuery m]
    (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (domain : PatricializeDomain obj level) (empty : obj.size = 0) :
    patricialize (m := m) obj level domain = pure none := by
  rw [patricialize, patricializeWith, dite_eq_left empty]

/-- A singleton keeps the original value and actual suffix, even if either is empty. -/
theorem patricialize_singleton {m : Type → Type} [Monad m] [KeccakQuery m]
    (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (domain : PatricializeDomain obj level) (singleton : obj.size = 1)
    (representative : Nibbles) (member : representative ∈ obj) :
    patricialize (m := m) obj level domain =
      pure (some (.leaf (representative.drop level) (.bytes (obj[representative]'member)))) := by
  have empty : obj.size ≠ 0 := by omega
  have same := singleton_member_eq singleton
    (minimumKeySelector obj level empty).val representative
    (minimumKeySelector obj level empty).property member
  rw [patricialize, patricializeWith, dite_eq_right empty, dite_eq_left singleton]
  simp only [same]

/-- A positive maximal shared prefix copies just the extension segment, recursively
constructs the same full map at the advanced depth, and C6-encodes that child once.
Maximality is expressed with the public reachable-domain contract. The representative
may be any actual member; no monad laws or hash assumptions are used. -/
theorem patricialize_extension {m : Type → Type} [Monad m] [KeccakQuery m]
    (obj : Std.ExtTreeMap Nibbles ByteArray) (level amount : Nat)
    (domain : PatricializeDomain obj level) (multikey : 1 < obj.size)
    (representative : Nibbles) (member : representative ∈ obj) (positive : 0 < amount)
    (advanced : PatricializeDomain obj (level + amount))
    (maximal : ∀ extra, PatricializeDomain obj (level + extra) → extra ≤ amount) :
    patricialize (m := m) obj level domain = (do
      let child ← patricialize obj (level + amount) advanced
      let reference ← encodeInternalNode child
      pure (some (.extension (representative.extract level (level + amount)) reference)) :
      m (Option InternalNode)) := by
  have empty : obj.size ≠ 0 := by omega
  have singleton : obj.size ≠ 1 := by omega
  let selected := minimumKeySelector obj level empty
  have lengthEq : sharedPrefixFrom obj level selected.val = amount :=
    Nat.le_antisymm
      (maximal _ (sharedPrefixFrom_domain domain selected.val selected.property))
      (sharedPrefixFrom_maximal domain selected.val selected.property advanced)
  have path : selected.val.extract level (level + amount) =
      representative.extract level (level + amount) := by
    have h := congrArg (fun k : Nibbles ↦ k.drop level)
      (advanced.consumedPrefix selected.val selected.property representative member)
    simpa only [Nibbles.drop_take] using h
  rw [patricialize, patricializeWith, dite_eq_right empty, dite_eq_right singleton]
  change sharedPrefixFrom obj level (minimumKeySelector obj level empty).val = amount at lengthEq
  simp only [lengthEq, dite_eq_left positive]
  change (do
    let child ← patricialize (m := m) obj (level + amount) advanced
    let reference ← encodeInternalNode child
    pure (some (InternalNode.extension (selected.val.extract level (level + amount)) reference))) = _
  rw [path]

/-- With no positive shared prefix, construction uses sixteen full-key partitions
in numeric order. Each supplied child is constructed then C6-encoded. The ending
lookup defaults only in the final field. Literal bind association is retained, so
this equation needs only `Monad`; the returned branch has no parent query. -/
theorem patricialize_branch {m : Type → Type} [Monad m] [KeccakQuery m]
    (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (domain : PatricializeDomain obj level) (multikey : 1 < obj.size)
    (representative : Nibbles) (member : representative ∈ obj)
    (noPrefix : ¬ PatricializeDomain obj (level + 1)) :
    patricialize (m := m) obj level domain = (do
      let branch ← (do
        let children ← Vector.ofFnM (fun digit : Fin 16 ↦ do
          let child ← patricialize
            (obj.filter (fun key _ ↦
              if h : level < key.size then decide (key.get ⟨level, h⟩ = digit) else false))
            (level + 1) (domain.child digit)
          encodeInternalNode child)
        pure (InternalNode.branch children
          (.bytes (obj[representative.take level]?.getD ByteArray.empty))) : m InternalNode)
      pure (some branch) : m (Option InternalNode)) := by
  have empty : obj.size ≠ 0 := by omega
  have singleton : obj.size ≠ 1 := by omega
  let selected := minimumKeySelector obj level empty
  have zero := (sharedPrefixFrom_zero_iff domain selected.val selected.property).mpr noPrefix
  have nonpositive : ¬ 0 < sharedPrefixFrom obj level selected.val := by omega
  rw [patricialize, patricializeWith, dite_eq_right empty, dite_eq_right singleton]
  change ¬ 0 < sharedPrefixFrom obj level (minimumKeySelector obj level empty).val at nonpositive
  rw [dite_eq_right nonpositive, branchStage_representative obj level domain _ representative
    (minimumKeySelector obj level empty).property member]
  rfl

/-- Lawful sequencing removes the final intermediate branch bind, while preserving
ascending construction/encoding order and every query's original failure. -/
theorem patricialize_branch_lawful {m : Type → Type} [Monad m] [LawfulMonad m]
    [KeccakQuery m] (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (domain : PatricializeDomain obj level) (multikey : 1 < obj.size)
    (representative : Nibbles) (member : representative ∈ obj)
    (noPrefix : ¬ PatricializeDomain obj (level + 1)) :
    patricialize (m := m) obj level domain = (do
      let children ← Vector.ofFnM (fun digit : Fin 16 ↦ do
        let child ← patricialize
          (obj.filter (fun key _ ↦
            if h : level < key.size then decide (key.get ⟨level, h⟩ = digit) else false))
          (level + 1) (domain.child digit)
        encodeInternalNode child)
      pure (some (.branch children
        (.bytes (obj[representative.take level]?.getD ByteArray.empty)))) : m (Option InternalNode)) := by
  rw [patricialize_branch obj level domain multikey representative member noPrefix]
  simp only [bind_assoc, pure_bind]

/-! Mathematical root: C6/root reference and its fused complete-top query. -/

private theorem size_encode_hash_answer (answer : Hash32) :
    (Rlp.encode (.bytes answer.toBytes.toByteArray)).size = 33 := by
  rw [Rlp.encode_bytes, Rlp.size_encodeBytes, Bytes.size_toByteArray, Hash32.size_toBytes]
  simp

-- EELS root returns Extended: short structures are hashed, while C6 hash answers
-- are returned as raw bytes, not their 33-byte RLP encodings. This reference
-- observes that result as an RlpItem; it makes no typed Hash32 conversion.
private def encodeRootReference {m : Type → Type} [Monad m] [KeccakQuery m]
    (node : Option InternalNode) : m RlpItem := do
  let reference ← encodeInternalNode node
  if (Rlp.encode reference).size < 32 then do
    let answer ← KeccakQuery.keccak (Rlp.encode reference)
    pure (.bytes answer.toBytes.toByteArray)
  else pure reference

private theorem encodeRootReference_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    [KeccakQuery m] (node : Option InternalNode) :
    encodeRootReference (m := m) node = (do
      let answer ← KeccakQuery.keccak (Rlp.encode (assembleInternalNode node))
      pure (.bytes answer.toBytes.toByteArray) : m RlpItem) := by
  by_cases short : (Rlp.encode (assembleInternalNode node)).size < 32
  · rw [encodeRootReference, encodeInternalNode_inline node short, pure_bind,
      ite_eq_left short]
  · rw [encodeRootReference, encodeInternalNode_hash node (by omega)]
    simp only [bind_assoc, pure_bind]
    apply congrArg (fun continuation : Hash32 → m RlpItem ↦
      (KeccakQuery.keccak (Rlp.encode (assembleInternalNode node)) : m Hash32) >>= continuation)
    funext answer
    rw [size_encode_hash_answer, ite_eq_right (by decide)]

private def mathRootReference {m : Type → Type} [Monad m] [KeccakQuery m]
    (emptyRoot : Hash32) (obj : Std.ExtTreeMap Nibbles ByteArray) : m RlpItem :=
  if obj.size = 0 then pure (.bytes emptyRoot.toBytes.toByteArray)
  else do
    let node ← patricialize obj 0 (PatricializeDomain.zero obj)
    encodeRootReference node

/-- Mathematical full-map root. Q50 returns the supplied constant on empty maps
with no local query. Otherwise C7's descendants precede exactly one query on the
complete top assembly, with no threshold on the root itself. Pinned EELS
`src/ethereum/merkle_patricia_trie.py:478–504`, with caller-owned preparation/F20. -/
def mathRoot {m : Type → Type} [Monad m] [KeccakQuery m]
    (emptyRoot : Hash32) (obj : Std.ExtTreeMap Nibbles ByteArray) : m Hash32 :=
  if obj.size = 0 then pure emptyRoot
  else do
    let node ← patricialize obj 0 (PatricializeDomain.zero obj)
    KeccakQuery.keccak (Rlp.encode (assembleInternalNode node))

-- Ordinary whole-action equality includes every answer byte and all monadic effects.
-- Q47 makes it unconditional on Encodable. LawfulMonad explicitly licenses the
-- eliminated/reassociated intermediate binds. This is the total local reference,
-- not generic equality to Python's acquisition/preparation effects on empty input.
private theorem mathRoot_eq_reference {m : Type → Type} [Monad m] [LawfulMonad m]
    [KeccakQuery m] (emptyRoot : Hash32) (obj : Std.ExtTreeMap Nibbles ByteArray) :
    (do let answer ← mathRoot (m := m) emptyRoot obj
        pure (RlpItem.bytes answer.toBytes.toByteArray)) =
      mathRootReference emptyRoot obj := by
  by_cases empty : obj.size = 0
  · rw [mathRoot, mathRootReference, ite_eq_left empty, ite_eq_left empty, pure_bind]
  · rw [mathRoot, mathRootReference, ite_eq_right empty, ite_eq_right empty, bind_assoc]
    apply congrArg (fun continuation : Option InternalNode → m RlpItem ↦
      patricialize obj 0 (PatricializeDomain.zero obj) >>= continuation)
    funext node
    exact (encodeRootReference_eq node).symm

/-- Exact local root dispatch; the literal monadic association needs only Monad. -/
theorem mathRoot_eq {m : Type → Type} [Monad m] [KeccakQuery m]
    (emptyRoot : Hash32) (obj : Std.ExtTreeMap Nibbles ByteArray) :
    mathRoot (m := m) emptyRoot obj =
      (if obj.size = 0 then pure emptyRoot else do
        let node ← patricialize obj 0 (PatricializeDomain.zero obj)
        KeccakQuery.keccak (Rlp.encode (assembleInternalNode node)) : m Hash32) := rfl

/-- Empty input bypasses C7 and even a failing oracle, retaining the supplied constant. -/
theorem mathRoot_empty {m : Type → Type} [Monad m] [KeccakQuery m]
    (emptyRoot : Hash32) (obj : Std.ExtTreeMap Nibbles ByteArray) (empty : obj.size = 0) :
    mathRoot (m := m) emptyRoot obj = pure emptyRoot := by
  rw [mathRoot_eq, ite_eq_left empty]

/-- Every nonempty map constructs descendants then queries the entire top wire once. -/
theorem mathRoot_nonempty {m : Type → Type} [Monad m] [KeccakQuery m]
    (emptyRoot : Hash32) (obj : Std.ExtTreeMap Nibbles ByteArray) (nonempty : obj.size ≠ 0) :
    mathRoot (m := m) emptyRoot obj = (do
      let node ← patricialize obj 0 (PatricializeDomain.zero obj)
      KeccakQuery.keccak (Rlp.encode (assembleInternalNode node)) : m Hash32) := by
  rw [mathRoot_eq, ite_eq_right nonempty]

/-- Matching every optional full-key lookup determines the complete root action. -/
theorem mathRoot_ext {m : Type → Type} [Monad m] [KeccakQuery m]
    (emptyRoot : Hash32) (obj other : Std.ExtTreeMap Nibbles ByteArray)
    (same : ∀ key : Nibbles, obj[key]? = other[key]?) :
    mathRoot (m := m) emptyRoot obj = mathRoot emptyRoot other := by
  have equal : obj = other := Std.ExtTreeMap.ext_getElem? same
  subst other
  rfl

/-- Id runs actual C7 followed by the concrete complete-top digest. Empty constants
are still caller supplied; their coherence with C5 is a separate premise. -/
theorem mathRoot_id (emptyRoot : Hash32) (obj : Std.ExtTreeMap Nibbles ByteArray) :
    mathRoot (m := Id) emptyRoot obj =
      if obj.size = 0 then emptyRoot else
        keccak256 (Rlp.encode (assembleInternalNode
          (patricialize (m := Id) obj 0 (PatricializeDomain.zero obj)))) := rfl

/-- An original construction failure suppresses the final root query. -/
theorem run_mathRoot_construction_error {m : Type → Type} {ε : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery (ExceptT ε m)]
    (emptyRoot : Hash32) (obj : Std.ExtTreeMap Nibbles ByteArray)
    (nonempty : obj.size ≠ 0) (error : ε)
    (failed : (patricialize (m := ExceptT ε m) obj 0 (PatricializeDomain.zero obj)).run =
      pure (.error error)) :
    (mathRoot (m := ExceptT ε m) emptyRoot obj).run = pure (.error error) := by
  rw [mathRoot_nonempty emptyRoot obj nonempty, ExceptT.run_bind, failed, pure_bind]

/-- The final query's original error is retained after a pure successful construction. -/
theorem run_mathRoot_query_error {m : Type → Type} {ε : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery (ExceptT ε m)]
    (emptyRoot : Hash32) (obj : Std.ExtTreeMap Nibbles ByteArray)
    (nonempty : obj.size ≠ 0) (node : Option InternalNode) (error : ε)
    (constructed : patricialize (m := ExceptT ε m) obj 0 (PatricializeDomain.zero obj) =
      pure node)
    (failed : (KeccakQuery.keccak (m := ExceptT ε m)
      (Rlp.encode (assembleInternalNode node))).run = pure (.error error)) :
    (mathRoot (m := ExceptT ε m) emptyRoot obj).run = pure (.error error) := by
  rw [mathRoot_nonempty emptyRoot obj nonempty, constructed, pure_bind]
  exact failed

/-- Exception-lift execution preserves C7's actual transformer computation; success
forwards the final query, while a construction error skips it. No C7 lift is assumed. -/
theorem run_mathRoot_exceptT {m : Type → Type} {ε : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m]
    (emptyRoot : Hash32) (obj : Std.ExtTreeMap Nibbles ByteArray) :
    (mathRoot (m := ExceptT ε m) emptyRoot obj).run =
      (if obj.size = 0 then pure (.ok emptyRoot) else do
        let result ← (patricialize (m := ExceptT ε m) obj 0
          (PatricializeDomain.zero obj)).run
        match result with
        | .error error => pure (.error error)
        | .ok node => do
          let answer ← KeccakQuery.keccak (Rlp.encode (assembleInternalNode node))
          pure (.ok answer) : m (Except ε Hash32)) := by
  rw [mathRoot_eq]
  split
  · rfl
  · rw [ExceptT.run_bind]
    apply congrArg (fun continuation : Except ε (Option InternalNode) → m (Except ε Hash32) ↦
      (patricialize (m := ExceptT ε m) obj 0 (PatricializeDomain.zero obj)).run >>= continuation)
    funext result
    cases result with
    | error error => rfl
    | ok node => simp [KeccakQuery.keccak_exceptT, ExceptT.run_lift]

/-- State-lift execution carries C7's returned state into the final query and
preserves it there; any underlying effects remain in the underlying monad. -/
theorem run_mathRoot_stateT {m : Type → Type} {σ : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m]
    (emptyRoot : Hash32) (obj : Std.ExtTreeMap Nibbles ByteArray) (state : σ) :
    (mathRoot (m := StateT σ m) emptyRoot obj).run state =
      (if obj.size = 0 then pure (emptyRoot, state) else do
        let (node, next) ← (patricialize (m := StateT σ m) obj 0
          (PatricializeDomain.zero obj)).run state
        let answer ← KeccakQuery.keccak (Rlp.encode (assembleInternalNode node))
        pure (answer, next) : m (Hash32 × σ)) := by
  rw [mathRoot_eq]
  split
  · rfl
  · rfl

end STFSpec.Commit
