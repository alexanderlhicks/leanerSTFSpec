/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import Std.Data.ExtTreeMap

/-!
# Persistent first-write order

Internal support for `EthState`: two inverse persistent position maps retain the
first live write of each key. Raw operations are total even on malformed records;
list laws require the separate `WF` predicate and lawful comparison equality.
Future State callers use ordered semantic observers, rather than these maps.
Spec guidance: `STFSpec/informal/modules/EthState.md`.
-/

namespace STFSpec.State

/-- Internal raw first-write index; `next` is unbounded and positions may have gaps. -/
structure WriteOrder (K : Type) [Ord K] [Std.TransOrd K] where
  next : Nat
  positions : Std.ExtTreeMap K Nat
  keysByPosition : Std.ExtTreeMap Nat K

namespace WriteOrder

variable {K : Type} [Ord K] [Std.TransOrd K]

/-- Empty order metadata for a fresh write sequence. Supports fresh dictionaries in EELS
`src/ethereum/forks/amsterdam/state_tracker.py:869–871,874` at the pin. -/
def empty : WriteOrder K := ⟨0, ∅, ∅⟩

/-- Retain an existing whole record, or append a fresh live key. Supports EELS
`src/ethereum/forks/amsterdam/state_tracker.py:473,499–500,855–856,864–866` at the pin. -/
def record (r : WriteOrder K) (k : K) : WriteOrder K :=
  match r.positions[k]? with
  | some _ => r
  | none =>
      ⟨r.next + 1, r.positions.insert k r.next,
        r.keysByPosition.insert r.next k⟩

/-- Remove a live key and its selected reverse position without compacting holes.
Supports EELS `src/ethereum/forks/amsterdam/state_tracker.py:567,860` at the pin. -/
def erase (r : WriteOrder K) (k : K) : WriteOrder K :=
  match r.positions[k]? with
  | none => r
  | some p => ⟨r.next, r.positions.erase k, r.keysByPosition.erase p⟩

/-- Extract live keys in ascending recorded position, independently of key order.
Supports EELS `src/ethereum/forks/amsterdam/state_tracker.py:895–900` at the pin. -/
def toList (r : WriteOrder K) : List K :=
  r.keysByPosition.toList.map Prod.snd

/-- The two maps are inverse and every live reverse position precedes `next`. -/
def WF (r : WriteOrder K) : Prop :=
  (∀ (k : K) (p : Nat), r.positions[k]? = some p ↔ r.keysByPosition[p]? = some k) ∧
  (∀ (p : Nat) (k : K), r.keysByPosition[p]? = some k → p < r.next)

/-- Forward optional presence agrees with an arbitrary separately supplied value map.
Stored tombstones and zero values count as present. -/
def Agrees {V : Type} (r : WriteOrder K)
    (writes : Std.ExtTreeMap K V) : Prop :=
  ∀ (k : K), r.positions[k]?.isSome = writes[k]?.isSome

-- List operations are reference/test models only. The executable record/erase
-- definitions above do not traverse, filter or reconstruct the extracted list.
private def eraseModel (xs : List K) (k : K) : List K :=
  xs.filter (fun x => compare k x != .eq)

/-- Recording a present key returns the exact original raw record. -/
theorem record_of_present (r : WriteOrder K) (k : K) (p : Nat)
    (h : r.positions[k]? = some p) : record r k = r := by
  simp only [record, h]

/-- Erasing an absent key returns the exact original raw record. -/
theorem erase_of_absent (r : WriteOrder K) (k : K)
    (h : r.positions[k]? = none) : erase r k = r := by
  simp only [erase, h]

/-- Only a fresh recording increments the unbounded counter. -/
theorem next_record (r : WriteOrder K) (k : K) :
    (record r k).next =
      if r.positions[k]?.isSome then r.next else r.next + 1 := by
  cases h : r.positions[k]? <;> simp [record, h]

/-- Erasure preserves the counter. -/
theorem next_erase (r : WriteOrder K) (k : K) :
    (erase r k).next = r.next := by
  cases h : r.positions[k]? <;> simp [erase, h]

/-- An empty index enumerates no keys. -/
theorem toList_empty : toList (empty : WriteOrder K) = [] := by
  simp [toList, empty]

/-- An empty index satisfies both invariant clauses. -/
theorem wf_empty : WF (empty : WriteOrder K) := by
  simp [WF, empty]

private theorem positions_record_new (r : WriteOrder K) (k a : K)
    (h : r.positions[k]? = none) :
    (record r k).positions[a]? =
      if compare k a = .eq then some r.next else r.positions[a]? := by
  simp only [record, h]
  exact Std.ExtTreeMap.getElem?_insert

private theorem keys_record_new (r : WriteOrder K) (k : K) (p : Nat)
    (h : r.positions[k]? = none) :
    (record r k).keysByPosition[p]? =
      if compare r.next p = .eq then some k else r.keysByPosition[p]? := by
  simp only [record, h]
  exact Std.ExtTreeMap.getElem?_insert

private theorem positions_erase_present (r : WriteOrder K) (k a : K) (p : Nat)
    (h : r.positions[k]? = some p) :
    (erase r k).positions[a]? =
      if compare k a = .eq then none else r.positions[a]? := by
  simp only [erase, h]
  exact Std.ExtTreeMap.getElem?_erase

private theorem keys_erase_present (r : WriteOrder K) (k : K) (p q : Nat)
    (h : r.positions[k]? = some p) :
    (erase r k).keysByPosition[q]? =
      if compare p q = .eq then none else r.keysByPosition[q]? := by
  simp only [erase, h]
  exact Std.ExtTreeMap.getElem?_erase

private theorem next_fresh (r : WriteOrder K) (h : WF r) :
    r.keysByPosition[r.next]? = none := by
  cases hk : r.keysByPosition[r.next]? with
  | none => rfl
  | some k => exact False.elim ((Nat.lt_irrefl r.next) (h.2 r.next k hk))

private theorem forward_not_next (r : WriteOrder K) (h : WF r) (k : K) :
    r.positions[k]? ≠ some r.next := by
  intro hk
  exact (Nat.lt_irrefl r.next) (h.2 r.next k ((h.1 k r.next).mp hk))

private theorem reverse_not_absent (r : WriteOrder K) (h : WF r) (k : K)
    (hk : r.positions[k]? = none) (p : Nat) :
    r.keysByPosition[p]? ≠ some k := by
  intro hp
  have := (h.1 k p).mpr hp
  simp [hk] at this

/-- Recording preserves the inverse and position-bound invariant. -/
theorem wf_record [Std.LawfulEqOrd K] (r : WriteOrder K) (k : K) (h : WF r) :
    WF (record r k) := by
  cases hk : r.positions[k]? with
  | some p => simpa [record, hk] using h
  | none =>
    constructor
    · intro a p
      rw [positions_record_new r k a hk, keys_record_new r k p hk]
      by_cases ha : k = a
      · subst a
        by_cases hp : r.next = p
        · subst p
          simp
        · simp [hp, reverse_not_absent r h k hk p]
      · by_cases hp : r.next = p
        · subst p
          simp [ha, forward_not_next r h a]
        · simpa [ha, hp] using h.1 a p
    · intro p a hp
      rw [keys_record_new r k p hk] at hp
      simp only [record, hk]
      by_cases he : r.next = p
      · subst p; exact Nat.lt_succ_self _
      · simp [he] at hp
        exact Nat.lt_trans (h.2 p a hp) (Nat.lt_succ_self _)

/-- Erasing preserves the inverse and position-bound invariant. -/
theorem wf_erase [Std.LawfulEqOrd K] (r : WriteOrder K) (k : K) (h : WF r) :
    WF (erase r k) := by
  cases hk : r.positions[k]? with
  | none => simpa [erase, hk] using h
  | some p =>
    have hr : r.keysByPosition[p]? = some k := (h.1 k p).mp hk
    constructor
    · intro a q
      rw [positions_erase_present r k a p hk, keys_erase_present r k p q hk]
      by_cases ha : k = a
      · subst a
        by_cases hq : p = q
        · subst q; simp
        · have hn : r.keysByPosition[q]? ≠ some k := by
            intro hx
            have hy := (h.1 k q).mpr hx
            rw [hk] at hy
            exact hq (Option.some.inj hy)
          simp [hq, hn]
      · by_cases hq : p = q
        · subst q
          have hn : r.positions[a]? ≠ some p := by
            intro hx
            have hy := (h.1 a p).mp hx
            rw [hr] at hy
            exact ha (Option.some.inj hy)
          simp [ha, hn]
        · simpa [ha, hq] using h.1 a q
    · intro q a hq
      rw [keys_erase_present r k p q hk] at hq
      simp only [erase, hk]
      by_cases he : p = q
      · simp [he] at hq
      · simp [he] at hq
        exact h.2 q a hq

/-- Under `WF`, traversal contains exactly the forward-map keys. -/
theorem mem_toList_iff [Std.LawfulEqOrd K] (r : WriteOrder K) (k : K) (h : WF r) :
    k ∈ toList r ↔ r.positions[k]?.isSome = true := by
  constructor
  · intro hk
    obtain ⟨⟨p,a⟩, hp, ha⟩ := List.mem_map.mp hk
    change a = k at ha
    subst a
    have hr := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hp
    rw [(h.1 k p).mpr hr]
    rfl
  · intro hk
    cases hp : r.positions[k]? with
    | none => simp [hp] at hk
    | some p =>
      apply List.mem_map.mpr
      exact ⟨(p,k), Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr
        ((h.1 k p).mp hp), rfl⟩

/-- Under `WF`, traversal contains no duplicate actual keys. -/
theorem toList_nodup [Std.LawfulEqOrd K] (r : WriteOrder K) (h : WF r) :
    (toList r).Nodup := by
  change (r.keysByPosition.toList.map Prod.snd).Pairwise (· ≠ ·)
  rw [List.pairwise_map]
  apply List.Pairwise.imp_of_mem _ r.keysByPosition.distinct_keys_toList
  intro a b ha hb hab he
  have hpa := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp ha
  have hpb := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hb
  have hfa := (h.1 a.2 a.1).mpr hpa
  have hfb := (h.1 b.2 b.1).mpr hpb
  rw [he, hfb] at hfa
  have hp := Option.some.inj hfa
  exact hab (by simp [hp])

/-- Recording and value insertion preserve domain agreement, independently of `WF`. -/
theorem agrees_record_insert [Std.LawfulEqOrd K] {V : Type} (r : WriteOrder K)
    (writes : Std.ExtTreeMap K V) (k : K) (v : V) (h : Agrees r writes) :
    Agrees (record r k) (writes.insert k v) := by
  intro a
  cases hk : r.positions[k]? with
  | none =>
    rw [positions_record_new r k a hk, Std.ExtTreeMap.getElem?_insert]
    by_cases ha : k = a
    · simp [ha]
    · simpa [ha] using h a
  | some p =>
    simp only [record, hk, Std.ExtTreeMap.getElem?_insert]
    by_cases ha : k = a
    · subst a
      simp [hk]
    · simpa [ha] using h a

/-- Paired index and value erasure preserve domain agreement, independently of `WF`. -/
theorem agrees_erase_erase [Std.LawfulEqOrd K] {V : Type} (r : WriteOrder K)
    (writes : Std.ExtTreeMap K V) (k : K) (h : Agrees r writes) :
    Agrees (erase r k) (writes.erase k) := by
  intro a
  cases hk : r.positions[k]? with
  | some p =>
    rw [positions_erase_present r k a p hk, Std.ExtTreeMap.getElem?_erase]
    by_cases ha : k = a
    · simp [ha]
    · simpa [ha] using h a
  | none =>
    simp only [erase, hk, Std.ExtTreeMap.getElem?_erase]
    by_cases ha : k = a
    · subst a
      have hd := h k
      simp [hk] at hd
      simp [hk]
    · simpa [ha] using h a

private def posLt {V : Type} (a b : Nat × V) : Prop := a.1 < b.1

private theorem pairs_sorted {V : Type} (m : Std.ExtTreeMap Nat V) :
    m.toList.Pairwise posLt := by
  apply m.ordered_keys_toList.imp
  intro a b h
  exact Nat.compare_eq_lt.mp h

private theorem sorted_nodup {V : Type} (xs : List (Nat × V))
    (h : xs.Pairwise posLt) : xs.Nodup := by
  apply h.imp
  intro a b hab he
  subst b
  exact Nat.lt_irrefl a.1 hab

private theorem sorted_perm_eq {V : Type} (xs ys : List (Nat × V))
    (hx : xs.Pairwise posLt) (hy : ys.Pairwise posLt)
    (hm : ∀ a, a ∈ xs ↔ a ∈ ys) : xs = ys := by
  exact List.Perm.eq_of_pairwise
    (fun _a _b _ha _hb hab hba => False.elim (Nat.lt_asymm hab hba)) hx hy
    ((List.perm_ext_iff_of_nodup (sorted_nodup xs hx)
      (sorted_nodup ys hy)).mpr hm)

private theorem pairs_insert_fresh {V : Type} (m : Std.ExtTreeMap Nat V)
    (n : Nat) (v : V) (h : ∀ (p : Nat) (a : V), m[p]? = some a → p < n) :
    (m.insert n v).toList = m.toList ++ [(n,v)] := by
  have hn : m[n]? = none := by
    cases hx : m[n]? with
    | none => rfl
    | some a => exact False.elim (Nat.lt_irrefl n (h n a hx))
  have hs : (m.toList ++ [(n,v)]).Pairwise posLt := by
    apply List.pairwise_append.mpr
    refine ⟨pairs_sorted m, by simp, ?_⟩
    intro a ha b hb
    have he : b = (n,v) := by simpa using hb
    subst b
    exact h a.1 a.2 (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp ha)
  apply sorted_perm_eq _ _ (pairs_sorted _) hs
  intro a
  rcases a with ⟨p,b⟩
  simp only [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some,
    Std.ExtTreeMap.getElem?_insert, List.mem_append, List.mem_singleton]
  by_cases hp : n = p
  · subst p
    simp [hn, Prod.ext_iff, eq_comm]
  · simp [hp, Ne.symm hp, Prod.ext_iff]

private theorem pairs_erase {V : Type} (m : Std.ExtTreeMap Nat V) (n : Nat) :
    (m.erase n).toList =
      m.toList.filter (fun a => compare n a.1 != .eq) := by
  apply sorted_perm_eq _ _ (pairs_sorted _) ((pairs_sorted m).filter _)
  intro a
  rcases a with ⟨p,b⟩
  simp only [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some,
    Std.ExtTreeMap.getElem?_erase, List.mem_filter,
    Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some]
  by_cases hp : n = p
  · subst p
    simp
  · simp [hp]

private theorem map_filter_transport {A B : Type} (xs : List A)
    (f : A → B) (p : A → Bool) (q : B → Bool)
    (h : ∀ x ∈ xs, p x = q (f x)) :
    (xs.filter p).map f = (xs.map f).filter q := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht : ∀ x ∈ xs, p x = q (f x) := by
      intro x hx; exact h x (by simp [hx])
    simp only [List.filter_cons, List.map_cons]
    rw [← ha]
    split <;> simp_all

/-- Under `WF`, a fresh key appends; an existing key retains its position. -/
theorem toList_record [Std.LawfulEqOrd K]
    (r : WriteOrder K) (k : K) (h : WF r) :
    toList (record r k) =
      if r.positions[k]?.isSome then toList r else toList r ++ [k] := by
  cases hk : r.positions[k]? with
  | some p => simp [record, hk]
  | none =>
    simp only [record, hk, Option.isSome_none, Bool.false_eq_true,
      ↓reduceIte, toList]
    rw [pairs_insert_fresh r.keysByPosition r.next k h.2]
    simp

/-- Under `WF`, erasure removes only the selected key and retains survivor order. -/
theorem toList_erase [Std.LawfulEqOrd K]
    (r : WriteOrder K) (k : K) (h : WF r) :
    toList (erase r k) = (toList r).filter (fun a => compare k a != .eq) := by
  change toList (erase r k) = eraseModel (toList r) k
  cases hk : r.positions[k]? with
  | none =>
    simp only [erase, hk, eraseModel]
    symm
    apply List.filter_eq_self.mpr
    intro a ha
    have hn : k ≠ a := by
      intro he; subst a
      have hm := (mem_toList_iff r k h).mp ha
      simp [hk] at hm
    simp [hn]
  | some p =>
    have hr := (h.1 k p).mp hk
    simp only [erase, hk, toList, eraseModel]
    rw [pairs_erase r.keysByPosition p]
    apply map_filter_transport
    intro a ha
    have hra := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp ha
    have he : p = a.1 ↔ k = a.2 := by
      constructor
      · intro hp
        rw [← hp, hr] at hra
        exact Option.some.inj hra
      · intro he
        have hfa := (h.1 a.2 a.1).mpr hra
        rw [← he, hk] at hfa
        exact Option.some.inj hfa
    by_cases hp : p = a.1
    · have hv := he.mp hp
      simp [hp, hv]
    · have hv : k ≠ a.2 := fun hx => hp (he.mpr hx)
      apply Bool.eq_iff_iff.mpr
      simp [hp, hv]

end WriteOrder
end STFSpec.State
