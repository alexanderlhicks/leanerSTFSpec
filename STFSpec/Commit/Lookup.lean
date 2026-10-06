/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit.Node
import STFSpec.Commit.TrieError

/-!
# Pure partial-trie lookup

Library `EthCommit`. EELS `src/ethereum/forks/amsterdam/witness_state.py:53–100`.
The selected-slot diagnostic is the Q59 typed adaptation of Python IndexError.
Traversal ignores caches and admits every finite bare node. An offset scan avoids
copying the remaining key at branches; private structural reference equality
covers empty extensions and arbitrary branch arity without admission premises.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` C20/Q59/§7.0.5.
-/

namespace STFSpec.Commit
open STFSpec.Base

private def digitAt (p : Nibbles) (i : Nat) : Fin 16 :=
  if hi : i < p.size then p.get ⟨i, hi⟩ else 0

private def scan (p key : Nibbles) (pos : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => digitAt p i == digitAt key (pos + i) && scan p key pos n (i + 1)

private theorem scan_true (p key : Nibbles) (pos n i : Nat) :
    scan p key pos n i = true ↔
      ∀ j, j < n → digitAt p (i + j) = digitAt key (pos + (i + j)) := by
  induction n generalizing i with
  | zero => simp [scan]
  | succ n ih =>
    rw [scan, Bool.and_eq_true, beq_iff_eq, ih]
    constructor
    · rintro ⟨hzero, hrest⟩ j hj
      cases j with
      | zero => simpa using hzero
      | succ j => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest j (by omega)
    · intro h
      constructor
      · simpa using h 0 (by omega)
      · intro j hj
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h (j + 1) (by omega)

private def matchWindow (p key : Nibbles) (pos : Nat) : Bool :=
  decide (p.size ≤ key.size - pos) && scan p key pos p.size 0

private theorem matchWindow_true (p key : Nibbles) (pos : Nat) :
    matchWindow p key pos = true ↔ p = (key.drop pos).take p.size := by
  rw [matchWindow, Bool.and_eq_true, decide_eq_true_eq, scan_true]
  simp only [Nat.zero_add]
  constructor
  · rintro ⟨hlen, hdigits⟩
    apply Nibbles.ext
    apply List.ext_getElem
    · simp only [Nibbles.length_toList, Nibbles.size_take, Nibbles.size_drop]
      omega
    · intro i hi hj
      have hp : i < p.size := by rwa [Nibbles.length_toList] at hi
      have hk : pos + i < key.size := by omega
      rw [Nibbles.getElem_toList _ _ hp, Nibbles.getElem_toList _ _
        (by rwa [Nibbles.length_toList] at hj), Nibbles.get_take, Nibbles.get_drop]
      simpa [digitAt, hp, hk] using hdigits i hp
  · intro he
    have hs := congrArg Nibbles.size he
    simp only [Nibbles.size_take, Nibbles.size_drop] at hs
    have hlen : p.size ≤ key.size - pos := by omega
    refine ⟨hlen, ?_⟩
    intro i hi
    have hk : pos + i < key.size := by omega
    have hd := congrArg (fun x => x.toList[i]?) he
    have hr : i < ((key.drop pos).take p.size).toList.length := by
      rw [Nibbles.length_toList, Nibbles.size_take, Nibbles.size_drop]
      omega
    rw [List.getElem?_eq_getElem (by rw [Nibbles.length_toList]; exact hi),
      List.getElem?_eq_getElem hr] at hd
    have hrsize : i < ((key.drop pos).take p.size).size := by
      rwa [Nibbles.length_toList] at hr
    rw [Nibbles.getElem_toList p i hi, Nibbles.getElem_toList _ i hrsize,
      Nibbles.get_take, Nibbles.get_drop] at hd
    simpa [digitAt, hi, hk] using Option.some.inj hd

private theorem ext_smaller (path : Nibbles) (child : Node) (enc : Enc) :
    sizeOf (some child : Ref) < sizeOf (some (.ext path child enc) : Ref) := by
  simp only [Option.some.sizeOf_spec, Node.ext.sizeOf_spec]
  omega

private theorem branch_smaller (children : Array Ref) (value : ByteArray) (enc : Enc)
    (i : Nat) (hi : i < children.size) :
    sizeOf (children[i]'hi) < sizeOf (some (.branch children value enc) : Ref) := by
  have h := Array.sizeOf_getElem children i hi
  simp only [Option.some.sizeOf_spec, Node.branch.sizeOf_spec]
  omega

private def reference (root : Ref) (key : Nibbles) : Except TrieError (Option ByteArray) :=
  match root with
  | none => .ok none
  | some (.hashed h) => .error (.unresolved h)
  | some (.leaf path value _) => .ok (if path = key then some value else none)
  | some (.ext path child _) =>
    if path = key.take path.size then reference (some child) (key.drop path.size) else .ok none
  | some (.branch children value _) =>
    if hk : 0 < key.size then
      let i := (key.get ⟨0, hk⟩).val
      if hi : i < children.size then reference (children[i]'hi) (key.drop 1)
      else .error (.malformed (.branchIndex i children.size))
    else .ok (if value.size = 0 then none else some value)
termination_by sizeOf root
decreasing_by
  · exact ext_smaller _ _ _
  · exact branch_smaller _ _ _ _ _

private def cursor (root : Ref) (key : Nibbles) (pos : Nat) :
    Except TrieError (Option ByteArray) :=
  match root with
  | none => .ok none
  | some (.hashed h) => .error (.unresolved h)
  | some (.leaf path value _) =>
    .ok (if path.size = key.size - pos ∧ matchWindow path key pos = true then
      some value else none)
  | some (.ext path child _) =>
    if matchWindow path key pos then cursor (some child) key (pos + path.size)
    else .ok none
  | some (.branch children value _) =>
    if hk : pos < key.size then
      let i := (key.get ⟨pos, hk⟩).val
      if hi : i < children.size then cursor (children[i]'hi) key (pos + 1)
      else .error (.malformed (.branchIndex i children.size))
    else .ok (if value.size = 0 then none else some value)
termination_by sizeOf root
decreasing_by
  · exact ext_smaller _ _ _
  · exact branch_smaller _ _ _ _ _

private theorem leaf_matchWindow (path key : Nibbles) (pos : Nat) :
    (path.size = key.size - pos ∧ matchWindow path key pos = true) ↔ path = key.drop pos := by
  rw [matchWindow_true]
  constructor
  · rintro ⟨hs, he⟩
    rw [hs, ← Nibbles.size_drop key pos, Nibbles.take_size] at he
    exact he
  · intro he
    subst path
    refine ⟨Nibbles.size_drop _ _, ?_⟩
    exact (Nibbles.take_size _).symm

private theorem cursor_reference (root : Ref) (key : Nibbles) (pos : Nat) :
    cursor root key pos = reference root (key.drop pos) := by
  cases root with
  | none => rw [cursor, reference]
  | some node =>
    cases node with
    | hashed h => rw [cursor, reference]
    | leaf path value enc => rw [cursor, reference]; simp only [leaf_matchWindow]
    | ext path child enc =>
      rw [cursor, reference]
      simp only [matchWindow_true]
      split
      · rw [cursor_reference, Nibbles.drop_drop]
      · rfl
    | branch children value enc =>
      rw [cursor, reference]
      have hk : (pos < key.size) ↔ 0 < (key.drop pos).size := by rw [Nibbles.size_drop]; omega
      by_cases hp : pos < key.size
      · have hp' := hk.mp hp
        simp only [hp, hp', dite_true, Nibbles.get_drop, Nat.add_zero]
        split
        · rw [cursor_reference, Nibbles.drop_drop]
        · rfl
      · have hp' : ¬ 0 < (key.drop pos).size := fun h => hp (hk.mpr h)
        simp [hp, hp']
termination_by sizeOf root
decreasing_by
  · exact ext_smaller _ _ _
  · exact branch_smaller _ _ _ _ _


/-- Total pure bare-tree lookup. Pinned EELS
`src/ethereum/forks/amsterdam/witness_state.py:53–100`; Q59
adapts a reached missing selected slot to its exact typed index/arity diagnostic. -/
def lookup (root : Ref) (key : Nibbles) : Except TrieError (Option ByteArray) := cursor root key 0

private theorem lookup_reference (root : Ref) (key : Nibbles) :
    lookup root key = reference root key := by
  rw [lookup, cursor_reference, Nibbles.drop_zero]


/-- An absent root is successful absence. -/
theorem lookup_none (key : Nibbles) : lookup none key = .ok none := by
  rw [lookup_reference, reference]

/-- A reached unresolved stub fails before key exhaustion. -/
theorem lookup_hashed (h : Hash32) (key : Nibbles) :
    lookup (some (.hashed h)) key = .error (.unresolved h) := by
  rw [lookup_reference, reference]

/-- A leaf matches the complete remaining key and preserves even an empty value. -/
theorem lookup_leaf (path : Nibbles) (value : ByteArray) (enc : Enc) (key : Nibbles) :
    lookup (some (.leaf path value enc)) key = .ok (if path = key then some value else none) := by
  rw [lookup_reference, reference]

/-- An extension descends only after its whole clipped-prefix match. -/
theorem lookup_ext (path : Nibbles) (child : Node) (enc : Enc) (key : Nibbles) :
    lookup (some (.ext path child enc)) key =
      if path = key.take path.size then lookup (some child) (key.drop path.size)
      else .ok none := by
  rw [lookup_reference, reference]
  split <;> simp only [lookup_reference]

/-- Terminal branch value dispatch precedes all selected-slot bounds. -/
theorem lookup_branch_emptyKey (children : Array Ref) (value : ByteArray)
    (enc : Enc) (key : Nibbles) (hkey : key.size = 0) :
    lookup (some (.branch children value enc)) key =
      .ok (if value.size = 0 then none else some value) := by
  rw [lookup_reference, reference]
  simp [hkey]

/-- A nonterminal in-bounds branch follows exactly its selected child. -/
theorem lookup_branch_index (children : Array Ref) (value : ByteArray)
    (enc : Enc) (key : Nibbles) (hkey : 0 < key.size)
    (hindex : (key.get ⟨0, hkey⟩).val < children.size) :
    lookup (some (.branch children value enc)) key =
      lookup (children[(key.get ⟨0, hkey⟩).val]'hindex) (key.drop 1) := by
  rw [lookup_reference, reference]
  simp only [hkey, dite_true, hindex, lookup_reference]

/-- A missing selected slot retains the actual nibble and actual array arity. -/
theorem lookup_branch_oob (children : Array Ref) (value : ByteArray)
    (enc : Enc) (key : Nibbles) (hkey : 0 < key.size)
    (hindex : children.size ≤ (key.get ⟨0, hkey⟩).val) :
    lookup (some (.branch children value enc)) key =
      .error (.malformed (.branchIndex (key.get ⟨0, hkey⟩).val children.size)) := by
  rw [lookup_reference, reference]
  simp [hkey, show ¬ (key.get ⟨0, hkey⟩).val < children.size by omega]

end STFSpec.Commit
