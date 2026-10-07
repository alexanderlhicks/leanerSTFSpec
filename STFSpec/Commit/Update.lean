/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit.Leaf
import STFSpec.Commit.ChildRef
import STFSpec.Commit.TrieError

/-!
# Total bare partial-trie insertion

Library `EthCommit`. Pinned EELS `incremental_mpt.py:473–677`.
Insertion preserves the reached source constructors, completes fresh nodes in
old-side/new-side/child/parent order, and retains every off-path field and cache.
The private copying reference has the same literal CPS monad action on all inputs.
Source mutable invalidation and later materialization have separate local premises.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` C23/Q60/§7.0.10.
-/

namespace STFSpec.Commit
open STFSpec.Base STFSpec.Codec STFSpec.Hash
variable {m : Type → Type} [Monad m] [KeccakQuery m]

private theorem compact_model (p : Nibbles) (leaf : Bool) :
    nibbleListToCompact p leaf = (nibbleListToCompactModel p.toList leaf).toByteArray := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simpa only [List.toList_data_toByteArray] using nibbleListToCompact_eq_model p leaf

private theorem wire_model (item : RlpItem) :
    Rlp.encode item = (Rlp.encodeModel item).toByteArray := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simpa only [List.toList_data_toByteArray] using Rlp.toList_encode item

private def branchItem (xs : Array Ref) (v : ByteArray) : RlpItem :=
  .list (List.ofFn (fun i : Fin xs.size => childRef xs[i]) ++ [.bytes v])
private def branchItemReference (xs : List Ref) (v : ByteArray) : RlpItem :=
  .list (xs.map childRef ++ [.bytes v])

private theorem branchItem_eq (xs : Array Ref) (v : ByteArray) :
    branchItem xs v = branchItemReference xs.toList v := by
  have indexed : List.ofFn (fun i : Fin xs.size => childRef xs[i]) =
      xs.toList.map childRef := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  rw [branchItem, branchItemReference, indexed]

private def freshExt (p : Nibbles) (child : Node) : m Node :=
  let raw := Rlp.encode (.list [.bytes (nibbleListToCompact p false), childRef (some child)])
  if raw.size < 32 then pure (.ext p child ⟨raw, none⟩)
  else KeccakQuery.keccak raw >>= fun answer => pure (.ext p child ⟨raw, some answer⟩)

private def freshBranch (xs : Array Ref) (v : ByteArray) : m Node :=
  let raw := Rlp.encode (branchItem xs v)
  if raw.size < 32 then pure (.branch xs v ⟨raw, none⟩)
  else KeccakQuery.keccak raw >>= fun answer => pure (.branch xs v ⟨raw, some answer⟩)

private def freshLeafReference (p : List (Fin 16)) (v : ByteArray) : m Node :=
  let raw := (Rlp.encodeModel (.list
    [.bytes (nibbleListToCompactModel p true).toByteArray, .bytes v])).toByteArray
  if raw.size < 32 then pure (.leaf (Nibbles.ofList p) v ⟨raw, none⟩)
  else KeccakQuery.keccak raw >>= fun answer =>
    pure (.leaf (Nibbles.ofList p) v ⟨raw, some answer⟩)

private def freshExtReference (p : List (Fin 16)) (child : Node) : m Node :=
  let raw := (Rlp.encodeModel (.list
    [.bytes (nibbleListToCompactModel p false).toByteArray, childRef (some child)])).toByteArray
  if raw.size < 32 then pure (.ext (Nibbles.ofList p) child ⟨raw, none⟩)
  else KeccakQuery.keccak raw >>= fun answer =>
    pure (.ext (Nibbles.ofList p) child ⟨raw, some answer⟩)

private def freshBranchReference (xs : List Ref) (v : ByteArray) : m Node :=
  let raw := (Rlp.encodeModel (branchItemReference xs v)).toByteArray
  if raw.size < 32 then pure (.branch xs.toArray v ⟨raw, none⟩)
  else KeccakQuery.keccak raw >>= fun answer => pure (.branch xs.toArray v ⟨raw, some answer⟩)

private theorem freshLeaf_eq_reference (p : Nibbles) (v : ByteArray) :
    mkLeaf (m := m) p v = freshLeafReference p.toList v := by
  have raw : Rlp.encode (assembleInternalNode (some (.leaf p (.bytes v)))) =
      (Rlp.encodeModel (.list [.bytes (nibbleListToCompactModel p.toList true).toByteArray,
        .bytes v])).toByteArray := by
    rw [assembleInternalNode_leaf, compact_model, wire_model]
  by_cases h : (Rlp.encode (assembleInternalNode (some (.leaf p (.bytes v))))).size < 32
  · rw [mkLeaf_inline p v h, freshLeafReference, ← raw]
    simp only [h, ↓reduceIte, Nibbles.ofList_toList]
  · rw [mkLeaf_hash p v (by omega), freshLeafReference, ← raw]
    simp only [h, ↓reduceIte, Nibbles.ofList_toList]

private theorem freshExt_eq_reference (p : Nibbles) (c : Node) :
    freshExt (m := m) p c = freshExtReference p.toList c := by
  simp only [freshExt, freshExtReference, compact_model, wire_model, Nibbles.ofList_toList]

private theorem freshBranch_eq_reference (xs : Array Ref) (v : ByteArray) :
    freshBranch (m := m) xs v = freshBranchReference xs.toList v := by
  simp only [freshBranch, freshBranchReference, wire_model, branchItem_eq,
    Array.toArray_toList]

private theorem selected_set_model (xs : Array Ref) (i : Nat) (v : Ref)
    (hi : i < xs.size) :
    (xs.set i v hi).toList = xs.toList.set i v := by simp

private def digitAt (p : Nibbles) (i : Nat) : Fin 16 :=
  if hi : i < p.size then p.get ⟨i, hi⟩ else 0

private def prefixWindowScan (p key : Nibbles) (pos : Nat) : Nat → Nat → Nat
  | 0, i => i
  | remaining + 1, i =>
    if digitAt p i = digitAt key (pos + i) then
      prefixWindowScan p key pos remaining (i + 1)
    else i

private def prefixWindow (p key : Nibbles) (pos : Nat) : Nat :=
  prefixWindowScan p key pos (min p.size (key.size - pos)) 0

private theorem prefixWindowScan_model (p key : Nibbles) (pos remaining i : Nat)
    (h : remaining + i = min p.size (key.size - pos)) :
    prefixWindowScan p key pos remaining i =
      i + commonPrefixLengthModel (p.toList.drop i) (key.toList.drop (pos + i)) := by
  induction remaining generalizing i with
  | zero =>
    have he : p.toList.drop i = [] ∨ key.toList.drop (pos + i) = [] := by
      by_cases hp : p.size ≤ key.size - pos
      · left
        rw [List.drop_of_length_le (by rw [Nibbles.length_toList]; omega)]
      · right
        rw [List.drop_of_length_le (by rw [Nibbles.length_toList]; omega)]
    rcases he with he | he
    · simp [prefixWindowScan, he, commonPrefixLengthModel]
    · cases hx : p.toList.drop i <;> simp [prefixWindowScan, he, commonPrefixLengthModel]
  | succ remaining ih =>
    have hp : i < p.size := by omega
    have hk : pos + i < key.size := by omega
    have ep : p.toList.drop i = p.get ⟨i, hp⟩ :: p.toList.drop (i + 1) := by
      rw [← List.getElem_cons_drop (by rw [Nibbles.length_toList]; exact hp),
        Nibbles.getElem_toList _ _ hp]
    have ek : key.toList.drop (pos + i) =
        key.get ⟨pos + i, hk⟩ :: key.toList.drop (pos + (i + 1)) := by
      rw [← List.getElem_cons_drop (by rw [Nibbles.length_toList]; exact hk),
        Nibbles.getElem_toList _ _ hk]
      simp only [Nat.add_assoc]
    rw [prefixWindowScan, ep, ek, commonPrefixLengthModel]
    simp only [digitAt, dite_eq_left hp, dite_eq_left hk]
    split
    · rw [ih (i + 1) (by omega)]
      omega
    · omega

private theorem prefixWindow_model (p key : Nibbles) (pos : Nat) :
    prefixWindow p key pos = commonPrefixLengthModel p.toList (key.toList.drop pos) := by
  rw [prefixWindow, prefixWindowScan_model _ _ _ _ _ (by omega)]
  simp

-- The source collision assertion cannot be reached by a maximal-prefix split.
private theorem split_digits_distinct (p key : Nibbles) (pos : Nat)
    (hp : prefixWindow p key pos < p.size)
    (hk : prefixWindow p key pos < key.size - pos) :
    p.get ⟨prefixWindow p key pos, hp⟩ ≠
      key.get ⟨pos + prefixWindow p key pos, by omega⟩ := by
  have window : prefixWindow p key pos = commonPrefixLength p (key.drop pos) := by
    rw [prefixWindow_model, commonPrefixLength_eq_model, Nibbles.toList_drop]
  have h := commonPrefixLength_maximal p (key.drop pos)
    (by rwa [← window]) (by rwa [← window, Nibbles.size_drop])
  simpa only [← window, Nibbles.get_drop] using h

private theorem ext_split_nonempty (p key : Nibbles) (pos : Nat)
    (h : prefixWindow p key pos ≠ p.size) : (p.drop (prefixWindow p key pos)).size > 0 := by
  have bound : prefixWindow p key pos ≤ p.size := by
    rw [prefixWindow_model, ← Nibbles.toList_drop, ← commonPrefixLength_eq_model]
    exact commonPrefixLength_le_left _ _
  rw [Nibbles.size_drop]
  omega

private theorem ext_smaller (p : Nibbles) (c : Node) (e : Enc) :
    sizeOf (some c : Ref) < sizeOf (some (.ext p c e) : Ref) := by
  simp only [Option.some.sizeOf_spec, Node.ext.sizeOf_spec]
  omega

private theorem branch_smaller (xs : Array Ref) (v : ByteArray) (e : Enc)
    (i : Nat) (hi : i < xs.size) :
    sizeOf (xs[i]'hi) < sizeOf (some (.branch xs v e) : Ref) := by
  have h := Array.sizeOf_getElem xs i hi
  simp only [Option.some.sizeOf_spec, Node.branch.sizeOf_spec]
  omega

private def reference (root : Ref) (key : List (Fin 16)) (v : ByteArray)
    (k : Node → m (Except TrieError Ref)) : m (Except TrieError Ref) :=
  match root with
  | none => freshLeafReference key v >>= k
  | some (.hashed h) => pure (.error (.unresolved h))
  | some (.leaf p old _) =>
    if p.toList = key then freshLeafReference p.toList v >>= k
    else
      let l := commonPrefixLengthModel p.toList key
      let finish := fun xs terminal => freshBranchReference xs terminal >>= fun b =>
        if 0 < l then freshExtReference (p.toList.take l) b >>= k else k b
      let newSide := fun xs terminal =>
        match key.drop l with
        | [] => finish xs v
        | i :: tail => freshLeafReference tail v >>= fun n =>
          finish (xs.set i.val (some n)) terminal
      match p.toList.drop l with
      | [] => newSide (List.replicate 16 none) old
      | i :: tail => freshLeafReference tail old >>= fun n =>
        newSide ((List.replicate 16 none).set i.val (some n)) ByteArray.empty
  | some (.ext p child _enc) =>
    let l := commonPrefixLengthModel p.toList key
    if l = p.size then reference (some child) (key.drop l) v
      (fun child' => freshExtReference p.toList child' >>= k)
    else
      let finish := fun xs terminal => freshBranchReference xs terminal >>= fun b =>
        if 0 < l then freshExtReference (p.toList.take l) b >>= k else k b
      let newSide := fun xs =>
        match key.drop l with
        | [] => finish xs v
        | i :: tail => freshLeafReference tail v >>= fun n =>
          finish (xs.set i.val (some n)) ByteArray.empty
      match p.toList.drop l with
      | [] => newSide (List.replicate 16 none)
      | i :: [] => newSide ((List.replicate 16 none).set i.val (some child))
      | i :: j :: tail => freshExtReference (j :: tail) child >>= fun n =>
        newSide ((List.replicate 16 none).set i.val (some n))
  | some (.branch xs old _enc) =>
    match key with
    | [] => freshBranchReference xs.toList v >>= k
    | i :: tail =>
      if hi : i.val < xs.size then reference (xs[i.val]'hi) tail v
        (fun child' => freshBranchReference (xs.toList.set i.val (some child')) old >>= k)
      else pure (.error (.malformed (.branchIndex i.val xs.size)))
termination_by sizeOf root
decreasing_by
  · exact ext_smaller _ _ _
  · exact branch_smaller _ _ _ _ _

private def cursor (root : Ref) (key : Nibbles) (pos : Nat) (v : ByteArray)
    (k : Node → m (Except TrieError Ref)) : m (Except TrieError Ref) :=
  match root with
  | none => mkLeaf (key.drop pos) v >>= k
  | some (.hashed h) => pure (.error (.unresolved h))
  | some (.leaf p old _) =>
    let l := prefixWindow p key pos
    if l = p.size ∧ p.size = key.size - pos then mkLeaf p v >>= k
    else
      let finish := fun xs terminal => freshBranch xs terminal >>= fun b =>
        if 0 < l then freshExt (p.take l) b >>= k else k b
      let newSide := fun (xs : Array Ref) terminal =>
        match (key.drop (pos + l)).toList with
        | [] => finish xs v
        | i :: tail => mkLeaf (Nibbles.ofList tail) v >>= fun n =>
          finish (xs.setIfInBounds i.val (some n)) terminal
      match (p.drop l).toList with
      | [] => newSide (Array.replicate 16 none) old
      | i :: tail => mkLeaf (Nibbles.ofList tail) old >>= fun n =>
        newSide ((Array.replicate 16 none).setIfInBounds i.val (some n)) ByteArray.empty
  | some (.ext p child _enc) =>
    let l := prefixWindow p key pos
    if l = p.size then cursor (some child) key (pos + l) v
      (fun child' => freshExt p child' >>= k)
    else
      let finish := fun xs terminal => freshBranch xs terminal >>= fun b =>
        if 0 < l then freshExt (p.take l) b >>= k else k b
      let newSide := fun (xs : Array Ref) =>
        match (key.drop (pos + l)).toList with
        | [] => finish xs v
        | i :: tail => mkLeaf (Nibbles.ofList tail) v >>= fun n =>
          finish (xs.setIfInBounds i.val (some n)) ByteArray.empty
      match (p.drop l).toList with
      | [] => newSide (Array.replicate 16 none)
      | i :: [] => newSide ((Array.replicate 16 none).setIfInBounds i.val (some child))
      | i :: j :: tail => freshExt (Nibbles.ofList (j :: tail)) child >>= fun n =>
        newSide ((Array.replicate 16 none).setIfInBounds i.val (some n))
  | some (.branch xs old _enc) =>
    if hk : pos < key.size then
      let i := (key.get ⟨pos, hk⟩).val
      if hi : i < xs.size then cursor (xs[i]'hi) key (pos + 1) v
        (fun child' => freshBranch (xs.set i (some child') hi) old >>= k)
      else pure (.error (.malformed (.branchIndex i xs.size)))
    else freshBranch xs v >>= k
termination_by sizeOf root
decreasing_by
  · exact ext_smaller _ _ _
  · exact branch_smaller _ _ _ _ _

private theorem leaf_match (p key : Nibbles) (pos : Nat) :
    (prefixWindow p key pos = p.size ∧ p.size = key.size - pos) ↔
      p.toList = key.toList.drop pos := by
  have window : prefixWindow p key pos = commonPrefixLength p (key.drop pos) := by
    rw [prefixWindow_model, commonPrefixLength_eq_model, Nibbles.toList_drop]
  rw [window, ← Nibbles.toList_drop, Nibbles.toList_inj]
  constructor
  · rintro ⟨hp, hs⟩
    apply Nibbles.ext
    have h := commonPrefixLength_equal_prefixes p (key.drop pos)
    rw [hp, ← Nibbles.length_toList p, List.take_length] at h
    rw [← Nibbles.size_drop key pos] at hs
    have lengths : p.toList.length = (key.drop pos).toList.length := by
      simpa only [Nibbles.length_toList] using hs
    rw [lengths, List.take_length] at h
    exact h
  · intro he
    subst p
    exact ⟨commonPrefixLength_self _, Nibbles.size_drop _ _⟩

private theorem cursor_eq_reference (root : Ref) (key : Nibbles) (pos : Nat)
    (v : ByteArray) (k : Node → m (Except TrieError Ref)) :
    cursor root key pos v k = reference root (key.toList.drop pos) v k := by
  cases root with
  | none =>
    rw [cursor, reference, freshLeaf_eq_reference, Nibbles.toList_drop]
  | some node =>
    cases node with
    | hashed h => rw [cursor, reference]
    | leaf p old e =>
      rw [cursor, reference]
      dsimp only
      simp only [leaf_match]
      simp only [prefixWindow_model, freshLeaf_eq_reference,
        freshExt_eq_reference, freshBranch_eq_reference, Nibbles.toList_take,
        Nibbles.toList_drop, Nibbles.toList_ofList, Array.toList_replicate,
        Array.toList_setIfInBounds, List.drop_drop]
    | ext p c e =>
      rw [cursor, reference]
      simp only [prefixWindow_model]
      split
      · rw [cursor_eq_reference]
        simp only [freshExt_eq_reference, List.drop_drop]
      · simp only [freshLeaf_eq_reference, freshExt_eq_reference,
          freshBranch_eq_reference, Nibbles.toList_take, Nibbles.toList_drop,
          Nibbles.toList_ofList, Array.toList_replicate, Array.toList_setIfInBounds,
          List.drop_drop]
    | branch xs old e =>
      rw [cursor, reference.eq_def]
      by_cases hp : pos < key.size
      · have hk : key.toList.drop pos =
            key.get ⟨pos, hp⟩ :: key.toList.drop (pos + 1) := by
          rw [← List.getElem_cons_drop (by rw [Nibbles.length_toList]; exact hp),
            Nibbles.getElem_toList _ _ hp]
        simp only [hp, ↓reduceDIte, hk]
        split
        · rw [cursor_eq_reference]
          simp only [freshBranch_eq_reference, selected_set_model]
        · rfl
      · have hk : key.toList.drop pos = [] := by
          rw [List.drop_of_length_le (by rw [Nibbles.length_toList]; omega)]
        simp only [hp, ↓reduceDIte, hk, freshBranch_eq_reference]
termination_by sizeOf root
decreasing_by
  · exact ext_smaller _ _ _
  · exact branch_smaller _ _ _ _ _

/-- Insert every finite value, including empty bytes, into a bare partial tree.
Pinned EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:231–237,473–677`.
Only reached stubs and missing selected branch slots produce structural errors;
strict fresh completion forwards the actual query action and answer unchanged. -/
def update (t : Ref) (key : Nibbles) (value : ByteArray) : m (Except TrieError Ref) :=
  cursor t key 0 value (fun n => pure (.ok (some n)))

/-- Root selected-slot failure precedes every completion and query, with the
exact actual nibble and supplied arity, under plain `Monad` (Q60). -/
theorem update_branch_oob (children : Array Ref) (value : ByteArray)
    (enc : Enc) (key : Nibbles) (newValue : ByteArray)
    (hkey : 0 < key.size)
    (hindex : children.size ≤ (key.get ⟨0, hkey⟩).val) :
    update (m := m) (some (.branch children value enc)) key newValue =
      pure (.error (.malformed
        (.branchIndex (key.get ⟨0, hkey⟩).val children.size))) := by
  rw [update, cursor]
  simp only [hkey, ↓reduceDIte]
  rw [dite_eq_right (show ¬ (key.get ⟨0, hkey⟩).val < children.size by omega)]

-- Colocated direct helper controls expose preserving completion and literal binds.
private structure Count (α : Type) where
  value : α
  ticks : Nat
private instance : Monad Count where
  pure a := ⟨a,1⟩
  bind a k := let b := k a.value; ⟨b.value,2*a.ticks+b.ticks+1⟩
private def countAnswer : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat 77)
private abbrev countQuery : KeccakQuery Count := ⟨fun _ => ⟨countAnswer,5⟩⟩

private def countChild : Node :=
  .leaf (Nibbles.ofList [0,15]) ([0,255] : List UInt8).toByteArray
    ⟨([255,0] : List UInt8).toByteArray,some countAnswer⟩
#guard let child := countChild
  let action := @freshExt Count inferInstance countQuery (Nibbles.ofList []) child
  let model := @freshExtReference Count inferInstance countQuery [] child
  action.ticks == 12 && action.ticks == model.ticks &&
    match action.value with
    | .ext p (.leaf q v e) own =>
      p.size == 0 && q.toList == [0,15] && v.data.toList == [0,255] &&
        e.rlp.data.toList == [255,0] && e.hash? == some countAnswer &&
        own.rlp.size ≥ 32 && own.hash? == some countAnswer
    | _ => false
#guard let slots : Array Ref := #[none,some (.hashed countAnswer),none]
  let action := @freshBranch Count inferInstance countQuery slots ByteArray.empty
  let model := @freshBranchReference Count inferInstance countQuery slots.toList ByteArray.empty
  action.ticks == 12 && action.ticks == model.ticks &&
    match action.value with
    | .branch xs v own =>
      xs.size == 3 && v.size == 0 && own.hash? == some countAnswer &&
        match xs[0]?,xs[1]?,xs[2]? with
        | some none,some (some (Node.hashed h)),some none => h == countAnswer
        | _,_,_ => false
    | _ => false
#guard let key := Nibbles.ofList [0,15,0,2]
  let value := (List.replicate 40 (255 : UInt8)).toByteArray
  let root : Ref := some (.ext (Nibbles.ofList [0,15])
    (.leaf (Nibbles.ofList [0,1]) value ⟨ByteArray.empty,none⟩) ⟨ByteArray.empty,none⟩)
  let k := fun n => (pure (.ok (some n)) : Count (Except TrieError Ref))
  (@cursor Count inferInstance countQuery root key 0 value k).ticks ==
    (@reference Count inferInstance countQuery root key.toList value k).ticks

end STFSpec.Commit
