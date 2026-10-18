/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Commit.Branch

/-!
# Total bare partial-trie deletion

Library `EthCommit`. Pinned EELS
`src/ethereum/forks/amsterdam/incremental_mpt.py:680–828`.
Visited surviving nodes are strictly recompleted, including no-op nodes. Private
source-control metadata distinguishes clean same-origin returns from changes;
nominal structural or allocation equality never decides source changedness.
Off-path fields and caches remain intact. The independent List-wire/CPS reference
has the same complete action under plain Monad. Mutable source correspondence
requires the precise local observed-clean and embedding premises in the guidance.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` C19/C24/C25/§7.0.10.
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

private structure ChangedResult where
  ref : Ref
  sameOrigin : Bool
  dirty : Bool

private def hasPresent (xs : Array Ref) : Bool := xs.any Option.isSome

private def collapseThen {m : Type → Type} [Monad m] [KeccakQuery m]
    (xs : Array Ref) (v : ByteArray)
    (k : ChangedResult → m (Except TrieError Ref)) : m (Except TrieError Ref) :=
  if v.size = 0 && hasPresent xs = false then
    pure (.error (.malformed (.occupancy 0)))
  else
    mkBranch xs v >>= fun result =>
      match result with
      | .error e => pure (.error e)
      | .ok ref => k ⟨ref, (match ref with | some (.branch ..) => true | _ => false),
          ref.isSome⟩

private def collapseReferenceThen {m : Type → Type} [Monad m] [KeccakQuery m]
    (xs : List Ref) (v : ByteArray)
    (k : ChangedResult → m (Except TrieError Ref)) : m (Except TrieError Ref) :=
  if v.size = 0 && xs.any Option.isSome = false then
    pure (.error (.malformed (.occupancy 0)))
  else
    mkBranch xs.toArray v >>= fun result =>
      match result with
      | .error e => pure (.error e)
      | .ok ref => k ⟨ref, (match ref with | some (.branch ..) => true | _ => false),
          ref.isSome⟩

private theorem collapseThen_eq_reference {m : Type → Type} [Monad m] [KeccakQuery m]
    (xs : Array Ref) (v : ByteArray)
    (k : ChangedResult → m (Except TrieError Ref)) :
    collapseThen xs v k = collapseReferenceThen xs.toList v k := by
  simp only [collapseThen, collapseReferenceThen, hasPresent, Array.any_toList,
    Array.toArray_toList]
  rfl

private theorem reached_zero_literal {m : Type → Type} [Monad m] [KeccakQuery m]
    (k : ChangedResult → m (Except TrieError Ref)) :
    collapseThen #[] ByteArray.empty k = pure (.error (.malformed (.occupancy 0))) := by
  simp [collapseThen, hasPresent]

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

private theorem leaf_matchWindow (p key : Nibbles) (pos : Nat) :
    (p.size = key.size - pos ∧ matchWindow p key pos = true) ↔ p = key.drop pos := by
  rw [matchWindow_true]
  constructor
  · rintro ⟨hs, he⟩
    rw [hs, ← Nibbles.size_drop key pos, Nibbles.take_size] at he
    exact he
  · intro he
    subst p
    refine ⟨Nibbles.size_drop _ _, ?_⟩
    exact (Nibbles.take_size _).symm

private theorem ext_smaller (p : Nibbles) (c : Node) (enc : Enc) :
    sizeOf (some c : Ref) < sizeOf (some (.ext p c enc) : Ref) := by
  simp only [Option.some.sizeOf_spec, Node.ext.sizeOf_spec]
  omega

private theorem branch_smaller (xs : Array Ref) (v : ByteArray) (enc : Enc)
    (i : Nat) (hi : i < xs.size) :
    sizeOf (xs[i]'hi) < sizeOf (some (.branch xs v enc) : Ref) := by
  have h := Array.sizeOf_getElem xs i hi
  simp only [Option.some.sizeOf_spec, Node.branch.sizeOf_spec]
  omega

private def extThen {m : Type → Type} [Monad m] [KeccakQuery m]
    (p : Nibbles) (r : ChangedResult)
    (k : ChangedResult → m (Except TrieError Ref)) : m (Except TrieError Ref) :=
  match r.ref with
  | none => k ⟨none, false, false⟩
  | some (.hashed h) => pure (.error (.unresolved h))
  | some n@(.leaf ..) | some n@(.ext ..) =>
    mkExt p n >>= fun parent => k ⟨some parent, false, true⟩
  | some n@(.branch ..) =>
    freshExt p n >>= fun parent => k ⟨some parent, true, (!r.sameOrigin || r.dirty)⟩

private def branchThen {m : Type → Type} [Monad m] [KeccakQuery m]
    (xs : Array Ref) (v : ByteArray) (i : Nat) (hi : i < xs.size) (r : ChangedResult)
    (k : ChangedResult → m (Except TrieError Ref)) : m (Except TrieError Ref) :=
  match r.ref with
  | some (.hashed h) => pure (.error (.unresolved h))
  | _ =>
    let changed := xs.set i r.ref (h := hi)
    if r.sameOrigin && !r.dirty then
      freshBranch changed v >>= fun parent => k ⟨some parent, true, false⟩
    else collapseThen changed v k

private def extReferenceThen (p : List (Fin 16)) (r : ChangedResult)
    (k : ChangedResult → m (Except TrieError Ref)) : m (Except TrieError Ref) :=
  match r.ref with
  | none => k ⟨none, false, false⟩
  | some (.hashed h) => pure (.error (.unresolved h))
  | some n@(.leaf ..) | some n@(.ext ..) =>
    mkExt (Nibbles.ofList p) n >>= fun parent => k ⟨some parent, false, true⟩
  | some n@(.branch ..) =>
    freshExtReference p n >>= fun parent =>
      k ⟨some parent, true, (!r.sameOrigin || r.dirty)⟩

private def branchReferenceThen (xs : List Ref) (v : ByteArray) (i : Nat)
    (r : ChangedResult) (k : ChangedResult → m (Except TrieError Ref)) :
    m (Except TrieError Ref) :=
  match r.ref with
  | some (.hashed h) => pure (.error (.unresolved h))
  | _ =>
    let changed := xs.set i r.ref
    if r.sameOrigin && !r.dirty then
      freshBranchReference changed v >>= fun parent => k ⟨some parent, true, false⟩
    else collapseReferenceThen changed v k

private theorem extThen_eq_reference (p : Nibbles) (r : ChangedResult)
    (k : ChangedResult → m (Except TrieError Ref)) :
    extThen p r k = extReferenceThen p.toList r k := by
  cases hr : r.ref with
  | none => simp only [extThen, extReferenceThen, hr]
  | some node =>
    cases node <;> simp only [extThen, extReferenceThen, hr,
      Nibbles.ofList_toList, freshExt_eq_reference]

private theorem branchThen_eq_reference (xs : Array Ref) (v : ByteArray)
    (i : Nat) (hi : i < xs.size) (r : ChangedResult)
    (k : ChangedResult → m (Except TrieError Ref)) :
    branchThen xs v i hi r k = branchReferenceThen xs.toList v i r k := by
  cases hr : r.ref with
  | none =>
    simp only [branchThen, branchReferenceThen, hr, freshBranch_eq_reference,
      collapseThen_eq_reference, selected_set_model]
  | some node =>
    cases node <;> simp only [branchThen, branchReferenceThen, hr,
      freshBranch_eq_reference, collapseThen_eq_reference, selected_set_model]

private def cursor {m : Type → Type} [Monad m] [KeccakQuery m]
    (root : Ref) (key : Nibbles) (pos : Nat)
    (k : ChangedResult → m (Except TrieError Ref)) : m (Except TrieError Ref) :=
  match root with
  | none => k ⟨none, true, false⟩
  | some (.hashed h) => pure (.error (.unresolved h))
  | some (.leaf p v _) =>
    if p.size = key.size - pos ∧ matchWindow p key pos = true then k ⟨none, false, false⟩
    else mkLeaf p v >>= fun n => k ⟨some n, true, false⟩
  | some (.ext p child _) =>
    if matchWindow p key pos then
      cursor (some child) key (pos + p.size) (fun r => extThen p r k)
    else freshExt p child >>= fun n => k ⟨some n, true, false⟩
  | some (.branch xs v _) =>
    if hp : pos < key.size then
      let i := (key.get ⟨pos, hp⟩).val
      if hi : i < xs.size then
        cursor (xs[i]'hi) key (pos + 1) (fun r => branchThen xs v i hi r k)
      else pure (.error (.malformed (.branchIndex i xs.size)))
    else
      if v.size = 0 then freshBranch xs v >>= fun n => k ⟨some n, true, false⟩
      else collapseThen xs ByteArray.empty k
termination_by sizeOf root
decreasing_by
  · exact ext_smaller _ _ _
  · exact branch_smaller _ _ _ _ _

private def reference {m : Type → Type} [Monad m] [KeccakQuery m]
    (root : Ref) (key : List (Fin 16))
    (k : ChangedResult → m (Except TrieError Ref)) : m (Except TrieError Ref) :=
  match root with
  | none => k ⟨none, true, false⟩
  | some (.hashed h) => pure (.error (.unresolved h))
  | some (.leaf p v _) =>
    if p.toList = key then k ⟨none, false, false⟩
    else freshLeafReference p.toList v >>= fun n => k ⟨some n, true, false⟩
  | some (.ext p child _) =>
    if p.toList = key.take p.size then
      reference (some child) (key.drop p.size) (fun r => extReferenceThen p.toList r k)
    else freshExtReference p.toList child >>= fun n => k ⟨some n, true, false⟩
  | some (.branch xs v _) =>
    match key with
    | [] =>
      if v.size = 0 then freshBranchReference xs.toList v >>= fun n => k ⟨some n, true, false⟩
      else collapseReferenceThen xs.toList ByteArray.empty k
    | digit :: tail =>
      if hi : digit.val < xs.size then
        reference (xs[digit.val]'hi) tail (fun r => branchReferenceThen xs.toList v digit.val r k)
      else pure (.error (.malformed (.branchIndex digit.val xs.size)))
termination_by sizeOf root
decreasing_by
  · exact ext_smaller _ _ _
  · exact branch_smaller _ _ _ _ _

private theorem cursor_eq_reference (root : Ref) (key : Nibbles) (pos : Nat)
    (k : ChangedResult → m (Except TrieError Ref)) :
    cursor root key pos k = reference root (key.toList.drop pos) k := by
  cases root with
  | none => rw [cursor, reference]
  | some node =>
    cases node with
    | hashed h => rw [cursor, reference]
    | leaf p v enc =>
      rw [cursor, reference]
      have hc : (p = key.drop pos) ↔ p.toList = key.toList.drop pos := by
        rw [← Nibbles.toList_inj, Nibbles.toList_drop]
      simp only [leaf_matchWindow, hc, freshLeaf_eq_reference]
    | ext p child enc =>
      rw [cursor, reference]
      have hc : matchWindow p key pos = true ↔
          p.toList = (key.toList.drop pos).take p.size := by
        rw [matchWindow_true, ← Nibbles.toList_inj, Nibbles.toList_take,
          Nibbles.toList_drop]
      simp only [hc]
      split
      · rw [cursor_eq_reference, List.drop_drop]
        have hk : (fun r => extThen (m := m) p r k) =
            (fun r => extReferenceThen (m := m) p.toList r k) :=
          funext (fun r => extThen_eq_reference p r k)
        rw [hk]
      · rw [freshExt_eq_reference]
    | branch xs v enc =>
      rw [cursor]
      by_cases hp : pos < key.size
      · have hs : key.toList.drop pos = key.get ⟨pos, hp⟩ :: key.toList.drop (pos + 1) := by
          have hp' : pos < key.toList.length := by simpa [Nibbles.length_toList] using hp
          rw [List.drop_eq_getElem_cons hp', Nibbles.getElem_toList key pos hp]
        rw [hs, reference]
        simp only [hp, ↓reduceDIte]
        split
        · rename_i hi
          rw [cursor_eq_reference]
          have hk : (fun r => branchThen (m := m) xs v (key.get ⟨pos, hp⟩).val hi r k) =
              (fun r => branchReferenceThen (m := m) xs.toList v
                (key.get ⟨pos, hp⟩).val r k) :=
            funext (fun r => branchThen_eq_reference xs v (key.get ⟨pos, hp⟩).val hi r k)
          rw [hk]
        · rfl
      · have hs : key.toList.drop pos = [] := by
          apply List.drop_eq_nil_of_le
          rw [Nibbles.length_toList]
          omega
        rw [hs, reference]
        simp only [hp, ↓reduceDIte, freshBranch_eq_reference, collapseThen_eq_reference]
termination_by sizeOf root
decreasing_by
  · exact ext_smaller _ _ _
  · exact branch_smaller _ _ _ _ _

/-- Total deletion on all finite bare partial tries. Pinned EELS
`src/ethereum/forks/amsterdam/incremental_mpt.py:680–828`. -/
def delete {m : Type → Type} [Monad m] [KeccakQuery m]
    (root : Ref) (key : Nibbles) : m (Except TrieError Ref) :=
  cursor root key 0 (fun r => pure (.ok r.ref))

/-- A reached root missing selected slot fails before any query or completion. -/
theorem delete_branch_oob {m : Type → Type} [Monad m] [KeccakQuery m]
    (xs : Array Ref) (v : ByteArray) (enc : Enc) (key : Nibbles)
    (hkey : 0 < key.size) (hindex : xs.size ≤ (key.get ⟨0, hkey⟩).val) :
    delete (m := m) (some (.branch xs v enc)) key =
      pure (.error (.malformed (.branchIndex (key.get ⟨0, hkey⟩).val xs.size))) := by
  simp only [delete, cursor, hkey, ↓reduceDIte]
  simp only [show ¬ (key.get ⟨0, hkey⟩).val < xs.size from Nat.not_lt.mpr hindex,
    ↓reduceDIte]

/-- Clearing a nonempty terminal value in an empty actual array returns bare `occupancy 0`. -/
theorem delete_terminal_clear_empty {m : Type → Type} [Monad m]
    [KeccakQuery m] (v : ByteArray) (enc : Enc) (key : Nibbles)
    (hkey : key.size = 0) (hvalue : 0 < v.size) :
    delete (m := m) (some (.branch #[] v enc)) key =
      pure (.error (.malformed (.occupancy 0))) := by
  simp only [delete, cursor, hkey, Nat.lt_irrefl, ↓reduceDIte,
    show v.size ≠ 0 from Nat.ne_of_gt hvalue, ↓reduceIte]
  exact reached_zero_literal _

/-! ### Private source-control and literal-error guards

These observers stay with their private owner. Synthetic flag payloads are test
observations; they introduce no protocol error site or public metadata API.
-/
private structure Probe (α : Type) where
  value : α
  ticks : Nat
private instance : Monad Probe where
  pure a := ⟨a, 1⟩
  bind a k := let b := k a.value; ⟨b.value, 2 * a.ticks + b.ticks + 1⟩
private abbrev probeQuery : KeccakQuery Probe :=
  ⟨fun _ => ⟨Hash32.ofBytes32 (FixedBytes.ofNat 37), 5⟩⟩
private def probeClassify (r : ChangedResult) : Probe (Except TrieError Ref) :=
  pure (.error (.malformed (.branchIndex (if r.sameOrigin then 1 else 0)
    (if r.dirty then 1 else 0))))
private def probeFlags (r : Probe (Except TrieError Ref)) : List Nat :=
  match r.value with
  | .error (.malformed (.branchIndex a b)) => [a,b,r.ticks]
  | .error (.malformed (.occupancy n)) => [2,n,r.ticks]
  | .error (.unresolved _) => [3,r.ticks]
  | _ => []
private def probeEnc : Enc :=
  ⟨[255].toByteArray, some (Hash32.ofBytes32 (FixedBytes.ofNat 99))⟩
private def probeLeaf : Node :=
  .leaf (Nibbles.ofList [1]) [170].toByteArray probeEnc
#guard probeFlags (@cursor Probe inferInstance probeQuery none (Nibbles.ofList []) 0
  probeClassify) == [1,0,1]
#guard probeFlags (@cursor Probe inferInstance probeQuery (some probeLeaf)
  (Nibbles.ofList [1]) 0 probeClassify) == [0,0,1]
#guard probeFlags (@cursor Probe inferInstance probeQuery (some probeLeaf)
  (Nibbles.ofList [2]) 0 probeClassify) == [1,0,4]
#guard probeFlags (@cursor Probe inferInstance probeQuery
  (some (.ext (Nibbles.ofList []) probeLeaf probeEnc))
  (Nibbles.ofList [2]) 0 probeClassify) == [0,1,7]
#guard probeFlags (@cursor Probe inferInstance probeQuery
  (some (.branch #[some probeLeaf,none] ByteArray.empty probeEnc))
  (Nibbles.ofList [0,2]) 0 probeClassify) == [1,0,7]
#guard probeFlags (@cursor Probe inferInstance probeQuery
  (some (.branch #[some probeLeaf,none] [255].toByteArray probeEnc))
  (Nibbles.ofList [0,1]) 0 probeClassify) == [0,1,10]
#guard probeFlags (@cursor Probe inferInstance probeQuery
  (some (.branch #[some probeLeaf,some probeLeaf] [255].toByteArray probeEnc))
  (Nibbles.ofList [0,1]) 0 probeClassify) == [1,1,54]
#guard probeFlags (@collapseThen Probe inferInstance probeQuery #[] ByteArray.empty
  probeClassify) == [2,0,1]
#guard probeFlags (@collapseThen Probe inferInstance probeQuery
  ((Array.replicate 17 none).push (some (.hashed
    (Hash32.ofBytes32 (FixedBytes.ofNat 17))))) ByteArray.empty probeClassify) == [3,4]

end STFSpec.Commit
