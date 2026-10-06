/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit.Extension
import STFSpec.Commit.TrieError

/-!
# Completed reached-branch collapse

Library `EthCommit`. Pinned EELS `incremental_mpt.py:240–254,316–346,787–828`.
All finite bare slots are admitted. A sole empty-terminal survivor is witnessed
before its index is classified; fresh outputs receive strict own completion.
The private clean supplied-cache realization is a local source correspondence
choice, not arbitrary mutable dirty/history refinement. Source immediate collapse
and later completed cache erasure are separate comparison stages (B15/Q33/Q60).
Private ordinary Array/List/wire/action equalities require only Monad.
Spec guidance: `STFSpec/informal/modules/EthCommit.md`.
-/

namespace STFSpec.Commit
open STFSpec.Base STFSpec.Codec STFSpec.Hash
universe u
variable {α : Type u}

private inductive Census (α : Type u) where
  | zero
  | sole (index : Nat) (child : α)
  | multiple

private def enumeratePresentFrom (start : Nat) : List (Option α) → List (Nat × α)
  | [] => []
  | none :: xs => enumeratePresentFrom (start + 1) xs
  | some a :: xs => (start, a) :: enumeratePresentFrom (start + 1) xs

private def classify : List (Nat × α) → Census α
  | [] => .zero
  | [(i, a)] => .sole i a
  | _ :: _ :: _ => .multiple

private def join : Census α → Census α → Census α
  | .zero, b => b
  | a, .zero => a
  | _, _ => .multiple

private theorem join_assoc (a b c : Census α) : join (join a b) c = join a (join b c) := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem classify_cons (p : Nat × α) (xs : List (Nat × α)) :
    classify (p :: xs) = join (.sole p.1 p.2) (classify xs) := by
  cases xs with
  | nil => rfl
  | cons q xs => cases xs <;> rfl

private def step (s : Nat × Census α) (v : Option α) : Nat × Census α :=
  (s.1 + 1, match v with
    | none => s.2
    | some a => join s.2 (.sole s.1 a))

private def scan (xs : Array (Option α)) : Census α := (xs.foldl step (0, .zero)).2
private def censusReference (xs : Array (Option α)) : Census α :=
  classify (enumeratePresentFrom 0 xs.toList)

private theorem fold_eq (xs : List (Option α)) (i : Nat) (c : Census α) :
    (xs.foldl step (i, c)).2 = join c (classify (enumeratePresentFrom i xs)) := by
  induction xs generalizing i c with
  | nil => cases c <;> rfl
  | cons x xs ih =>
    cases x with
    | none => simpa [List.foldl_cons, step, enumeratePresentFrom] using ih (i + 1) c
    | some a =>
      simpa [List.foldl_cons, step, enumeratePresentFrom, classify_cons, join_assoc]
        using ih (i + 1) (join c (.sole i a))

private theorem scan_eq_reference (xs : Array (Option α)) : scan xs = censusReference xs := by
  unfold scan censusReference
  rw [← Array.foldl_toList]
  simpa [join] using fold_eq xs.toList 0 .zero

private theorem classify_sole_mem (xs : List (Nat × α)) (i : Nat) (a : α)
    (h : classify xs = .sole i a) : (i, a) ∈ xs := by
  cases xs with
  | nil => cases h
  | cons p xs =>
    cases xs with
    | nil =>
      simp only [classify, Census.sole.injEq] at h
      rcases p with ⟨j,b⟩
      rcases h with ⟨rfl,rfl⟩
      exact List.mem_cons_self
    | cons q xs => cases h

private theorem enumerate_mem (xs : List (Option α)) (start i : Nat) (a : α)
    (h : (i,a) ∈ enumeratePresentFrom start xs) :
    ∃ j, ∃ hj : j < xs.length, i = start + j ∧ xs[j] = some a := by
  induction xs generalizing start with
  | nil => simp [enumeratePresentFrom] at h
  | cons x xs ih =>
    cases x with
    | none =>
      obtain ⟨j,hj,hi,ha⟩ := ih (start + 1) (by simpa [enumeratePresentFrom] using h)
      refine ⟨j+1, by simp only [List.length_cons]; omega, ?_, ?_⟩
      · omega
      · simpa using ha
    | some b =>
      simp only [enumeratePresentFrom, List.mem_cons, Prod.mk.injEq] at h
      rcases h with h | h
      · rcases h with ⟨rfl,rfl⟩
        exact ⟨0, by simp, by simp, by simp⟩
      · obtain ⟨j,hj,hi,ha⟩ := ih (start + 1) h
        refine ⟨j+1, by simp only [List.length_cons]; omega, ?_, ?_⟩
        · omega
        · simpa using ha

private theorem scan_sole (xs : Array (Option α)) (i : Nat) (a : α)
    (h : scan xs = .sole i a) : ∃ hi : i < xs.size, xs[i] = some a := by
  rw [scan_eq_reference] at h
  have hm := classify_sole_mem (enumeratePresentFrom 0 xs.toList) i a h
  obtain ⟨j,hj,hi,ha⟩ := enumerate_mem xs.toList 0 i a hm
  have hij : i = j := by simpa using hi
  subst j
  have hs : i < xs.size := by simpa using hj
  exact ⟨hs, by simpa using ha⟩

private def branchItem (xs : Array Ref) (v : ByteArray) : RlpItem :=
  .list (List.ofFn (fun i : Fin xs.size => childRef xs[i]) ++ [.bytes v])
private def branchItemReference (xs : List Ref) (v : ByteArray) : RlpItem :=
  .list (xs.map childRef ++ [.bytes v])

private theorem indexed_map (xs : Array Ref) :
    List.ofFn (fun i : Fin xs.size => childRef xs[i]) = xs.toList.map childRef := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

private theorem branchItem_eq (xs : Array Ref) (v : ByteArray) :
    branchItem xs v = branchItemReference xs.toList v := by
  rw [branchItem, branchItemReference, indexed_map]

private def currentRootItem : Node → RlpItem
  | .leaf p v _ => .list [.bytes (nibbleListToCompact p true), .bytes v]
  | .ext p c _ => .list [.bytes (nibbleListToCompact p false), childRef (some c)]
  | .branch xs v _ => branchItem xs v
  | .hashed h => .bytes h.toBytes.toByteArray

private def currentRootItemReference : Node → RlpItem
  | .leaf p v _ => .list [.bytes (nibbleListToCompactModel p.toList true).toByteArray, .bytes v]
  | .ext p c _ => .list [.bytes (nibbleListToCompactModel p.toList false).toByteArray,
      childRef (some c)]
  | .branch xs v _ => branchItemReference xs.toList v
  | .hashed h => .bytes h.toBytes.toByteArray

private theorem compact_model (p : Nibbles) (leaf : Bool) :
    nibbleListToCompact p leaf = (nibbleListToCompactModel p.toList leaf).toByteArray := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simpa only [List.toList_data_toByteArray] using nibbleListToCompact_eq_model p leaf

private theorem currentRootItem_eq (n : Node) :
    currentRootItem n = currentRootItemReference n := by
  cases n <;> simp only [currentRootItem, currentRootItemReference, compact_model, branchItem_eq]

private def replaceTopEnc : Node → Enc → Node
  | .leaf p v _, enc => .leaf p v enc
  | .ext p c _, enc => .ext p c enc
  | .branch xs v _, enc => .branch xs v enc
  | .hashed h, _ => .hashed h

private structure Witnessed where
  survivor : Node
  raw : ByteArray
  computedHash? : Option Hash32
  entries : List (Hash32 × ByteArray)

private def insertFirst (es : List (Hash32 × ByteArray)) (h : Hash32) (raw : ByteArray) :
    List (Hash32 × ByteArray) :=
  if es.any (fun e => decide (e.1 = h)) then es else es ++ [(h, raw)]

private theorem insertFirst_present (es : List (Hash32 × ByteArray)) (h : Hash32)
    (raw : ByteArray) (present : es.any (fun e => decide (e.1 = h)) = true) :
    insertFirst es h raw = es := by
  simp only [insertFirst, present, ↓reduceIte]

private theorem insertFirst_absent (es : List (Hash32 × ByteArray)) (h : Hash32)
    (raw : ByteArray) (absent : es.any (fun e => decide (e.1 = h)) = false) :
    insertFirst es h raw = es ++ [(h, raw)] := by
  simp only [insertFirst, absent, Bool.false_eq_true, ↓reduceIte]

private def witnessResolvedThen {m : Type → Type} [Monad m] [KeccakQuery m]
    (n : Node) (enc : Enc) (es : List (Hash32 × ByteArray))
    (k : Witnessed → m (Except TrieError Ref)) : m (Except TrieError Ref) :=
  match enc.hash? with
  | some h => k ⟨n, enc.rlp, some h, insertFirst es h enc.rlp⟩
  | none =>
    if 32 ≤ enc.rlp.size then
      KeccakQuery.keccak enc.rlp >>= fun answer =>
        k ⟨n, enc.rlp, some answer, insertFirst es answer enc.rlp⟩
    else
      let raw := Rlp.encode (currentRootItem n)
      if raw.size < 32 then k ⟨replaceTopEnc n ⟨raw, none⟩, raw, none, es⟩
      else KeccakQuery.keccak raw >>= fun answer =>
        k ⟨replaceTopEnc n ⟨raw, some answer⟩, raw, some answer, insertFirst es answer raw⟩

private def witnessThen {m : Type → Type} [Monad m] [KeccakQuery m]
    (n : Node) (es : List (Hash32 × ByteArray))
    (k : Witnessed → m (Except TrieError Ref)) : m (Except TrieError Ref) :=
  match n with
  | .hashed h => pure (.error (.unresolved h))
  | .leaf _ _ enc | .ext _ _ enc | .branch _ _ enc => witnessResolvedThen n enc es k

private theorem wire_model (x : RlpItem) : Rlp.encode x = (Rlp.encodeModel x).toByteArray := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simpa only [List.toList_data_toByteArray] using Rlp.toList_encode x

private def witnessResolvedReferenceThen {m : Type → Type} [Monad m] [KeccakQuery m]
    (n : Node) (enc : Enc) (es : List (Hash32 × ByteArray))
    (k : Witnessed → m (Except TrieError Ref)) : m (Except TrieError Ref) :=
  match enc.hash? with
  | some h => k ⟨n, enc.rlp, some h, insertFirst es h enc.rlp⟩
  | none =>
    if 32 ≤ enc.rlp.size then
      KeccakQuery.keccak enc.rlp >>= fun answer =>
        k ⟨n, enc.rlp, some answer, insertFirst es answer enc.rlp⟩
    else
      let raw := (Rlp.encodeModel (currentRootItemReference n)).toByteArray
      if raw.size < 32 then k ⟨replaceTopEnc n ⟨raw, none⟩, raw, none, es⟩
      else KeccakQuery.keccak raw >>= fun answer =>
        k ⟨replaceTopEnc n ⟨raw, some answer⟩, raw, some answer, insertFirst es answer raw⟩

private theorem witnessResolvedThen_eq {m : Type → Type} [Monad m] [KeccakQuery m]
    (n : Node) (enc : Enc) (es : List (Hash32 × ByteArray))
    (k : Witnessed → m (Except TrieError Ref)) :
    witnessResolvedThen n enc es k = witnessResolvedReferenceThen n enc es k := by
  simp only [witnessResolvedThen, witnessResolvedReferenceThen, wire_model, currentRootItem_eq]

private def witnessReferenceThen {m : Type → Type} [Monad m] [KeccakQuery m]
    (n : Node) (es : List (Hash32 × ByteArray))
    (k : Witnessed → m (Except TrieError Ref)) : m (Except TrieError Ref) :=
  match n with
  | .hashed h => pure (.error (.unresolved h))
  | .leaf _ _ enc | .ext _ _ enc | .branch _ _ enc => witnessResolvedReferenceThen n enc es k

private theorem witnessThen_eq {m : Type → Type} [Monad m] [KeccakQuery m]
    (n : Node) (es : List (Hash32 × ByteArray))
    (k : Witnessed → m (Except TrieError Ref)) :
    witnessThen n es k = witnessReferenceThen n es k := by
  cases n <;> simp only [witnessThen, witnessReferenceThen, witnessResolvedThen_eq]

private def freshBranch {m : Type → Type} [Monad m] [KeccakQuery m]
    (xs : Array Ref) (v : ByteArray) : m Node :=
  let raw := Rlp.encode (branchItem xs v)
  if raw.size < 32 then pure (.branch xs v ⟨raw, none⟩)
  else KeccakQuery.keccak raw >>= fun answer => pure (.branch xs v ⟨raw, some answer⟩)

private def freshBranchReference {m : Type → Type} [Monad m] [KeccakQuery m]
    (xs : List Ref) (v : ByteArray) : m Node :=
  let raw := (Rlp.encodeModel (branchItemReference xs v)).toByteArray
  if raw.size < 32 then pure (.branch xs.toArray v ⟨raw, none⟩)
  else KeccakQuery.keccak raw >>= fun answer => pure (.branch xs.toArray v ⟨raw, some answer⟩)

private theorem freshBranch_eq {m : Type → Type} [Monad m] [KeccakQuery m]
    (xs : Array Ref) (v : ByteArray) :
    freshBranch (m := m) xs v = freshBranchReference xs.toList v := by
  simp only [freshBranch, freshBranchReference, wire_model, branchItem_eq, Array.toArray_toList]

private def singletonNibble (i : Nat) (hi : i < 16) : Nibbles :=
  Nibbles.generate 1 (fun _ => ⟨i, hi⟩)

private theorem singletonNibble_toList (i : Nat) (hi : i < 16) :
    (singletonNibble i hi).toList = [⟨i, hi⟩] := by
  simp [singletonNibble, Nibbles.toList_generate]

private def collapseContinuation {m : Type → Type} [Monad m] [KeccakQuery m]
    (index : Nat) (w : Witnessed) : m (Except TrieError Ref) :=
  if hi : index < 16 then
    mkExt (singletonNibble index hi) w.survivor >>= fun n => pure (.ok (some n))
  else pure (.error (.malformed (.collapseIndex index)))

private def controller {m : Type → Type} [Monad m] [KeccakQuery m]
    (xs : Array Ref) (v : ByteArray) (c : Census Node) : m (Except TrieError Ref) :=
  match c with
  | .zero =>
    if v.size = 0 then pure (.error (.malformed (.occupancy 0)))
    else mkLeaf (Nibbles.ofList []) v >>= fun n => pure (.ok (some n))
  | .sole i n =>
    if v.size = 0 then witnessThen n [] (collapseContinuation i)
    else freshBranch xs v >>= fun n => pure (.ok (some n))
  | .multiple => freshBranch xs v >>= fun n => pure (.ok (some n))

/-- Complete a reached branch on every finite bare input.
Pinned EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:787–828`.
Sole empty-terminal collapse witnesses first, then diagnoses a nonnibble actual
index. Zero-child/nonempty-terminal input makes a completed empty-path leaf;
retained branch cases preserve every actual slot/value and strictly complete own raw.
No arity/WF/dirty test or caller-side source witness contract is introduced. -/
def mkBranch {m : Type → Type} [Monad m] [KeccakQuery m]
    (children : Array Ref) (value : ByteArray) : m (Except TrieError Ref) :=
  controller children value (scan children)

private def controllerReference {m : Type → Type} [Monad m] [KeccakQuery m]
    (xs : Array Ref) (v : ByteArray) (c : Census Node) : m (Except TrieError Ref) :=
  match c with
  | .zero =>
    if v.size = 0 then pure (.error (.malformed (.occupancy 0)))
    else mkLeaf (Nibbles.ofList []) v >>= fun n => pure (.ok (some n))
  | .sole i n =>
    if v.size = 0 then witnessReferenceThen n [] (collapseContinuation i)
    else freshBranchReference xs.toList v >>= fun n => pure (.ok (some n))
  | .multiple => freshBranchReference xs.toList v >>= fun n => pure (.ok (some n))

private theorem controller_eq {m : Type → Type} [Monad m] [KeccakQuery m]
    (xs : Array Ref) (v : ByteArray) (c : Census Node) :
    controller (m := m) xs v c = controllerReference xs v c := by
  cases c <;> simp only [controller, controllerReference, witnessThen_eq, freshBranch_eq]

private def mkBranchReference {m : Type → Type} [Monad m] [KeccakQuery m]
    (xs : Array Ref) (v : ByteArray) : m (Except TrieError Ref) :=
  controllerReference xs v (censusReference xs)

/-- Complete literal actions for all finite inputs, without monad laws or WF. -/
private theorem mkBranch_eq_reference {m : Type → Type} [Monad m] [KeccakQuery m]
    (xs : Array Ref) (v : ByteArray) : mkBranch (m := m) xs v = mkBranchReference xs v := by
  rw [mkBranch, mkBranchReference, scan_eq_reference, controller_eq]

end STFSpec.Commit
