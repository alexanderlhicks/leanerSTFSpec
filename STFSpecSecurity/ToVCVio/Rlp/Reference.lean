/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import ToVCVio.Rlp.Codec
import ToVCVio.Oracle.QueryMorphism
import STFSpec.Base.FixedBytes

/-!
# Canonical RLP child references

One complete node encoding selects an inline list or one full-preimage query.
This is local reference support, not canonical Patricia grammar or map binding.
Library `ToVCVio` in `STFSpecSecurity`.
Spec guidance: `STFSpec/informal/modules/ToVCVio.md` §§3/5/7.
-/

namespace ToVCVio.Rlp
open STFSpec.Base STFSpec.Codec ToVCVio.Oracle

/-- Absence, a valid inline list, or all thirty-two digest bytes. -/
inductive ChildRef where
  | empty
  | inline (node : RlpListNode)
  | hashed (digest : Hash32)

/-- The actual RLP item occupying a child position. -/
def wireItem : ChildRef → RlpItem
  | .empty => .bytes ByteArray.empty
  | .inline node => node.val.val
  | .hashed digest => .bytes digest.toBytes.toByteArray

/-- Every wire is in the recursive standard RLP domain. -/
theorem wireItem_encodable (ref : ChildRef) : STFSpec.Codec.Rlp.Encodable (wireItem ref) := by
  cases ref with
  | empty => rw [wireItem, STFSpec.Codec.Rlp.encodable_bytes_iff]; decide
  | inline node => exact node.val.property
  | hashed digest =>
    rw [wireItem, STFSpec.Codec.Rlp.encodable_bytes_iff, Bytes.size_toByteArray,
      Hash32.size_toBytes]
    decide

/-- The typed reference retains its shape, complete list item and all digest bytes. -/
theorem wireItem_inj (x y : ChildRef) : wireItem x = wireItem y ↔ x = y := by
  constructor
  · intro he
    cases x <;> cases y <;> simp only [wireItem] at he
    · rfl
    · rename_i node
      exact False.elim (node.ne_bytes _ he.symm)
    · rename_i digest
      have hs := congrArg ByteArray.size (RlpItem.bytes.inj he)
      simp only [ByteArray.size_empty, Bytes.size_toByteArray, Hash32.size_toBytes] at hs
      contradiction
    · rename_i node
      exact False.elim (node.ne_bytes _ he)
    · rename_i a b
      exact congrArg ChildRef.inline (RlpListNode.eq_of_item_eq he)
    · rename_i node digest
      exact False.elim (node.ne_bytes _ he)
    · rename_i digest
      have hs := congrArg ByteArray.size (RlpItem.bytes.inj he)
      simp only [Bytes.size_toByteArray, Hash32.size_toBytes, ByteArray.size_empty] at hs
      contradiction
    · rename_i digest node
      exact False.elim (node.ne_bytes _ he.symm)
    · rename_i a b
      have hb := congrArg Bytes.ofByteArray (RlpItem.bytes.inj he)
      simp only [Bytes.ofByteArray_toByteArray] at hb
      exact congrArg ChildRef.hashed (Hash32.toBytes_inj.mp hb)
  · exact congrArg wireItem

/-- Canonical complete reference wires also determine their typed references. -/
theorem wire_encode_inj (x y : ChildRef) :
    STFSpec.Codec.Rlp.encode (wireItem x) = STFSpec.Codec.Rlp.encode (wireItem y) ↔ x = y := by
  rw [STFSpec.Codec.Rlp.encode_inj _ _ (wireItem_encodable x) (wireItem_encodable y),
    wireItem_inj]

/-- Only inline references additionally require the complete encoded width below 32 bytes. -/
def AdmissibleRef : ChildRef → Prop
  | .empty => True
  | .inline node => node.encode.size < 32
  | .hashed _ => True

/-- The local width rule is decidable by the public complete encoding size. -/
instance (ref : ChildRef) : Decidable (AdmissibleRef ref) := by
  cases ref <;> unfold AdmissibleRef <;> infer_instance

/-- Compute the full packed encoding once, then preserve the supplied query action. -/
def childRefM {m : Type → Type} [Monad m]
    (q : ByteArray → m Hash32) (node : RlpListNode) : m ChildRef :=
  let encoded := node.encode
  if encoded.size < 32 then pure (.inline node)
  else q encoded >>= fun digest => pure (.hashed digest)

/-- Literal zero-or-one query expansion on the complete preimage. -/
theorem childRefM_eq {m : Type → Type} [Monad m]
    (q : ByteArray → m Hash32) (node : RlpListNode) :
    childRefM q node = (if node.encode.size < 32 then pure (.inline node)
      else q node.encode >>= fun digest => pure (.hashed digest) : m ChildRef) := rfl

/-- Short complete wires bypass the callback, including failing callbacks. -/
theorem childRefM_inline {m : Type → Type} [Monad m]
    (q : ByteArray → m Hash32) (node : RlpListNode) (hs : node.encode.size < 32) :
    childRefM q node = pure (.inline node) := by rw [childRefM_eq, ite_eq_left hs]

/-- At and above 32 bytes there is one query, without truncating its answer. -/
theorem childRefM_hash {m : Type → Type} [Monad m]
    (q : ByteArray → m Hash32) (node : RlpListNode) (hs : 32 ≤ node.encode.size) :
    childRefM q node = (q node.encode >>= fun digest => pure (.hashed digest) : m ChildRef) := by
  rw [childRefM_eq, ite_eq_right (by omega)]

/-- An empty child is a pure absent reference, independent of any query capability. -/
def emptyRefM {m : Type → Type} [Monad m] : m ChildRef := pure .empty

/-- Arbitrary pure answers are forwarded under the ordinary monad law. -/
theorem childRefM_of_pure_answer {m : Type → Type} [Monad m] [LawfulMonad m]
    (q : ByteArray → m Hash32) (node : RlpListNode) (answer : Hash32)
    (hs : 32 ≤ node.encode.size) (hq : q node.encode = pure answer) :
    childRefM q node = pure (.hashed answer) := by
  rw [childRefM_hash q node hs, hq, pure_bind]

/-- Every returned reference satisfies the local width rule, retaining all effects. -/
theorem childRefM_admissible {m : Type → Type} [Monad m] [LawfulMonad m]
    (q : ByteArray → m Hash32) (node : RlpListNode) :
    (do let ref ← childRefM q node; pure (decide (AdmissibleRef ref))) =
      (do let _ ← childRefM q node; pure true : m Bool) := by
  by_cases hs : node.encode.size < 32
  · simp [childRefM, hs, AdmissibleRef]
  · simp [childRefM, hs, AdmissibleRef]
    apply map_congr
    intro digest
    rfl

/-- This particular threshold kernel commutes with an explicit query-preserving map. -/
theorem childRefM_natural {m n : Type → Type} [Monad m] [Monad n]
    (qm : ByteArray → m Hash32) (qn : ByteArray → n Hash32)
    (F : QueryMorphism ByteArray Hash32 m n qm qn) (node : RlpListNode) :
    F.map (childRefM qm node) = childRefM qn node := by
  rw [childRefM_eq, childRefM_eq]
  split
  · exact F.map_pure _
  · rw [F.map_bind, F.map_query]
    congr 1
    funext digest
    exact F.map_pure _

/-- Record zero or one full preimage while returning every answer byte. -/
theorem childRefM_recording (node : RlpListNode) (answer : Hash32) (seen : List ByteArray) :
    (childRefM (m := StateM (List ByteArray))
      (fun bytes trace => (answer, trace ++ [bytes])) node).run seen =
    if node.encode.size < 32 then (.inline node, seen)
    else (.hashed answer, seen ++ [node.encode]) := by
  by_cases hs : node.encode.size < 32 <;> simp only [childRefM, hs, ↓reduceIte] <;> rfl

/-- Exception lifting uses the same callback, adding only the success wrapper. -/
theorem run_childRefM_exceptT {m : Type → Type} {ε : Type} [Monad m] [LawfulMonad m]
    (q : ByteArray → m Hash32) (node : RlpListNode) :
    (childRefM (m := ExceptT ε m) (fun bytes => ExceptT.lift (q bytes)) node).run =
      (do let ref ← childRefM q node; pure (.ok ref : Except ε ChildRef)) := by
  by_cases hs : node.encode.size < 32 <;>
    simp [childRefM, hs, ExceptT.run_lift, Except.map]

/-- State lifting uses the same callback and leaves the added state unchanged. -/
theorem run_childRefM_stateT {m : Type → Type} {σ : Type} [Monad m] [LawfulMonad m]
    (q : ByteArray → m Hash32) (node : RlpListNode) (state : σ) :
    (childRefM (m := StateT σ m) (fun bytes => StateT.lift (q bytes)) node).run state =
      (do let ref ← childRefM q node; pure (ref, state)) := by
  by_cases hs : node.encode.size < 32 <;> simp [childRefM, hs]

/-- A specified error action is propagated without a local error or handler. -/
theorem run_childRefM_error {m : Type → Type} {ε : Type} [Monad m] [LawfulMonad m]
    (q : ByteArray → ExceptT ε m Hash32) (node : RlpListNode) (error : ε)
    (hs : 32 ≤ node.encode.size) (hq : q node.encode = ExceptT.mk (pure (.error error))) :
    (childRefM q node).run = pure (.error error) := by
  rw [childRefM_hash q node hs, hq]
  simp only [ExceptT.run_bind, ExceptT.run_mk, pure_bind]

/-- Deterministic evaluation under this chosen answer function, not an implicit Id oracle. -/
def refWithHash (h : ByteArray → Hash32) (node : RlpListNode) : ChildRef :=
  childRefM (m := Id) h node

/-- Exact Id expansion with the same h at every occurrence. -/
theorem refWithHash_eq (h : ByteArray → Hash32) (node : RlpListNode) :
    refWithHash h node = if node.encode.size < 32 then .inline node else .hashed (h node.encode) := rfl

/-- The deterministic reference is admissible on every valid list. -/
theorem refWithHash_admissible (h : ByteArray → Hash32) (node : RlpListNode) :
    AdmissibleRef (refWithHash h node) := by
  rw [refWithHash_eq]
  split <;> simp_all [AdmissibleRef]

/-- Equal references under one h imply equal nodes or a collision in complete raw wires. -/
theorem equal_or_collision (h : ByteArray → Hash32) (x y : RlpListNode)
    (he : refWithHash h x = refWithHash h y) :
    x = y ∨ (x.encode ≠ y.encode ∧ h x.encode = h y.encode) := by
  rw [refWithHash_eq, refWithHash_eq] at he
  split at he <;> split at he
  · exact Or.inl (ChildRef.inline.inj he)
  · contradiction
  · contradiction
  · have hh := ChildRef.hashed.inj he
    by_cases hw : x.encode = y.encode
    · exact Or.inl ((RlpListNode.encode_inj _ _).mp hw)
    · exact Or.inr ⟨hw, hh⟩

/-- Compare each full preimage once; return the raw pair when distinct.
Soundness requires equal references under the same h; no verification query is added. -/
def extractCollision (x y : RlpListNode) : Option (ByteArray × ByteArray) :=
  let a := x.encode
  let b := y.encode
  if a = b then none else some (a, b)

/-- An equal preimage yields none, exactly when the valid nodes are equal. -/
theorem extractCollision_none_iff (x y : RlpListNode) :
    extractCollision x y = none ↔ x = y := by
  unfold extractCollision
  dsimp only
  split <;> simp_all [RlpListNode.encode_inj]

/-- Distinct valid nodes produce the complete raw preimage pair. -/
theorem extractCollision_of_ne (x y : RlpListNode) (hne : x ≠ y) :
    extractCollision x y = some (x.encode, y.encode) := by
  unfold extractCollision
  rw [ite_eq_right (fun he => hne ((RlpListNode.encode_inj _ _).mp he))]

/-- Conditional local extractor soundness; both wires belong to the compared pair. -/
theorem extractCollision_sound (h : ByteArray → Hash32) (x y : RlpListNode)
    (he : refWithHash h x = refWithHash h y) (a b : ByteArray)
    (hf : extractCollision x y = some (a, b)) :
    a = x.encode ∧ b = y.encode ∧ a ≠ b ∧ h a = h b := by
  unfold extractCollision at hf
  dsimp only at hf
  split at hf
  · contradiction
  · have hp := Option.some.inj hf
    obtain ⟨ha, hb⟩ := Prod.mk.inj hp
    subst a; subst b
    rcases equal_or_collision h x y he with hxy | hc
    · subst y; contradiction
    · exact ⟨rfl, rfl, hc⟩

end ToVCVio.Rlp
