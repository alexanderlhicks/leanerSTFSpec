/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit.Nibbles
import STFSpec.Codec.RlpEncode
import STFSpec.Hash.KeccakQuery

/-!
# Mathematical internal-node assembly and encoding

Library `EthCommit`. Children are already encoded byte/list references, so the node
is nonrecursive. One assembled item and one packed RLP encoding determine inline
versus one oracle query. The unconditional model inherits RLP's total completion
(Q47); standard/pinned correspondence requires the complete assembly's `Encodable`
premise and caller-owned interpretation of Python Extended fields. No witness
cache, root construction or global oracle coupling is supplied here.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§2.2/3/5/7.
-/

namespace STFSpec.Commit

open STFSpec.Base STFSpec.Codec STFSpec.Hash

/-- The three nonrecursive construction-node variants; fields are encoded references.
Pinned EELS `src/ethereum/merkle_patricia_trie.py:88–183`. -/
inductive InternalNode where
  | leaf (restOfKey : Nibbles) (value : RlpItem)
  | extension (keySegment : Nibbles) (subnode : RlpItem)
  | branch (subnodes : Vector RlpItem 16) (value : RlpItem)

/-- The unencoded complete structure, preserving all child items and their order.
Pinned EELS `src/ethereum/merkle_patricia_trie.py:228–241`. -/
def assembleInternalNode : Option InternalNode → RlpItem
  | none => .bytes ByteArray.empty
  | some (.leaf path value) => .list [.bytes (nibbleListToCompact path true), value]
  | some (.extension path subnode) =>
      .list [.bytes (nibbleListToCompact path false), subnode]
  | some (.branch subnodes value) => .list (subnodes.toList ++ [value])

/-- Legible byte-list assembly model; HP uses the public nibble model. -/
def assembleInternalNodeModel : Option InternalNode → RlpItem
  | none => .bytes ByteArray.empty
  | some (.leaf path value) =>
      .list [.bytes (nibbleListToCompactModel path.toList true).toByteArray, value]
  | some (.extension path subnode) =>
      .list [.bytes (nibbleListToCompactModel path.toList false).toByteArray, subnode]
  | some (.branch subnodes value) => .list (subnodes.toList ++ [value])

/-- Ordinary equality of packed assembly and its model, for every node. -/
theorem assembleInternalNode_eq_model (node : Option InternalNode) :
    assembleInternalNode node = assembleInternalNodeModel node := by
  have compact (p : Nibbles) (leaf : Bool) : nibbleListToCompact p leaf =
      (nibbleListToCompactModel p.toList leaf).toByteArray := by
    apply ByteArray.ext
    apply Array.toList_inj.mp
    simpa only [List.toList_data_toByteArray] using nibbleListToCompact_eq_model p leaf
  cases node with
  | none => rfl
  | some node => cases node <;> simp only [assembleInternalNode, assembleInternalNodeModel,
      compact]

/-- Absence assembles the empty byte string, rather than a root digest. -/
theorem assembleInternalNode_none : assembleInternalNode none = .bytes ByteArray.empty := rfl

/-- A leaf's arbitrary value is retained after the leaf HP bytes. -/
theorem assembleInternalNode_leaf (p : Nibbles) (v : RlpItem) :
    assembleInternalNode (some (.leaf p v)) =
      .list [.bytes (nibbleListToCompact p true), v] := rfl

/-- An extension's arbitrary child is retained after the extension HP bytes. -/
theorem assembleInternalNode_extension (p : Nibbles) (child : RlpItem) :
    assembleInternalNode (some (.extension p child)) =
      .list [.bytes (nibbleListToCompact p false), child] := rfl

/-- A branch contains its sixteen children in nibble order and its value last. -/
theorem assembleInternalNode_branch (children : Vector RlpItem 16) (v : RlpItem) :
    assembleInternalNode (some (.branch children v)) = .list (children.toList ++ [v]) := rfl

/-- Every branch child position observes the originally supplied child. -/
theorem branch_items_get (children : Vector RlpItem 16) (v : RlpItem) (i : Fin 16) :
    (children.toList ++ [v])[i.val]'(by simp; omega) = children[i] := by
  simp

/-- Position sixteen observes the branch value, including nested list values. -/
theorem branch_items_value (children : Vector RlpItem 16) (v : RlpItem) :
    (children.toList ++ [v])[16]'(by simp) = v := by simp

/-- The branch's complete arity is seventeen. -/
theorem branch_items_length (children : Vector RlpItem 16) (v : RlpItem) :
    (children.toList ++ [v]).length = 17 := by simp

/-- Complete total byte-list preimage model, including HP and every nested child. -/
def internalNodeWireModel (node : Option InternalNode) : List UInt8 :=
  Rlp.encodeModel (assembleInternalNodeModel node)

/-- Packed preimage observation equals the total list model unconditionally. -/
theorem toList_encode_assembleInternalNode (node : Option InternalNode) :
    (Rlp.encode (assembleInternalNode node)).data.toList = internalNodeWireModel node := by
  rw [Rlp.toList_encode, assembleInternalNode_eq_model]; rfl

/-- The threshold uses the full model encoding length, including the outer header. -/
theorem size_encode_assembleInternalNode (node : Option InternalNode) :
    (Rlp.encode (assembleInternalNode node)).size = (internalNodeWireModel node).length := by
  rw [Rlp.size_encode, Rlp.encodedSize_eq_model_length, assembleInternalNode_eq_model]; rfl

/-- Inline the complete assembled structure iff its complete RLP is shorter than 32;
otherwise forward the full oracle answer as a byte item, without hashing children.
Pinned EELS `src/ethereum/merkle_patricia_trie.py:213–249`. -/
def encodeInternalNode {m : Type → Type} [Monad m] [KeccakQuery m]
    (node : Option InternalNode) : m RlpItem := do
  let unencoded := assembleInternalNode node
  let encoded := Rlp.encode unencoded
  if encoded.size < 32 then pure unencoded
  else
    let answer ← KeccakQuery.keccak encoded
    pure (.bytes answer.toBytes.toByteArray)

/-- Public zero-or-one query equation, with the exact full preimage and all answer bytes. -/
theorem encodeInternalNode_eq {m : Type → Type} [Monad m] [KeccakQuery m]
    (node : Option InternalNode) :
    encodeInternalNode (m := m) node =
      (if (Rlp.encode (assembleInternalNode node)).size < 32 then
        pure (assembleInternalNode node)
      else do
        let answer ← KeccakQuery.keccak (Rlp.encode (assembleInternalNode node))
        pure (.bytes answer.toBytes.toByteArray) : m RlpItem) := rfl

/-- Legible operational model: one model preimage, then the same threshold and query. -/
def encodeInternalNodeModel {m : Type → Type} [Monad m] [KeccakQuery m]
    (node : Option InternalNode) : m RlpItem := do
  if (internalNodeWireModel node).length < 32 then
    pure (assembleInternalNodeModel node)
  else
    let answer ← KeccakQuery.keccak (internalNodeWireModel node).toByteArray
    pure (.bytes answer.toBytes.toByteArray)

/-- Ordinary all-input equality to the total operational model, without `Encodable`. -/
theorem encodeInternalNode_eq_model {m : Type → Type} [Monad m] [KeccakQuery m]
    (node : Option InternalNode) :
    encodeInternalNode (m := m) node = encodeInternalNodeModel node := by
  have wire :
      Rlp.encode (assembleInternalNode node) = (internalNodeWireModel node).toByteArray := by
    apply ByteArray.ext
    apply Array.toList_inj.mp
    simpa only [List.toList_data_toByteArray] using toList_encode_assembleInternalNode node
  rw [encodeInternalNode_eq, size_encode_assembleInternalNode, wire,
    assembleInternalNode_eq_model]
  rfl

/-- A short complete encoding returns its structure and performs no query. -/
theorem encodeInternalNode_inline {m : Type → Type} [Monad m] [KeccakQuery m]
    (node : Option InternalNode) (h : (Rlp.encode (assembleInternalNode node)).size < 32) :
    encodeInternalNode (m := m) node = pure (assembleInternalNode node) := by
  rw [encodeInternalNode_eq, ite_eq_left h]

/-- At or above the threshold there is exactly one query on the complete encoding. -/
theorem encodeInternalNode_hash {m : Type → Type} [Monad m] [KeccakQuery m]
    (node : Option InternalNode) (h : 32 ≤ (Rlp.encode (assembleInternalNode node)).size) :
    encodeInternalNode (m := m) node = (do
      let answer ← KeccakQuery.keccak (Rlp.encode (assembleInternalNode node))
      pure (.bytes answer.toBytes.toByteArray) : m RlpItem) := by
  rw [encodeInternalNode_eq, ite_eq_right (by omega)]

/-- Absence is always inline and bypasses even a failing oracle. -/
theorem encodeInternalNode_none {m : Type → Type} [Monad m] [KeccakQuery m] :
    encodeInternalNode (m := m) none = pure (.bytes ByteArray.empty) := by
  apply encodeInternalNode_inline
  decide

/-- Arbitrary pure answers, including leading zero bytes, are forwarded in full. -/
theorem encodeInternalNode_of_pure_answer {m : Type → Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m] (node : Option InternalNode) (answer : Hash32)
    (h : 32 ≤ (Rlp.encode (assembleInternalNode node)).size)
    (hq : KeccakQuery.keccak (m := m) (Rlp.encode (assembleInternalNode node)) = pure answer) :
    encodeInternalNode (m := m) node = pure (.bytes answer.toBytes.toByteArray) := by
  rw [encodeInternalNode_hash node h, hq, pure_bind]

/-- A recording interpretation observes zero or one exact full preimage and forwards
all thirty-two answer bytes. This local equation is not a global oracle coupling. -/
theorem encodeInternalNode_recording (node : Option InternalNode) (answer : Hash32)
    (seen : List ByteArray) :
    letI : KeccakQuery (StateM (List ByteArray)) :=
      ⟨fun bytes trace ↦ (answer, trace ++ [bytes])⟩
    (encodeInternalNode (m := StateM (List ByteArray)) node).run seen =
      if (Rlp.encode (assembleInternalNode node)).size < 32 then
        (assembleInternalNode node, seen)
      else (.bytes answer.toBytes.toByteArray,
        seen ++ [Rlp.encode (assembleInternalNode node)]) := by
  by_cases h : (Rlp.encode (assembleInternalNode node)).size < 32
  · simp only [encodeInternalNode, h, ↓reduceIte]; rfl
  · simp only [encodeInternalNode, h, ↓reduceIte]; rfl

/-- Identity specialization dispatches through the concrete Id query instance. -/
theorem encodeInternalNode_id (node : Option InternalNode) :
    encodeInternalNode (m := Id) node =
      if (Rlp.encode (assembleInternalNode node)).size < 32 then assembleInternalNode node
      else .bytes (keccak256 (Rlp.encode (assembleInternalNode node))).toBytes.toByteArray := rfl

/-- An exception lift preserves the underlying computation and wraps only its result. -/
theorem run_encodeInternalNode_exceptT {m : Type → Type} {ε : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m] (node : Option InternalNode) :
    (encodeInternalNode (m := ExceptT ε m) node).run =
      (do let result ← encodeInternalNode (m := m) node
          pure (.ok result : Except ε RlpItem)) := by
  simp only [encodeInternalNode_eq]
  split <;> simp [KeccakQuery.keccak_exceptT, ExceptT.run_lift, Except.map]

/-- A state lift retains all underlying effects and leaves the added state unchanged. -/
theorem run_encodeInternalNode_stateT {m : Type → Type} {σ : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m] (node : Option InternalNode) (s : σ) :
    (encodeInternalNode (m := StateT σ m) node).run s =
      (do let result ← encodeInternalNode (m := m) node; pure (result, s)) := by
  simp only [encodeInternalNode_eq]
  split <;> simp [KeccakQuery.keccak_stateT]

/-- A failing oracle retains its original error; no local error or handler is added. -/
theorem run_encodeInternalNode_error {m : Type → Type} {ε : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery (ExceptT ε m)]
    (node : Option InternalNode) (error : ε)
    (h : 32 ≤ (Rlp.encode (assembleInternalNode node)).size)
    (hq : KeccakQuery.keccak (m := ExceptT ε m) (Rlp.encode (assembleInternalNode node)) =
      ExceptT.mk (pure (.error error))) :
    (encodeInternalNode (m := ExceptT ε m) node).run = pure (.error error) := by
  rw [encodeInternalNode_hash node h, hq]
  simp only [ExceptT.run_bind, ExceptT.run_mk, pure_bind]

/-- Absence's complete assembly is in the standard RLP domain. -/
theorem encodable_assembleInternalNode_none : Rlp.Encodable (assembleInternalNode none) := by
  rw [assembleInternalNode_none, Rlp.encodable_bytes_iff]; decide

/-- A two-field node's standard-domain premise includes HP width, the arbitrary field,
and the full joined encoded payload. It is not merely a premise on the field. -/
theorem encodable_assembleInternalNode_leaf_iff (p : Nibbles) (v : RlpItem) :
    Rlp.Encodable (assembleInternalNode (some (.leaf p v))) ↔
      p.size / 2 + 1 < 2 ^ 64 ∧ Rlp.Encodable v ∧
      (Rlp.encodePayloadModel [.bytes (nibbleListToCompact p true), v]).length < 2 ^ 64 := by
  simp [assembleInternalNode_leaf, Rlp.encodable_list_iff, Rlp.encodable_bytes_iff,
    size_nibbleListToCompact, and_assoc]

/-- An extension's standard-domain premise likewise retains HP and full joined payload. -/
theorem encodable_assembleInternalNode_extension_iff (p : Nibbles) (v : RlpItem) :
    Rlp.Encodable (assembleInternalNode (some (.extension p v))) ↔
      p.size / 2 + 1 < 2 ^ 64 ∧ Rlp.Encodable v ∧
      (Rlp.encodePayloadModel [.bytes (nibbleListToCompact p false), v]).length < 2 ^ 64 := by
  simp [assembleInternalNode_extension, Rlp.encodable_list_iff, Rlp.encodable_bytes_iff,
    size_nibbleListToCompact, and_assoc]

/-- A branch's standard-domain premise includes all seventeen items and their complete
joined encoded payload; it supplies no caller bound automatically. -/
theorem encodable_assembleInternalNode_branch_iff (children : Vector RlpItem 16) (v : RlpItem) :
    Rlp.Encodable (assembleInternalNode (some (.branch children v))) ↔
      (∀ x ∈ children.toList ++ [v], Rlp.Encodable x) ∧
      (Rlp.encodePayloadModel (children.toList ++ [v])).length < 2 ^ 64 := by
  rw [assembleInternalNode_branch, Rlp.encodable_list_iff]

end STFSpec.Commit
