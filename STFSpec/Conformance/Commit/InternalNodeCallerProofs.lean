/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit

/-!
# Internal-node public-contract clients

Library `EthConformance`. These symbolic clients use public provider laws, without
unfolding packed paths, RLP writers or hash representations.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/7/8.
-/

namespace STFSpec.Conformance.Commit.InternalNodeCallerProofs

open STFSpec.Base STFSpec.Codec STFSpec.Hash STFSpec.Commit

/-- A client can select the short branch directly from the complete model width. -/
theorem inline_of_model_width {m : Type → Type} [Monad m] [KeccakQuery m]
    (node : Option InternalNode) (h : (internalNodeWireModel node).length < 32) :
    encodeInternalNode (m := m) node = pure (assembleInternalNodeModel node) := by
  rw [← assembleInternalNode_eq_model]
  apply encodeInternalNode_inline
  rwa [size_encode_assembleInternalNode]

/-- A client's arbitrary hash answer is preserved as the entire public byte observation. -/
theorem answer_preserved {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (node : Option InternalNode) (answer : Hash32)
    (h : 32 ≤ (internalNodeWireModel node).length)
    (hq : KeccakQuery.keccak (m := m) (Rlp.encode (assembleInternalNode node)) = pure answer) :
    encodeInternalNode (m := m) node = pure (.bytes answer.toBytes.toByteArray) := by
  apply encodeInternalNode_of_pure_answer node answer _ hq
  rwa [size_encode_assembleInternalNode]

/-- Standard-domain branch composition keeps each item and the joined payload premise. -/
theorem branch_domain (children : Vector RlpItem 16) (value : RlpItem)
    (hitems : ∀ x ∈ children.toList ++ [value], Rlp.Encodable x)
    (hpayload : ((children.toList ++ [value]).map Rlp.encodedSize).sum < 2 ^ 64) :
    Rlp.Encodable (assembleInternalNode (some (.branch children value))) := by
  rw [encodable_assembleInternalNode_branch_iff, Rlp.length_encodePayloadModel]
  exact ⟨hitems, hpayload⟩

/-- A leaf caller supplies HP byte width and complete payload, including both headers. -/
theorem leaf_domain (path : Nibbles) (value : RlpItem)
    (hhp : path.size / 2 + 1 < 2 ^ 64) (hv : Rlp.Encodable value)
    (hpayload : (Rlp.encodePayloadModel
      [.bytes (nibbleListToCompact path true), value]).length < 2 ^ 64) :
    Rlp.Encodable (assembleInternalNode (some (.leaf path value))) := by
  exact (encodable_assembleInternalNode_leaf_iff path value).mpr ⟨hhp, hv, hpayload⟩

/-- A branch client obtains every ordered child and the separate value by public laws. -/
theorem ordered_branch (children : Vector RlpItem 16) (value : RlpItem) (i : Fin 16) :
    (children.toList ++ [value])[i.val]'(by simp; omega) = children[i] ∧
      (children.toList ++ [value])[16]'(by simp) = value :=
  ⟨branch_items_get children value i, branch_items_value children value⟩

/-- Transformer composition preserves underlying effects and the added state. -/
theorem lifted_context {m : Type → Type} {ε σ : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m] (node : Option InternalNode) (s : σ) :
    ((encodeInternalNode (m := ExceptT ε (StateT σ m)) node).run).run s =
      (do let result ← encodeInternalNode (m := m) node
          pure ((.ok result : Except ε RlpItem), s)) := by
  rw [run_encodeInternalNode_exceptT]
  simp [run_encodeInternalNode_stateT]

/-- At Id the production kernel uses the concrete query instance. -/
theorem concrete_result (node : Option InternalNode) :
    encodeInternalNode (m := Id) node =
      if (Rlp.encode (assembleInternalNode node)).size < 32 then assembleInternalNode node
      else .bytes (keccak256 (Rlp.encode (assembleInternalNode node))).toBytes.toByteArray :=
  encodeInternalNode_id node

end STFSpec.Conformance.Commit.InternalNodeCallerProofs
