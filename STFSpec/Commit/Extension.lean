/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit.Leaf
import STFSpec.Commit.ChildRef

/-!
# Completed immediate-extension construction

Library `EthCommit`. Pinned EELS
`src/ethereum/forks/amsterdam/incremental_mpt.py:719–750,795–819`.
Match the immediate child once, splice its leaf/extension path once, and strictly
complete only the fresh outer node. Retained descendants keep all fields/caches.
This is not a transitive normalization or every mutation extension stage.
Private packed concatenation and ordinary List/wire equality cover all finite
inputs; source/cache/action correspondence has separate conditional premises.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` C18/C19/C23/C24/§7.
-/

namespace STFSpec.Commit
open STFSpec.Base STFSpec.Codec STFSpec.Hash

private def concat (p q : Nibbles) : Nibbles :=
  Nibbles.generate (p.size + q.size) fun i =>
    if hp : i < p.size then p.get ⟨i, hp⟩
    else if hq : i - p.size < q.size then q.get ⟨i - p.size, hq⟩ else 0

private theorem concat_model (p q : Nibbles) :
    concat p q = Nibbles.ofList (p.toList ++ q.toList) := by
  apply Nibbles.ext
  rw [concat, Nibbles.toList_generate, Nibbles.toList_ofList]
  apply List.ext_getElem
  · simp [Nibbles.length_toList]
  · intro i hi hj
    have hib : i < p.size + q.size := by simpa using hi
    simp only [List.getElem_map, List.getElem_range]
    by_cases hp : i < p.size
    · rw [List.getElem_append_left (by rwa [Nibbles.length_toList]),
        Nibbles.getElem_toList p i hp]
      simp only [hp, ↓reduceDIte]
    · have hq : i - p.size < q.size := by omega
      rw [List.getElem_append_right (by rw [Nibbles.length_toList]; omega)]
      simp only [Nibbles.length_toList, Nibbles.getElem_toList q _ hq, hp, hq, ↓reduceDIte]

private def freshExt {m : Type → Type} [Monad m] [KeccakQuery m]
    (p : Nibbles) (child : Node) : m Node :=
  let raw := Rlp.encode (assembleInternalNode (some (.extension p (childRef (some child)))))
  if raw.size < 32 then pure (.ext p child ⟨raw, none⟩)
  else KeccakQuery.keccak raw >>= fun answer => pure (.ext p child ⟨raw, some answer⟩)

/-- Splice exactly one immediate child path, then complete the fresh outer node.
The immediate old cache is discarded only in leaf/ext cases; every retained child
and descendant is preserved. Empty prefixes still follow the same cases. Pinned EELS
`src/ethereum/forks/amsterdam/incremental_mpt.py:719–750,795–819`, with fresh outer
completion at `:316–346`. -/
def mkExt {m : Type → Type} [Monad m] [KeccakQuery m]
    (path : Nibbles) (child : Node) : m Node :=
  match child with
  | .leaf q v _ => mkLeaf (concat path q) v
  | .ext q c _ => freshExt (concat path q) c
  | .branch _ _ _ => freshExt path child
  | .hashed _ => freshExt path child

/-- A leaf child is rebuilt through the public completed-leaf operation. -/
theorem mkExt_leaf {m : Type → Type} [Monad m] [KeccakQuery m]
    (p q : Nibbles) (v : ByteArray) (old : Enc) :
    mkExt (m := m) p (.leaf q v old) =
      mkLeaf (m := m) (Nibbles.ofList (p.toList ++ q.toList)) v := by
  rw [mkExt, concat_model]

/-- An extension child is spliced once; the entire grandchild is retained. -/
theorem mkExt_ext {m : Type → Type} [Monad m] [KeccakQuery m]
    (p q : Nibbles) (c : Node) (old : Enc) :
    mkExt (m := m) p (.ext q c old) =
      let joined := Nibbles.ofList (p.toList ++ q.toList)
      let raw := Rlp.encode (assembleInternalNode
        (some (.extension joined (childRef (some c)))))
      if raw.size < 32 then pure (Node.ext joined c (Enc.mk raw none))
      else KeccakQuery.keccak raw >>= fun answer =>
        pure (Node.ext joined c (Enc.mk raw (some answer))) := by
  rw [mkExt, concat_model, freshExt]

/-- A branch child, with arbitrary actual arity/fields/cache, is retained whole. -/
theorem mkExt_branch {m : Type → Type} [Monad m] [KeccakQuery m]
    (p : Nibbles) (children : Array Ref) (v : ByteArray) (childEnc : Enc) :
    mkExt (m := m) p (.branch children v childEnc) =
      let c := Node.branch children v childEnc
      let raw := Rlp.encode (assembleInternalNode
        (some (.extension p (childRef (some c)))))
      if raw.size < 32 then pure (Node.ext p c (Enc.mk raw none))
      else KeccakQuery.keccak raw >>= fun answer =>
        pure (Node.ext p c (Enc.mk raw (some answer))) := by
  rw [mkExt, freshExt]

/-- An unresolved stub remains embedded; no witness lookup/failure is added. -/
theorem mkExt_hashed {m : Type → Type} [Monad m] [KeccakQuery m]
    (p : Nibbles) (h : Hash32) :
    mkExt (m := m) p (.hashed h) =
      let c := Node.hashed h
      let raw := Rlp.encode (assembleInternalNode
        (some (.extension p (childRef (some c)))))
      if raw.size < 32 then pure (Node.ext p c (Enc.mk raw none))
      else KeccakQuery.keccak raw >>= fun answer =>
        pure (Node.ext p c (Enc.mk raw (some answer))) := by
  rw [mkExt, freshExt]

private def completeModel {m : Type → Type} [Monad m] [KeccakQuery m]
    (node : Option InternalNode) (make : Enc → Node) : m Node :=
  let bytes := internalNodeWireModel node
  if bytes.length < 32 then pure (make ⟨bytes.toByteArray, none⟩)
  else KeccakQuery.keccak bytes.toByteArray >>= fun answer =>
    pure (make ⟨bytes.toByteArray, some answer⟩)

private def reference {m : Type → Type} [Monad m] [KeccakQuery m]
    (p : Nibbles) (child : Node) : m Node :=
  match child with
  | .leaf q v _ =>
    let joined := Nibbles.ofList (p.toList ++ q.toList)
    completeModel (some (.leaf joined (.bytes v))) (Node.leaf joined v)
  | .ext q c _ =>
    let joined := Nibbles.ofList (p.toList ++ q.toList)
    completeModel (some (.extension joined (childRef (some c)))) (Node.ext joined c)
  | .branch _ _ _ =>
    completeModel (some (.extension p (childRef (some child)))) (Node.ext p child)
  | .hashed _ =>
    completeModel (some (.extension p (childRef (some child)))) (Node.ext p child)

private theorem raw_model (node : Option InternalNode) :
    Rlp.encode (assembleInternalNode node) = (internalNodeWireModel node).toByteArray := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simpa only [List.toList_data_toByteArray] using toList_encode_assembleInternalNode node

private theorem freshExt_reference {m : Type → Type} [Monad m] [KeccakQuery m]
    (p : Nibbles) (c : Node) :
    freshExt (m := m) p c =
      completeModel (some (.extension p (childRef (some c)))) (Node.ext p c) := by
  rw [freshExt, completeModel, size_encode_assembleInternalNode, raw_model]

private theorem leaf_reference {m : Type → Type} [Monad m] [KeccakQuery m]
    (p : Nibbles) (v : ByteArray) :
    mkLeaf (m := m) p v = completeModel (some (.leaf p (.bytes v))) (Node.leaf p v) := by
  by_cases hs : (Rlp.encode (assembleInternalNode (some (.leaf p (.bytes v))))).size < 32
  · rw [mkLeaf_inline p v hs, completeModel]
    have hm : (internalNodeWireModel (some (.leaf p (.bytes v)))).length < 32 := by
      rwa [size_encode_assembleInternalNode] at hs
    simp only [hm, ↓reduceIte, raw_model]
  · rw [mkLeaf_hash p v (by omega), completeModel]
    have hm : ¬ (internalNodeWireModel (some (.leaf p (.bytes v)))).length < 32 := by
      rwa [size_encode_assembleInternalNode] at hs
    simp only [hm, ↓reduceIte, raw_model]

/-- Literal action equality on every finite input; no monad laws or WF binder. -/
private theorem mkExt_reference {m : Type → Type} [Monad m] [KeccakQuery m]
    (p : Nibbles) (child : Node) : mkExt (m := m) p child = reference p child := by
  cases child <;> simp only [mkExt, reference, concat_model, leaf_reference, freshExt_reference]

end STFSpec.Commit
