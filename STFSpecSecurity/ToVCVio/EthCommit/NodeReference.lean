/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import ToVCVio.Rlp.Reference
import STFSpec.Commit.InternalNode

/-!
# Public internal-node reference adapter

The callback and actual core capability must describe the same complete action.
The valid-list certificate retains the entire assembly's recursive RLP domain.
Library `ToVCVio` in `STFSpecSecurity`.
Spec guidance: `STFSpec/informal/modules/ToVCVio.md` §§5/7; `EthCommit.md` §7.
-/

namespace ToVCVio.EthCommit
open STFSpec.Base STFSpec.Codec STFSpec.Hash STFSpec.Commit ToVCVio.Rlp

/-- Construct a valid RLP list from the actual assembly and its complete domain proof. -/
def asListNode (node : InternalNode)
    (henc : STFSpec.Codec.Rlp.Encodable (assembleInternalNode (some node))) : RlpListNode :=
  ⟨⟨assembleInternalNode (some node), henc⟩,
    by cases node <;> exact ⟨_, rfl⟩⟩

/-- The facade retains exactly the actual complete assembly, including all fields. -/
theorem asListNode_item (node : InternalNode)
    (henc : STFSpec.Codec.Rlp.Encodable (assembleInternalNode (some node))) :
    (asListNode node henc).val.val = assembleInternalNode (some node) := rfl

/-- One same-preimage query-action premise couples an arbitrary callback to core. -/
theorem callback_adapter {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (q : ByteArray → m Hash32) (x : RlpListNode) (node : InternalNode)
    (hshape : x.val.val = assembleInternalNode (some node))
    (hq : q (STFSpec.Codec.Rlp.encode (assembleInternalNode (some node))) =
      KeccakQuery.keccak (m := m) (STFSpec.Codec.Rlp.encode (assembleInternalNode (some node)))) :
    wireItem <$> childRefM q x = encodeInternalNode (m := m) (some node) := by
  have hw : x.encode = STFSpec.Codec.Rlp.encode (assembleInternalNode (some node)) :=
    congrArg STFSpec.Codec.Rlp.encode hshape
  rw [childRefM_eq, hw, encodeInternalNode_eq]
  by_cases hs : (STFSpec.Codec.Rlp.encode (assembleInternalNode (some node))).size < 32
  · simp [hs, wireItem, hshape]
  · simp only [hs, ↓reduceIte]
    rw [hq]
    simp [wireItem]

/-- The installed capability supplies both sides, with no inferred handler coupling. -/
theorem keccak_adapter {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (node : InternalNode)
    (henc : STFSpec.Codec.Rlp.Encodable (assembleInternalNode (some node))) :
    wireItem <$> childRefM (KeccakQuery.keccak (m := m)) (asListNode node henc) =
      encodeInternalNode (m := m) (some node) :=
  callback_adapter _ _ node rfl rfl

/-- Absence is pure and needs no LawfulMonad comparison or oracle answer premise. -/
theorem empty_adapter {m : Type → Type} [Monad m] [KeccakQuery m] :
    (pure (wireItem .empty) : m RlpItem) = encodeInternalNode (m := m) none :=
  (encodeInternalNode_none (m := m)).symm

end ToVCVio.EthCommit
