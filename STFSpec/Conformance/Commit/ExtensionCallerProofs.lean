/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit

/-!
# Immediate-extension public-law clients

Library `EthConformance`. Literal cases need only Monad; observations and
transformer simplifications state LawfulMonad explicitly. No production/provider
implementation is unfolded. Standard domains cover the complete assembly.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/7/8.
-/

namespace STFSpec.Conformance.Commit.ExtensionCallerProofs
open STFSpec.Base STFSpec.Codec STFSpec.Hash STFSpec.Commit

private def fields : Node → Option (Nibbles × Node × ByteArray × Option Hash32)
  | .ext p c e => some (p, c, e.rlp, e.hash?)
  | _ => none

private theorem merged_leaf {m : Type → Type} [Monad m] [KeccakQuery m]
    (p q : Nibbles) (v : ByteArray) (old : Enc) :
    mkExt (m := m) p (.leaf q v old) =
      mkLeaf (m := m) (Nibbles.ofList (p.toList ++ q.toList)) v := mkExt_leaf p q v old

private theorem short_ext_fields {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (p q : Nibbles) (c : Node) (old : Enc)
    (h : (Rlp.encode (assembleInternalNode (some (.extension
      (Nibbles.ofList (p.toList ++ q.toList)) (childRef (some c)))))).size < 32) :
    (mkExt (m := m) p (.ext q c old) >>= fun node => pure (fields node)) =
      pure (some (Nibbles.ofList (p.toList ++ q.toList), c,
        Rlp.encode (assembleInternalNode (some (.extension
          (Nibbles.ofList (p.toList ++ q.toList)) (childRef (some c))))), none)) := by
  rw [mkExt_ext]
  simp only [h, ↓reduceIte, pure_bind, fields]

private theorem branch_answer {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (p : Nibbles) (children : Array Ref) (v : ByteArray) (childEnc : Enc) (answer : Hash32)
    (h : 32 ≤ (Rlp.encode (assembleInternalNode (some (.extension p
      (childRef (some (.branch children v childEnc))))))).size)
    (hq : KeccakQuery.keccak (m := m) (Rlp.encode (assembleInternalNode (some (.extension p
      (childRef (some (.branch children v childEnc))))))) = pure answer) :
    (mkExt (m := m) p (.branch children v childEnc) >>= fun node => pure (fields node)) =
      pure (some (p, Node.branch children v childEnc,
        Rlp.encode (assembleInternalNode (some (.extension p
          (childRef (some (.branch children v childEnc)))))), some answer)) := by
  rw [mkExt_branch]
  simp only [ite_eq_right (Nat.not_lt.mpr h)]
  rw [hq]
  simp only [pure_bind, fields]

private theorem stub_state_lift {m : Type → Type} {σ : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m] (p : Nibbles) (h : Hash32) (s : σ) :
    (mkExt (m := StateT σ m) p (.hashed h)).run s =
      (do let node ← mkExt (m := m) p (.hashed h); pure (node, s)) := by
  rw [mkExt_hashed, mkExt_hashed]
  dsimp only
  split <;> simp [KeccakQuery.keccak_stateT]

private theorem stub_except_lift {m : Type → Type} {ε : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m] (p : Nibbles) (h : Hash32) :
    (mkExt (m := ExceptT ε m) p (.hashed h)).run =
      (do let node ← mkExt (m := m) p (.hashed h); pure (.ok node : Except ε Node)) := by
  rw [mkExt_hashed, mkExt_hashed]
  dsimp only
  split <;> simp [KeccakQuery.keccak_exceptT, ExceptT.run_lift, Except.map]

private theorem complete_extension_domain (p : Nibbles) (c : Node)
    (hhp : p.size / 2 + 1 < 2 ^ 64) (hc : Rlp.Encodable (childRef (some c)))
    (hpayload : (Rlp.encodePayloadModel
      [.bytes (nibbleListToCompact p false), childRef (some c)]).length < 2 ^ 64) :
    Rlp.Encodable (assembleInternalNode (some (.extension p (childRef (some c))))) := by
  exact (encodable_assembleInternalNode_extension_iff p (childRef (some c))).mpr
    ⟨hhp, hc, hpayload⟩

end STFSpec.Conformance.Commit.ExtensionCallerProofs
