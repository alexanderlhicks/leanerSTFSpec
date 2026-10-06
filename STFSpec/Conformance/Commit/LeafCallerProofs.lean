/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit

/-!
# Completed-leaf public-law clients

Library `EthConformance`. Ordinary clients consume the two public constructor/cache
equations and provider laws without unfolding provider or constructor implementations.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/7/8.
-/

namespace STFSpec.Conformance.Commit.LeafCallerProofs
open STFSpec.Base STFSpec.Codec STFSpec.Hash STFSpec.Commit

private def fields : Node → Option (Nibbles × ByteArray × ByteArray × Option Hash32)
  | .leaf path value enc => some (path, value, enc.rlp, enc.hash?)
  | _ => none

private theorem short_fields {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (path : Nibbles) (value : ByteArray)
    (h : (internalNodeWireModel (some (.leaf path (.bytes value)))).length < 32) :
    (mkLeaf (m := m) path value >>= fun node => pure (fields node)) =
      pure (some (path, value,
        Rlp.encode (assembleInternalNode (some (.leaf path (.bytes value)))), none)) := by
  rw [mkLeaf_inline path value (by rwa [size_encode_assembleInternalNode])]
  simp only [pure_bind, fields]

private theorem answer_fields {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (path : Nibbles) (value : ByteArray) (answer : Hash32)
    (h : 32 ≤ (internalNodeWireModel (some (.leaf path (.bytes value)))).length)
    (hq : KeccakQuery.keccak (m := m)
      (Rlp.encode (assembleInternalNode (some (.leaf path (.bytes value))))) = pure answer) :
    (mkLeaf (m := m) path value >>= fun node => pure (fields node)) =
      pure (some (path, value,
        Rlp.encode (assembleInternalNode (some (.leaf path (.bytes value)))), some answer)) := by
  rw [mkLeaf_hash path value (by rwa [size_encode_assembleInternalNode])]
  dsimp only
  rw [hq]
  simp only [pure_bind, fields]

private theorem complete_domain (path : Nibbles) (value : ByteArray)
    (hhp : path.size / 2 + 1 < 2 ^ 64) (hv : value.size < 2 ^ 64)
    (hpayload : (Rlp.encodePayloadModel
      [.bytes (nibbleListToCompact path true), .bytes value]).length < 2 ^ 64) :
    Rlp.Encodable (assembleInternalNode (some (.leaf path (.bytes value)))) := by
  exact (encodable_assembleInternalNode_leaf_iff path (.bytes value)).mpr
    ⟨hhp, (Rlp.encodable_bytes_iff value).mpr hv, hpayload⟩

private theorem except_lift {m : Type → Type} {ε : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m] (path : Nibbles) (value : ByteArray)
    (h : 32 ≤ (Rlp.encode (assembleInternalNode (some (.leaf path (.bytes value))))).size) :
    (mkLeaf (m := ExceptT ε m) path value).run =
      (do let node ← mkLeaf (m := m) path value; pure (.ok node : Except ε Node)) := by
  rw [mkLeaf_hash path value h, mkLeaf_hash path value h]
  simp [KeccakQuery.keccak_exceptT, ExceptT.run_lift, Except.map]

private theorem state_lift {m : Type → Type} {σ : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m] (path : Nibbles) (value : ByteArray) (s : σ)
    (h : 32 ≤ (Rlp.encode (assembleInternalNode (some (.leaf path (.bytes value))))).size) :
    (mkLeaf (m := StateT σ m) path value).run s =
      (do let node ← mkLeaf (m := m) path value; pure (node, s)) := by
  rw [mkLeaf_hash path value h, mkLeaf_hash path value h]
  simp [KeccakQuery.keccak_stateT]

end STFSpec.Conformance.Commit.LeafCallerProofs
