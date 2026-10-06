/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit.Node
import STFSpec.Commit.InternalNode

/-!
# Completed fresh-leaf construction

Library `EthCommit`. A new leaf retains its fields and complete total RLP encoding;
only encodings of at least 32 bytes acquire a cached hash, using the actual oracle
answer. This strict local completion does not simulate arbitrary mutable caches or
the source's lazy update schedule. Standard/source correspondence needs the whole
assembly's `Encodable` and concrete class/host/hash premises (Q47, B15).
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/5/7/8.
-/

namespace STFSpec.Commit

open STFSpec.Base STFSpec.Codec STFSpec.Hash

/-- Complete a fresh leaf once. Pinned EELS
`src/ethereum/forks/amsterdam/incremental_mpt.py:48–57,267–271,316–346,486–488`, with initially
absent raw/hash caches, followed by materialization; paths and values may be empty. -/
def mkLeaf {m : Type → Type} [Monad m] [KeccakQuery m]
    (path : Nibbles) (value : ByteArray) : m Node :=
  let raw := Rlp.encode (assembleInternalNode (some (.leaf path (.bytes value))))
  if raw.size < 32 then pure (.leaf path value ⟨raw, none⟩)
  else KeccakQuery.keccak raw >>= fun answer => pure (.leaf path value ⟨raw, some answer⟩)

/-- A short completed leaf retains every field and makes no local query. -/
theorem mkLeaf_inline {m : Type → Type} [Monad m] [KeccakQuery m]
    (path : Nibbles) (value : ByteArray)
    (h : (Rlp.encode (assembleInternalNode (some (.leaf path (.bytes value))))).size < 32) :
    mkLeaf (m := m) path value =
      let raw := Rlp.encode (assembleInternalNode (some (.leaf path (.bytes value))))
      pure (Node.leaf path value (Enc.mk raw none)) := by
  simp only [mkLeaf, h, ↓reduceIte]

/-- A long completed leaf queries its complete raw encoding once and retains the
actual complete answer. The literal bind equation requires only `Monad`. -/
theorem mkLeaf_hash {m : Type → Type} [Monad m] [KeccakQuery m]
    (path : Nibbles) (value : ByteArray)
    (h : 32 ≤ (Rlp.encode (assembleInternalNode (some (.leaf path (.bytes value))))).size) :
    mkLeaf (m := m) path value =
      let raw := Rlp.encode (assembleInternalNode (some (.leaf path (.bytes value))))
      (KeccakQuery.keccak raw >>= fun answer =>
        pure (Node.leaf path value (Enc.mk raw (some answer)))) := by
  simp only [mkLeaf, ite_eq_right (Nat.not_lt.mpr h)]

private def mkLeafReference {m : Type → Type} [Monad m] [KeccakQuery m]
    (path : Nibbles) (value : ByteArray) : m Node :=
  let bytes := internalNodeWireModel (some (.leaf path (.bytes value)))
  if bytes.length < 32 then pure (.leaf path value ⟨bytes.toByteArray, none⟩)
  else KeccakQuery.keccak bytes.toByteArray >>= fun answer =>
    pure (.leaf path value ⟨bytes.toByteArray, some answer⟩)

/-- All finite inputs, including the total encoding extension outside Encodable. -/
private theorem mkLeaf_eq_reference {m : Type → Type} [Monad m] [KeccakQuery m]
    (path : Nibbles) (value : ByteArray) :
    mkLeaf (m := m) path value = mkLeafReference path value := by
  have wire : Rlp.encode (assembleInternalNode (some (.leaf path (.bytes value)))) =
      (internalNodeWireModel (some (.leaf path (.bytes value)))).toByteArray := by
    apply ByteArray.ext
    apply Array.toList_inj.mp
    simpa only [List.toList_data_toByteArray] using
      toList_encode_assembleInternalNode (some (.leaf path (.bytes value)))
  rw [mkLeaf, mkLeafReference, size_encode_assembleInternalNode, wire]

end STFSpec.Commit
