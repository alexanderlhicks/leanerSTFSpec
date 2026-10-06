/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit.ChildRef
import STFSpec.Commit.IncrementalMPT
import STFSpec.Codec.RlpEncode
import STFSpec.Hash.KeccakQuery

/-!
# Supplied incremental-root commitment

Library `EthCommit`. Pinned EELS
`src/ethereum/forks/amsterdam/incremental_mpt.py:831–856,257–313`.
Absence returns the caller's supplied empty root; a stored hash bypasses fields.
A hashless resolved root forwards one query on its complete current-field item.
This local observer installs no cache and has no top width threshold. Source dirty
history, descendant materialization and mutable effects have separate premises.
Private ordinary full-byte/action equality uses the public total RLP model.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` C5/C18/C27/§7.
-/

namespace STFSpec.Commit
open STFSpec.Base STFSpec.Codec STFSpec.Hash

private def storedHash : Node → Option Hash32
  | .hashed h => some h
  | .leaf _ _ enc | .ext _ _ enc | .branch _ _ enc => enc.hash?

/-- Commit a supplied partial root. Stored hashes win; otherwise query the entire
current-field item once, forwarding the original oracle action without rebinding. Pinned EELS
`src/ethereum/forks/amsterdam/incremental_mpt.py:831–856,257–313`. -/
def rootHash {m : Type → Type} [Monad m] [KeccakQuery m]
    (emptyRoot : Hash32) (root : Ref) : m Hash32 :=
  match root with
  | none => pure emptyRoot
  | some node =>
    match storedHash node with
    | some h => pure h
    | none => KeccakQuery.keccak (Rlp.encode (childRef root))

/-- Root commitment forwards the supplied root; the secured flag is irrelevant. Pinned EELS
`src/ethereum/forks/amsterdam/incremental_mpt.py:831–856`. -/
def mptRoot {m : Type → Type} [Monad m] [KeccakQuery m]
    (emptyRoot : Hash32) (trie : IncrementalMPT) : m Hash32 :=
  rootHash emptyRoot trie.root

/-- Absence returns the exact supplied constant without a local query. -/
theorem rootHash_none {m : Type → Type} [Monad m] [KeccakQuery m] (e : Hash32) :
    rootHash (m := m) e none = pure e := rfl

/-- A stub returns its full typed hash without encoding or querying. -/
theorem rootHash_hashed {m : Type → Type} [Monad m] [KeccakQuery m] (e h : Hash32) :
    rootHash (m := m) e (some (.hashed h)) = pure h := rfl

/-- A leaf ignores raw cache bytes and forwards the hash or complete field query. -/
theorem rootHash_leaf {m : Type → Type} [Monad m] [KeccakQuery m]
    (e : Hash32) (p : Nibbles) (v : ByteArray) (enc : Enc) :
    rootHash (m := m) e (some (.leaf p v enc)) =
      match enc.hash? with
      | some h => pure h
      | none => KeccakQuery.keccak
          (Rlp.encode (.list [.bytes (nibbleListToCompact p true), .bytes v])) := by
  rw [rootHash, storedHash]
  cases h : enc.hash? <;> simp only [childRef_leaf, h]

/-- A stored extension hash wins; a hashless extension queries current path/child fields. -/
theorem rootHash_ext {m : Type → Type} [Monad m] [KeccakQuery m]
    (e : Hash32) (p : Nibbles) (child : Node) (enc : Enc) :
    rootHash (m := m) e (some (.ext p child enc)) =
      match enc.hash? with
      | some h => pure h
      | none => KeccakQuery.keccak
          (Rlp.encode (.list [.bytes (nibbleListToCompact p false), childRef (some child)])) := by
  rw [rootHash, storedHash]
  cases h : enc.hash? <;> simp only [childRef_ext, h]

/-- A stored branch hash wins; otherwise encode every ordered slot and the ending value. -/
theorem rootHash_branch {m : Type → Type} [Monad m] [KeccakQuery m]
    (e : Hash32) (cs : Array Ref) (v : ByteArray) (enc : Enc) :
    rootHash (m := m) e (some (.branch cs v enc)) =
      match enc.hash? with
      | some h => pure h
      | none => KeccakQuery.keccak
          (Rlp.encode (.list (cs.toList.map childRef ++ [.bytes v]))) := by
  rw [rootHash, storedHash]
  cases h : enc.hash? <;> simp only [childRef_branch, h]

/-- The wrapper is the exact rootHash action on the supplied root. -/
theorem mptRoot_eq {m : Type → Type} [Monad m] [KeccakQuery m]
    (e : Hash32) (t : IncrementalMPT) :
    mptRoot (m := m) e t = rootHash (m := m) e t.root := rfl

private def reference {m : Type → Type} [Monad m] [KeccakQuery m]
    (e : Hash32) (root : Ref) : m Hash32 :=
  match root with
  | none => pure e
  | some node =>
    match storedHash node with
    | some h => pure h
    | none => KeccakQuery.keccak ((Rlp.encodeModel (childRef root)).toByteArray)

private theorem wire_model (root : Ref) :
    Rlp.encode (childRef root) = (Rlp.encodeModel (childRef root)).toByteArray := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simpa only [List.toList_data_toByteArray] using Rlp.toList_encode (childRef root)

/-- Ordinary whole-action equality for every finite bare input under plain Monad. -/
private theorem rootHash_reference {m : Type → Type} [Monad m] [KeccakQuery m]
    (e : Hash32) (root : Ref) : rootHash (m := m) e root = reference e root := by
  simp only [rootHash, reference, wire_model]


end STFSpec.Commit
