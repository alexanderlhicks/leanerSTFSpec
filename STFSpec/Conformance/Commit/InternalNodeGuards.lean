/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit
import STFSpec.Conformance.Commit.NibblesGuards

/-!
# Complete internal-node operation observations

Library `EthConformance`. Compare all constructors, bytes, query preimages and
arbitrary answer bytes; no nested derived instances. Actual-source comparisons
are emitted by `STFSpec/Conformance/Commit/internal_node_differential.py`.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3–4.
-/

namespace STFSpec.Conformance.Commit.InternalNodeGuards

open STFSpec.Base STFSpec.Codec STFSpec.Hash STFSpec.Commit
open STFSpec.Conformance.Commit.NibblesGuards (path)

mutual
  /-- Structural test comparison, including every byte and ordered nested item. -/
  def sameItem : RlpItem → RlpItem → Bool
    | .bytes a, .bytes b => decide (a = b)
    | .list xs, .list ys => sameItems xs ys
    | _, _ => false
  /-- Ordered full list comparison. -/
  def sameItems : List RlpItem → List RlpItem → Bool
    | [], [] => true
    | x :: xs, y :: ys => sameItem x y && sameItems xs ys
    | _, _ => false
end

/-- Recording oracle returns a deliberately nonconcrete arbitrary answer. -/
def testAnswer : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat
  0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f)

/-- Entire production result and exact complete preimages under a recording oracle. -/
def observe (node : Option InternalNode) : RlpItem × List ByteArray :=
  letI : KeccakQuery (StateM (List ByteArray)) :=
    ⟨fun bytes trace ↦ (testAnswer, trace ++ [bytes])⟩
  (encodeInternalNode (m := StateM (List ByteArray)) node).run []

/-- Entire error result and full query trace with a failing oracle. -/
def observeFailure (node : Option InternalNode) : Except String RlpItem × List ByteArray :=
  letI : KeccakQuery (ExceptT String (StateM (List ByteArray))) :=
    ⟨fun bytes ↦ ExceptT.mk fun trace ↦ (.error "original oracle failure", trace ++ [bytes])⟩
  (encodeInternalNode (m := ExceptT String (StateM (List ByteArray))) node).run.run []

private def raw (xs : List UInt8) : RlpItem := .bytes xs.toByteArray
private def fieldNode (n : Nat) : Option InternalNode :=
  some (.leaf (path []) (raw (List.replicate n 0xab)))

#guard sameItem (observe none).1 (raw []) && (observe none).2 == []
#guard sameItem (observe (some (.leaf (path []) (raw [0x76])))).1
  (.list [raw [0x20], raw [0x76]])
#guard sameItem (observe (some (.extension (path []) (raw [1])))).1
  (.list [raw [0], raw [1]])
#guard sameItem (observe (some (.leaf (path [1, 2, 3]) (.list [raw [], raw [0xff]])))).1
  (.list [raw [0x31, 0x23], .list [raw [], raw [0xff]]])
#guard (observe (fieldNode 28)).2 == []
#guard sameItem (observe (fieldNode 28)).1 (assembleInternalNode (fieldNode 28))
#guard (observe (fieldNode 29)).2 ==
  [(([0xdf, 0x20, 0x9d] ++ List.replicate 29 0xab) : List UInt8).toByteArray]
#guard sameItem (observe (fieldNode 29)).1 (.bytes testAnswer.toBytes.toByteArray)
#guard (observe (fieldNode 30)).2 ==
  [(([0xe0, 0x20, 0x9e] ++ List.replicate 30 0xab) : List UInt8).toByteArray]
#guard testAnswer.toBytes.toByteArray.data.toList ==
  (List.range 32).map (fun n ↦ UInt8.ofNat n)
#guard match observeFailure none with
  | (.ok result, trace) => sameItem result (raw []) && trace == []
  | _ => false
#guard match observeFailure (fieldNode 29) with
  | (.error error, trace) => error == "original oracle failure" &&
      trace == [(([0xdf, 0x20, 0x9d] ++ List.replicate 29 0xab) : List UInt8).toByteArray]
  | _ => false

private def hashedBranch : Option InternalNode :=
  some (.branch
    (Vector.ofFn fun i : Fin 16 ↦ raw (List.replicate 32 (UInt8.ofNat i.val)))
    (raw []))

-- Authenticated pinned EELS `src/ethereum/merkle_patricia_trie.py:213–249`:
-- `branch-sixteen-hash-children` in `internal_node_differential.py` reproduces
-- the complete 532-byte preimage and this full digest, with child i = [i] * 32.
private def hashedBranchDigest : Bytes32 := FixedBytes.ofNat
  0x8e0d034470bd60bdbdbf045479a8862776c17ff853843627dfffc3e237d54a4c

#guard (Rlp.encode (assembleInternalNode hashedBranch)).size == 532
#guard sameItem (encodeInternalNode (m := Id) hashedBranch)
  (.bytes hashedBranchDigest.toBytes.toByteArray)

end STFSpec.Conformance.Commit.InternalNodeGuards
