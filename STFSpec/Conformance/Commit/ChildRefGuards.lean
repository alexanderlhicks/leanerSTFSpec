/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit

/-!
# Complete child-reference controls

Library `EthConformance`. Full recursive-item and bare-field framing distinguishes
all bytes, actual ordered slots and optional caches. No query, parse or admission
premise is attached to the production pure observer.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/7/8.
-/

namespace STFSpec.Conformance.Commit.ChildRefGuards
open STFSpec.Base STFSpec.Codec STFSpec.Commit

private def bytes (xs : List UInt8) : ByteArray := xs.toByteArray
private def path (xs : List (Fin 16)) : Nibbles := Nibbles.ofList xs
private def hash (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)
private def enc (raw : List UInt8 := []) (h : Option Hash32 := none) : Enc := ⟨bytes raw, h⟩

-- Full item framing, independent of serialized RLP or nested generated recursion.
private def wireBytes (b : ByteArray) : List Nat := b.size :: b.data.toList.map UInt8.toNat
mutual
private def wireItem : RlpItem → List Nat
  | .bytes b => 0 :: wireBytes b
  | .list xs => 1 :: xs.length :: wireItems xs
termination_by x => sizeOf x
decreasing_by all_goals simp_wf; all_goals omega
private def wireItems : List RlpItem → List Nat
  | [] => []
  | x :: xs => wireItem x ++ wireItems xs
termination_by xs => sizeOf xs
decreasing_by all_goals simp_wf; all_goals omega
end

private def wireHash : Option Hash32 → List Nat
  | none => [0]
  | some h => 1 :: h.toBytes.toByteArray.data.toList.map UInt8.toNat
private def wireEnc (e : Enc) : List Nat := wireBytes e.rlp ++ wireHash e.hash?
private def wirePath (p : Nibbles) : List Nat := p.size :: p.toList.map Fin.val
private def wireRef (root : Ref) : List Nat :=
  match root with
  | none => [0]
  | some (.hashed h) => 1 :: h.toBytes.toByteArray.data.toList.map UInt8.toNat
  | some (.leaf p v e) => 2 :: wirePath p ++ wireBytes v ++ wireEnc e
  | some (.ext p child e) => 3 :: wirePath p ++ wireRef (some child) ++ wireEnc e
  | some (.branch children v e) => 4 :: children.size ::
      (List.ofFn (fun i : Fin children.size => wireRef children[i])).flatten ++
      wireBytes v ++ wireEnc e
termination_by sizeOf root
decreasing_by
  · simp only [Option.some.sizeOf_spec, Node.ext.sizeOf_spec]; omega
  · have h := Array.sizeOf_getElem children i.val i.isLt
    simp only [Option.some.sizeOf_spec, Node.branch.sizeOf_spec, Fin.getElem_fin]; omega

private def same (root : Ref) (expected : RlpItem) : Bool :=
  wireItem (childRef root) == wireItem expected
#guard same none (.bytes (bytes []))
#guard same (some (.hashed (hash 7))) (.bytes (hash 7).toBytes.toByteArray)
#guard same (some (.leaf (path []) (bytes []) (enc [255])))
  (.list [.bytes (bytes [32]), .bytes (bytes [])])
#guard same (some (.leaf (path [0,15,0]) (bytes [0,255,0]) (enc [0,128,255])))
  (.list [.bytes (bytes [48,240]), .bytes (bytes [0,255,0])])
#guard same (some (.leaf (path [0,15]) (bytes [0,128,255]) (enc (List.replicate 40 255))))
  (.list [.bytes (bytes [32,15]), .bytes (bytes [0,128,255])])
private def longLeaf : Node := .leaf (path []) (bytes (List.replicate 29 0xab)) (enc [])
#guard (Rlp.encode (childRef (some longLeaf))).size = 32
#guard same (some (.leaf (path []) (bytes (List.replicate 29 0xab))
  (enc [] (some (hash 4))))) (.bytes (hash 4).toBytes.toByteArray)
#guard same (some longLeaf) (.list [.bytes (bytes [32]), .bytes (bytes (List.replicate 29 0xab))])
private def nested : Node := .ext (path []) (.ext (path [0,15])
  (.leaf (path [1]) (bytes [0,255]) (enc [193])) (enc [255])) (enc [0])
#guard same (some nested) (.list [.bytes (bytes [0]), .list [.bytes (bytes [0,15]),
  .list [.bytes (bytes [49]), .bytes (bytes [0,255])]]])
#guard same (some (.ext (path []) (.hashed (hash 11)) (enc [])))
  (.list [.bytes (bytes [0]), .bytes (hash 11).toBytes.toByteArray])
#guard same (some (.leaf (path []) (bytes (List.replicate 60 0xff)) (enc [] (some (hash 3)))))
  (.bytes (hash 3).toBytes.toByteArray)
#guard same (some (.ext (path []) longLeaf (enc [255] (some (hash 5)))))
  (.bytes (hash 5).toBytes.toByteArray)
#guard same (some (.branch #[some nested, some longLeaf] (bytes [0, 255])
  (enc [0] (some (hash 17)))))
  (.bytes (hash 17).toBytes.toByteArray)
private def slots (n : Nat) : Array Ref :=
  Array.ofFn (fun i : Fin n => some (.hashed (hash (i.val + 1))))
private def expectedSlots (n : Nat) : RlpItem := .list
  (List.ofFn (fun i : Fin n => .bytes (hash (i.val + 1)).toBytes.toByteArray) ++
    [.bytes (bytes [0, 255, 0])])
#guard [0, 1, 15, 16, 17, 33].all fun n =>
  same (some (.branch (slots n) (bytes [0, 255, 0]) (enc [255]))) (expectedSlots n)
#guard same (some (.branch
  #[none, some (.leaf (path []) (bytes []) (enc [])), some (.hashed (hash 9))]
  (bytes []) (enc []))) (.list [.bytes (bytes []), .list [.bytes (bytes [32]), .bytes (bytes [])],
    .bytes (hash 9).toBytes.toByteArray, .bytes (bytes [])])

-- Copied into external generated comparisons; emit every original bare field too.
private def emit (cases : List Ref) : IO Unit := do
  for (root, i) in cases.zipIdx do
    IO.println s!"\{\"case\":{i},\"input\":{wireRef root},\"result\":{wireItem (childRef root)}}"

end STFSpec.Conformance.Commit.ChildRefGuards
