/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Commit

/-!
# Complete immediate-extension controls

Library `EthConformance`. Full recursive fields/caches and generic effects are
observed; an independent List-wire immediate model completes only the outer node.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/4/7/8.
-/
namespace STFSpec.Conformance.Commit.ExtensionGuards
open STFSpec.Base STFSpec.Codec STFSpec.Hash STFSpec.Commit
private def bytes (xs : List UInt8) : ByteArray := xs.toByteArray
private def path (xs : List (Fin 16)) : Nibbles := Nibbles.ofList xs
private def answer (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)
private def enc (raw : List UInt8 := []) (h : Option Hash32 := none) : Enc := ⟨bytes raw, h⟩
private def wireBytes (b : ByteArray) : List Nat := b.size :: b.data.toList.map UInt8.toNat
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

private def joined (p q : Nibbles) : Nibbles := path (p.toList ++ q.toList)
private def raw (p : Nibbles) (c : Node) : ByteArray :=
  (match c with
   | .leaf q v _ => internalNodeWireModel (some (.leaf (joined p q) (.bytes v)))
   | .ext q grandchild _ => internalNodeWireModel
       (some (.extension (joined p q) (childRef (some grandchild))))
   | _ => internalNodeWireModel (some (.extension p (childRef (some c))))).toByteArray
private def expected (p : Nibbles) (c : Node) (h : Option Hash32) : Node :=
  let e := Enc.mk (raw p c) h
  match c with
  | .leaf q v _ => .leaf (joined p q) v e
  | .ext q grandchild _ => .ext (joined p q) grandchild e
  | _ => .ext p c e
private abbrev Trace := List ByteArray × Nat
private def seed : Trace := ([bytes [0, 255, 66]], 7)
private def recording (p : Nibbles) (c : Node) (s : Trace) : Node × Trace :=
  letI : KeccakQuery (StateM Trace) :=
    ⟨fun preimage state => (answer state.2, (state.1 ++ [preimage], state.2 + 1))⟩
  (mkExt (m := StateM Trace) p c).run s
private def check (p : Nibbles) (c : Node) : Bool :=
  let r := raw p c
  let (node, state) := recording p c seed
  (wireRef (some node) == wireRef (some
    (expected p c (if r.size < 32 then none else some (answer 7))))) &&
    decide (state = if r.size < 32 then seed else (seed.1 ++ [r], 8))
private def digits (n : Nat) : Nibbles :=
  path ((List.range n).map fun i => (⟨i % 16, Nat.mod_lt _ (by decide)⟩ : Fin 16))
private def leaf (p : Nibbles) (n : Nat) : Node :=
  .leaf p (bytes ((List.range n).map UInt8.ofNat)) (enc [0,255,0] (some (answer 99)))
private def nested : Node := .ext (path [1,0])
  (.ext (path []) (.leaf (path [0,15]) (bytes [0,255]) (enc [255] (some (answer 31))))
    (enc [0] (some (answer 47)))) (enc [128,255] (some (answer 93)))
#guard check (path []) (leaf (path []) 0)
#guard check (path [0,15,0]) (leaf (path [15,0]) 3)
#guard check (path []) nested
#guard check (path [0,15]) nested
#guard check (path []) (.hashed (answer 23))
#guard check (path [0,0]) (.hashed (answer 23))
#guard (List.range 16).all fun n => check (path [⟨n % 16, Nat.mod_lt _ (by decide)⟩])
  (leaf (path [0,15]) 3)
#guard [0,1,2,63,64,65,108,110,508,510].all fun n =>
  [0,1,28,29,30,53,54,55,56,252,253,254,255,256].all fun size =>
    check (digits n) (leaf (digits 1) size)
#guard [28,29,30].map (fun n => (raw (path []) (leaf (path []) n)).size) == [31,32,33]
private def boundaryBranch (n : Nat) : Node :=
  .branch #[] (bytes (List.replicate n 0)) (enc [])
#guard [27, 28, 29].map (fun n => (raw (path []) (boundaryBranch n)).size) == [31, 32, 33]
#guard [27, 28, 29].all fun n => check (path []) (boundaryBranch n)
#guard [27, 28, 29].map (fun n =>
  (raw (path []) (.ext (path []) (boundaryBranch n) (enc [255]))).size) == [31, 32, 33]
#guard [27, 28, 29].all fun n =>
  check (path []) (.ext (path []) (boundaryBranch n) (enc [255]))
#guard [0,1,15,16,17,33].all fun n =>
  [none, some (answer 3)].all fun h =>
    check (path []) (.branch (Array.replicate n (some nested)) (bytes [0,255,0]) (enc [255,0] h))
-- Full arbitrary answer retains leading zeros and differs from concrete hashing.
#guard (answer 7).toBytes.toByteArray.data.toList == List.replicate 31 0 ++ [7]
#guard answer 7 != keccak256 (raw (path []) (.hashed (answer 23)))
private def independent : Bool :=
  let p := path [0,15]
  let c := leaf (path [0]) 40
  let (first, s₁) := recording p c seed
  let (second, s₂) := recording p c s₁
  (wireRef (some first) == wireRef (some (expected p c (some (answer 7))))) &&
    (wireRef (some second) == wireRef (some (expected p c (some (answer 8))))) &&
    decide (s₂ = (seed.1 ++ [raw p c, raw p c], 9))
#guard independent
private def failOuter (p : Nibbles) (c : Node) : Except String Node × Trace :=
  letI : KeccakQuery (ExceptT String (StateM Trace)) :=
    ⟨fun r => ExceptT.mk fun s => (.error "original failure", (s.1 ++ [r], s.2 + 1))⟩
  (mkExt (m := ExceptT String (StateM Trace)) p c).run.run seed
private def failInner (p : Nibbles) (c : Node) : Except String (Node × Trace) :=
  letI : KeccakQuery (StateT Trace (Except String)) := ⟨fun _ _ => .error "original failure"⟩
  (mkExt (m := StateT Trace (Except String)) p c).run seed
#guard match failOuter (path []) (leaf (path []) 0) with
  | (.ok node, s) => wireRef (some node) == wireRef
      (some (expected (path []) (leaf (path []) 0) none)) && decide (s = seed)
  | _ => false
#guard match failInner (path []) (leaf (path []) 0) with
  | .ok (node, s) => wireRef (some node) == wireRef
      (some (expected (path []) (leaf (path []) 0) none)) && decide (s = seed)
  | _ => false
#guard match failOuter (path []) (.hashed (answer 3)) with
  | (.error e, s) => e == "original failure" &&
      decide (s = (seed.1 ++ [raw (path []) (.hashed (answer 3))], 8))
  | _ => false
#guard match failInner (path []) (.hashed (answer 3)) with
  | .error e => e == "original failure"
  | _ => false
private def firstFailure : Except String (Node × Node) × Trace :=
  letI : KeccakQuery (ExceptT String (StateM Trace)) :=
    ⟨fun r => ExceptT.mk fun s =>
      (if s.2 == 8 then .error "second query failed" else .ok (answer s.2),
        (s.1 ++ [r], s.2 + 1))⟩
  let action : ExceptT String (StateM Trace) (Node × Node) := do
    let first ← mkExt (path [0]) (.hashed (answer 1))
    let second ← mkExt (path [1]) nested
    let _third ← mkExt (path [2]) (.hashed (answer 3))
    pure (first, second)
  action.run.run seed
#guard match firstFailure with
  | (.error e, s) => e == "second query failed" && decide (s = (seed.1 ++
      [raw (path [0]) (.hashed (answer 1)), raw (path [1]) nested], 9))
  | _ => false
-- Complete public operation frames used in external original-stage comparisons.
private def emit (cases : List (Nibbles × Node)) : IO Unit := do
  for ((p,c),i) in cases.zipIdx do
    let node := mkExt (m := Id) p c
    IO.println (s!"\{\"case\":{i},\"path\":{p.toList.map Fin.val}," ++
      s!"\"input\":{wireRef (some c)},\"result\":{wireRef (some node)}}")
end STFSpec.Conformance.Commit.ExtensionGuards
