/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Commit

/-!
# Complete fresh-leaf controls

Library `EthConformance`. Every leaf field, raw byte, answer byte and seeded oracle
effect is observed. The separate source driver compares actual concrete completion.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/4/7/8.
-/
namespace STFSpec.Conformance.Commit.LeafGuards
open STFSpec.Base STFSpec.Codec STFSpec.Hash STFSpec.Commit

private def bytes (xs : List UInt8) : ByteArray := xs.toByteArray
private def path (xs : List (Fin 16)) : Nibbles := Nibbles.ofList xs
private def answer (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)
private def raw (p : Nibbles) (v : ByteArray) : ByteArray :=
  (internalNodeWireModel (some (.leaf p (.bytes v)))).toByteArray
private def sameLeaf (node : Node) (p : Nibbles) (v r : ByteArray) (h : Option Hash32) : Bool :=
  match node with
  | .leaf q w enc => decide (q.toList = p.toList) && decide (w = v) &&
      decide (enc.rlp = r) && decide (enc.hash? = h)
  | _ => false
private abbrev Trace := List ByteArray × Nat
private def seed : Trace := ([bytes [0, 0xff, 0x42]], 7)
private def recording (p : Nibbles) (v : ByteArray) (s : Trace) : Node × Trace :=
  letI : KeccakQuery (StateM Trace) :=
    ⟨fun preimage state => (answer state.2, (state.1 ++ [preimage], state.2 + 1))⟩
  (mkLeaf (m := StateM Trace) p v).run s
private def check (p : Nibbles) (v : ByteArray) : Bool :=
  let r := raw p v
  let (node, state) := recording p v seed
  sameLeaf node p v r (if r.size < 32 then none else some (answer seed.2)) &&
    decide (state = if r.size < 32 then seed else (seed.1 ++ [r], seed.2 + 1))
private def digits (n : Nat) : Nibbles :=
  path ((List.range n).map fun i => (⟨i % 16, Nat.mod_lt _ (by decide)⟩ : Fin 16))

#guard check (path []) (bytes [])
#guard check (path [0]) (bytes [0])
#guard check (path [0, 0]) (bytes [0x7f])
#guard check (path [15, 0, 15]) (bytes [0x80])
#guard check (path [0, 1, 0]) (bytes [0, 0xff, 0])
#guard [0, 1, 2, 63, 64, 65, 108, 110, 508, 510].all fun n =>
  [0, 1, 28, 29, 30, 52, 53, 54, 55, 56, 252, 253, 254, 255, 256].all fun v =>
    check (digits n) (bytes ((List.range v).map fun i => UInt8.ofNat i))
#guard (List.range 16).all fun n =>
  check (path [⟨n % 16, Nat.mod_lt _ (by decide)⟩]) (bytes [UInt8.ofNat n, 0xff, 0])
#guard [28, 29, 30].map (fun n => (raw (path []) (bytes (List.replicate n 0xab))).size) ==
  [31, 32, 33]
#guard (raw (path []) (bytes (List.replicate 29 0xab))).data.toList ==
  [0xdf, 0x20, 0x9d] ++ List.replicate 29 0xab
#guard (answer 7).toBytes.toByteArray.data.toList == List.replicate 31 0 ++ [7]
#guard answer 7 != keccak256 (raw (path []) (bytes (List.replicate 29 0xab)))

private def independent : Bool :=
  let p := path [0, 15, 0]
  let v := bytes (List.replicate 40 0xff)
  let (first, s1) := recording p v seed
  let (second, s2) := recording p v s1
  sameLeaf first p v (raw p v) (some (answer 7)) &&
    sameLeaf second p v (raw p v) (some (answer 8)) &&
    decide (s2 = (seed.1 ++ [raw p v, raw p v], 9))
#guard independent

private def failOuter (p : Nibbles) (v : ByteArray) : Except String Node × Trace :=
  letI : KeccakQuery (ExceptT String (StateM Trace)) :=
    ⟨fun r => ExceptT.mk fun s => (.error "original failure", (s.1 ++ [r], s.2 + 1))⟩
  (mkLeaf (m := ExceptT String (StateM Trace)) p v).run.run seed
private def failInner (p : Nibbles) (v : ByteArray) : Except String (Node × Trace) :=
  letI : KeccakQuery (StateT Trace (Except String)) := ⟨fun _ _ => .error "original failure"⟩
  (mkLeaf (m := StateT Trace (Except String)) p v).run seed
#guard match failOuter (path []) (bytes []) with
  | (.ok node, s) => sameLeaf node (path []) (bytes []) (raw (path []) (bytes [])) none &&
      decide (s = seed)
  | _ => false
#guard match failInner (path []) (bytes []) with
  | .ok (node, s) => sameLeaf node (path []) (bytes []) (raw (path []) (bytes [])) none &&
      decide (s = seed)
  | _ => false
#guard match failOuter (path []) (bytes (List.replicate 29 0xab)) with
  | (.error e, s) => e == "original failure" &&
      decide (s = (seed.1 ++ [raw (path []) (bytes (List.replicate 29 0xab))], 8))
  | _ => false
#guard match failInner (path []) (bytes (List.replicate 29 0xab)) with
  | .error e => e == "original failure"
  | _ => false

private def firstFailure : Except String (Node × Node) × Trace :=
  letI : KeccakQuery (ExceptT String (StateM Trace)) :=
    ⟨fun r => ExceptT.mk fun s =>
      (if s.2 == 8 then .error "second query failed" else .ok (answer s.2),
        (s.1 ++ [r], s.2 + 1))⟩
  let action : ExceptT String (StateM Trace) (Node × Node) := do
    let first ← mkLeaf (path [1]) (bytes (List.replicate 40 1))
    let second ← mkLeaf (path [2]) (bytes (List.replicate 40 2))
    let _third ← mkLeaf (path [3]) (bytes (List.replicate 40 3))
    pure (first, second)
  action.run.run seed
#guard match firstFailure with
  | (.error e, s) => e == "second query failed" && s.2 == 9 &&
      decide (s.1 = seed.1 ++ [raw (path [1]) (bytes (List.replicate 40 1)),
        raw (path [2]) (bytes (List.replicate 40 2))])
  | _ => false

-- Private complete reply framing used by external actual-source comparisons.
private def wireBytes (b : ByteArray) : List Nat := b.size :: b.data.toList.map UInt8.toNat
private def wireHash : Option Hash32 → List Nat
  | none => [0]
  | some h => 1 :: h.toBytes.toByteArray.data.toList.map UInt8.toNat
private def wireNode : Node → List Nat
  | .leaf p v enc => 2 :: (p.size :: p.toList.map Fin.val) ++ wireBytes v ++
      wireBytes enc.rlp ++ wireHash enc.hash?
  | _ => [255]
private def emit (cases : List (Nibbles × ByteArray)) : IO Unit := do
  for ((p, v), i) in cases.zipIdx do
    let result := wireNode (mkLeaf (m := Id) p v)
    IO.println (s!"\{\"case\":{i},\"path\":{p.toList.map Fin.val}," ++
      s!"\"value\":{v.data.toList.map UInt8.toNat},\"result\":{result}}")

end STFSpec.Conformance.Commit.LeafGuards
