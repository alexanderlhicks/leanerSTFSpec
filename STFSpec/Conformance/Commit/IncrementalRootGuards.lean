/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Commit

/-!
# Complete supplied incremental-root controls

Library `EthConformance`. Complete input/cache/flag/constant, preimage/answer and
state/error observations distinguish local root effects from mutable source stages.
All support is private. Spec guidance: `STFSpec/informal/modules/EthCommit.md` C27/§7.
-/
namespace STFSpec.Conformance.Commit.IncrementalRootGuards
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

private def stored : Ref → Option Hash32
  | none => none
  | some (.hashed h) => some h
  | some (.leaf _ _ e) | some (.ext _ _ e) | some (.branch _ _ e) => e.hash?
private def raw (root : Ref) : ByteArray := (Rlp.encodeModel (childRef root)).toByteArray
private abbrev Trace := List (ByteArray × Hash32) × Nat
private def seed : Trace := ([(bytes [0,255,66], answer 91)], 7)
private def recording (e : Hash32) (root : Ref) (secured : Bool) (s : Trace) : Hash32 × Trace :=
  letI : KeccakQuery (StateM Trace) :=
    ⟨fun b state => (answer state.2, (state.1 ++ [(b, answer state.2)], state.2 + 1))⟩
  (mptRoot (m := StateM Trace) e ⟨secured, root⟩).run s
private def check (e : Hash32) (root : Ref) : Bool :=
  let expected := match root with
    | none => (e, seed)
    | some _ => match stored root with
      | some h => (h, seed)
      | none => (answer 7, (seed.1 ++ [(raw root, answer 7)], 8))
  decide (recording e root true seed = expected) &&
    decide (recording e root false seed = expected)
private def digits (n : Nat) : Nibbles :=
  path ((List.range n).map fun i => (⟨i % 16, Nat.mod_lt _ (by decide)⟩ : Fin 16))
private def leaf (n : Nat) (length : Nat) (h : Option Hash32 := none) : Node :=
  .leaf (digits n) (bytes ((List.range length).map UInt8.ofNat)) (enc [255,0,255] h)
private def nested : Node := .ext (path [])
  (.ext (path [0,15]) (leaf 3 40 (some (answer 22))) (enc [0,255] none))
  (enc [255] none)
#guard check (answer 37) none
#guard check (answer 37) (some (.hashed (answer 0)))
-- A clean stored zero hash bypasses a hashless 35-byte descendant.
#guard (raw (some (leaf 0 32))).size == 35
#guard check (answer 37) (some (.ext (path []) (leaf 0 32) (enc [255] (some (answer 0)))))
#guard check (answer 37) (some (leaf 0 0))
#guard raw (some (leaf 0 0)) != bytes [128]
#guard [28,29,30].map (fun n => (raw (some (leaf 0 n))).size) == [31,32,33]
#guard [0,1,2,63,64,65,108,110,508,510].all fun n =>
  [0,1,28,29,30,53,54,55,56,252,253,254,255,256].all fun size =>
    [none, some (answer 3)].all fun h => check (answer 37) (some (leaf n size h))
#guard (List.range 16).all fun n => check (answer 37)
  (some (.leaf (path [⟨n % 16, Nat.mod_lt _ (by decide)⟩]) (bytes [0,255,0]) (enc [255])))
#guard [0,1,15,16,17,33].all fun n =>
  [none, some (answer 3)].all fun h => check (answer 37)
    (some (.branch (Array.ofFn fun i : Fin n =>
      if i.val % 3 == 0 then none else if i.val % 3 == 1 then some (leaf i.val 2)
      else some (.hashed (answer i.val))) (bytes [0,255,0]) (enc [128,255] h)))
#guard check (answer 37) (some nested)
#guard check (answer 37) (some (.ext (path []) nested (enc [255] (some (answer 3)))))
-- Malformed raw caches never supply a root preimage or a parse failure.
#guard recording (answer 37) (some (.leaf (path [0,15]) (bytes [0,255]) (enc []))) true seed ==
  recording (answer 37) (some (.leaf (path [0,15]) (bytes [0,255]) (enc [255,128,255]))) true seed
#guard (answer 7).toBytes.toByteArray.data.toList == List.replicate 31 0 ++ [7]
#guard answer 7 != keccak256 (raw (some (leaf 0 29)))
private def repeated : Bool :=
  let root := some (leaf 0 29)
  let (h₁, s₁) := recording (answer 37) root true seed
  let (h₂, s₂) := recording (answer 37) root false s₁
  decide (h₁ = answer 7 ∧ h₂ = answer 8 ∧
    s₂ = (seed.1 ++ [(raw root, answer 7), (raw root, answer 8)], 9))
#guard repeated
private def failOuter (root : Ref) : Except String Hash32 × Trace :=
  letI : KeccakQuery (ExceptT String (StateM Trace)) :=
    ⟨fun b => ExceptT.mk fun s =>
      (.error "original failure", (s.1 ++ [(b, answer s.2)], s.2 + 1))⟩
  (rootHash (m := ExceptT String (StateM Trace)) (answer 37) root).run.run seed
private def failInner (root : Ref) : Except String (Hash32 × Trace) :=
  letI : KeccakQuery (StateT Trace (Except String)) := ⟨fun _ _ => .error "original failure"⟩
  (rootHash (m := StateT Trace (Except String)) (answer 37) root).run seed
private def outerOk (r : Except String Hash32 × Trace) (h : Hash32) (s : Trace) : Bool :=
  match r with
  | (.ok actual, state) => decide (actual = h ∧ state = s)
  | _ => false
private def innerOk (r : Except String (Hash32 × Trace)) (h : Hash32) (s : Trace) : Bool :=
  match r with
  | .ok (actual, state) => decide (actual = h ∧ state = s)
  | _ => false
private def outerError {α : Type} (r : Except String α × Trace)
    (error : String) (s : Trace) : Bool :=
  match r with
  | (.error actual, state) => actual == error && decide (state = s)
  | _ => false
private def innerError {α : Type} (r : Except String α) (error : String) : Bool :=
  match r with
  | .error actual => actual == error
  | _ => false
#guard outerOk (failOuter none) (answer 37) seed
#guard innerOk (failInner none) (answer 37) seed
#guard outerOk (failOuter (some (.hashed (answer 3)))) (answer 3) seed
#guard outerOk (failOuter (some (leaf 64 256 (some (answer 3))))) (answer 3) seed
#guard outerOk (failOuter (some (.ext (path []) nested (enc [] (some (answer 3))))))
  (answer 3) seed
#guard innerOk
  (failInner (some (.branch #[some nested] (bytes [0,255]) (enc [255] (some (answer 3))))))
  (answer 3) seed
#guard [28,29,30].all fun n =>
  outerError (failOuter (some (leaf 0 n))) "original failure"
    (seed.1 ++ [(raw (some (leaf 0 n)), answer 7)], 8) &&
    innerError (failInner (some (leaf 0 n))) "original failure"
private def firstFailure : Except String (Hash32 × Hash32) × Trace :=
  letI : KeccakQuery (ExceptT String (StateM Trace)) :=
    ⟨fun b => ExceptT.mk fun s =>
      (if s.2 == 8 then .error "second query failed" else .ok (answer s.2),
        (s.1 ++ [(b, answer s.2)], s.2 + 1))⟩
  let action : ExceptT String (StateM Trace) (Hash32 × Hash32) := do
    let h₁ ← rootHash (answer 37) (some (leaf 0 28))
    let h₂ ← mptRoot (answer 37) ⟨true, some nested⟩
    let _third ← rootHash (answer 37) (some (leaf 0 30))
    pure (h₁,h₂)
  action.run.run seed
#guard outerError firstFailure "second query failed" (seed.1 ++
  [(raw (some (leaf 0 28)), answer 7), (raw (some nested), answer 8)], 9)
private def firstFailureInner : Except String ((Hash32 × Hash32) × Trace) :=
  letI : KeccakQuery (StateT Trace (Except String)) :=
    ⟨fun b s => if s.2 == 8 then .error "second query failed"
      else if s.2 == 9 then .error "third query reached"
      else .ok (answer s.2, (s.1 ++ [(b,answer s.2)], s.2 + 1))⟩
  let action : StateT Trace (Except String) (Hash32 × Hash32) := do
    let h₁ ← rootHash (answer 37) (some (leaf 0 28))
    let h₂ ← mptRoot (answer 37) ⟨false, some nested⟩
    let _third ← rootHash (answer 37) (some (leaf 0 30))
    pure (h₁,h₂)
  action.run seed
#guard innerError firstFailureInner "second query failed"

-- Full concrete local queries/results for fresh original-source comparisons.
private def concrete (e : Hash32) (root : Ref) (secured : Bool) :
    Hash32 × List (ByteArray × Hash32) :=
  letI : KeccakQuery (StateM (List (ByteArray × Hash32))) :=
    ⟨fun b s => let h := keccak256 b; (h, s ++ [(b,h)])⟩
  (mptRoot (m := StateM (List (ByteArray × Hash32))) e ⟨secured,root⟩).run []
private def emit (cases : List (Bool × Hash32 × Ref)) : IO Unit := do
  for ((secured,e,root),i) in cases.zipIdx do
    let (h,qs) := concrete e root secured
    let queryFrames := qs.map fun (b,h) =>
      wireBytes b ++ h.toBytes.toByteArray.data.toList.map UInt8.toNat
    IO.println (s!"\{\"case\":{i},\"secured\":{secured}," ++
      s!"\"empty\":{e.toBytes.toByteArray.data.toList.map UInt8.toNat}," ++
      s!"\"input\":{wireRef root}," ++
      s!"\"result\":{h.toBytes.toByteArray.data.toList.map UInt8.toNat}," ++
      s!"\"queries\":{queryFrames}}")
end STFSpec.Conformance.Commit.IncrementalRootGuards
