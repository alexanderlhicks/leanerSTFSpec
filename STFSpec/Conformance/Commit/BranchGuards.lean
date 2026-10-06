/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Commit

/-!
# Complete reached-collapse controls

Library `EthConformance`. Full recursive public fields, query preimages and actual
answers are compared. Generic controls use explicit query instances. Source
stages and conditional cache/embedding correspondence remain separate.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/4/5/7 (Q60).
-/

namespace STFSpec.Conformance.Commit.BranchGuards
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
  | some (.ext p c e) => 3 :: wirePath p ++ wireRef (some c) ++ wireEnc e
  | some (.branch xs v e) => 4 :: xs.size ::
      (List.ofFn (fun i : Fin xs.size => wireRef xs[i])).flatten ++ wireBytes v ++ wireEnc e
termination_by sizeOf root
decreasing_by
  · simp only [Option.some.sizeOf_spec, Node.ext.sizeOf_spec]; omega
  · have h := Array.sizeOf_getElem xs i.val i.isLt
    simp only [Option.some.sizeOf_spec, Node.branch.sizeOf_spec, Fin.getElem_fin]; omega

private def wireResult : Except TrieError Ref → List Nat
  | .ok n => 0 :: wireRef n
  | .error (.unresolved h) => 1 :: 0 :: h.toBytes.toByteArray.data.toList.map UInt8.toNat
  | .error (.malformed (.occupancy n)) => [1,1,n]
  | .error (.malformed (.collapseIndex i)) => [1,2,i]
  | .error _ => [1,3]

private def item (n : Node) : RlpItem :=
  match n with
  | .leaf p v _ => .list [.bytes (nibbleListToCompactModel p.toList true).toByteArray, .bytes v]
  | .ext p c _ => .list [.bytes (nibbleListToCompactModel p.toList false).toByteArray,
      childRef (some c)]
  | .branch xs v _ => .list (xs.toList.map childRef ++ [.bytes v])
  | .hashed h => .bytes h.toBytes.toByteArray
private def top : Node → Enc
  | .leaf _ _ e | .ext _ _ e | .branch _ _ e => e
  | .hashed _ => enc []
private def replace : Node → Enc → Node
  | .leaf p v _, e => .leaf p v e
  | .ext p c _, e => .ext p c e
  | .branch xs v _, e => .branch xs v e
  | .hashed h, _ => .hashed h
private abbrev Trace := List ByteArray × Nat
private def seed : Trace := ([bytes [0,255,66]], 7)
private abbrev query : KeccakQuery (StateM Trace) :=
  ⟨fun r s => (answer s.2, (s.1 ++ [r], s.2 + 1))⟩
private def recording (xs : Array Ref) (v : ByteArray) (s : Trace) :
    Except TrieError Ref × Trace :=
  (@mkBranch (StateM Trace) inferInstance query xs v).run s

-- Independent List census and raw-byte model; literal source-cache gates.
private def complete (raw : ByteArray) (make : Enc → Node) (s : Trace) : Node × Trace :=
  if raw.size < 32 then (make ⟨raw, none⟩, s)
  else (make ⟨raw, some (answer s.2)⟩, (s.1 ++ [raw], s.2 + 1))
private def splice (i : Nat) (hi : i < 16) (n : Node) (s : Trace) : Node × Trace :=
  let headPath := path [⟨i,hi⟩]
  match n with
  | .leaf p v _ =>
    let joined := path (headPath.toList ++ p.toList)
    complete (Rlp.encodeModel (.list [
      .bytes (nibbleListToCompactModel joined.toList true).toByteArray,
      .bytes v])).toByteArray (Node.leaf joined v) s
  | .ext p c _ =>
    let joined := path (headPath.toList ++ p.toList)
    complete (Rlp.encodeModel (.list [
      .bytes (nibbleListToCompactModel joined.toList false).toByteArray,
      childRef (some c)])).toByteArray (Node.ext joined c) s
  | _ => complete (Rlp.encodeModel (.list [
      .bytes (nibbleListToCompactModel headPath.toList false).toByteArray,
      childRef (some n)])).toByteArray (Node.ext headPath n) s
private def witnessed (n : Node) (s : Trace) : Node × Trace :=
  let e := top n
  if e.hash?.isSome then (n,s)
  else if 32 ≤ e.rlp.size then (n,(s.1 ++ [e.rlp],s.2+1))
  else complete (Rlp.encodeModel (item n)).toByteArray (replace n) s
private def model (xs : Array Ref) (v : ByteArray) (s : Trace) : Except TrieError Ref × Trace :=
  let present := (xs.toList.zipIdx).filterMap fun (n,i) => n.map (i,·)
  match present with
  | [] =>
    if v.size = 0 then (.error (.malformed (.occupancy 0)),s)
    else
      let (n,t) := complete (Rlp.encodeModel (.list [.bytes (bytes [32]),.bytes v])).toByteArray
        (Node.leaf (path []) v) s
      (.ok (some n),t)
  | [(i,n)] =>
    if v.size = 0 then
      match n with
      | .hashed h => (.error (.unresolved h),s)
      | _ =>
        let (updated,t) := witnessed n s
        if hi : i < 16 then let (out,u) := splice i hi updated t; (.ok (some out),u)
        else (.error (.malformed (.collapseIndex i)),t)
    else
      let (n,t) := complete
        (Rlp.encodeModel (.list (xs.toList.map childRef ++ [.bytes v]))).toByteArray
        (Node.branch xs v) s
      (.ok (some n),t)
  | _ =>
    let (n,t) := complete
      (Rlp.encodeModel (.list (xs.toList.map childRef ++ [.bytes v]))).toByteArray
      (Node.branch xs v) s
    (.ok (some n),t)
private def check (xs : Array Ref) (v : ByteArray) : Bool :=
  let (actual,t) := recording xs v seed
  let (expected,u) := model xs v seed
  wireResult actual == wireResult expected && decide (t = u)
private def sole (i : Nat) (n : Node) : Array Ref :=
  Array.replicate i none |>.push (some n)
private def leaf (len : Nat) (rawLen : Nat) (h : Option Hash32) : Node :=
  .leaf (path [0,15]) (bytes ((List.range len).map UInt8.ofNat))
    (enc (List.replicate rawLen 255) h)
private def nested : Node := .ext (path [])
  (.ext (path [0,15]) (.branch #[none,some (.hashed (answer 83)),none] (bytes [0,255])
    (enc [255] (some (answer 61)))) (enc [0] (some (answer 42)))) (enc [255] none)
#guard check #[] (bytes [])
#guard check (Array.replicate 257 none) (bytes [0,255])
#guard [0,15,16,255,256].all fun i =>
  [0,28,29,30,40].all fun len =>
    [0,31,32,33].all fun r =>
      [none,some (answer 91)].all fun h => check (sole i (leaf len r h)) (bytes [])
#guard [0,15,16,255,256].all fun i =>
  check (sole i (.hashed (answer 9))) (bytes []) && check (sole i (.hashed (answer 9))) (bytes [0])
#guard [0,1,15,16,17,33,256].all fun arity =>
  [[],[0,255]].all fun v => check (Array.replicate arity (some nested)) (bytes v)
#guard [0,31,32,33].all fun r =>
  [none,some (answer 90)].all fun h =>
    check (sole 15 (.branch #[none,some nested,none] (bytes [0,255])
      (enc (List.replicate r 255) h))) (bytes [])
#guard [0,31,32,33].all fun r =>
  check (sole 0 (.ext (path []) nested (enc (List.replicate r 128) none))) (bytes [])
#guard [28,29,30].map (fun n =>
  (Rlp.encodeModel (.list [.bytes (bytes [32]),
    .bytes (bytes (List.replicate n 0))])).length) == [31,32,33]
-- Actual retained-branch calls cross the strict own-encoding threshold.
private def retainedThreshold (valueWidth expectedWidth : Nat) : Bool :=
  let child := Node.leaf (path []) (bytes []) (enc [] none)
  let xs := #[some child, some child]
  let value := bytes (List.replicate valueWidth 0)
  let raw := (Rlp.encodeModel (.list (xs.toList.map childRef ++ [.bytes value]))).toByteArray
  let (actual, trace) := recording xs value seed
  let hash := if expectedWidth < 32 then none else some (answer seed.2)
  let expected := Node.branch xs value ⟨raw, hash⟩
  let expectedTrace := if expectedWidth < 32 then seed else (seed.1 ++ [raw], seed.2 + 1)
  raw.size == expectedWidth && wireResult actual == wireResult (.ok (some expected)) &&
    decide (trace = expectedTrace)
#guard retainedThreshold 23 31
#guard retainedThreshold 24 32
#guard retainedThreshold 25 33

-- Census must retain a sole position even when later slots are absent.
private def paddedSole (i : Nat) (n : Node) : Array Ref :=
  ((List.range 16).map fun j => if j == i then some n else none).toArray
private def trailingSlotChecks : Bool :=
  check (Array.replicate 16 none) (bytes []) &&
    [0,3,15].all fun i =>
      check (paddedSole i (leaf 0 0 (some (answer 91)))) (bytes []) &&
      check (paddedSole i (.hashed (answer 9))) (bytes [])
#guard trailingSlotChecks

-- Repeat exactly the same input: answers at each occurrence remain independent.
private def repeated : Bool :=
  let xs := sole 0 (leaf 40 33 none)
  let (a,t) := recording xs (bytes []) seed
  let (b,u) := recording xs (bytes []) t
  let (ea,et) := model xs (bytes []) seed
  let (eb,eu) := model xs (bytes []) et
  wireResult a == wireResult ea && wireResult b == wireResult eb && decide (u = eu)
#guard repeated

private def failOuter (xs : Array Ref) (v : ByteArray) (failAt : Nat) :
    Except String (Except TrieError Ref) × Trace :=
  let q : KeccakQuery (ExceptT String (StateM Trace)) :=
    ⟨fun r => ExceptT.mk fun s =>
      (if s.2 = failAt then .error "query failed" else .ok (answer s.2), (s.1 ++ [r],s.2+1))⟩
  (@mkBranch (ExceptT String (StateM Trace)) inferInstance q xs v).run.run seed
private def failInner (xs : Array Ref) (v : ByteArray) (failAt : Nat) :
    Except String (Except TrieError Ref × Trace) :=
  let q : KeccakQuery (StateT Trace (Except String)) :=
    ⟨fun r s => if s.2 = failAt then .error "query failed"
      else .ok (answer s.2,(s.1 ++ [r],s.2+1))⟩
  (@mkBranch (StateT Trace (Except String)) inferInstance q xs v).run seed
#guard match failOuter (sole 256 (leaf 0 32 none)) (bytes []) 7 with
  | (.error e,s) => e == "query failed" &&
      decide (s = (seed.1 ++ [bytes (List.replicate 32 255)],8))
  | _ => false
#guard match failInner (sole 256 (leaf 0 32 none)) (bytes []) 7 with
  | .error e => e == "query failed"
  | _ => false
#guard match failOuter (sole 256 (.hashed (answer 5))) (bytes []) 7 with
  | (.ok (.error (.unresolved h)),s) => h == answer 5 && decide (s = seed)
  | _ => false
#guard match failOuter (sole 0 (leaf 40 32 none)) (bytes []) 8 with
  | (.error e,s) => e == "query failed" && s.1.length == 3 && s.2 == 9 &&
      s.1[1]? == some (bytes (List.replicate 32 255)) &&
      s.1[2]? == some (Rlp.encodeModel (.list [
        .bytes (nibbleListToCompactModel [0,0,15] true).toByteArray,
        .bytes (bytes ((List.range 40).map UInt8.ofNat))])).toByteArray
  | _ => false
#guard match failInner (sole 0 (leaf 40 32 none)) (bytes []) 8 with
  | .error e => e == "query failed"
  | _ => false

-- A deliberately nonlawful syntax-sensitive Monad: bind/pure cannot be erased.
private structure Syntax (α : Type) where
  value : α
  events : List Nat
private instance : Monad Syntax where
  pure a := ⟨a,[0]⟩
  bind a k := let b := k a.value; ⟨b.value,a.events ++ [1] ++ b.events⟩
private abbrev syntaxQuery : KeccakQuery Syntax := ⟨fun _ => ⟨answer 7,[2]⟩⟩
private def syntaxRun (xs : Array Ref) (v : ByteArray) : List Nat :=
  (@mkBranch Syntax inferInstance syntaxQuery xs v).events
#guard syntaxRun #[] (bytes []) == [0]
#guard syntaxRun (sole 0 (.hashed (answer 3))) (bytes []) == [0]
#guard syntaxRun (sole 16 (leaf 0 32 none)) (bytes []) == [2,1,0]
#guard syntaxRun (sole 0 (leaf 0 33 (some (answer 3)))) (bytes []) == [0,1,0]
#guard syntaxRun (sole 0 (leaf 40 32 none)) (bytes []) == [2,1,2,1,0,1,0]

-- Driver extracts this complete observer without importing private production support.
private def emit (cases : List (Array Ref × ByteArray)) : IO Unit := do
  for ((xs,v),i) in cases.zipIdx do
    let result := mkBranch (m := Id) xs v
    let (stateResult,t) := recording xs v seed
    IO.println (s!"\{\"case\":{i},\"input\":{wireRef (some (.branch xs v (enc [])))}" ++
      s!",\"result\":{wireResult result},\"stateResult\":{wireResult stateResult}" ++
      s!",\"queries\":{t.1.map wireBytes},\"counter\":{t.2}}")

end STFSpec.Conformance.Commit.BranchGuards
