/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Commit.Update

/-!
# Complete bare-insertion controls

Library `EthConformance`. Public operations and providers only. Every observation
retains recursive fields, actual arity, full raw/cache bytes, error payloads and
ordered query preimages/answers. Generic oracles never fall back to concrete Id.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §4/§7.0.10.
-/
namespace STFSpec.Conformance.Commit.UpdateGuards
open STFSpec.Base STFSpec.Codec STFSpec.Hash STFSpec.Commit
variable {m : Type → Type} [Monad m] [KeccakQuery m]

private def bytes (xs : List UInt8) : ByteArray := xs.toByteArray
private def path (xs : List (Fin 16)) : Nibbles := Nibbles.ofList xs
private def answer (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)
private def enc (raw : List UInt8 := [255,0]) (h : Option Hash32 := some (answer 91)) : Enc :=
  ⟨bytes raw, h⟩
private def wireBytes (b : ByteArray) : List Nat := b.size :: b.data.toList.map UInt8.toNat
private def wireHash (h : Hash32) : List Nat := h.toBytes.toByteArray.data.toList.map UInt8.toNat
private def wireEnc (e : Enc) : List Nat := wireBytes e.rlp ++
  match e.hash? with | none => [0] | some h => 1 :: wireHash h
private def wirePath (p : Nibbles) : List Nat := p.size :: p.toList.map Fin.val
private def wireRef (root : Ref) : List Nat :=
  match root with
  | none => [0]
  | some (.hashed h) => 1 :: wireHash h
  | some (.leaf p v e) => 2 :: wirePath p ++ wireBytes v ++ wireEnc e
  | some (.ext p c e) => 3 :: wirePath p ++ wireRef (some c) ++ wireEnc e
  | some (.branch xs v e) => 4 :: xs.size ::
      (List.ofFn (fun i : Fin xs.size => wireRef xs[i])).flatten ++ wireBytes v ++ wireEnc e
termination_by sizeOf root
decreasing_by
  · simp only [Option.some.sizeOf_spec, Node.ext.sizeOf_spec]; omega
  · have h := Array.sizeOf_getElem xs i.val i.isLt
    simp only [Option.some.sizeOf_spec, Node.branch.sizeOf_spec, Fin.getElem_fin]; omega

private def wireMalformed : Malformed → List Nat
  | .rlp => [0]
  | .nonEmptyString => [1]
  | .compactPathList => [2]
  | .compactEmpty => [3]
  | .leafValueList => [4]
  | .pathEmpty => [5]
  | .badListLength n => [6,n]
  | .refLength n => [7,n]
  | .extChild => [8]
  | .occupancy n => [9,n]
  | .cycle => [10]
  | .branchIndex i n => [11,i,n]
  | .collapseIndex i => [12,i]
private def wireResult : Except TrieError Ref → List Nat
  | .ok n => 0 :: wireRef n
  | .error (.missingRoot h) => 1 :: wireHash h
  | .error (.malformed why) => 2 :: wireMalformed why
  | .error (.unresolved h) => 3 :: wireHash h

private def complete (item : RlpItem) (make : Enc → Node) : m Node :=
  let raw := (Rlp.encodeModel item).toByteArray
  if raw.size < 32 then pure (make ⟨raw,none⟩)
  else KeccakQuery.keccak raw >>= fun h => pure (make ⟨raw,some h⟩)
private def leafModel (p : List (Fin 16)) (v : ByteArray) : m Node :=
  complete (.list [.bytes (nibbleListToCompactModel p true).toByteArray,.bytes v])
    (Node.leaf (path p) v)
private def extModel (p : List (Fin 16)) (c : Node) : m Node :=
  complete (.list [.bytes (nibbleListToCompactModel p false).toByteArray,childRef (some c)])
    (Node.ext (path p) c)
private def branchModel (xs : List Ref) (v : ByteArray) : m Node :=
  complete (.list (xs.map childRef ++ [.bytes v])) (Node.branch xs.toArray v)
private theorem ext_smaller (p : Nibbles) (c : Node) (e : Enc) :
    sizeOf (some c : Ref) < sizeOf (some (.ext p c e) : Ref) := by
  simp only [Option.some.sizeOf_spec, Node.ext.sizeOf_spec]; omega
private theorem branch_smaller (xs : Array Ref) (v : ByteArray) (e : Enc)
    (i : Nat) (hi : i < xs.size) :
    sizeOf (xs[i]'hi) < sizeOf (some (.branch xs v e) : Ref) := by
  have h := Array.sizeOf_getElem xs i hi
  simp only [Option.some.sizeOf_spec, Node.branch.sizeOf_spec]; omega

private def model (root : Ref) (key : List (Fin 16)) (v : ByteArray)
    (k : Node → m (Except TrieError Ref)) : m (Except TrieError Ref) :=
  match root with
  | none => leafModel key v >>= k
  | some (.hashed h) => pure (.error (.unresolved h))
  | some (.leaf p old _) =>
    if p.toList = key then leafModel p.toList v >>= k
    else
      let l := commonPrefixLengthModel p.toList key
      let finish := fun xs terminal => branchModel xs terminal >>= fun b =>
        if 0 < l then extModel (p.toList.take l) b >>= k else k b
      let newSide := fun xs terminal =>
        match key.drop l with
        | [] => finish xs v
        | i :: tail => leafModel tail v >>= fun n =>
          finish (xs.set i.val (some n)) terminal
      match p.toList.drop l with
      | [] => newSide (List.replicate 16 none) old
      | i :: tail => leafModel tail old >>= fun n =>
        newSide ((List.replicate 16 none).set i.val (some n)) ByteArray.empty
  | some (.ext p child _enc) =>
    let l := commonPrefixLengthModel p.toList key
    if l = p.size then model (some child) (key.drop l) v
      (fun child' => extModel p.toList child' >>= k)
    else
      let finish := fun xs terminal => branchModel xs terminal >>= fun b =>
        if 0 < l then extModel (p.toList.take l) b >>= k else k b
      let newSide := fun xs =>
        match key.drop l with
        | [] => finish xs v
        | i :: tail => leafModel tail v >>= fun n =>
          finish (xs.set i.val (some n)) ByteArray.empty
      match p.toList.drop l with
      | [] => newSide (List.replicate 16 none)
      | i :: [] => newSide ((List.replicate 16 none).set i.val (some child))
      | i :: j :: tail => extModel (j :: tail) child >>= fun n =>
        newSide ((List.replicate 16 none).set i.val (some n))
  | some (.branch xs old _enc) =>
    match key with
    | [] => branchModel xs.toList v >>= k
    | i :: tail =>
      if hi : i.val < xs.size then model (xs[i.val]'hi) tail v
        (fun child' => branchModel (xs.toList.set i.val (some child')) old >>= k)
      else pure (.error (.malformed (.branchIndex i.val xs.size)))
termination_by sizeOf root
decreasing_by
  · exact ext_smaller _ _ _
  · exact branch_smaller _ _ _ _ _

private abbrev Trace := List (ByteArray × Hash32) × Nat
private def seed (n : Nat) : Trace := ([(bytes [0,255,66],answer 199)],n)
private def recording (t : Ref) (key : Nibbles) (v : ByteArray) (initial : Trace)
    (constant : Bool := false) : Except TrieError Ref × Trace :=
  let q : KeccakQuery (StateM Trace) := ⟨fun raw s =>
    let h := answer (if constant then 93 else s.2)
    (h,(s.1 ++ [(raw,h)],s.2+1))⟩
  (@update (StateM Trace) inferInstance q t key v).run initial
private def expected (t : Ref) (key : Nibbles) (v : ByteArray) (initial : Trace)
    (constant : Bool := false) : Except TrieError Ref × Trace :=
  let q : KeccakQuery (StateM Trace) := ⟨fun raw s =>
    let h := answer (if constant then 93 else s.2)
    (h,(s.1 ++ [(raw,h)],s.2+1))⟩
  (@model (StateM Trace) inferInstance q t key.toList v (fun n => pure (.ok (some n)))).run initial
private def check (t : Ref) (key : Nibbles) (v : ByteArray) : Bool :=
  [0,7].all fun n => [false,true].all fun constant =>
    let (a,s) := recording t key v (seed n) constant
    let (b,u) := expected t key v (seed n) constant
    wireResult a == wireResult b && decide (s = u)
private def leaf (p : List (Fin 16)) (len : Nat := 2) : Node :=
  .leaf (path p) (bytes ((List.range len).map UInt8.ofNat)) (enc [])
private def variants : List Node :=
  [leaf [0,15],.ext (path []) (leaf [0]) (enc [128] none),
    .branch #[none,some (.hashed (answer 17)),some (leaf [])] (bytes [0,255]) (enc [255]),
    .hashed (answer 31)]
private def branch (arity : Nat) (selected : Nat) (child : Ref) : Ref :=
  some (.branch ((Array.replicate arity none).setIfInBounds selected child)
    (bytes [0,255]) (enc [255,0]))

-- U01–03: absent/stub/equal leaf, including direct empty replacement.
#guard [[],[0],[15,0]].all fun p => [0,1,40].all fun n =>
  check none (path p) (bytes (List.replicate n 255))
#guard [[],[0],[15,0]].all fun p => check (some (.hashed (answer 9))) (path p) (bytes [])
#guard [[],[0],[15,0]].all fun p => [0,1,40].all fun n =>
  check (some (leaf p)) (path p) (bytes (List.replicate n 0))
-- U04–08: first/shared-prefix/proper-prefix/odd-last-digit leaf splits.
#guard [([0],[15]),([0,15,0],[0,15,1]),([],[0]),([0],[]),
  ([0,15,0,15,1],[0,15,0,15,2])].all fun (p,k) =>
  [0,2,40].all fun old => [0,1,40].all fun n =>
    check (some (leaf p old)) (path k) (bytes (List.replicate n 255))
-- U09–12: original-child descent, with matched empty and nested empty extensions.
#guard variants.all fun c => [[],[0,15]].all fun p =>
  check (some (.ext (path p) c (enc [255]))) (path (p ++ [0,15])) (bytes [])
#guard variants.all fun c => check
  (some (.ext (path []) (.ext (path []) c (enc [0])) (enc [255])))
  (path [0,15]) (bytes [0,255])
-- U13–17: preserving suffix 1/longer wrappers; new terminal; exhausted key.
#guard variants.all fun c => [([0],[15]),([0,1],[15]),([0,15],[0,1]),
  ([0,15,0],[0,1]),([0,15],[]),([0,15],[0])].all fun (p,k) =>
  [[],[0,255]].all fun v => check (some (.ext (path p) c (enc []))) (path k) (bytes v)
-- U18–20: terminal before bounds, with every supplied slot retained.
#guard [0,1,15,16,17,257].all fun arity => [none,some (leaf []),
  some (.hashed (answer 7))].all fun child => [[],[0,255]].all fun v =>
    check (some (.branch (Array.replicate arity child) (bytes v) (enc [])))
      (path []) (bytes v) &&
    check (some (.branch (Array.replicate arity child) (bytes v) (enc [])))
      (path []) (bytes [])
-- U21–24: selected absence/resolved/stub/missing at actual bounds.
#guard [0,1,15,16,17,257].all fun arity => [0,14,15].all fun digit =>
  [none,some (leaf []),some (.hashed (answer 7))].all fun c =>
    check (branch arity digit.val c) (path [digit]) (bytes [0,255])
-- U25: arbitrary unselected fields/caches and stubs at every available off-path slot.
#guard [1,15,16,17,257].all fun arity => variants.all fun c =>
  check (some (.branch ((Array.replicate arity (some c)).setIfInBounds 0 none)
    (bytes [255]) (enc [0] none))) (path [0,15]) (bytes [0,255])
-- U26: bounds/stub precedence, including retained stub during a divergent split.
#guard check (branch 0 0 (some (.hashed (answer 9)))) (path [0]) (bytes []) &&
  check (some (.ext (path [0]) (.branch #[] (bytes []) (enc [])) (enc [])))
    (path [0,15]) (bytes []) &&
  check (some (.ext (path [0]) (.hashed (answer 9)) (enc []))) (path [15]) (bytes [])
-- U27: own raw widths 31/32/33 for all three preserving constructors.
#guard [28,29,30].all fun n => check none (path []) (bytes (List.replicate n 0))
#guard [50,52,54].all fun n => check
  (some (.ext (path (List.replicate n 0))
    (.leaf (path []) (bytes []) (enc [] none)) (enc [])))
  (path (List.replicate n 0)) (bytes [])
#guard [29,30,31].all fun n => check
  (some (.branch #[] (bytes []) (enc []))) (path []) (bytes (List.replicate n 0))
#guard [28,29,30].map (fun n =>
  (Rlp.encodeModel (.list [.bytes (bytes [32]),.bytes (bytes (List.replicate n 0))])).length)
    == [31,32,33]
#guard [50,52,54].map (fun n =>
  (Rlp.encodeModel (.list
    [.bytes (nibbleListToCompactModel (List.replicate n 0) false).toByteArray,
    childRef (some (.leaf (path []) (bytes []) (enc [] none)))])).length) == [31,32,33]
#guard [29,30,31].map (fun n => (Rlp.encodeModel (.list [.bytes
  (bytes (List.replicate n 0))])).length) == [31,32,33]
-- U28: odd/even long joins and full RLP payload boundaries.
#guard [1,2,49,50,51,110,111,510,511].all fun sharedLen =>
  [52,53,54,253,254,255,256].all fun n =>
  check (some (leaf (List.replicate sharedLen 0 ++ [1]) n))
    (path (List.replicate sharedLen 0 ++ [15])) (bytes (List.replicate n 255))

private def chain : Ref := some (.ext (path [0,15])
  (.ext (path []) (leaf [0,1] 40) (enc [])) (enc []))
private def chainKey : Nibbles := path [0,15,0,2]
private def chainValue : ByteArray := bytes (List.replicate 40 255)
-- U29: two calls, with genuinely state-dependent and repeated complete answers.
private def repeated : Bool := [0,7].all fun n => [false,true].all fun constant =>
  let (a,s) := recording chain chainKey chainValue (seed n) constant
  let (b,t) := recording chain chainKey chainValue s constant
  let (ea,es) := expected chain chainKey chainValue (seed n) constant
  let (eb,et) := expected chain chainKey chainValue es constant
  wireResult a == wireResult ea && wireResult b == wireResult eb && decide (t = et)
#guard repeated

private def wideAnswer (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat
  ((List.range 32).foldl (fun a i => a * 256 + (n + 17*i) % 256) 0))
private def wideCheck : Bool := [0,7].all fun initial => [false,true].all fun constant =>
  let q : KeccakQuery (StateM Trace) := ⟨fun raw s =>
    let h := wideAnswer (if constant then 93 else s.2)
    (h,(s.1 ++ [(raw,h)],s.2+1))⟩
  let a := (@update (StateM Trace) inferInstance q chain chainKey chainValue).run (seed initial)
  let b := (@model (StateM Trace) inferInstance q chain chainKey.toList chainValue
    (fun n => pure (.ok (some n)))).run (seed initial)
  wireResult a.1 == wireResult b.1 && decide (a.2 = b.2) &&
    (a.2.1.drop 1).all fun (_,h) => h.toBytes.toByteArray.data.toList[1]? != some 0
#guard wideCheck

private def failOuter (t : Ref) (key : Nibbles) (v : ByteArray) (failAt : Nat)
    (useModel : Bool) : Except String (Except TrieError Ref) × Trace :=
  let q : KeccakQuery (ExceptT String (StateM Trace)) :=
    ⟨fun raw => ExceptT.mk fun s =>
      let h := answer s.2
      (if s.2 = failAt then .error "query failed" else .ok h,
        (s.1 ++ [(raw,h)],s.2+1))⟩
  let action := if useModel then
    @model (ExceptT String (StateM Trace)) inferInstance q t key.toList v
      (fun n => pure (.ok (some n)))
    else @update (ExceptT String (StateM Trace)) inferInstance q t key v
  action.run.run (seed 7)
private def failInner (t : Ref) (key : Nibbles) (v : ByteArray) (failAt : Nat)
    (useModel : Bool) :
    Except (String × List (ByteArray × Hash32)) (Except TrieError Ref × Trace) :=
  -- The separate spy prefix travels in the underlying error, not an absent StateT result.
  let q : KeccakQuery (StateT Trace (Except (String × List (ByteArray × Hash32)))) :=
    ⟨fun raw s =>
      let h := answer s.2
      if s.2 = failAt then .error ("query failed",s.1 ++ [(raw,h)])
      else .ok (h,(s.1 ++ [(raw,h)],s.2+1))⟩
  let action := if useModel then
    @model (StateT Trace (Except (String × List (ByteArray × Hash32))))
      inferInstance q t key.toList v (fun n => pure (.ok (some n)))
    else @update (StateT Trace (Except (String × List (ByteArray × Hash32))))
      inferInstance q t key v
  action.run (seed 7)
private def outerWire (a : Except String (Except TrieError Ref) × Trace) :
    List Nat × Trace :=
  (match a.1 with
    | .ok r => 0 :: wireResult r
    | .error e => 1 :: e.toList.map Char.toNat, a.2)
private def innerWire (a : Except (String × List (ByteArray × Hash32))
    (Except TrieError Ref × Trace)) : List Nat × Trace :=
  match a with
  | .ok (r,s) => (0 :: wireResult r,s)
  | .error (e,spy) => (1 :: e.toList.map Char.toNat,(spy,0))
-- U30: each actual query ordinal in both transformer orders; every full prefix retained.
#guard let (_,s) := recording chain chainKey chainValue (seed 7)
  3 ≤ s.2 - 7 && (List.range (s.2-7)).all fun i =>
    decide (outerWire (failOuter chain chainKey chainValue (7+i) false) =
      outerWire (failOuter chain chainKey chainValue (7+i) true)) &&
    decide (innerWire (failInner chain chainKey chainValue (7+i) false) =
      innerWire (failInner chain chainKey chainValue (7+i) true)) &&
    match failOuter chain chainKey chainValue (7+i) false,
      failInner chain chainKey chainValue (7+i) false with
    | (.error e,t),.error (f,spy) =>
      e == "query failed" && f == e && t.2 == 8+i &&
        decide (t.1 = s.1.take (i+2)) && decide (spy = t.1)
    | _,_ => false
#guard let stub := branch 1 0 (some (.hashed (answer 17)))
  match failOuter stub (path [0]) chainValue 7 false with
  | (.ok (.error (.unresolved h)),s) => h == answer 17 && decide (s = seed 7)
  | _ => false

private structure Count (α : Type) where
  value : α
  ticks : Nat
private instance : Monad Count where
  pure a := ⟨a,1⟩
  bind a k := let b := k a.value; ⟨b.value,2*a.ticks+b.ticks+1⟩
private abbrev countQuery : KeccakQuery Count := ⟨fun _ => ⟨answer 77,5⟩⟩
private def countCheck (t : Ref) (key : Nibbles) (v : ByteArray) : Bool :=
  let a := @update Count inferInstance countQuery t key v
  let b := @model Count inferInstance countQuery t key.toList v (fun n => pure (.ok (some n)))
  wireResult a.value == wireResult b.value && a.ticks == b.ticks
-- U31: syntax-sensitive complete insertion and the unreassociated bind counterexample.
#guard countCheck chain chainKey chainValue
#guard let a : Count Nat := ⟨0,5⟩
  let b := fun (_ : Nat) => (⟨0,5⟩ : Count Nat)
  let c := fun (_ : Nat) => (⟨0,5⟩ : Count Nat)
  ((a >>= b) >>= c).ticks == 38 && (a >>= fun x => b x >>= c).ticks == 27
#guard [0,1,15,16,17,257].all fun arity => [0,14,15].all fun digit =>
  let a := @update Count inferInstance countQuery (branch arity 0 none) (path [digit]) (bytes [])
  countCheck (branch arity 0 none) (path [digit]) (bytes []) &&
    (if arity ≤ digit.val then a.ticks == 1 else true)

-- Complete framed public-operation observer; the source driver extracts only this
-- test-local observer/support, never a private production declaration.
private def emit (cases : List (Ref × Nibbles × ByteArray)) : IO Unit := do
  for ((t,key,v),i) in cases.zipIdx do
    let result := update (m := Id) t key v
    let (stateResult,s) := recording t key v (seed 7)
    let frame := s!"\{\"case\":{i},\"input\":{wireRef t}," ++
      s!"\"key\":{key.toList.map Fin.val},\"value\":{v.data.toList.map UInt8.toNat}," ++
      s!"\"result\":{wireResult result},\"stateResult\":{wireResult stateResult}," ++
      s!"\"queries\":{s.1.map (fun x => wireBytes x.1)}," ++
      s!"\"answers\":{s.1.map (fun x => wireHash x.2)},\"counter\":{s.2}}"
    IO.println frame

end STFSpec.Conformance.Commit.UpdateGuards
