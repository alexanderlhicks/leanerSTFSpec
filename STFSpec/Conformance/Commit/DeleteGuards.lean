/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Commit.Delete

/-!
# Complete bare-deletion controls

Library `EthConformance`. Public operations/providers only. The copying reference
below pins compiled regression behavior; its definitions mirror the private
production reference and are not independent source expectations. Separate literal
controls and the pinned-source driver provide independent expectations. Complete
observations retain every recursive cache, actual arity, query/answer byte and first
failure in both transformer orders. No production private helper is imported.
Generic action and source mutable history are separate statements.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` C19/C24/C25/§7.0.10.
-/
namespace STFSpec.Conformance.Commit.DeleteGuards
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

private def branchItemReference (xs : List Ref) (v : ByteArray) : RlpItem :=
  .list (xs.map childRef ++ [.bytes v])

private def freshLeafReference (p : List (Fin 16)) (v : ByteArray) : m Node :=
  let raw := (Rlp.encodeModel (.list
    [.bytes (nibbleListToCompactModel p true).toByteArray, .bytes v])).toByteArray
  if raw.size < 32 then pure (.leaf (Nibbles.ofList p) v ⟨raw, none⟩)
  else KeccakQuery.keccak raw >>= fun answer =>
    pure (.leaf (Nibbles.ofList p) v ⟨raw, some answer⟩)

private def freshExtReference (p : List (Fin 16)) (child : Node) : m Node :=
  let raw := (Rlp.encodeModel (.list
    [.bytes (nibbleListToCompactModel p false).toByteArray, childRef (some child)])).toByteArray
  if raw.size < 32 then pure (.ext (Nibbles.ofList p) child ⟨raw, none⟩)
  else KeccakQuery.keccak raw >>= fun answer =>
    pure (.ext (Nibbles.ofList p) child ⟨raw, some answer⟩)

private def freshBranchReference (xs : List Ref) (v : ByteArray) : m Node :=
  let raw := (Rlp.encodeModel (branchItemReference xs v)).toByteArray
  if raw.size < 32 then pure (.branch xs.toArray v ⟨raw, none⟩)
  else KeccakQuery.keccak raw >>= fun answer => pure (.branch xs.toArray v ⟨raw, some answer⟩)

private structure ChangedResult where
  ref : Ref
  sameOrigin : Bool
  dirty : Bool

private def collapseReferenceThen {m : Type → Type} [Monad m] [KeccakQuery m]
    (xs : List Ref) (v : ByteArray)
    (k : ChangedResult → m (Except TrieError Ref)) : m (Except TrieError Ref) :=
  if v.size = 0 && xs.any Option.isSome = false then
    pure (.error (.malformed (.occupancy 0)))
  else
    mkBranch xs.toArray v >>= fun result =>
      match result with
      | .error e => pure (.error e)
      | .ok ref => k ⟨ref, (match ref with | some (.branch ..) => true | _ => false),
          ref.isSome⟩

private def extReferenceThen (p : List (Fin 16)) (r : ChangedResult)
    (k : ChangedResult → m (Except TrieError Ref)) : m (Except TrieError Ref) :=
  match r.ref with
  | none => k ⟨none, false, false⟩
  | some (.hashed h) => pure (.error (.unresolved h))
  | some n@(.leaf ..) | some n@(.ext ..) =>
    mkExt (Nibbles.ofList p) n >>= fun parent => k ⟨some parent, false, true⟩
  | some n@(.branch ..) =>
    freshExtReference p n >>= fun parent =>
      k ⟨some parent, true, (!r.sameOrigin || r.dirty)⟩

private def branchReferenceThen (xs : List Ref) (v : ByteArray) (i : Nat)
    (r : ChangedResult) (k : ChangedResult → m (Except TrieError Ref)) :
    m (Except TrieError Ref) :=
  match r.ref with
  | some (.hashed h) => pure (.error (.unresolved h))
  | _ =>
    let changed := xs.set i r.ref
    if r.sameOrigin && !r.dirty then
      freshBranchReference changed v >>= fun parent => k ⟨some parent, true, false⟩
    else collapseReferenceThen changed v k

private theorem ext_smaller (p : Nibbles) (c : Node) (enc : Enc) :
    sizeOf (some c : Ref) < sizeOf (some (.ext p c enc) : Ref) := by
  simp only [Option.some.sizeOf_spec, Node.ext.sizeOf_spec]
  omega

private theorem branch_smaller (xs : Array Ref) (v : ByteArray) (enc : Enc)
    (i : Nat) (hi : i < xs.size) :
    sizeOf (xs[i]'hi) < sizeOf (some (.branch xs v enc) : Ref) := by
  have h := Array.sizeOf_getElem xs i hi
  simp only [Option.some.sizeOf_spec, Node.branch.sizeOf_spec]
  omega

private def reference {m : Type → Type} [Monad m] [KeccakQuery m]
    (root : Ref) (key : List (Fin 16))
    (k : ChangedResult → m (Except TrieError Ref)) : m (Except TrieError Ref) :=
  match root with
  | none => k ⟨none, true, false⟩
  | some (.hashed h) => pure (.error (.unresolved h))
  | some (.leaf p v _) =>
    if p.toList = key then k ⟨none, false, false⟩
    else freshLeafReference p.toList v >>= fun n => k ⟨some n, true, false⟩
  | some (.ext p child _) =>
    if p.toList = key.take p.size then
      reference (some child) (key.drop p.size) (fun r => extReferenceThen p.toList r k)
    else freshExtReference p.toList child >>= fun n => k ⟨some n, true, false⟩
  | some (.branch xs v _) =>
    match key with
    | [] =>
      if v.size = 0 then freshBranchReference xs.toList v >>= fun n => k ⟨some n, true, false⟩
      else collapseReferenceThen xs.toList ByteArray.empty k
    | digit :: tail =>
      if hi : digit.val < xs.size then
        reference (xs[digit.val]'hi) tail (fun r => branchReferenceThen xs.toList v digit.val r k)
      else pure (.error (.malformed (.branchIndex digit.val xs.size)))
termination_by sizeOf root
decreasing_by
  · exact ext_smaller _ _ _
  · exact branch_smaller _ _ _ _ _

private abbrev Trace := List (ByteArray × Hash32) × Nat
private def seed (n : Nat) : Trace := ([(bytes [0,255,66],answer 199)],n)
private def recording (t : Ref) (key : Nibbles) (initial : Trace)
    (constant : Bool := false) : Except TrieError Ref × Trace :=
  let q : KeccakQuery (StateM Trace) := ⟨fun raw s =>
    let h := answer (if constant then 93 else s.2)
    (h,(s.1 ++ [(raw,h)],s.2+1))⟩
  (@delete (StateM Trace) inferInstance q t key).run initial
private def expected (t : Ref) (key : Nibbles) (initial : Trace)
    (constant : Bool := false) : Except TrieError Ref × Trace :=
  let q : KeccakQuery (StateM Trace) := ⟨fun raw s =>
    let h := answer (if constant then 93 else s.2)
    (h,(s.1 ++ [(raw,h)],s.2+1))⟩
  (@reference (StateM Trace) inferInstance q t key.toList (fun r => pure (.ok r.ref))).run initial
private def check (t : Ref) (key : Nibbles) : Bool :=
  [0,7].all fun n => [false,true].all fun constant =>
    let (a,s) := recording t key (seed n) constant
    let (b,u) := expected t key (seed n) constant
    wireResult a == wireResult b && decide (s = u)
private def leaf (p : List (Fin 16)) (n : Nat := 2) : Node :=
  .leaf (path p) (bytes (List.replicate n 0)) (enc [255])
private def branch (arity selected : Nat) (c : Ref) (v : List UInt8 := []) : Ref :=
  some (.branch ((Array.replicate arity none).setIfInBounds selected c) (bytes v) (enc []))

-- A changed same-origin inner branch must trigger collapse of its sole-child parent.
-- The expected bytes are literal HP/RLP encodings, independent of `reference`.
private def dirtyChildCollapse : Ref :=
  let child : Ref := some (.leaf (path []) (bytes [1]) (enc [194,32,1] none))
  let slots := (Array.replicate 16 none).setIfInBounds 0 child
  let children := (slots.setIfInBounds 1 child).setIfInBounds 2 child
  branch 16 0 (some (.branch children (bytes []) (enc [])))
private def dirtyChildExpected : List Nat :=
  [0,3,1,0,4,16,0,2,0,1,1,3,194,32,1,0,2,0,1,1,3,194,32,1,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,22,213,128,194,32,1,194,32,1,
   128,128,128,128,128,128,128,128,128,128,128,128,128,128,0,
   24,215,16,213,128,194,32,1,194,32,1,
   128,128,128,128,128,128,128,128,128,128,128,128,128,128,0]
#guard dirtyChildExpected.length == 89
#guard wireResult (delete (m := Id) dirtyChildCollapse (path [0,0])) == dirtyChildExpected
#guard let (result,s) := recording dirtyChildCollapse (path [0,0]) ([],7)
  wireResult result == dirtyChildExpected && s.1.isEmpty && s.2 == 7

private def variants : List Node :=
  [leaf [1], .ext (path [2]) (leaf [3]) (enc []),
    .branch #[none,some (.hashed (answer 17))] (bytes [255]) (enc []),
    .hashed (answer 17)]

-- D01–04: none/stub/match/mismatch with all original own cache fields discarded.
#guard [[],[0],[15,0]].all fun p => check none (path p) &&
  check (some (.hashed (answer 9))) (path p)
#guard [[],[0],[15,0]].all fun p => [0,1,28,29,30,40].all fun n =>
  check (some (leaf p n)) (path p) && check (some (leaf p n)) (path (p ++ [15]))
#guard [0,31,32,33].all fun n => [none,some (answer 63)].all fun h =>
  check (some (.leaf (path []) (bytes []) (enc (List.replicate n 255) h))) (path [0])
-- D05–10: mismatch, disappear, immediate single splice and empty-path proper descent.
#guard variants.all fun c => [[],[0],[0,15]].all fun p =>
  check (some (.ext (path p) c (enc []))) (path (p ++ [0,15])) &&
  check (some (.ext (path p) c (enc []))) (path [15]) &&
  check (some (.ext (path []) (.ext (path []) c (enc [])) (enc []))) (path [0,15])
-- D11–17: terminal/no-change bypass and actual selected short/long array bounds.
#guard [0,1,15,16,17,257].all fun arity =>
  [none,some (leaf []),some (.hashed (answer 17))].all fun c =>
    check (some (.branch (Array.replicate arity c) (bytes []) (enc []))) (path []) &&
    check (some (.branch (Array.replicate arity c) (bytes [255]) (enc []))) (path []) &&
    [0,14,15].all fun digit => check (branch arity digit.val c) (path [digit,0])
-- D18–25: full no-op cache propagation and reached collapse versus bypass.
#guard check (some (.branch #[some (leaf [1]),some (.hashed (answer 17))]
  (bytes []) (enc []))) (path [0,2])
#guard [1,15,16,255,256].all fun i => variants.all fun c =>
  let slots := (Array.replicate (i+1) none).setIfInBounds 0 (some (leaf []))
  let xs := slots.setIfInBounds i (some c)
  check (some (.branch xs (bytes []) (enc []))) (path [0]) &&
  check (some (.branch xs (bytes [255]) (enc []))) (path [0])
#guard check (branch 1 0 (some (leaf []))) (path [0]) &&
  check (branch 1 0 none) (path [0]) && check (branch 0 0 none) (path [])
-- D26: exact own 31/32/33-byte leaf, extension and arbitrary-arity branch encodings.
#guard [28,29,30].all fun n => check (some (leaf [] n)) (path [0])
#guard [50,52,54].all fun n => check
  (some (.ext (path (List.replicate n 0))
    (.leaf (path []) (bytes []) (enc [] none)) (enc []))) (path [15])
#guard [29,30,31].all fun n => check (branch n 0 none) (path [])
#guard [28,29,30].map (fun n =>
  (Rlp.encodeModel (.list [.bytes (bytes [32]),.bytes (bytes (List.replicate n 0))])).length)
    == [31,32,33]
#guard [50,52,54].map (fun n =>
  (Rlp.encodeModel (.list
    [.bytes (nibbleListToCompactModel (List.replicate n 0) false).toByteArray,
     childRef (some (.leaf (path []) (bytes []) (enc [] none)))])).length) == [31,32,33]
#guard [29,30,31].map (fun n =>
  (Rlp.encodeModel (.list (List.replicate n (.bytes (bytes [])) ++ [.bytes (bytes [])]))).length)
    == [31,32,33]
#guard [0,1,2,49,50,51,110,111,510,511].all fun n => [52,53,54,253,254,255,256].all fun v =>
  check (some (.ext (path (List.replicate n 0)) (leaf [1] v) (enc [])))
    (path (List.replicate n 0 ++ [2]))
-- D27–28: complete noncanonical caches and witness-before-index provider stages.
#guard [15,16,255,256].all fun i => [31,32,33].all fun n =>
  let c := Node.leaf (path [1]) (bytes [170]) (enc (List.replicate n 255) none)
  let slots := (Array.replicate (i+1) none).setIfInBounds 0 (some (leaf []))
  let xs := slots.setIfInBounds i (some c)
  check (some (.branch xs (bytes []) (enc []))) (path [0])

private def chain : Ref := some (.ext (path [0,15])
  (.ext (path []) (leaf [0,1] 40) (enc [])) (enc []))
private def chainKey : Nibbles := path [0,15,0,2]
private def repeated : Bool := [0,7].all fun n => [false,true].all fun constant =>
  let (a,s) := recording chain chainKey (seed n) constant
  let (b,t) := recording chain chainKey s constant
  let (ea,es) := expected chain chainKey (seed n) constant
  let (eb,et) := expected chain chainKey es constant
  wireResult a == wireResult ea && wireResult b == wireResult eb && decide (t = et)
-- D29: repeated, constant, distinct and full-width answers (Lean-only effects).
#guard repeated
private def wideAnswer (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat
  ((List.range 32).foldl (fun a i => a * 256 + (n + 17*i) % 256) 0))
private def wideCheck : Bool := [0,7].all fun initial => [false,true].all fun constant =>
  let q : KeccakQuery (StateM Trace) := ⟨fun raw s =>
    let h := wideAnswer (if constant then 93 else s.2)
    (h,(s.1 ++ [(raw,h)],s.2+1))⟩
  let a := (@delete (StateM Trace) inferInstance q chain chainKey).run (seed initial)
  let b := (@reference (StateM Trace) inferInstance q chain chainKey.toList
    (fun r => pure (.ok r.ref))).run (seed initial)
  wireResult a.1 == wireResult b.1 && decide (a.2 = b.2) &&
    (a.2.1.drop 1).all fun (_,h) => h.toBytes.toByteArray.data.toList[1]? != some 0
#guard wideCheck

private def failOuter (t : Ref) (key : Nibbles) (failAt : Nat)
    (useModel : Bool) : Except String (Except TrieError Ref) × Trace :=
  let q : KeccakQuery (ExceptT String (StateM Trace)) :=
    ⟨fun raw => ExceptT.mk fun s =>
      let h := answer s.2
      (if s.2 = failAt then .error "query failed" else .ok h,
        (s.1 ++ [(raw,h)],s.2+1))⟩
  let action := if useModel then
    @reference (ExceptT String (StateM Trace)) inferInstance q t key.toList
      (fun r => pure (.ok r.ref))
    else @delete (ExceptT String (StateM Trace)) inferInstance q t key
  action.run.run (seed 7)
private def failInner (t : Ref) (key : Nibbles) (failAt : Nat)
    (useModel : Bool) :
    Except (String × List (ByteArray × Hash32)) (Except TrieError Ref × Trace) :=
  -- The separate spy prefix travels in the underlying error, not an absent StateT result.
  let q : KeccakQuery (StateT Trace (Except (String × List (ByteArray × Hash32)))) :=
    ⟨fun raw s =>
      let h := answer s.2
      if s.2 = failAt then .error ("query failed",s.1 ++ [(raw,h)])
      else .ok (h,(s.1 ++ [(raw,h)],s.2+1))⟩
  let action := if useModel then
    @reference (StateT Trace (Except (String × List (ByteArray × Hash32))))
      inferInstance q t key.toList (fun r => pure (.ok r.ref))
    else @delete (StateT Trace (Except (String × List (ByteArray × Hash32))))
      inferInstance q t key
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
-- D30: each actual query ordinal in both transformer orders; every full prefix retained.
#guard let (_,s) := recording chain chainKey (seed 7)
  3 ≤ s.2 - 7 && (List.range (s.2-7)).all fun i =>
    decide (outerWire (failOuter chain chainKey (7+i) false) =
      outerWire (failOuter chain chainKey (7+i) true)) &&
    decide (innerWire (failInner chain chainKey (7+i) false) =
      innerWire (failInner chain chainKey (7+i) true)) &&
    match failOuter chain chainKey (7+i) false,
      failInner chain chainKey (7+i) false with
    | (.error e,t),.error (f,spy) =>
      e == "query failed" && f == e && t.2 == 8+i &&
        decide (t.1 = s.1.take (i+2)) && decide (spy = t.1)
    | _,_ => false
-- D31: typed failure before the first query (Lean-only transformer observation).
#guard let stub := branch 1 0 (some (.hashed (answer 17)))
  match failOuter stub (path [0]) 7 false with
  | (.ok (.error (.unresolved h)),s) => h == answer 17 && decide (s = seed 7)
  | _ => false

private structure Count (α : Type) where
  value : α
  ticks : Nat
private instance : Monad Count where
  pure a := ⟨a,1⟩
  bind a k := let b := k a.value; ⟨b.value,2*a.ticks+b.ticks+1⟩
private abbrev countQuery : KeccakQuery Count := ⟨fun _ => ⟨answer 77,5⟩⟩
private def countCheck (t : Ref) (key : Nibbles) : Bool :=
  let a := @delete Count inferInstance countQuery t key
  let b := @reference Count inferInstance countQuery t key.toList (fun r => pure (.ok r.ref))
  wireResult a.value == wireResult b.value && a.ticks == b.ticks
-- D32: syntax-sensitive complete deletion and the unreassociated bind counterexample.
#guard countCheck chain chainKey
#guard let a : Count Nat := ⟨0,5⟩
  let b := fun (_ : Nat) => (⟨0,5⟩ : Count Nat)
  let c := fun (_ : Nat) => (⟨0,5⟩ : Count Nat)
  ((a >>= b) >>= c).ticks == 38 && (a >>= fun x => b x >>= c).ticks == 27
#guard [0,1,15,16,17,257].all fun arity => [0,14,15].all fun digit =>
  let a := @delete Count inferInstance countQuery (branch arity 0 none) (path [digit])
  countCheck (branch arity 0 none) (path [digit]) &&
    (if arity ≤ digit.val then a.ticks == 1 else true)

-- Bare root errors count one pure; an added error-forwarding bind counts four.
#guard let t := some (.branch #[] (bytes [255]) (enc []))
  let a := @delete Count inferInstance countQuery t (path [])
  a.ticks == 1 && (a >>= fun e => pure e).ticks == 4
#guard let a := @delete Count inferInstance countQuery chain chainKey
  a.ticks == 76
-- Reassociate the actual three completions: complete value agrees, action count differs.
#guard let good := @delete Count inferInstance countQuery chain chainKey
  let bad := (((@mkLeaf Count inferInstance countQuery (path [0,1])
      (bytes (List.replicate 40 0)) >>= fun n =>
        @mkExt Count inferInstance countQuery (path []) n) >>= fun n =>
          @mkExt Count inferInstance countQuery (path [0,15]) n) >>= fun n =>
            (pure (.ok (some n)) : Count (Except TrieError Ref)))
  wireResult good.value == wireResult bad.value && good.ticks == 76 && bad.ticks == 176
-- Complete framed public observer; source driver extracts only test-local support.
private def emit (cases : List (Ref × Nibbles)) : IO Unit := do
  for ((t,key),i) in cases.zipIdx do
    let result := delete (m := Id) t key
    let (stateResult,s) := recording t key (seed 7)
    let frame := s!"\{\"case\":{i},\"input\":{wireRef t},\"key\":{key.toList.map Fin.val}," ++
      s!"\"result\":{wireResult result},\"stateResult\":{wireResult stateResult}," ++
      s!"\"queries\":{s.1.map (fun x => wireBytes x.1)}," ++
      s!"\"answers\":{s.1.map (fun x => wireHash x.2)},\"counter\":{s.2}}"
    IO.println frame

end STFSpec.Conformance.Commit.DeleteGuards
