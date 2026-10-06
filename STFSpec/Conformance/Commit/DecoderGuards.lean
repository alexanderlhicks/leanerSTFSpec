/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Commit

/-!
# Complete decoder structural and effect controls

Library `EthConformance`. Private total observers retain every field, including
all raw/cache bytes and ordered children. Stateful oracle answers intentionally
differ from database keys and from concrete digests. No observer depth or fuel is
used. These finite controls are conformance evidence, not an admission invariant.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` C13–C17/Q55.
-/

namespace STFSpec.Conformance.Commit.DecoderGuards
open STFSpec.Base STFSpec.Hash STFSpec.Codec STFSpec.Commit

private def bytes (xs : List UInt8) : ByteArray := xs.toByteArray
private def key (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)
private def answer (n : Nat) : Hash32 := key (1000 + n)
private def byteWire (b : ByteArray) : List Nat := b.size :: b.data.toList.map UInt8.toNat
private def hashWire (h : Hash32) : List Nat := h.toBytes.toList.map UInt8.toNat
private def pathWire (p : Nibbles) : List Nat := p.size :: p.toList.map Fin.val
private def encWire (e : Enc) : List Nat := byteWire e.rlp ++
  match e.hash? with | none => [0] | some h => 1 :: hashWire h

mutual
private def nodeWire (node : Node) : List Nat :=
  match node with
  | .hashed h => 1 :: hashWire h
  | .leaf p v e => 2 :: (pathWire p ++ byteWire v ++ encWire e)
  | .ext p child e => 3 :: (pathWire p ++ encWire e ++ nodeWire child)
  | .branch cs v e => 4 :: (byteWire v ++ encWire e ++ [cs.size] ++ childrenWire cs.toList)
termination_by sizeOf node
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (cases cs; simp_all; omega)
private def childrenWire (children : List Ref) : List Nat :=
  match children with
  | [] => []
  | none :: rest => 0 :: childrenWire rest
  | some node :: rest => nodeWire node ++ childrenWire rest
termination_by sizeOf children
end

private def refWire : Ref → List Nat
  | none => [0]
  | some node => nodeWire node

private def malformedWire : Malformed → List Nat
  | .rlp => [0]
  | .nonEmptyString => [1]
  | .compactPathList => [2]
  | .compactEmpty => [3]
  | .leafValueList => [4]
  | .pathEmpty => [5]
  | .badListLength n => [6, n]
  | .refLength n => [7, n]
  | .extChild => [8]
  | .occupancy n => [9, n]
  | .cycle => [10]
  | .branchIndex index arity => [11, index, arity]
  | .collapseIndex index => [12, index]

#guard malformedWire (.branchIndex 0 0) = [11, 0, 0]
#guard malformedWire (.branchIndex 1 0) = [11, 1, 0]
#guard malformedWire (.branchIndex 0 1) = [11, 0, 1]
#guard malformedWire (.branchIndex (10^100) (10^200)) = [11, 10^100, 10^200]
#guard ([0, 1, 15, 16, 255, 256, 10^200] : List Nat).all fun i =>
  malformedWire (.collapseIndex i) == [12, i]
#guard malformedWire (.collapseIndex 16) ≠ malformedWire (.branchIndex 16 0)
#guard malformedWire (.collapseIndex 0) ≠ malformedWire (.occupancy 0)

private def errorWire : TrieError → List Nat
  | .missingRoot h => 0 :: hashWire h
  | .malformed why => 1 :: malformedWire why
  | .unresolved h => 2 :: hashWire h

private def resultWire : Except TrieError Ref → List Nat
  | .error error => 0 :: errorWire error
  | .ok root => 1 :: refWire root

private abbrev Trace := List (ByteArray × Hash32)
private def traceWire (trace : Trace) : List (List Nat) :=
  trace.map (fun (raw, h) => byteWire raw ++ hashWire h)
private def expectedTrace (raws : List ByteArray) : List (List Nat) :=
  raws.zipIdx.map (fun (raw, i) => byteWire raw ++ hashWire (answer (i + 1)))
private def traceOracle (raw : ByteArray) : StateM Trace Hash32 := fun trace =>
  let h := answer (trace.length + 1)
  (h, trace ++ [(raw, h)])
private def database (entries : List (Nat × ByteArray)) : NodeDB :=
  ⟨entries.foldl (fun map (n, raw) => map.insert (key n) raw) {}⟩
private def observe (db : NodeDB) (r : Hash32 := key 1) (empty : Hash32 := key 0) :
    List Nat × List (List Nat) :=
  letI : KeccakQuery (StateM Trace) := ⟨traceOracle⟩
  let (result, trace) := (decodeRoot (m := StateM Trace) empty db r).run []
  (resultWire result, traceWire trace)
private def checkRoot (raw : ByteArray) (expected : Ref) (raws : List ByteArray)
    (extra : List (Nat × ByteArray) := []) : Bool :=
  observe (database ((1, raw) :: extra)) = (resultWire (.ok expected), expectedTrace raws)
private def checkError (raw : ByteArray) (why : Malformed) (raws : List ByteArray)
    (extra : List (Nat × ByteArray) := []) : Bool :=
  observe (database ((1, raw) :: extra)) =
    (resultWire (.error (.malformed why)), expectedTrace raws)

private def emptyItem : RlpItem := .bytes ByteArray.empty
private def hashItem (n : Nat) : RlpItem := .bytes (key n).toBytes.toByteArray
private def leafItem (valueWidth : Nat := 0) (flag : UInt8 := 0x20) : RlpItem :=
  .list [.bytes (bytes [flag]), .bytes (bytes (List.replicate valueWidth 0x7a))]
private def leafRaw (width : Nat := 0) (flag : UInt8 := 0x20) : ByteArray :=
  Rlp.encode (leafItem width flag)
private def extensionItem (child : RlpItem) (flag : UInt8 := 0x11) : RlpItem :=
  .list [.bytes (bytes [flag]), child]
private def branchItem (children : List RlpItem) (value : RlpItem := emptyItem) : RlpItem :=
  .list (children ++ [value])
private def branchRaw (children : List RlpItem) (value : RlpItem := emptyItem) : ByteArray :=
  Rlp.encode (branchItem children value)
private def entered (raw : ByteArray) (index : Nat) : Enc :=
  ⟨raw, if raw.size < 32 then none else some (answer index)⟩
private def emptyLeaf (raw : ByteArray) (index : Nat) : Node :=
  .leaf (Nibbles.ofList []) ByteArray.empty (entered raw index)

-- Supplied empty-root bypass, missing root, and both raw empty-node spellings.
#guard observe (database [(87, bytes (List.replicate 40 0xff))]) (key 87) (key 87) = ([1, 0], [])
#guard observe (database []) = (resultWire (.error (.missingRoot (key 1))), [])
#guard checkRoot (bytes [0x80]) none []
#guard checkError (bytes []) .rlp []
#guard checkError (bytes [0]) .nonEmptyString []
#guard checkError (bytes [0xc0]) (.badListLength 0) []

-- Exact 31/32/33 threshold, actual cache answers, empty paths/values and ignored HP bits/pad.
#guard ([28, 29, 30].map fun width => (leafRaw width).size) = [31, 32, 33]
#guard [28, 29, 30].all fun width =>
  let raw := leafRaw width
  checkRoot raw (some (.leaf (Nibbles.ofList []) (bytes (List.replicate width 0x7a))
    (entered raw 1))) (if raw.size < 32 then [] else [raw])
#guard [0x20, 0x2f, 0x60, 0x6f, 0xa0, 0xaf, 0xe0, 0xef].all fun flag =>
  let raw := leafRaw 0 flag
  checkRoot raw (some (emptyLeaf raw 1)) []
#guard checkRoot (leafRaw 0 0xf1)
  (some (.leaf (Nibbles.ofList [1]) ByteArray.empty (entered (leafRaw 0 0xf1) 1))) []

-- Whole strict RLP wins over all compact fields, and eligible malformed raw still queries.
#guard checkError (bytes [0xc1, 0x80, 0]) .rlp []
#guard checkError (bytes (List.replicate 32 0xff)) .rlp [bytes (List.replicate 32 0xff)]
#guard checkError (Rlp.encode (.list [.list [], .list []])) .compactPathList []
#guard checkError (Rlp.encode (.list [emptyItem, .list []])) .compactEmpty []
#guard checkError (Rlp.encode (.list [.bytes (bytes [0x20]), .list []])) .leafValueList []
#guard checkError (Rlp.encode (extensionItem (.bytes (bytes [1])) 0x00)) .pathEmpty []

-- All reference widths, ending-list leniency, and occupancy count presence rather than value.
#guard [1, 31, 33].all fun width =>
  let raw := branchRaw (.bytes (bytes (List.replicate width 1)) :: List.replicate 15 emptyItem)
  checkError raw (.refLength width) (if raw.size < 32 then [] else [raw])
#guard checkError (branchRaw (List.replicate 16 emptyItem)) (.occupancy 0) []
#guard checkError (branchRaw (List.replicate 16 emptyItem) (.list [leafItem])) (.occupancy 0) []
#guard checkError (branchRaw (hashItem 2 :: List.replicate 15 emptyItem)) (.occupancy 1)
  [branchRaw (hashItem 2 :: List.replicate 15 emptyItem)]
#guard
  let raw := branchRaw (hashItem 2 :: List.replicate 15 emptyItem) (.bytes (bytes [9]))
  checkRoot raw (some (.branch (#[some (.hashed (key 2))] ++ Array.replicate 15 none)
    (bytes [9]) (entered raw 1))) [raw]
#guard
  let raw := branchRaw (leafItem :: hashItem 2 :: List.replicate 14 emptyItem) (.list [])
  checkRoot raw (some (.branch (#[some (emptyLeaf (leafRaw) 1), some (.hashed (key 2))] ++
    Array.replicate 14 none) ByteArray.empty (entered raw 1))) [raw]

-- Present short database preimages are decoded; an absent key instead remains a stub.
#guard
  let raw := branchRaw (hashItem 2 :: hashItem 3 :: List.replicate 14 emptyItem)
  checkRoot raw (some (.branch (#[some (emptyLeaf leafRaw 2), some (.hashed (key 3))] ++
    Array.replicate 14 none) ByteArray.empty (entered raw 1))) [raw] [(2, leafRaw)]
#guard
  let raw := branchRaw (hashItem 2 :: hashItem 3 :: List.replicate 14 emptyItem)
  checkError raw (.occupancy 1) [raw] [(2, bytes [0x80])]

-- Extension child admission occurs after the entire descendant action/error.
#guard checkError (Rlp.encode (extensionItem emptyItem)) .extChild []
#guard checkError (Rlp.encode (extensionItem leafItem)) .extChild []
#guard checkError (Rlp.encode (extensionItem (extensionItem emptyItem))) .extChild []
#guard checkError (Rlp.encode (extensionItem (.list []))) (.badListLength 0) []
#guard
  let raw := Rlp.encode (extensionItem (hashItem 2))
  checkRoot raw (some (.ext (Nibbles.ofList [1]) (.hashed (key 2)) (entered raw 1))) [raw]
#guard
  let child := branchItem (hashItem 2 :: hashItem 3 :: List.replicate 14 emptyItem)
  let cr := Rlp.encode child
  let raw := Rlp.encode (extensionItem child)
  checkRoot raw (some (.ext (Nibbles.ofList [1])
    (.branch (#[some (.hashed (key 2)), some (.hashed (key 3))] ++ Array.replicate 14 none)
      ByteArray.empty (entered cr 2)) (entered raw 1))) [raw, cr]

-- Root-seeded direct, three-key and inline cycles; answers never replace actual path keys.
#guard
  let raw := Rlp.encode (extensionItem (hashItem 1))
  checkError raw .cycle [raw]
#guard
  let r1 := Rlp.encode (extensionItem (hashItem 2))
  let r2 := Rlp.encode (extensionItem (hashItem 3))
  let r3 := Rlp.encode (extensionItem (hashItem 1))
  checkError r1 .cycle [r1, r2, r3] [(2, r2), (3, r3)]
#guard
  let child := extensionItem (hashItem 1)
  let raw := branchRaw (child :: hashItem 2 :: List.replicate 14 emptyItem)
  checkError raw .cycle [raw, Rlp.encode child]

-- Every branch position fails eagerly, preserving only the earlier occurrence queries.
#guard (List.range 16).all fun position =>
  let good := leafItem 29
  let children := List.replicate position good ++ [.bytes (bytes [1])] ++
    List.replicate (15 - position) good
  let raw := branchRaw children
  checkError raw (.refLength 1) (raw :: List.replicate position (Rlp.encode good))

-- Sixteen references to the same entry are separate complete occurrences/cache answers.
#guard
  let childRaw := leafRaw 29
  let raw := branchRaw (List.replicate 16 (hashItem 2))
  let children := (List.range 16).map fun i =>
    some (.leaf (Nibbles.ofList []) (bytes (List.replicate 29 0x7a)) (entered childRaw (i + 2)))
  checkRoot raw (some (.branch children.toArray ByteArray.empty (entered raw 1)))
    (raw :: List.replicate 16 childRaw) [(2, childRaw)]

private def observeWrapper (db : NodeDB) (secured : Bool) : List Nat × List (List Nat) :=
  letI : KeccakQuery (StateM Trace) := ⟨traceOracle⟩
  let (result, trace) := (decodeWitnessToMpt (m := StateM Trace) (key 0) db (key 1) secured).run []
  let wire := match result with
    | .error error => 0 :: errorWire error
    | .ok trie => 1 :: (if trie.secured then 1 else 0) :: refWire trie.root
  (wire, traceWire trace)

#guard [false, true].all fun flag =>
  let raw := leafRaw 29
  observeWrapper (database [(1, raw)]) flag =
    (1 :: (if flag then 1 else 0) :: refWire
      (some (.leaf (Nibbles.ofList []) (bytes (List.replicate 29 0x7a)) (entered raw 1))),
      expectedTrace [raw])
#guard [false, true].all fun flag =>
  let raw := bytes (List.replicate 32 0xff)
  observeWrapper (database [(1, raw)]) flag =
    (resultWire (.error (.malformed .rlp)), expectedTrace [raw])

private def failingOracle (failAt : Nat) (raw : ByteArray) : ExceptT Nat (StateM Trace) Hash32 :=
  ExceptT.mk fun trace =>
    let h := answer (trace.length + 1)
    let trace' := trace ++ [(raw, h)]
    (if trace'.length = failAt then .error failAt else .ok h, trace')
private def observeFailure (db : NodeDB) (failAt : Nat) (secured : Bool) :
    List Nat × List (List Nat) :=
  letI : KeccakQuery (ExceptT Nat (StateM Trace)) := ⟨failingOracle failAt⟩
  let (result, trace) :=
    ((decodeWitnessToMpt (m := ExceptT Nat (StateM Trace))
      (key 0) db (key 1) secured).run).run []
  let wire := match result with
    | .error error => [2, error]
    | .ok (.error error) => 0 :: errorWire error
    | .ok (.ok trie) => 1 :: (if trie.secured then 1 else 0) :: refWire trie.root
  (wire, traceWire trace)

-- A failing query still retains earlier and failing state effects, suppressing parse/laterwork.
#guard [false, true].all fun flag =>
  let raw := bytes (List.replicate 32 0xff)
  observeFailure (database [(1, raw)]) 1 flag = ([2, 1], expectedTrace [raw])
#guard (List.range 17).all fun i =>
  let raw := branchRaw (List.replicate 16 (hashItem 2))
  let child := leafRaw 29
  observeFailure (database [(1, raw), (2, child)]) (i + 1) true =
    ([2, i + 1], expectedTrace (raw :: List.replicate i child))

-- Stateful alias, diamond and transformer controls.
-- The actual database key, rather than an earlier answer equal to that key, seeds descent.
#guard
  let raw := branchRaw (hashItem 1001 :: hashItem 3 :: List.replicate 14 emptyItem)
  checkRoot raw (some (.branch (#[some (emptyLeaf leafRaw 2), some (.hashed (key 3))] ++
    Array.replicate 14 none) ByteArray.empty (entered raw 1))) [raw] [(1001, leafRaw)]

-- C16(f) uses the exact supplied empty-root value as the child key.
#guard
  let raw := branchRaw (hashItem 0 :: hashItem 3 :: List.replicate 14 emptyItem)
  checkRoot raw (some (.branch (#[some (.hashed (key 0)), some (.hashed (key 3))] ++
    Array.replicate 14 none) ByteArray.empty (entered raw 1))) [raw]
#guard
  let raw := branchRaw (hashItem 0 :: hashItem 3 :: List.replicate 14 emptyItem)
  checkError raw (.occupancy 1) [raw] [(0, bytes [0x80])]

-- A stateful diamond retains four independent leaf answers and both inline-parent answers.
#guard
  let lr := leafRaw 29
  let shared := branchItem (hashItem 2 :: hashItem 2 :: List.replicate 14 emptyItem)
  let sr := Rlp.encode shared
  let raw := branchRaw (shared :: shared :: List.replicate 14 emptyItem)
  let leaf := fun i =>
    some (.leaf (Nibbles.ofList []) (bytes (List.replicate 29 0x7a)) (entered lr i))
  let left := Node.branch (#[leaf 3, leaf 4] ++ Array.replicate 14 none)
    ByteArray.empty (entered sr 2)
  let right := Node.branch (#[leaf 6, leaf 7] ++ Array.replicate 14 none)
    ByteArray.empty (entered sr 5)
  checkRoot raw (some (.branch (#[some left, some right] ++ Array.replicate 14 none)
    ByteArray.empty (entered raw 1))) [raw, sr, lr, lr, sr, lr, lr] [(2, lr)]

-- A successful nested extension is rejected by its parent only after all descendant queries.
#guard
  let br := branchItem (hashItem 2 :: hashItem 3 :: List.replicate 14 emptyItem)
  let child := extensionItem br
  let raw := Rlp.encode (extensionItem child)
  checkError raw .extChild [raw, Rlp.encode child, Rlp.encode br]

-- A separate state layer preserves its arbitrary supplied state on success and
-- forwards underlying failure without introducing a decoder error or later query.
private def observeAddedState (db : NodeDB) (failAt : Nat) : List Nat × List (List Nat) :=
  letI : KeccakQuery (ExceptT Nat (StateM Trace)) := ⟨failingOracle failAt⟩
  let (result, trace) :=
    (((decodeWitnessToMpt (m := StateT Nat (ExceptT Nat (StateM Trace)))
      (key 0) db (key 1) true).run 77).run).run []
  let wire := match result with
    | .error error => [2, error]
    | .ok (.error error, state) => state :: 0 :: errorWire error
    | .ok (.ok trie, state) => state :: 1 :: (if trie.secured then 1 else 0) :: refWire trie.root
  (wire, traceWire trace)
#guard
  let raw := leafRaw 29
  observeAddedState (database [(1, raw)]) 0 =
    (77 :: 1 :: 1 :: refWire (some (.leaf (Nibbles.ofList [])
      (bytes (List.replicate 29 0x7a)) (entered raw 1))), expectedTrace [raw])
#guard
  let raw := bytes (List.replicate 32 0xff)
  observeAddedState (database [(1, raw)]) 0 =
    (77 :: resultWire (.error (.malformed .rlp)), expectedTrace [raw])
#guard
  let raw := bytes (List.replicate 32 0xff)
  observeAddedState (database [(1, raw)]) 1 = ([2, 1], expectedTrace [raw])

end STFSpec.Conformance.Commit.DecoderGuards
