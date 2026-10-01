/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Conformance.Commit.RootDomainGuards

/-!
# Complete observations of private sixteen-child branch support

Library `EthConformance`. `rootBranchOwner%` is test instrumentation of verified
actual private Root declarations, not a new production API. No recursive
algorithm is copied. Finite callbacks exercise actual child encoding and effects;
reusable consumers retain public domain/provider laws. Source context: pinned
EELS `src/ethereum/merkle_patricia_trie.py:564–581`; support only, not full C7/C8.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/4/7.1.
-/

namespace STFSpec.Conformance.Commit.RootBranchGuards

open STFSpec.Commit STFSpec.Codec STFSpec.Base STFSpec.Hash

/-- Pinned-toolchain test instrumentation of actual private Root declarations in scope zero.
This exports no production seam; reusable consumers use public domain/provider laws. -/
macro "rootBranchOwner% " helper:ident : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.STFSpec.Commit.Root 0).str "STFSpec" |>.str "Commit"
    |>.append helper.getId))

/-- Test-only wrapper of the actual guarded full-key partition; it preserves every raw value. -/
def partition (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat) (digit : Fin 16) :
    Std.ExtTreeMap Nibbles ByteArray := (rootBranchOwner% childPartition) obj level digit

/-- Test-only optional ending lookup; a present empty value remains distinct from absence. -/
def endingLookup (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat) (a : Nibbles) :
    Option ByteArray := (rootBranchOwner% BranchParts.ending) ((rootBranchOwner% branchParts) obj level a)

/-- Test-only bounded owner stage with supplied construction and actual C6 encoding.
The callback receives the exact full partition equality and next-depth domain proof. -/
def branchStage {m : Type → Type} [Monad m] [KeccakQuery m]
    (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (hd : PatricializeDomain obj level) (representative : Nibbles)
    (construct : (digit : Fin 16) → (child : Std.ExtTreeMap Nibbles ByteArray) →
      child = partition obj level digit → PatricializeDomain child (level + 1) → m (Option InternalNode)) : m InternalNode :=
  (rootBranchOwner% branchStage) obj level hd representative construct

/-- Finite test input adapter through the public bounded List model. -/
def key (digits : List (Fin 16)) : Nibbles := Nibbles.ofList digits

/-- Complete ordered full-key and byte-value observation through public map/path observers. -/
def entries (obj : Std.ExtTreeMap Nibbles ByteArray) : List (List Nat × List UInt8) :=
  obj.toList.map fun (k, v) ↦ (k.toList.map Fin.val, v.data.toList)

/-- Sixteen distinguishable root children with full retained values. -/
def allDigits : Std.ExtTreeMap Nibbles ByteArray :=
  (List.finRange 16).foldl
    (fun obj digit ↦ obj.insert (key [digit]) ⟨#[UInt8.ofNat digit.val, 255]⟩) ∅

/-- An empty ending value and two numeric continuations at a consumed depth. -/
def ending : Std.ExtTreeMap Nibbles ByteArray :=
  (∅ : Std.ExtTreeMap Nibbles ByteArray)
    |>.insert (key [7, 8]) ByteArray.empty
    |>.insert (key [7, 8, 0]) ⟨#[1, 2]⟩
    |>.insert (key [7, 8, 15]) ⟨#[254, 255]⟩

/-- The finite ending test map reaches and agrees through depth two. -/
theorem endingDomain : PatricializeDomain ending 2 :=
  (STFSpec.Conformance.Commit.RootDomainGuards.domainCheck_iff ending 2).mp (by decide)

/-- Odd full paths beyond secured widths, including an ending key and a continuation. -/
def longOdd : Std.ExtTreeMap Nibbles ByteArray :=
  (∅ : Std.ExtTreeMap Nibbles ByteArray)
    |>.insert (key (List.replicate 257 3)) ByteArray.empty
    |>.insert (key (List.replicate 257 3 ++ [4, 5])) ⟨#[9, 10]⟩

/-- Complete callback/query/error observations for finite stage checks. -/
inductive Event where
  | construct (digit : Nat) (entries : List (List Nat × List UInt8))
  | query (index : Nat) (preimage answer : List UInt8)
  | queryError (index : Nat) (preimage : List UInt8)
  deriving BEq, Repr

/-- Retained ordered events, query count and optional query-failure trigger. -/
structure Trace where
  events : List Event := []
  queries : Nat := 0
  failQueryAt : Option Nat := none
  deriving BEq, Repr

/-- Named original constructor or oracle failures retained by the test monad. -/
inductive Failure where
  | construction (digit : Nat) (payload : List UInt8)
  | oracle (index : Nat) (preimage : List UInt8)
  deriving BEq, Repr

/-- Stateful finite oracle/callback observations. -/
abbrev TestState := StateM Trace
/-- Original failures layered over retained state observations. -/
abbrev TestFailure := ExceptT Failure TestState

/-- Record the whole preimage and complete arbitrary answer in query order. -/
def healthyQuery (preimage : ByteArray) : TestState Hash32 := fun state ↦
  let answer := Hash32.ofBytes32 (FixedBytes.ofNat (1000 + state.queries))
  (answer, {state with
    events := state.events ++ [.query state.queries preimage.data.toList
      answer.toBytes.toByteArray.data.toList], queries := state.queries + 1})

instance : KeccakQuery TestState where
  keccak := healthyQuery

instance : KeccakQuery TestFailure where
  keccak preimage := ExceptT.mk fun state ↦
    if state.failQueryAt = some state.queries then
      (.error (.oracle state.queries preimage.data.toList), {state with
        events := state.events ++ [.queryError state.queries preimage.data.toList]})
    else
      let (answer, next) := healthyQuery preimage state
      (.ok answer, next)

/-- Cycle finite child payloads through the inline/hash boundary cases. -/
def payloadSize (digit : Nat) : Nat := 28 + digit % 3

/-- A finite leaf with an independently selected payload width. -/
def leafFor (digit : Nat) : Option InternalNode :=
  some (.leaf (key []) (.bytes ((List.replicate (payloadSize digit)
    (UInt8.ofNat digit)).toByteArray)))

/-- Record the complete supplied partition before returning its finite child node. -/
def observeConstruct (digit : Fin 16) (obj : Std.ExtTreeMap Nibbles ByteArray)
    (_ : PatricializeDomain obj 1) : TestState (Option InternalNode) := fun state ↦
  (leafFor digit.val, {state with events := state.events ++ [.construct digit.val (entries obj)]})

/-- Record construction and preserve the selected original constructor error. -/
def failingConstruct (stop : Option Nat) (digit : Fin 16)
    (obj : Std.ExtTreeMap Nibbles ByteArray) (_ : PatricializeDomain obj 1) :
    TestFailure (Option InternalNode) := ExceptT.mk fun state ↦
  (if stop = some digit.val then .error (.construction digit.val [200, 201])
    else .ok (leafFor digit.val),
    {state with events := state.events ++ [.construct digit.val (entries obj)]})

instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

/-- Independent count of expected hashed children before a numeric position. -/
def queryIndexBefore (digit : Nat) : Nat := digit - (digit + 2) / 3

/-- Complete independently written RLP preimage for a finite leaf. -/
def expectedPreimage (digit : Nat) : List UInt8 :=
  [UInt8.ofNat (194 + payloadSize digit), 32, UInt8.ofNat (128 + payloadSize digit)] ++
    List.replicate (payloadSize digit) (UInt8.ofNat digit)

/-- Independent inline structure or full arbitrary answer expected at each child position. -/
def expectedReference (digit : Fin 16) : RlpItem :=
  if payloadSize digit.val = 28 then
    .list [.bytes ⟨#[32]⟩,
      .bytes ((List.replicate 28 (UInt8.ofNat digit.val)).toByteArray)]
  else .bytes (Hash32.ofBytes32 (FixedBytes.ofNat (1000 + queryIndexBefore digit.val))).toBytes.toByteArray

/-- Independent complete constructor/query event prefix. -/
def expectedEventsBefore (count : Nat) : List Event :=
  (List.range count).flatMap fun digit ↦
    [.construct digit [([digit], [UInt8.ofNat digit, 255])]] ++
      (if payloadSize digit = 28 then [] else
        [.query (queryIndexBefore digit) (expectedPreimage digit)
          (Hash32.ofBytes32 (FixedBytes.ofNat (1000 + queryIndexBefore digit))).toBytes.toByteArray.data.toList])

/-- Observe the complete assembled and RLP-encoded branch bytes without a parent query. -/
def wire (node : InternalNode) : List UInt8 :=
  (Rlp.encode (assembleInternalNode (some node))).data.toList

/-- Actual sixteen-child stage output and full retained state. -/
def healthy : List UInt8 × Trace :=
  let (node, state) := (branchStage allDigits 0 (PatricializeDomain.zero allDigits)
    (key [0]) (fun digit child _ hd ↦ observeConstruct digit child hd)).run {}
  (wire node, state)

/-- Independent full branch bytes and ordered state expected across hash thresholds. -/
def expectedHealthy : List UInt8 × Trace :=
  (Rlp.encode (.list ((Vector.ofFn expectedReference).toList ++
    [RlpItem.bytes ByteArray.empty])) |>.data.toList,
    {events := expectedEventsBefore 16, queries := 10})

/-- Observe the original stage failure and all retained preceding effects. -/
def failed (constructAt queryAt : Option Nat) : Except Failure (List UInt8) × Trace :=
  let (result, state) := ((branchStage (m := TestFailure) allDigits 0
    (PatricializeDomain.zero allDigits) (key [0]) (fun digit child _ hd ↦ failingConstruct constructAt digit child hd)).run).run
    {failQueryAt := queryAt}
  (result.map wire, state)

/-- Independent original constructor error and complete retained event prefix. -/
def expectedConstructFailure (digit : Nat) : Except Failure (List UInt8) × Trace :=
  (.error (.construction digit [200, 201]),
    {events := expectedEventsBefore digit ++
      [.construct digit [([digit], [UInt8.ofNat digit, 255])]],
     queries := queryIndexBefore digit})

/-- Independent original oracle error, whole preimage and retained event prefix. -/
def expectedQueryFailure (digit : Nat) : Except Failure (List UInt8) × Trace :=
  let index := queryIndexBefore digit
  (.error (.oracle index (expectedPreimage digit)),
    {events := expectedEventsBefore digit ++
      [.construct digit [([digit], [UInt8.ofNat digit, 255])],
       .queryError index (expectedPreimage digit)], queries := index, failQueryAt := some index})

/-- Finite complete observations for all sixteen constructor-error positions. -/
def constructFailureCases : List (String × Bool) :=
  (List.range 16).map fun digit ↦
    (s!"construction failure at {digit}",
      failed (some digit) none == expectedConstructFailure digit)

/-- Finite complete observations for every queried encoding-error position. -/
def queryFailureCases : List (String × Bool) :=
  ((List.range 16).filter (fun digit ↦ payloadSize digit != 28)).map fun digit ↦
    (s!"oracle failure after construction {digit}",
      failed none (some (queryIndexBefore digit)) == expectedQueryFailure digit)

/-- Finite supplied callback for empty/singleton child maps; this is not recursive construction. -/
def singletonCallback (digit : Fin 16) (obj : Std.ExtTreeMap Nibbles ByteArray)
    (depth : Nat) : TestState (Option InternalNode) := fun state ↦
  let node := match obj.keys with
    | [] => none
    | first :: _ => some (.leaf (first.drop depth) (.bytes (obj[first]?.getD ByteArray.empty)))
  (node, {state with events := state.events ++ [.construct digit.val (entries obj)]})

/-- Complete actual branch wire/state with a present empty ending value. -/
def endingStage : List UInt8 × Trace :=
  let (node, state) := (branchStage ending 2 endingDomain (key [7, 8, 15])
    (fun digit obj _ _ ↦ singletonCallback digit obj 3)).run {}
  (wire node, state)

/-- Independent fixed numeric child references for the ending test map. -/
def expectedEndingItems : Vector RlpItem 16 := Vector.ofFn fun digit ↦
  if digit.val = 0 then .list [.bytes ⟨#[32]⟩, .bytes ⟨#[1, 2]⟩]
  else if digit.val = 15 then .list [.bytes ⟨#[32]⟩, .bytes ⟨#[254, 255]⟩]
  else .bytes ByteArray.empty

/-- Independent complete assembled wire/state for the present-empty ending case. -/
def expectedEndingStage : List UInt8 × Trace :=
  ((Rlp.encode (.list (expectedEndingItems.toList ++ [.bytes ByteArray.empty]))).data.toList,
    {events := (List.range 16).map fun digit ↦ .construct digit
      (if digit = 0 then [([7, 8, 0], [1, 2])]
       else if digit = 15 then [([7, 8, 15], [254, 255])] else [])})

def oneChildEmptyValue : Std.ExtTreeMap Nibbles ByteArray :=
  (∅ : Std.ExtTreeMap Nibbles ByteArray)
    |>.insert (key []) ByteArray.empty
    |>.insert (key [0]) ByteArray.empty

/-- Actual bounded stage for the one-child/empty-ending counter-premise case. -/
def oneChildStage : List UInt8 × Trace :=
  let (node, state) := (branchStage oneChildEmptyValue 0
    (PatricializeDomain.zero oneChildEmptyValue) (key [])
    (fun digit obj _ _ ↦ singletonCallback digit obj 1)).run {}
  (wire node, state)

/-- Independent full wire/state; no canonical occupancy conclusion follows. -/
def expectedOneChildStage : List UInt8 × Trace :=
  let children : Vector RlpItem 16 := Vector.ofFn fun digit ↦
    if digit.val = 0 then .list [.bytes ⟨#[32]⟩, .bytes ByteArray.empty]
    else .bytes ByteArray.empty
  ((Rlp.encode (.list (children.toList ++ [.bytes ByteArray.empty]))).data.toList,
    {events := (List.range 16).map fun digit ↦ .construct digit
      (if digit = 0 then [([0], [])] else [])})

/-- Observe present empty ending bytes independently of absence. -/
def emptyValuePresent : Bool :=
  ((endingLookup ending 2 (key [7, 8])).map (fun b ↦ b.data.toList)) == some []

/-- Complete full-key/value observations for all sixteen actual numeric partitions. -/
def allPartitionEntries (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat) :
    List (List (List Nat × List UInt8)) :=
  (Vector.ofFn (partition obj level)).toList.map entries

/-- Complete source-support observer through actual private partitions and ending lookup. -/
def branchData (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat) (a : Nibbles) :
    List (List (List Nat × List UInt8)) × Option (List UInt8) :=
  (allPartitionEntries obj level, (endingLookup obj level a).map (fun b ↦ b.data.toList))

/-- The same finite full map constructed in reverse insertion order. -/
def endingReversed : Std.ExtTreeMap Nibbles ByteArray :=
  (∅ : Std.ExtTreeMap Nibbles ByteArray)
    |>.insert (key [7, 8, 15]) ⟨#[254, 255]⟩
    |>.insert (key [7, 8, 0]) ⟨#[1, 2]⟩
    |>.insert (key [7, 8]) ByteArray.empty

/-- The reversed finite map has the same depth-two domain. -/
theorem reversedDomain : PatricializeDomain endingReversed 2 :=
  (RootDomainGuards.domainCheck_iff endingReversed 2).mp (by decide)

/-- Complete stage results for every actual member of the finite ending map. -/
def alternativeStages : List (List UInt8 × Trace) :=
  ending.keys.map fun a ↦
    let (node, state) := (branchStage ending 2 endingDomain a
      (fun digit obj _ _ ↦ singletonCallback digit obj 3)).run {}
    (wire node, state)

/-- Complete branch wire/state after reversed insertion. -/
def reversedStage : List UInt8 × Trace :=
  let (node, state) := (branchStage endingReversed 2 reversedDomain (key [7, 8, 0])
    (fun digit obj _ _ ↦ singletonCallback digit obj 3)).run {}
  (wire node, state)

/-- Complete bounded empty stage at an arbitrary consumed depth. -/
def emptyStage : List UInt8 × Trace :=
  let hd := (RootDomainGuards.domainCheck_iff ∅ 999).mp (by decide)
  let (node, state) := (branchStage ∅ 999 hd (key [])
    (fun digit obj _ _ ↦ singletonCallback digit obj 1000)).run {}
  (wire node, state)

/-- Independent full empty wire and all sixteen empty callback observations. -/
def expectedEmptyStage : List UInt8 × Trace :=
  ((Rlp.encode (.list (List.replicate 17 (.bytes ByteArray.empty)))).data.toList,
    {events := (List.range 16).map fun digit ↦ .construct digit []})

/-- A nonempty ending value with one numeric continuation. -/
def nonemptyEnding : Std.ExtTreeMap Nibbles ByteArray :=
  (∅ : Std.ExtTreeMap Nibbles ByteArray)
    |>.insert (key [7, 8]) ⟨#[0, 1, 2]⟩
    |>.insert (key [7, 8, 0]) ⟨#[3]⟩

/-- Reachable consumed-prefix domain for the nonempty ending-value stage case. -/
theorem nonemptyEndingDomain : PatricializeDomain nonemptyEnding 2 :=
  (RootDomainGuards.domainCheck_iff nonemptyEnding 2).mp (by decide)

/-- Complete branch assembly and trace preserve nonempty ending bytes at position sixteen. -/
def nonemptyEndingStage : List UInt8 × Trace :=
  let (node, state) := (branchStage nonemptyEnding 2 nonemptyEndingDomain (key [7, 8, 0])
    (fun digit obj _ _ ↦ singletonCallback digit obj 3)).run {}
  (wire node, state)

/-- Independently written full wire/state expectation, including the inline child and final value. -/
def expectedNonemptyEndingStage : List UInt8 × Trace :=
  ((Rlp.encode (.list ([.list [.bytes ⟨#[32]⟩, .bytes ⟨#[3]⟩]] ++
    List.replicate 15 (.bytes ByteArray.empty) ++ [.bytes ⟨#[0, 1, 2]⟩]))).data.toList,
    {events := (List.range 16).map fun digit ↦
      .construct digit (if digit = 0 then [([7, 8, 0], [3])] else [])})

/-- Negative domain example whose consumed full-key prefixes disagree. -/
def wrongPrefix : Std.ExtTreeMap Nibbles ByteArray :=
  (∅ : Std.ExtTreeMap Nibbles ByteArray)
    |>.insert (key [0, 2]) ByteArray.empty
    |>.insert (key [1, 2]) ⟨#[1]⟩

/-- Complete named stage/support comparisons, including errors and domain counter-premises. -/
def cases : List (String × Bool) := [
  ("nonempty ending complete wire and callback trace",
    nonemptyEndingStage == expectedNonemptyEndingStage),
  ("all sixteen complete partitions", allPartitionEntries allDigits 0 ==
    (List.range 16).map (fun digit ↦ [([digit], [UInt8.ofNat digit, 255])])),
  ("empty partitions at arbitrary depth", allPartitionEntries ∅ 999 == List.replicate 16 []),
  ("ending keys excluded, full values retained", allPartitionEntries ending 2 ==
    ([[([7, 8, 0], [1, 2])]] ++ List.replicate 14 [] ++ [[([7, 8, 15], [254, 255])]])),
  ("present empty ending value", emptyValuePresent),
  ("ending representative agreement", ((endingLookup ending 2 (key [7, 8, 15])).map
    (fun b ↦ b.data.toList)) == some []),
  ("absent ending separate from empty", ((endingLookup allDigits 0 (key [0])).map
    (fun b ↦ b.data.toList)) == none),
  ("long odd full-key partition", allPartitionEntries longOdd 257 ==
    (List.replicate 4 [] ++ [[(List.replicate 257 3 ++ [4, 5], [9, 10])]] ++
      List.replicate 11 [])),
  ("full C6 child reference/wire and event order", healthy == expectedHealthy),
  ("ending full assembly and sixteen empty/nonempty callbacks", endingStage == expectedEndingStage),
  ("empty-value one-child formation needs separate occupancy premise",
    oneChildStage == expectedOneChildStage),
  ("original constructor error precedes later oracle failure", failed (some 1) (some 0) ==
    ({expectedConstructFailure 1 with snd :=
      {(expectedConstructFailure 1).2 with failQueryAt := some 0}})),
  ("31/32/33 complete preimage widths", ((List.range 3).map fun digit ↦
    (Rlp.encode (assembleInternalNode (leafFor digit))).size) == [31, 32, 33])
  , ("all actual members preserve complete branch", alternativeStages ==
      List.replicate ending.size expectedEndingStage)
  , ("insertion permutation preserves full map/branch", entries endingReversed == entries ending &&
      reversedStage == expectedEndingStage)
  , ("empty stage at arbitrary depth", emptyStage == expectedEmptyStage)
  , ("nonempty ending bytes remain exact", (endingLookup nonemptyEnding 2 (key [7, 8, 0])).map
      (fun b ↦ b.data.toList) == some [0, 1, 2])
  , ("wrong depth domain premise fails", RootDomainGuards.domainCheck ending 4 == false)
  , ("wrong consumed prefix premise fails", RootDomainGuards.domainCheck wrongPrefix 1 == false)
  , ("guarded partitions remain safe beyond key ends", allPartitionEntries ending 99 ==
      List.replicate 16 [])
] ++ constructFailureCases ++ queryFailureCases

#guard cases.all (fun (_, ok) ↦ ok)

/-- Complete observations printed for a standalone prototype run; no timing/checksum loop. -/
def printComplete : IO UInt32 := do
  IO.println s!"complete full partition/ending data: {reprStr (branchData ending 2 (key [7, 8]))}"
  IO.println s!"long odd full partition data: {reprStr (allPartitionEntries longOdd 257)}"
  IO.println s!"alternative complete branches: {reprStr alternativeStages}"
  IO.println s!"empty actual/expected stage: {reprStr emptyStage}; {reprStr expectedEmptyStage}"
  IO.println s!"ending actual full wire/state: {reprStr endingStage}"
  IO.println s!"ending expected full wire/state: {reprStr expectedEndingStage}"
  IO.println s!"one-child actual full wire/state: {reprStr oneChildStage}"
  IO.println s!"one-child expected full wire/state: {reprStr expectedOneChildStage}"
  IO.println s!"nonempty ending actual full wire/state: {reprStr nonemptyEndingStage}"
  IO.println s!"nonempty ending expected full wire/state: {reprStr expectedNonemptyEndingStage}"
  IO.println s!"healthy actual full wire/state: {reprStr healthy}"
  IO.println s!"healthy expected full wire/state: {reprStr expectedHealthy}"
  for digit in List.range 16 do
    IO.println s!"failure {digit}: actual={reprStr (failed (some digit) none)}; expected={reprStr (expectedConstructFailure digit)}"
  for digit in (List.range 16).filter (fun digit ↦ payloadSize digit != 28) do
    IO.println s!"query failure {digit}: actual={reprStr (failed none (some (queryIndexBefore digit)))}; expected={reprStr (expectedQueryFailure digit)}"
  let failures := (cases.filter (fun (_, ok) ↦ !ok)).map Prod.fst
  IO.println s!"{cases.length} complete branch comparisons; failures={reprStr failures}"
  return if failures.isEmpty then 0 else 1


end STFSpec.Conformance.Commit.RootBranchGuards
