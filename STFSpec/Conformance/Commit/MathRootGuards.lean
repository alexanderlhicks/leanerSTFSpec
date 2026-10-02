/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Conformance.Commit.RootConstructionGuards

/-!
# Complete mathematical-root observations

Library `EthConformance`. Genuine construction precedes the complete top query;
finite controls retain all answer bytes, error diagnostics and initial trace prefixes.
Raw odd paths/empty values exercise Q50 composition, independently of original Tries.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Commit.MathRootGuards

open STFSpec.Base STFSpec.Codec STFSpec.Hash STFSpec.Commit
open RootConstructionGuards

/-- Complete digest observation and retained query state. -/
def recorded (obj : Std.ExtTreeMap Nibbles ByteArray)
    (emptyRoot : Hash32) (state : RootBranchGuards.Trace := {}) :
    List UInt8 × RootBranchGuards.Trace :=
  let (answer, next) := (mathRoot (m := RootBranchGuards.TestState) emptyRoot obj).run state
  (answer.toBytes.toByteArray.data.toList, next)

/-- Original errors with their complete retained state. -/
def failed (obj : Std.ExtTreeMap Nibbles ByteArray)
    (emptyRoot : Hash32) (state : RootBranchGuards.Trace) :
    Except RootBranchGuards.Failure (List UInt8) × RootBranchGuards.Trace :=
  let (answer, next) := (mathRoot (m := RootBranchGuards.TestFailure) emptyRoot obj).run.run state
  (answer.map (fun hash ↦ hash.toBytes.toByteArray.data.toList), next)

/-- Deliberately unrelated caller constant, retained verbatim on empty inputs. -/
def supplied : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat 424242)

/-- Nonempty initial trace to detect accidental trace resets. -/
def initial : RootBranchGuards.Trace :=
  {events := [.query 42 [0, 255, 1] [2, 3, 0]]}

/-- Expected descendants then complete final query, with arbitrary leading-zero answers. -/
def expected (node : Option InternalNode)
    (descendants : RootBranchGuards.Trace) : List UInt8 × RootBranchGuards.Trace :=
  let answer := Hash32.ofBytes32 (FixedBytes.ofNat (1000 + descendants.queries))
  (answer.toBytes.toByteArray.data.toList,
    {events := initial.events ++ descendants.events ++
      [.query descendants.queries (Rlp.encode (assembleInternalNode node)).data.toList
        answer.toBytes.toByteArray.data.toList], queries := descendants.queries + 1})

/-- Independent expected first error at every descendant and the top query. -/
def expectedError (healthy : List UInt8 × RootBranchGuards.Trace) (index : Nat) :
    Except RootBranchGuards.Failure (List UInt8) × RootBranchGuards.Trace :=
  match healthy.2.events[index + initial.events.length]? with
  | some (.query _ preimage _) =>
      (.error (.oracle index preimage),
        {events := healthy.2.events.take (index + initial.events.length) ++
          [.queryError index preimage], queries := index, failQueryAt := some index})
  | _ => (.ok healthy.1, {healthy.2 with failQueryAt := some index})

/-- Actual top leaf encodings have widths 31/32/33. -/
def top (width : Nat) : Std.ExtTreeMap Nibbles ByteArray :=
  mapOf [(key [], bytes (List.replicate (width - 3) 65))]

/-- Independently written full short-form leaf wire, including the outer header. -/
def topWire (width : Nat) : List UInt8 :=
  [UInt8.ofNat (191 + width), 32, UInt8.ofNat (125 + width)] ++
    List.replicate (width - 3) 65

/-- No answer assumptions: arbitrary full-width bit patterns are forwarded. -/
def constantAnswer (obj : Std.ExtTreeMap Nibbles ByteArray) (answer : Hash32) :
    List UInt8 × List (List UInt8) :=
  letI : KeccakQuery (StateM (List (List UInt8))) :=
    ⟨fun wire trace ↦ (answer, trace ++ [wire.data.toList])⟩
  let (result, trace) := (mathRoot (m := StateM (List (List UInt8))) supplied obj).run []
  (result.toBytes.toByteArray.data.toList, trace)

/-- Actual private reference action, used only for finite complete-effect instrumentation. -/
def referenceRecorded (obj : Std.ExtTreeMap Nibbles ByteArray)
    (state : RootBranchGuards.Trace := initial) :
    List Nat × RootBranchGuards.Trace :=
  let action : RootBranchGuards.TestState RlpItem :=
    (rootConstructionOwner% mathRootReference) supplied obj
  let (item, trace) := action.run state
  (itemTokens item, trace)

/-- Fused whole action observed in the same reference result representation. -/
def fusedRecorded (obj : Std.ExtTreeMap Nibbles ByteArray)
    (state : RootBranchGuards.Trace := initial) :
    List Nat × RootBranchGuards.Trace :=
  let (answer, trace) := (mathRoot (m := RootBranchGuards.TestState) supplied obj).run state
  (itemTokens (.bytes answer.toBytes.toByteArray), trace)

/-- Original reference failures and retained full state, without adapting diagnostics. -/
def referenceFailed (obj : Std.ExtTreeMap Nibbles ByteArray)
    (state : RootBranchGuards.Trace) :
    Except RootBranchGuards.Failure (List Nat) × RootBranchGuards.Trace :=
  let action : RootBranchGuards.TestFailure RlpItem :=
    (rootConstructionOwner% mathRootReference) supplied obj
  let (item, trace) := action.run.run state
  (item.map itemTokens, trace)

/-- Fused failures observed in the same complete reference token representation. -/
def fusedFailed (obj : Std.ExtTreeMap Nibbles ByteArray)
    (state : RootBranchGuards.Trace) :
    Except RootBranchGuards.Failure (List Nat) × RootBranchGuards.Trace :=
  let (answer, trace) := (mathRoot (m := RootBranchGuards.TestFailure) supplied obj).run.run state
  (answer.map (fun hash ↦ itemTokens (.bytes hash.toBytes.toByteArray)), trace)

/-- Concrete root and complete query values, for genuine-source comparisons. -/
def concreteTrace (obj : Std.ExtTreeMap Nibbles ByteArray) (emptyRoot : Hash32) :
    List UInt8 × List (List UInt8 × List UInt8) :=
  letI : KeccakQuery (StateM (List (List UInt8 × List UInt8))) :=
    ⟨fun preimage state ↦
      let answer := keccak256 preimage
      (answer, state ++ [(preimage.data.toList, answer.toBytes.toByteArray.data.toList)])⟩
  let (answer, trace) :=
    (mathRoot (m := StateM (List (List UInt8 × List UInt8))) emptyRoot obj).run []
  (answer.toBytes.toByteArray.data.toList, trace)

/-- Full arbitrary context with a nonzero oracle index, unrelated prior events,
and an inactive failure trigger. -/
def seeded (index : Nat) : RootBranchGuards.Trace :=
  {events := [.construct 99 [([1, 15, 0], [255, 0])],
    .query 777 [128, 0, 255] [0, 1], .queryError 998 [12, 13]],
    queries := index, failQueryAt := some (index + 99)}

/-- Independent shifted full-width child references, preserving leading zeros. -/
def seededReference (start : Nat) (digit : Fin 16) : RlpItem :=
  if RootBranchGuards.payloadSize digit.val = 28 then
    .list [.bytes (bytes [32]), .bytes (bytes (List.replicate 28 (UInt8.ofNat digit.val)))]
  else
    .bytes (Hash32.ofBytes32 (FixedBytes.ofNat
      (1000 + start + RootBranchGuards.queryIndexBefore digit.val))).toBytes.toByteArray

/-- Independently enumerated complete branch trace in an arbitrary seeded context. -/
def seededBranchExpected (state : RootBranchGuards.Trace) :
    List UInt8 × RootBranchGuards.Trace :=
  let descendants := (List.range 16).flatMap fun digit ↦
    if RootBranchGuards.payloadSize digit = 28 then [] else
      let index := state.queries + RootBranchGuards.queryIndexBefore digit
      [.query index (RootBranchGuards.expectedPreimage digit)
        (Hash32.ofBytes32 (FixedBytes.ofNat (1000 + index))).toBytes.toByteArray.data.toList]
  let answer := Hash32.ofBytes32 (FixedBytes.ofNat (1010 + state.queries))
  let node := some (.branch (Vector.ofFn (seededReference state.queries))
    (.bytes ByteArray.empty))
  (answer.toBytes.toByteArray.data.toList,
    {state with events := state.events ++ descendants ++
      [.query (state.queries + 10) (Rlp.encode (assembleInternalNode node)).data.toList
        answer.toBytes.toByteArray.data.toList], queries := state.queries + 11})

/-- First-error expectation retains every earlier event and every context field. -/
def seededErrorExpected (state : RootBranchGuards.Trace)
    (healthy : List UInt8 × RootBranchGuards.Trace) (offset : Nat) :
    Except RootBranchGuards.Failure (List UInt8) × RootBranchGuards.Trace :=
  let index := state.queries + offset
  match healthy.2.events[state.events.length + offset]? with
  | some (.query _ preimage _) =>
      (.error (.oracle index preimage),
        {state with events := healthy.2.events.take (state.events.length + offset) ++
          [.queryError index preimage], queries := index, failQueryAt := some index})
  | _ => (.ok healthy.1, {healthy.2 with failQueryAt := some index})

def cases : List (String × Bool) := [
  ("arbitrary supplied constant and unchanged initial state",
    recorded empty supplied initial == (supplied.toBytes.toByteArray.data.toList, initial)),
  ("empty bypasses failing oracle and retains original prefix",
    failed empty supplied {initial with failQueryAt := some 0} ==
      (.ok supplied.toBytes.toByteArray.data.toList, {initial with failQueryAt := some 0})),
  ("actual full top wires31/32/33 query exactly once",
    [31, 32, 33].all fun width ↦
      recorded (top width) supplied initial ==
        ((Hash32.ofBytes32 (FixedBytes.ofNat 1000)).toBytes.toByteArray.data.toList,
          {events := initial.events ++ [.query 0 (topWire width)
            (Hash32.ofBytes32 (FixedBytes.ofNat 1000)).toBytes.toByteArray.data.toList],
            queries := 1})),
  ("all arbitrary answer bytes including zero and leading zeros",
    [0, 1, 255, 2^255, 2^256-1].all fun value ↦
      let answer := Hash32.ofBytes32 (FixedBytes.ofNat value)
      [31, 32, 33].all fun width ↦ constantAnswer (top width) answer ==
        (answer.toBytes.toByteArray.data.toList, [topWire width])),
  ("descendants precede full branch top query",
    recorded thresholds supplied initial == expected expectedThresholdNode thresholdExpected.2),
  ("descendants and extension reference precede full extension top query",
    recorded nested supplied initial == expected expectedNestedNode nestedExpected.2),
  ("all eleven original errors in branch including final query",
    (List.range 11).all fun index ↦ failed thresholds supplied
      {initial with failQueryAt := some index} ==
        expectedError (expected expectedThresholdNode thresholdExpected.2) index),
  ("all twelve original errors in extension including final query",
    (List.range 12).all fun index ↦ failed nested supplied
      {initial with failQueryAt := some index} ==
        expectedError (expected expectedNestedNode nestedExpected.2) index),
  ("Q50 empty-key empty-value leaf fullwire",
    recorded emptySingleton supplied initial ==
      ((Hash32.ofBytes32 (FixedBytes.ofNat 1000)).toBytes.toByteArray.data.toList,
        {events := initial.events ++ [.query 0 [194, 32, 128]
          (Hash32.ofBytes32 (FixedBytes.ofNat 1000)).toBytes.toByteArray.data.toList], queries := 1})),
  ("Q50 raw odd-full-path empty-valued maps reference complete action",
    [empty, emptySingleton, ending, prefixed, thresholds, nested].all fun obj ↦
      referenceRecorded obj == fusedRecorded obj),
  ("nonzero counters retain complete arbitrary state on empty and branch",
    [7, 1000000].all fun start ↦
      recorded empty supplied (seeded start) ==
        (supplied.toBytes.toByteArray.data.toList, seeded start) &&
      recorded thresholds supplied (seeded start) == seededBranchExpected (seeded start)),
  ("all eleven original errors preserve seeded state and complete prefix",
    [7, 1000000].all fun start ↦ (List.range 11).all fun offset ↦
      failed thresholds supplied {(seeded start) with failQueryAt := some (start + offset)} ==
        seededErrorExpected (seeded start) (seededBranchExpected (seeded start)) offset),
  ("all reference-fused first errors retain diagnostics and seeded prefix",
    [7, 1000000].all fun start ↦ (List.range 12).all fun offset ↦
      referenceFailed nested {(seeded start) with failQueryAt := some (start + offset)} ==
        fusedFailed nested {(seeded start) with failQueryAt := some (start + offset)}),
  ("reference full action retains arbitrary original state",
    [7, 1000000].all fun start ↦ [empty, thresholds, nested, RootBranchGuards.longOdd].all
      fun obj ↦ referenceRecorded obj (seeded start) == fusedRecorded obj (seeded start)),
  ("concrete coherent literal empty root",
    (mathRoot (m := Id) HashConsts.literals.emptyTrieRoot empty).toBytes.toByteArray.data.toList ==
      HashConsts.literals.emptyTrieRoot.toBytes.toByteArray.data.toList),
  ("concrete supplied empty root", (mathRoot (m := Id) supplied empty).toBytes.toByteArray.data.toList ==
    supplied.toBytes.toByteArray.data.toList)]

#guard cases.all Prod.snd

/-- Native output includes full query/answer/error values, then finite guard verdicts. -/
def printComplete : IO UInt32 := do
  IO.println s!"root branch actual={reprStr (recorded thresholds supplied initial)}; expected={reprStr (expected expectedThresholdNode thresholdExpected.2)}"
  IO.println s!"root extension actual={reprStr (recorded nested supplied initial)}; expected={reprStr (expected expectedNestedNode nestedExpected.2)}"
  for index in List.range 12 do
    IO.println s!"root extension failure{index}={reprStr (failed nested supplied {initial with failQueryAt := some index})}"
  for width in [31, 32, 33] do
    IO.println s!"top{width}: actual={reprStr (recorded (top width) supplied initial)}"
    for value in [0, 1, 255, 2^255, 2^256-1] do
      let answer := Hash32.ofBytes32 (FixedBytes.ofNat value)
      IO.println s!"arbitrary answer{width}/{value}: actual={reprStr (constantAnswer (top width) answer)}"
  for start in [7, 1000000] do
    let state := seeded start
    IO.println s!"seeded branch{start}: actual={reprStr (recorded thresholds supplied state)}; expected={reprStr (seededBranchExpected state)}"
    for offset in List.range 11 do
      let actual := failed thresholds supplied {state with failQueryAt := some (start + offset)}
      let expected := seededErrorExpected state (seededBranchExpected state) offset
      IO.println s!"seeded error{start}/{offset}: actual={reprStr actual}; expected={reprStr expected}"
  let mut failures := 0
  for (name, result) in cases do
    IO.println s!"mathRoot {name}: {result}"
    if !result then failures := failures + 1
  return failures

end STFSpec.Conformance.Commit.MathRootGuards
