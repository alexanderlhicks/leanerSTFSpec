/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core
import Lean

/-!
# Full native log controls and scoped C3 lifetime diagnostic

Library `EthConformance` item diagnostic; build with `lake build log-rope-bench --wfail`
and audit with `lake exe check-decls LogRopeBench`. `--check-controls` retains all 22
full-field hand observations. `--measure FAMILY N TRIAL` separates construction,
flatten, observation, output/root release and fresh-child discard. Correctness
checks and serialization are outside all operation clocks; no timed checksum.

Expanded recipe occurrences count shared duplicates. Heartbeats count small
allocations, not bytes/all allocations; external process RSS includes runtime,
setup and complete observation storage, not exact peak-live heap. Generated-C
liveness and actual RC decrements must accompany cleanup claims. Fixed A/B/C/D
payload constants remain shared; mixed-payload generates fresh nonempty byte data.
No EVM/frame/helper/source replay, host cap or universal stack/resource claim.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/6/7/10; REVIEW §7.5 C3.
-/

open STFSpec.Vm.Core STFSpec.Base Lean

private abbrev View := List UInt8 × List (List UInt8) × List UInt8

private def view (entry : Log) : View :=
  (entry.address.toBytes.toList,
    entry.topics.toList.map (fun topic ↦ topic.toBytes.toList), entry.data.toList)

private def observe (tree : LogRope) : List View := tree.toList.map view

private def topic0 : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat 0)
private def topic1 : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat 1)
private def topicMax : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat (2 ^ 256 - 1))
private def logA : Log := ⟨Address.ofNat 0, #[], Bytes.empty⟩
private def logB : Log :=
  ⟨Address.ofNat 1, #[topic0, topic1], Bytes.ofList [0, 255, 0, 128]⟩
private def logC : Log :=
  ⟨Address.ofNat 1, #[topic1, topic0, topic1], Bytes.ofList [65, 0, 66, 10, 255]⟩
private def logD : Log :=
  ⟨Address.ofNat (2 ^ 160 - 1), #[topicMax, topic0, topic1, topic0, topicMax], Bytes.empty⟩
private def zero20 : List UInt8 := List.replicate 20 0
private def one20 : List UInt8 := List.replicate 19 0 ++ [1]
private def zero32 : List UInt8 := List.replicate 32 0
private def one32 : List UInt8 := List.replicate 31 0 ++ [1]
private def expectedA : View := (zero20, [], [])
private def expectedB : View := (one20, [zero32, one32], [0, 255, 0, 128])
private def expectedC : View := (one20, [one32, zero32, one32], [65, 0, 66, 10, 255])
private def expectedD : View :=
  (List.replicate 20 255, [List.replicate 32 255, zero32, one32, zero32,
    List.replicate 32 255], [])

private def leftAssociated : LogRope :=
  .concat (.concat (.concat (.leaf [logA]) (.leaf [logB])) (.leaf [logC])) (.leaf [logA])

private structure Control where
  id : String
  input : LogRope
  expected : List View
  retained : List (LogRope × List View) := []

-- Direct transliteration of the unchanged accepted 16+6 hand controls.
private def controls : List Control := [
  { id := "R01", input := .empty, expected := [] },
  { id := "R02", input := .leaf [], expected := [] },
  { id := "R03", input := .leaf [logA], expected := [expectedA] },
  { id := "R04", input := .leaf [logA, logB, logA], expected := [expectedA, expectedB, expectedA] },
  { id := "R05", input := .concat (.leaf [logA]) (.leaf [logB]),
    expected := [expectedA, expectedB] },
  { id := "R06", input := .concat (.leaf [logB]) (.leaf [logA]),
    expected := [expectedB, expectedA] },
  { id := "R07", input := .concat .empty (.concat (.leaf [logA, logB]) .empty),
    expected := [expectedA, expectedB] },
  { id := "R08", input := leftAssociated,
    expected := [expectedA, expectedB, expectedC, expectedA] },
  { id := "R09", input := .concat (.leaf [logA])
      (.concat (.leaf [logB]) (.concat (.leaf [logC]) (.leaf [logA]))),
    expected := [expectedA, expectedB, expectedC, expectedA] },
  { id := "R10", input := .concat (.concat (.leaf [])
      (.concat .empty (.leaf [logB, logA]))) (.leaf [logC]),
    expected := [expectedB, expectedA, expectedC] },
  { id := "R11", input := let t := LogRope.concat (.leaf [logA]) (.leaf [logB]); .concat t t,
    expected := [expectedA, expectedB, expectedA, expectedB] },
  { id := "R12", input := .leaf [logD], expected := [expectedD] },
  { id := "R13", input := .append .empty (.concat (.leaf [logA, logB]) (.leaf [logC])),
    expected := [expectedA, expectedB, expectedC] },
  { id := "R14", input := .append (.concat (.leaf [logA, logB]) (.leaf [logC])) .empty,
    expected := [expectedA, expectedB, expectedC] },
  (let p := LogRope.concat (.leaf [logA]) (.leaf [logB])
   let q := LogRope.leaf [logC, logA]
   { id := "R15", input := .append p q,
     expected := [expectedA, expectedB, expectedC, expectedA],
     retained := [(p, [expectedA, expectedB]), (q, [expectedC, expectedA])] }),
  (let r := leftAssociated
   { id := "R16", input := r,
     expected := [expectedA, expectedB, expectedC, expectedA],
     retained := [(r, [expectedA, expectedB, expectedC, expectedA])] }),
  { id := "S01", input := .append (.append (.leaf [logA]) (.leaf [logB, logC])) (.leaf [logA]),
    expected := [expectedA, expectedB, expectedC, expectedA] },
  (let p := LogRope.leaf [logA]
   let c := LogRope.leaf [logB, logC]
   { id := "S02", input := .append (if false then .append p c else p) (.leaf [logA]),
     expected := [expectedA, expectedA], retained := [(p, [expectedA]), (c, [expectedB, expectedC])] }),
  (let p := LogRope.leaf [logA]
   let c := LogRope.append (.leaf [logB]) (.leaf [logC])
   { id := "S03", input := .append (if false then .append p c else p) (.leaf [logA]),
     expected := [expectedA, expectedA], retained := [(p, [expectedA]), (c, [expectedB, expectedC])] }),
  { id := "S04", input := .append (.append (.leaf [logA]) .empty) (.leaf [logB]),
    expected := [expectedA, expectedB] },
  (let stored := LogRope.leaf [logA, logB]
   { id := "S05", input := if false then stored else .empty, expected := [],
     retained := [(stored, [expectedA, expectedB])] }),
  { id := "S06", input := .append (.leaf [logA]) (.leaf [logA]),
    expected := [expectedA, expectedA] }
]

private def bytesJson (bytes : List UInt8) : Json :=
  toJson (bytes.map UInt8.toNat)

private def viewJson (value : View) : Json :=
  Json.mkObj [("address", bytesJson value.1),
    ("topics", toJson (value.2.1.map bytesJson)), ("data", bytesJson value.2.2)]

private def viewsJson (values : List View) : Json := toJson (values.map viewJson)

private def treeJson : LogRope → Json
  | .empty => Json.mkObj [("node", toJson "empty")]
  | .leaf entries => Json.mkObj [("node", toJson "leaf"), ("logs", viewsJson (entries.map view))]
  | .concat left right => Json.mkObj [("node", toJson "concat"),
      ("left", treeJson left), ("right", treeJson right)]

@[noinline] private def checkControls (emit : Bool) : IO Unit := do
  for row in controls do
    let before := observe row.input
    unless before == row.expected do throw (IO.userError ("control before: " ++ row.id))
    let retainedBefore := row.retained.map (fun p ↦ observe p.1)
    unless retainedBefore == row.retained.map Prod.snd do
      throw (IO.userError ("control saved before: " ++ row.id))
    let distractor := LogRope.append (.leaf [logD]) (.leaf [logA])
    unless observe distractor == [expectedD, expectedA] do
      throw (IO.userError "distractor mismatch")
    let after := observe row.input
    let retainedAfter := row.retained.map (fun p ↦ observe p.1)
    unless after == row.expected && retainedAfter == retainedBefore do
      throw (IO.userError ("control retained after: " ++ row.id))
    if emit then
      IO.println ((Json.mkObj [("schema", toJson "log-rope-controls-v1"),
        ("id", toJson row.id), ("input", treeJson row.input),
        ("expected", viewsJson row.expected), ("before", viewsJson before),
        ("distractor", viewsJson (observe distractor)), ("after", viewsJson after),
        ("retained", toJson ((row.retained.zip (retainedBefore.zip retainedAfter)).map
          fun (pair, snapshots) ↦ Json.mkObj [("input", treeJson pair.1),
            ("expected", viewsJson pair.2), ("before", viewsJson snapshots.1),
            ("after", viewsJson snapshots.2)]))]).compress)

private inductive Family where
  | balanced | leftSkew | rightSkew | siblings | empty | longLeaf | shared | mixedSelect
  | mixedPayload

private def familyName : Family → String
  | .balanced => "balanced" | .leftSkew => "left-skew" | .rightSkew => "right-skew"
  | .siblings => "siblings" | .empty => "empty" | .longLeaf => "long-leaf"
  | .shared => "shared" | .mixedSelect => "mixed-select" | .mixedPayload => "mixed-payload"

private def parseFamily : String → Option Family
  | "balanced" => some .balanced | "left-skew" => some .leftSkew
  | "right-skew" => some .rightSkew | "siblings" => some .siblings | "empty" => some .empty
  | "long-leaf" => some .longLeaf | "shared" => some .shared
  | "mixed-select" => some .mixedSelect | "mixed-payload" => some .mixedPayload | _ => none

private def event (i : Nat) : Log :=
  match i % 4 with | 0 => logA | 1 => logB | 2 => logC | _ => logD

private def eventView (i : Nat) : View :=
  match i % 4 with | 0 => expectedA | 1 => expectedB | 2 => expectedC | _ => expectedD

private def dataLength (i : Nat) : Nat :=
  match i % 4 with | 0 => 0 | 1 => 4 | 2 => 33 | _ => 1024

private def freshEntry (i : Nat) : Log :=
  ⟨Address.ofNat i, ([topic0, topic1, topicMax, topic1, topic0, topicMax].take (i % 6)).toArray,
    Bytes.generate (dataLength i) (fun j ↦ UInt8.ofNat ((17 * i + 31 * j + 128) % 256))⟩

private def freshView (i : Nat) : View :=
  ((List.range 20).map (fun j ↦ UInt8.ofNat (i / 256 ^ (19 - j) % 256)),
    [zero32, one32, List.replicate 32 255, one32, zero32, List.replicate 32 255].take (i % 6),
    (List.range (dataLength i)).map (fun j ↦ UInt8.ofNat ((17 * i + 31 * j + 128) % 256)))

-- Dynamic IO results below prevent closed application lifting of measured roots.
@[noinline] private def dynamicValue {α : Type} (value : α) : IO α := do
  let holder ← IO.mkRef value
  holder.get

-- These builders receive dynamic arguments in measured closed-payload cases.
@[noinline] private def single (entry : Log) : LogRope := .leaf [entry]
@[noinline] private def sharedPair (a b : Log) : LogRope := .concat (single a) (single b)
@[noinline] private def emptyChild (entries : List Log) : LogRope := .concat .empty (.leaf entries)

private def pairLevel (level : Array LogRope) : Array LogRope := Id.run do
  let mut result := #[]
  for i in [:(level.size + 1) / 2] do
    if h : 2 * i < level.size then
      if h' : 2 * i + 1 < level.size then
        result := result.push (LogRope.append level[2 * i] level[2 * i + 1])
      else result := result.push level[2 * i]
  return result

@[noinline] private def balanced (n : Nat) : LogRope := Id.run do
  let mut level := ((List.range n).map (fun i ↦ single (event i))).toArray
  for _ in [:n] do
    if level.size > 1 then level := pairLevel level
  return level[0]?.getD .empty

@[noinline] private def skew (right : Bool) (n : Nat) : LogRope := Id.run do
  let mut result := LogRope.empty
  for i in [:n] do
    let child := single (event (if right then n - 1 - i else i))
    result := if right then .append child result else .append result child
  return result

@[noinline] private def repeatSubtree (n : Nat) (child : LogRope) : LogRope := Id.run do
  let mut result := LogRope.empty
  for _ in [:n] do result := .append result child
  return result

private abbrev RootRef := IO.Ref (Option LogRope)

@[noinline] private def joinRefs (parent child : RootRef) : IO Unit := do
  let some p ← parent.get | throw (IO.userError "missing parent")
  let some c ← child.get | throw (IO.userError "missing child")
  parent.set (some (LogRope.append p c))
  child.set none

-- IO writes force attempted failed children to exist; pure selection alone could erase them.
@[noinline] private def selectedConstruction (nested : Bool) (n : Nat)
    (root : RootRef) : IO Unit := do
  let first ← dynamicValue logA
  root.set (some (single first))
  let child ← IO.mkRef (none : Option LogRope)
  for i in [:n] do
    child.set (some (if nested then sharedPair (event i) (event (i + 1)) else single (event i)))
    if i % 2 == 0 then joinRefs root child else child.set none

@[noinline] private def construct (family : Family) (n : Nat) (root : RootRef) : IO Unit := do
  match family with
  | .balanced => root.set (some (balanced n))
  | .leftSkew => root.set (some (skew false n))
  | .rightSkew => root.set (some (skew true n))
  | .siblings => selectedConstruction false n root
  | .empty =>
    let entries ← dynamicValue ([] : List Log)
    root.set (some (repeatSubtree n (emptyChild entries)))
  | .longLeaf => root.set (some (.leaf ((List.range n).map event)))
  | .shared =>
    let a ← dynamicValue logA
    let b ← dynamicValue logB
    root.set (some (repeatSubtree n (sharedPair a b)))
  | .mixedSelect => selectedConstruction true n root
  | .mixedPayload => root.set (some (.leaf ((List.range n).map freshEntry)))

private def expected (family : Family) (n : Nat) : List View :=
  match family with
  | .balanced | .leftSkew | .rightSkew | .longLeaf => (List.range n).map eventView
  | .siblings => expectedA :: ((List.range n).filter (fun i ↦ i % 2 == 0)).map eventView
  | .empty => []
  | .shared => (List.range n).flatMap (fun _ ↦ [expectedA, expectedB])
  | .mixedSelect => expectedA :: ((List.range n).filter (fun i ↦ i % 2 == 0)).flatMap
      (fun i ↦ [eventView i, eventView (i + 1)])
  | .mixedPayload => (List.range n).map freshView

-- These are recipe-expanded occurrences, not distinct heap objects or byte allocations.
private def recipe (family : Family) (n : Nat) : Nat × Nat × Nat × Nat :=
  let m := (n + 1) / 2
  match family with
  | .balanced => (2 * n - 1, n, if n = 1 then 1 else (n - 1).log2 + 2, n - 1)
  | .leftSkew | .rightSkew => (2 * n + 1, n, n + 1, n)
  | .siblings => (2 * m + 1, m + 1, m + 1, m)
  | .empty => (4 * n + 1, 0, n + 2, n)
  | .longLeaf | .mixedPayload => (1, n, 1, 0)
  | .shared => (4 * n + 1, 2 * n, n + 2, n)
  | .mixedSelect => (4 * m + 1, 2 * m + 1, m + 2, m)

private structure Metric where
  ns : Nat
  smallAllocations : Nat

private def metricJson (value : Metric) : Json :=
  Json.mkObj [("ns", toJson value.ns), ("small_allocation_heartbeats", toJson value.smallAllocations)]

@[noinline] private def measureRegion (action : IO Unit) : IO Metric := do
  let hb0 ← IO.getNumHeartbeats
  let t0 ← IO.monoNanosNow
  action
  let t1 ← IO.monoNanosNow
  let hb1 ← IO.getNumHeartbeats
  return ⟨t1 - t0, hb1 - hb0⟩

@[noinline] private def flattenInto (root : RootRef) (output : IO.Ref (List Log)) : IO Unit := do
  let some tree ← root.get | throw (IO.userError "missing flatten input")
  output.set tree.toList

@[noinline] private def observeInto (output : IO.Ref (List Log))
    (observed : IO.Ref (List View)) : IO Unit := do
  observed.set ((← output.get).map view)

@[noinline] private def checkObserved (observed : IO.Ref (List View))
    (wanted : List View) : IO Unit := do
  unless (← observed.get) == wanted do throw (IO.userError "complete native model mismatch")

@[noinline] private def checkRoot (root : RootRef) (wanted : List View) : IO Unit := do
  let some tree ← root.get | throw (IO.userError "missing validation root")
  unless observe tree == wanted do throw (IO.userError "complete retained-root mismatch")

-- No root get: clearing this sole holder actually decrements its old owned value here.
@[noinline] private def releaseRoot (root : RootRef) : IO Unit := root.set none
@[noinline] private def releaseOutput (output : IO.Ref (List Log)) : IO Unit := output.set []
@[noinline] private def releaseObservation (observed : IO.Ref (List View)) : IO Unit :=
  observed.set []

@[noinline] private def runMeasurement (family : Family) (n trial : Nat) : IO Unit := do
  checkControls false
  let wanted := expected family n
  let root ← IO.mkRef (none : Option LogRope)
  let output ← IO.mkRef ([] : List Log)
  let observed ← IO.mkRef ([] : List View)
  let baseline ← measureRegion (pure ())
  let buildMetric ← measureRegion (construct family n root)
  let flattenMetric ← measureRegion (flattenInto root output)
  let observeMetric ← measureRegion (observeInto output observed)
  checkObserved observed wanted
  let observationRelease ← measureRegion (releaseObservation observed)
  let outputRelease ← measureRegion (releaseOutput output)
  let rootRelease ← measureRegion (releaseRoot root)
  -- Fresh independent owned child. Its builder/check IO frames return before last-owner release.
  let parent ← IO.mkRef (none : Option LogRope)
  let parentEntry ← dynamicValue logA
  parent.set (some (single parentEntry))
  let child ← IO.mkRef (none : Option LogRope)
  construct family n child
  checkRoot child wanted
  checkRoot parent [expectedA]
  let discardMetric ← measureRegion (releaseRoot child)
  checkRoot parent [expectedA]
  releaseRoot parent
  let units := recipe family n
  IO.println ((Json.mkObj [("schema", toJson "log-rope-c3-v1"),
    ("family", toJson (familyName family)), ("scale", toJson n), ("trial", toJson trial),
    ("node_occurrences", toJson units.1), ("log_occurrences", toJson units.2.1),
    ("height", toJson units.2.2.1), ("accepted_appends", toJson units.2.2.2),
    ("complete_model_gate", toJson true), ("saved_parent_gate", toJson true),
    ("metrics", Json.mkObj [("baseline", metricJson baseline),
      ("construction", metricJson buildMetric), ("flatten", metricJson flattenMetric),
      ("observation", metricJson observeMetric),
      ("observation_release", metricJson observationRelease),
      ("output_release", metricJson outputRelease), ("root_release", metricJson rootRelease),
      ("discard_release", metricJson discardMetric)])]).compress)

/-- Full-field controls or the bounded native C3 diagnostic. Bench errors are tool diagnostics,
not VM errors, semantic input caps or an implementation of child incorporation. -/
def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["--check-controls"] => checkControls true
    | ["--measure", familyText, nText, trialText] =>
      let some family := parseFamily familyText | throw (IO.userError "unknown family")
      let some n := nText.toNat? | throw (IO.userError "scale must be a natural")
      let some trial := trialText.toNat? | throw (IO.userError "trial must be a natural")
      if n = 0 then throw (IO.userError "scale must be positive")
      runMeasurement family n trial
    | _ => throw (IO.userError "expected --check-controls or --measure FAMILY N TRIAL")
    return 0
  catch error =>
    (← IO.getStderr).putStrLn s!"FAIL {error}"
    return 1
