/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Full-field chronological-log controls

Library `EthConformance`. The unchanged sixteen rope controls and six conditional
selection scenarios compare complete existing-provider observations. These are
pure data/model checks, not real child/handler execution or compiled cost evidence.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Vm.Core.LogsGuards
open STFSpec.Vm.Core STFSpec.Base

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

-- Direct transliteration of the unchanged accepted16+6 hand controls.
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

#guard controls.length == 22
#guard controls.all fun row ↦ observe row.input == row.expected
#guard controls.all fun row ↦
  row.retained.all fun pair ↦ observe pair.1 == pair.2
#guard controls.all fun row ↦
  let first := observe row.input
  let second := observe row.input
  first == row.expected && second == row.expected

private def shape : LogRope → Nat
  | .empty => 0
  | .leaf _ => 1
  | .concat _ _ => 2

#guard shape .empty != shape (.leaf [])
#guard shape .empty != shape (.concat .empty .empty)
#guard observe .empty == observe (.leaf [])
#guard observe .empty == observe (.concat .empty .empty)

end STFSpec.Conformance.Vm.Core.LogsGuards
