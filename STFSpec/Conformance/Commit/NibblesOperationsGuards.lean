/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit
import Std.Data.ExtTreeMap.Lemmas

/-!
# Packed nibble construction, copying and ordering regressions

Library `EthConformance`. Tests full public values and actual map-key equality.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Commit.NibblesOperationsGuards

open STFSpec.Commit

/-- Test ingress through the bounded model constructor. -/
def path (xs : List Nat) : Nibbles :=
  Nibbles.ofList (xs.map (fun n ↦ ⟨n % 16, by omega⟩))

/-- Complete digit observations, with no checksum. -/
def digits (x : Nibbles) : List Nat := x.toList.map Fin.val

/-- Bounded affine callback used by generation tests. -/
def affine (i : Nat) : Fin 16 := ⟨(3 * i + 7) % 16, by omega⟩

/-- Bounded mixed callback covers changing stretches on long paths. -/
def mixed (i : Nat) : Fin 16 := ⟨(i / 7 + 5 * i + i % 3) % 16, by omega⟩

/-- Every digit pair is compared in both singleton and shared-prefix paths. -/
def allDigitPairs : Bool := (List.range 16).all fun a ↦ (List.range 16).all fun b ↦
  compare (path [a]) (path [b]) == compare a b &&
  compare (path [0, a]) (path [0, b]) == compare a b &&
  decide ((path [a] = path [b]) ↔ a = b)

/-- All small windows, plus equal/reversed/unavailable huge natural windows. -/
def allWindows : Bool :=
  [[], [0], [15], List.range 16, [0, 15, 0, 1, 15]].all fun xs ↦
    let x := path xs
    let offsets := List.range (xs.length + 3) ++ [2^128, 2^1024]
    offsets.all fun start ↦ offsets.all fun stop ↦
      digits (x.extract start stop) == (xs.drop start).take (stop - start) &&
      (x.extract start stop).size == min stop xs.length - start &&
      digits (x.take stop) == xs.take stop &&
      digits (x.drop start) == xs.drop start

/-- Zero/extreme/affine/mixed callbacks produce every full expected output. -/
def allGenerators : Bool := [0, 1, 2, 15, 16, 64, 4096, 4097].all fun n ↦
  digits (Nibbles.generate n (fun _ ↦ 0)) == List.replicate n 0 &&
  digits (Nibbles.generate n (fun _ ↦ 15)) == List.replicate n 15 &&
  digits (Nibbles.generate n affine) == (List.range n).map (fun i ↦ (3*i+7)%16) &&
  digits (Nibbles.generate n mixed) == (List.range n).map (fun i ↦ (i/7+5*i+i%3)%16) &&
  (Nibbles.generate n mixed).size == n

/-- Equal long paths, proper prefixes and both early and late mismatch directions. -/
def longChecks : Bool :=
  let x := Nibbles.generate 4096 mixed
  let y := Nibbles.generate 4097 mixed
  let endMismatch := Nibbles.generate 4096 fun i ↦ if i = 4095 then 15 else mixed i
  let firstMismatch := Nibbles.generate 4096 fun i ↦ if i = 0 then 15 else mixed i
  digits (y.take 4096) == digits x &&
  digits (y.drop 4096) == [(mixed 4096).val] &&
  digits (y.extract 4095 (2^1024)) == [(mixed 4095).val, (mixed 4096).val] &&
  compare x x == .eq && compare x y == .lt && compare y x == .gt &&
  compare x endMismatch == .lt && compare endMismatch x == .gt &&
  compare x firstMismatch == .lt && compare firstMismatch x == .gt

/-- Real map keys distinguish proper prefixes and significant zero digits. -/
def mapChecks : Bool :=
  let m : Std.ExtTreeMap Nibbles Nat := ∅
  let m := ((m.insert (path [1]) 10).insert (path [1, 0]) 20).insert (path [0, 1]) 30
  let m := m.insert (path [1]) 40
  m[path [1]]? == some 40 && m[path [1, 0]]? == some 20 &&
  m[path [0, 1]]? == some 30 && m[path [0]]? == none &&
  m.size == 3 &&
  (m.toList.map (fun p ↦ (digits p.1, p.2))) == [([0, 1], 30), ([1], 40), ([1, 0], 20)]

#guard allDigitPairs
#guard allWindows
#guard allGenerators
#guard longChecks
#guard mapChecks
#guard compare (path []) (path []) == .eq
#guard compare (path []) (path [0]) == .lt
#guard compare (path [0]) (path []) == .gt
#guard compare (path [1]) (path [1, 0]) == .lt
#guard compare (path [15]) (path [0, 15]) == .gt
#guard compare (path [0, 1]) (path [1]) == .lt
#guard compare (path [1, 2, 3]) (path [1, 2, 4, 0]) == .lt
#guard compare (path [1, 3]) (path [1, 2, 15]) == .gt
#guard decide (Nibbles.generate 0 affine = Nibbles.generate 0 mixed)
#guard decide (Nibbles.generate 64 affine =
  Nibbles.generate 64 (fun i ↦ if i < 64 then affine i else 15))

end STFSpec.Conformance.Commit.NibblesOperationsGuards
