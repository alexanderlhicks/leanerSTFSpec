/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.WriteOrder
import STFSpec.Base.FixedBytes

/-!
# Compiled WriteOrder regression runner

Library `EthConformance`: complete finite observations of internal State order
support, including paired saved-root models. Proof clients live in
`STFSpec/Conformance/State/WriteOrderCallerProofs.lean` and `WriteOrderGuards.lean`.
Run with `lake build write-order-native-tests --wfail` followed by
`lake exe write-order-native-tests`.
Spec guidance: `STFSpec/informal/modules/EthState.md`.
-/

open STFSpec.State STFSpec.State.WriteOrder

private def observe (r : WriteOrder Nat) (w : Std.ExtTreeMap Nat (Option Nat)) :=
  (r.next, r.positions.toList, r.keysByPosition.toList, w.toList, toList r)
private def r0 : WriteOrder Nat := empty
private def w0 : Std.ExtTreeMap Nat (Option Nat) := ∅
private def r1 := record r0 9
private def w1 := w0.insert 9 (some 90)
private def r2 := record r1 2
private def w2 := w1.insert 2 none
private def rDuplicate := record r2 9
private def wDuplicate := w2.insert 9 (some 0)
private def rAbsent := erase rDuplicate 4
private def wAbsent := wDuplicate.erase 4
private def r3 := record rAbsent 7
private def w3 := wAbsent.insert 7 (some 70)
private def rMiddle := erase r3 2
private def wMiddle := w3.erase 2
private def rHead := erase rMiddle 9
private def wHead := wMiddle.erase 9
private def rTail := erase rHead 7
private def wTail := wHead.erase 7
private def rReinsert := record rTail 2
private def wReinsert := wTail.insert 2 none

private def sparse : WriteOrder Nat :=
  ⟨2^100+17, (∅ : Std.ExtTreeMap Nat Nat).insert 9 4 |>.insert 2 100,
    (∅ : Std.ExtTreeMap Nat Nat).insert 4 9 |>.insert 100 2⟩
private def sparseW := (∅ : Std.ExtTreeMap Nat (Option Nat)).insert 9 (some 90) |>.insert 2 none

-- Persistent roots are paired roots: restore includes next and both maps.
private def left := record (erase r2 9) 7
private def leftW := (w2.erase 9).insert 7 (some 70)
private def right := record r2 4
private def rightW := w2.insert 4 (some 40)
private def leftNested := record left 8
private def leftNestedW := leftW.insert 8 (some 80)
private def restoredInner := left
private def restoredOuter := r2

-- Bounded nested-map shape only: no F7 source-set iteration policy chosen.
private def nested0 : Std.ExtTreeMap Nat (WriteOrder Nat × Std.ExtTreeMap Nat (Option Nat)) :=
  (∅ : Std.ExtTreeMap Nat (WriteOrder Nat × Std.ExtTreeMap Nat (Option Nat))).insert 5 (r2,w2)
private def nestedClear := nested0.erase 5
private def nestedRecreate := nestedClear.insert 5
  (record empty 7, (∅ : Std.ExtTreeMap Nat (Option Nat)).insert 7 (some 0))
private def incoming := [4,9,1]
private def merged := incoming.foldl record r2
private def mergedW := (w2.insert 4 (some 40)).insert 9 (some 99) |>.insert 1 none

private def mismatch : WriteOrder Nat :=
  ⟨1, (∅ : Std.ExtTreeMap Nat Nat).insert 1 0, (∅ : Std.ExtTreeMap Nat Nat).insert 0 2⟩
private def orphan : WriteOrder Nat :=
  ⟨1, ∅, (∅ : Std.ExtTreeMap Nat Nat).insert 0 2⟩
private def collision : WriteOrder Nat :=
  ⟨0, (∅ : Std.ExtTreeMap Nat Nat).insert 2 0, (∅ : Std.ExtTreeMap Nat Nat).insert 0 2⟩
private def duplicates : WriteOrder Nat :=
  ⟨2, ∅, (∅ : Std.ExtTreeMap Nat Nat).insert 0 1 |>.insert 1 1⟩
private structure Alias where
  tag : Nat
  deriving BEq, DecidableEq
private instance : Ord Alias := ⟨fun _ _ => .eq⟩
private instance : Std.TransOrd Alias where
  eq_swap := rfl
  isLE_trans := by intros; rfl
private def aliasR : WriteOrder Alias := record (record empty ⟨1⟩) ⟨2⟩

-- Both retained parents and repeated saved roots are observed after descendants.
private def restoredInnerAgain := restoredInner
private def restoredOuterAgain := restoredOuter

private def missingReverse : WriteOrder Nat :=
  ⟨1, (∅ : Std.ExtTreeMap Nat Nat).insert 1 0, ∅⟩

private def pattern (n seed : Nat) : List UInt8 :=
  (List.range n).map (fun i ↦ UInt8.ofNat (seed + i * 37))
private def address (seed : Nat) : STFSpec.Base.Address :=
  STFSpec.Base.Address.ofNat ((pattern 20 seed).foldl (fun n b ↦ 256*n+b.toNat) 0)
private def slot (seed : Nat) : STFSpec.Base.Bytes32 :=
  STFSpec.Base.FixedBytes.ofNat ((pattern 32 seed).foldl (fun n b ↦ 256*n+b.toNat) 0)
private def addressEqual := STFSpec.Base.Address.ofNat (address 9).toNat
private def slotEqual : STFSpec.Base.Bytes32 := STFSpec.Base.FixedBytes.ofNat (slot 9).toNat
private def keyObservation {K : Type} [Ord K] [Std.TransOrd K]
    (bytes : K → List UInt8) (r : WriteOrder K) (w : Std.ExtTreeMap K (Option Nat)) :=
  (r.next, r.positions.toList.map (fun x ↦ (bytes x.1,x.2)),
    r.keysByPosition.toList.map (fun x ↦ (x.1,bytes x.2)),
    w.toList.map (fun x ↦ (bytes x.1,x.2)), (toList r).map bytes)
private def addressR := record (record (record empty (address 9)) (address 2)) addressEqual
private def addressW := (∅ : Std.ExtTreeMap STFSpec.Base.Address (Option Nat)).insert
  (address 9) (some 90) |>.insert (address 2) none |>.insert addressEqual (some 0)
private def slotR := record (record (record empty (slot 9)) (slot 2)) slotEqual
private def slotW := (∅ : Std.ExtTreeMap STFSpec.Base.Bytes32 (Option Nat)).insert
  (slot 9) (some 90) |>.insert (slot 2) none |>.insert slotEqual (some 0)

/-- Compiled complete-value regression entry point for internal State order support. -/
def main : IO UInt32 := do
  try
    unless (observe r0 w0 == (0, [], [], [], [])) do
      throw (IO.userError "case 0")
    unless (observe r1 w1 == (1, [(9,0)], [(0,9)], [(9,some 90)], [9])) do
      throw (IO.userError "case 1")
    unless (observe r2 w2 ==
      (2, [(2,1),(9,0)], [(0,9),(1,2)], [(2,none),(9,some 90)], [9,2])) do
      throw (IO.userError "case 2")
    unless (observe rDuplicate wDuplicate ==
      (2, [(2,1),(9,0)], [(0,9),(1,2)], [(2,none),(9,some 0)], [9,2])) do
      throw (IO.userError "case 3")
    unless (observe rAbsent wAbsent ==
      (2, [(2,1),(9,0)], [(0,9),(1,2)], [(2,none),(9,some 0)], [9,2])) do
      throw (IO.userError "case 4")
    unless (observe r3 w3 ==
      (3, [(2,1),(7,2),(9,0)], [(0,9),(1,2),(2,7)], [(2,none),(7,some 70),(9,some 0)], [9,2,7])) do
      throw (IO.userError "case 5")
    unless (observe rMiddle wMiddle ==
      (3, [(7,2),(9,0)], [(0,9),(2,7)], [(7,some 70),(9,some 0)], [9,7])) do
      throw (IO.userError "case 6")
    unless (observe rHead wHead == (3, [(7,2)], [(2,7)], [(7,some 70)], [7])) do
      throw (IO.userError "case 7")
    unless (observe rTail wTail == (3, [], [], [], [])) do
      throw (IO.userError "case 8")
    unless (observe rReinsert wReinsert == (4, [(2,3)], [(3,2)], [(2,none)], [2])) do
      throw (IO.userError "case 9")
    unless (observe sparse sparseW ==
      (2^100+17, [(2,100),(9,4)], [(4,9),(100,2)], [(2,none),(9,some 90)], [9,2])) do
      throw (IO.userError "case 10")
    unless (observe (record sparse 7) (sparseW.insert 7 (some 0)) ==
      (2^100+18, [(2,100),(7,2^100+17),(9,4)], [(4,9),(100,2),(2^100+17,7)],
        [(2,none),(7,some 0),(9,some 90)], [9,2,7])) do
      throw (IO.userError "case 11")
    unless (observe (erase sparse 9) (sparseW.erase 9) ==
      (2^100+17, [(2,100)], [(100,2)], [(2,none)], [2])) do
      throw (IO.userError "case 12")
    unless (observe left leftW ==
      (3, [(2,1),(7,2)], [(1,2),(2,7)], [(2,none),(7,some 70)], [2,7])) do
      throw (IO.userError "case 13")
    unless (observe right rightW ==
      (3, [(2,1),(4,2),(9,0)], [(0,9),(1,2),(2,4)],
        [(2,none),(4,some 40),(9,some 90)], [9,2,4])) do
      throw (IO.userError "case 14")
    unless (observe leftNested leftNestedW ==
      (4, [(2,1),(7,2),(8,3)], [(1,2),(2,7),(3,8)],
        [(2,none),(7,some 70),(8,some 80)], [2,7,8])) do
      throw (IO.userError "case 15")
    unless (observe restoredInner leftW ==
      (3, [(2,1),(7,2)], [(1,2),(2,7)], [(2,none),(7,some 70)], [2,7])) do
      throw (IO.userError "case 16")
    unless (observe restoredOuter w2 ==
      (2, [(2,1),(9,0)], [(0,9),(1,2)], [(2,none),(9,some 90)], [9,2])) do
      throw (IO.userError "case 17")
    unless (nestedClear.toList.map (fun x ↦ (x.1, observe x.2.1 x.2.2)) == []) do
      throw (IO.userError "case 18")
    unless ((nested0[5]?).map (fun x => observe x.1 x.2) ==
      some (2, [(2,1),(9,0)], [(0,9),(1,2)], [(2,none),(9,some 90)], [9,2])) do
      throw (IO.userError "case 19")
    unless ((nestedRecreate[5]?).map (fun x => observe x.1 x.2) ==
      some (1, [(7,0)], [(0,7)], [(7,some 0)], [7])) do
      throw (IO.userError "case 20")
    unless (observe merged mergedW ==
      (4, [(1,3),(2,1),(4,2),(9,0)], [(0,9),(1,2),(2,4),(3,1)],
        [(1,none),(2,none),(4,some 40),(9,some 99)], [9,2,4,1])) do
      throw (IO.userError "case 21")
    unless (toList mismatch == [2]) do
      throw (IO.userError "case 22")
    unless (toList (erase mismatch 1) == []) do
      throw (IO.userError "case 23")
    unless ((toList mismatch).filter (fun a => compare 1 a != .eq) == [2]) do
      throw (IO.userError "case 24")
    unless (toList orphan == [2]) do
      throw (IO.userError "case 25")
    unless (orphan.positions[2]? == none) do
      throw (IO.userError "case 26")
    unless (toList (record collision 1) == [1]) do
      throw (IO.userError "case 27")
    unless (toList collision ++ [1] == [2,1]) do
      throw (IO.userError "case 28")
    unless (toList duplicates == [1,1]) do
      throw (IO.userError "case 29")
    unless (toList (erase duplicates 1) == [1,1]) do
      throw (IO.userError "case 30")
    unless ((toList duplicates).filter (fun a => compare 1 a != .eq) == []) do
      throw (IO.userError "case 31")
    unless ((toList aliasR).map Alias.tag == [1]) do
      throw (IO.userError "case 32")
    unless (aliasR.next == 1) do
      throw (IO.userError "case 33")
    unless (aliasR.positions[(⟨2⟩ : Alias)]?.isSome) do
      throw (IO.userError "case 34")
    unless (observe restoredInnerAgain leftW ==
      (3, [(2,1),(7,2)], [(1,2),(2,7)], [(2,none),(7,some 70)], [2,7])) do
      throw (IO.userError "case 35")
    unless (observe restoredOuterAgain w2 ==
      (2, [(2,1),(9,0)], [(0,9),(1,2)], [(2,none),(9,some 90)], [9,2])) do
      throw (IO.userError "case 36")
    unless (observe r2 w2 ==
      (2, [(2,1),(9,0)], [(0,9),(1,2)], [(2,none),(9,some 90)], [9,2])) do
      throw (IO.userError "case 37")
    unless (observe mismatch w0 == (1, [(1,0)], [(0,2)], [], [2])) do
      throw (IO.userError "case 38")
    unless (observe (erase mismatch 1) w0 == (1, [], [], [], [])) do
      throw (IO.userError "case 39")
    unless (observe orphan w0 == (1, [], [(0,2)], [], [2])) do
      throw (IO.userError "case 40")
    unless (observe collision w0 == (0, [(2,0)], [(0,2)], [], [2])) do
      throw (IO.userError "case 41")
    unless (observe (record collision 1) w0 == (1, [(1,0),(2,0)], [(0,1)], [], [1])) do
      throw (IO.userError "case 42")
    unless (observe duplicates w0 == (2, [], [(0,1),(1,1)], [], [1,1])) do
      throw (IO.userError "case 43")
    unless (observe (erase duplicates 1) w0 == (2, [], [(0,1),(1,1)], [], [1,1])) do
      throw (IO.userError "case 44")
    unless (observe missingReverse w0 == (1, [(1,0)], [], [], [])) do
      throw (IO.userError "case 45")
    unless (observe (record mismatch 1) w0 == observe mismatch w0) do
      throw (IO.userError "case 46")
    unless (observe (erase orphan 1) w0 == observe orphan w0) do
      throw (IO.userError "case 47")
    unless (STFSpec.Base.Address.ofBytes? (address 9).toBytes == some addressEqual) do
      throw (IO.userError "case 48")
    unless (STFSpec.Base.FixedBytes.ofBytes? (slot 9).toBytes == some slotEqual) do
      throw (IO.userError "case 49")
    unless (keyObservation (fun a ↦ a.toBytes.toList) addressR addressW ==
      (2, [(pattern 20 2,1),(pattern 20 9,0)], [(0,pattern 20 9),(1,pattern 20 2)],
        [(pattern 20 2,none),(pattern 20 9,some 0)], [pattern 20 9,pattern 20 2])) do
      throw (IO.userError "case 50")
    unless (keyObservation (fun a ↦ a.toBytes.toList) slotR slotW ==
      (2, [(pattern 32 2,1),(pattern 32 9,0)], [(0,pattern 32 9),(1,pattern 32 2)],
        [(pattern 32 2,none),(pattern 32 9,some 0)], [pattern 32 9,pattern 32 2])) do
      throw (IO.userError "case 51")
    unless (keyObservation (fun a ↦ a.toBytes.toList) (erase addressR addressEqual)
      (addressW.erase addressEqual) ==
      (2, [(pattern 20 2,1)], [(1,pattern 20 2)], [(pattern 20 2,none)], [pattern 20 2])) do
      throw (IO.userError "case 52")
    unless (keyObservation (fun a ↦ a.toBytes.toList) (erase slotR slotEqual)
      (slotW.erase slotEqual) ==
      (2, [(pattern 32 2,1)], [(1,pattern 32 2)], [(pattern 32 2,none)], [pattern 32 2])) do
      throw (IO.userError "case 53")
    IO.println ("r0 " ++ reprStr (observe r0 w0))
    IO.println ("r1 " ++ reprStr (observe r1 w1))
    IO.println ("r2 " ++ reprStr (observe r2 w2))
    IO.println ("rDuplicate " ++ reprStr (observe rDuplicate wDuplicate))
    IO.println ("rAbsent " ++ reprStr (observe rAbsent wAbsent))
    IO.println ("r3 " ++ reprStr (observe r3 w3))
    IO.println ("rMiddle " ++ reprStr (observe rMiddle wMiddle))
    IO.println ("rHead " ++ reprStr (observe rHead wHead))
    IO.println ("rTail " ++ reprStr (observe rTail wTail))
    IO.println ("rReinsert " ++ reprStr (observe rReinsert wReinsert))
    IO.println ("sparse " ++ reprStr (observe sparse sparseW))
    IO.println ("left " ++ reprStr (observe left leftW))
    IO.println ("right " ++ reprStr (observe right rightW))
    IO.println ("leftNested " ++ reprStr (observe leftNested leftNestedW))
    IO.println ("restoredInner " ++ reprStr (observe restoredInner leftW))
    IO.println ("restoredOuter " ++ reprStr (observe restoredOuter w2))
    IO.println ("restoredInnerAgain " ++ reprStr (observe restoredInnerAgain leftW))
    IO.println ("restoredOuterAgain " ++ reprStr (observe restoredOuterAgain w2))
    IO.println ("merged " ++ reprStr (observe merged mergedW))
    IO.println ("mismatch " ++ reprStr (observe mismatch w0))
    IO.println ("orphan " ++ reprStr (observe orphan w0))
    IO.println ("collision " ++ reprStr (observe collision w0))
    IO.println ("duplicates " ++ reprStr (observe duplicates w0))
    IO.println ("missingReverse " ++ reprStr (observe missingReverse w0))
    IO.println ("sparseRecord " ++ reprStr (observe (record sparse 7) (sparseW.insert 7 (some 0))))
    IO.println ("sparseErase " ++ reprStr (observe (erase sparse 9) (sparseW.erase 9)))
    IO.println ("nestedParent " ++ reprStr ((nested0[5]?).map (fun x ↦ observe x.1 x.2)))
    IO.println ("nestedClear " ++ reprStr
      (nestedClear.toList.map (fun x ↦ (x.1, observe x.2.1 x.2.2))))
    IO.println ("nestedRecreate " ++ reprStr ((nestedRecreate[5]?).map (fun x ↦ observe x.1 x.2)))
    IO.println ("mismatchErase " ++ reprStr (observe (erase mismatch 1) w0))
    IO.println ("collisionRecord " ++ reprStr (observe (record collision 1) w0))
    IO.println ("duplicatesErase " ++ reprStr (observe (erase duplicates 1) w0))
    IO.println ("nonlawful " ++ reprStr
      (aliasR.next, aliasR.positions.toList.map (fun x ↦ (x.1.tag,x.2)),
        aliasR.keysByPosition.toList.map (fun x ↦ (x.1,x.2.tag)),
        ([] : List (Nat × Option Nat)), (toList aliasR).map Alias.tag))
    IO.println ("address " ++ reprStr
      (keyObservation (fun a ↦ a.toBytes.toList) addressR addressW))
    IO.println ("slot " ++ reprStr (keyObservation (fun a ↦ a.toBytes.toList) slotR slotW))
    IO.println ("addressErase " ++ reprStr (keyObservation (fun a ↦ a.toBytes.toList)
      (erase addressR addressEqual) (addressW.erase addressEqual)))
    IO.println ("slotErase " ++ reprStr (keyObservation (fun a ↦ a.toBytes.toList)
      (erase slotR slotEqual) (slotW.erase slotEqual)))
    IO.println "PASS complete WriteOrder observations"
    return 0
  catch error =>
    IO.eprintln s!"FAIL {error}"
    return 1
