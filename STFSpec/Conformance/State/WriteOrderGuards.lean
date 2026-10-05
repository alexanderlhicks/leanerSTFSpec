/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.WriteOrder
import STFSpec.Base.FixedBytes

/-!
# WriteOrder component tests

Library `EthConformance`: public-law clients and complete finite observations of
internal State support. Nested containers are test models of paired saved roots.
Spec guidance: `STFSpec/informal/modules/EthState.md`.
-/

namespace STFSpec.Conformance.State.WriteOrderGuards

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
#guard observe r0 w0 == (0, [], [], [], [])
#guard observe r1 w1 == (1, [(9,0)], [(0,9)], [(9,some 90)], [9])
#guard observe r2 w2 == (2, [(2,1),(9,0)], [(0,9),(1,2)], [(2,none),(9,some 90)], [9,2])
#guard observe rDuplicate wDuplicate ==
  (2, [(2,1),(9,0)], [(0,9),(1,2)], [(2,none),(9,some 0)], [9,2])
#guard observe rAbsent wAbsent == (2, [(2,1),(9,0)], [(0,9),(1,2)], [(2,none),(9,some 0)], [9,2])
#guard observe r3 w3 ==
  (3, [(2,1),(7,2),(9,0)], [(0,9),(1,2),(2,7)], [(2,none),(7,some 70),(9,some 0)], [9,2,7])
#guard observe rMiddle wMiddle ==
  (3, [(7,2),(9,0)], [(0,9),(2,7)], [(7,some 70),(9,some 0)], [9,7])
#guard observe rHead wHead == (3, [(7,2)], [(2,7)], [(7,some 70)], [7])
#guard observe rTail wTail == (3, [], [], [], [])
#guard observe rReinsert wReinsert == (4, [(2,3)], [(3,2)], [(2,none)], [2])

private def sparse : WriteOrder Nat :=
  ⟨2^100+17, (∅ : Std.ExtTreeMap Nat Nat).insert 9 4 |>.insert 2 100,
    (∅ : Std.ExtTreeMap Nat Nat).insert 4 9 |>.insert 100 2⟩
private def sparseW := (∅ : Std.ExtTreeMap Nat (Option Nat)).insert 9 (some 90) |>.insert 2 none
private theorem sparse_wf : WF sparse := by
  constructor
  · intro k p
    simp only [sparse, Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_empty,
      Std.LawfulEqOrd.compare_eq_iff_eq]
    by_cases h2 : k = 2 <;> by_cases h9 : k = 9 <;>
      by_cases h100 : p = 100 <;> by_cases h4 : p = 4 <;>
      simp_all [eq_comm]
  · intro p k hp
    simp only [sparse, Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_empty,
      Std.LawfulEqOrd.compare_eq_iff_eq] at hp
    by_cases h100 : p = 100
    · subst p; decide
    · by_cases h4 : p = 4
      · subst p; decide
      · simp [h100, h4, eq_comm] at hp
#guard observe sparse sparseW ==
  (2^100+17, [(2,100),(9,4)], [(4,9),(100,2)], [(2,none),(9,some 90)], [9,2])
#guard observe (record sparse 7) (sparseW.insert 7 (some 0)) ==
  (2^100+18, [(2,100),(7,2^100+17),(9,4)], [(4,9),(100,2),(2^100+17,7)],
    [(2,none),(7,some 0),(9,some 90)], [9,2,7])
#guard observe (erase sparse 9) (sparseW.erase 9) ==
  (2^100+17, [(2,100)], [(100,2)], [(2,none)], [2])

-- Persistent roots are paired roots: restore includes next and both maps.
private def left := record (erase r2 9) 7
private def leftW := (w2.erase 9).insert 7 (some 70)
private def right := record r2 4
private def rightW := w2.insert 4 (some 40)
private def leftNested := record left 8
private def leftNestedW := leftW.insert 8 (some 80)
private def restoredInner := left
private def restoredOuter := r2
#guard observe left leftW == (3, [(2,1),(7,2)], [(1,2),(2,7)], [(2,none),(7,some 70)], [2,7])
#guard observe right rightW ==
  (3, [(2,1),(4,2),(9,0)], [(0,9),(1,2),(2,4)], [(2,none),(4,some 40),(9,some 90)], [9,2,4])
#guard observe leftNested leftNestedW ==
  (4, [(2,1),(7,2),(8,3)], [(1,2),(2,7),(3,8)], [(2,none),(7,some 70),(8,some 80)], [2,7,8])
#guard observe restoredInner leftW ==
  (3, [(2,1),(7,2)], [(1,2),(2,7)], [(2,none),(7,some 70)], [2,7])
#guard observe restoredOuter w2 == (2, [(2,1),(9,0)], [(0,9),(1,2)], [(2,none),(9,some 90)], [9,2])

-- Bounded nested-map shape only: no F7 source-set iteration policy chosen.
private def nested0 : Std.ExtTreeMap Nat (WriteOrder Nat × Std.ExtTreeMap Nat (Option Nat)) :=
  (∅ : Std.ExtTreeMap Nat (WriteOrder Nat × Std.ExtTreeMap Nat (Option Nat))).insert 5 (r2,w2)
private def nestedClear := nested0.erase 5
private def nestedRecreate := nestedClear.insert 5
  (record empty 7, (∅ : Std.ExtTreeMap Nat (Option Nat)).insert 7 (some 0))
#guard nestedClear.toList.map (fun x ↦ (x.1, observe x.2.1 x.2.2)) == []
#guard (nested0[5]?).map (fun x => observe x.1 x.2) ==
  some (2, [(2,1),(9,0)], [(0,9),(1,2)], [(2,none),(9,some 90)], [9,2])
#guard (nestedRecreate[5]?).map (fun x => observe x.1 x.2) ==
  some (1, [(7,0)], [(0,7)], [(7,some 0)], [7])
private def incoming := [4,9,1]
private def merged := incoming.foldl record r2
private def mergedW := (w2.insert 4 (some 40)).insert 9 (some 99) |>.insert 1 none
#guard observe merged mergedW ==
  (4, [(1,3),(2,1),(4,2),(9,0)], [(0,9),(1,2),(2,4),(3,1)],
    [(1,none),(2,none),(4,some 40),(9,some 99)], [9,2,4,1])

private def mismatch : WriteOrder Nat :=
  ⟨1, (∅ : Std.ExtTreeMap Nat Nat).insert 1 0, (∅ : Std.ExtTreeMap Nat Nat).insert 0 2⟩
private def orphan : WriteOrder Nat :=
  ⟨1, ∅, (∅ : Std.ExtTreeMap Nat Nat).insert 0 2⟩
private def collision : WriteOrder Nat :=
  ⟨0, (∅ : Std.ExtTreeMap Nat Nat).insert 2 0, (∅ : Std.ExtTreeMap Nat Nat).insert 0 2⟩
private def duplicates : WriteOrder Nat :=
  ⟨2, ∅, (∅ : Std.ExtTreeMap Nat Nat).insert 0 1 |>.insert 1 1⟩
#guard toList mismatch == [2]
#guard toList (erase mismatch 1) == []
#guard (toList mismatch).filter (fun a => compare 1 a != .eq) == [2]
#guard toList orphan == [2]
#guard orphan.positions[2]? == none
#guard toList (record collision 1) == [1]
#guard toList collision ++ [1] == [2,1]
#guard toList duplicates == [1,1]
#guard toList (erase duplicates 1) == [1,1]
#guard (toList duplicates).filter (fun a => compare 1 a != .eq) == []
private theorem mismatch_not_wf : ¬ WF mismatch := by
  intro h
  have hx := (h.1 1 0).mp (by decide)
  have hn : mismatch.keysByPosition[0]? ≠ some 1 := by decide
  exact hn hx
private theorem orphan_not_wf : ¬ WF orphan := by
  intro h
  have hx := (h.1 2 0).mpr (by decide)
  have hn : orphan.positions[2]? ≠ some 0 := by decide
  exact hn hx
private theorem collision_not_wf : ¬ WF collision := by
  intro h
  have hp : collision.keysByPosition[0]? = some 2 := by decide
  exact Nat.lt_irrefl 0 (h.2 0 2 hp)
private theorem duplicates_not_wf : ¬ WF duplicates := by
  intro h
  have hx := (h.1 1 0).mpr (by decide)
  have hn : duplicates.positions[1]? ≠ some 0 := by decide
  exact hn hx

private structure Alias where
  tag : Nat
  deriving BEq, DecidableEq
private instance : Ord Alias := ⟨fun _ _ => .eq⟩
private instance : Std.TransOrd Alias where
  eq_swap := rfl
  isLE_trans := by intros; rfl
private theorem alias_not_lawful : ¬ Std.LawfulEqOrd Alias := by
  intro h
  letI := h
  have he : (⟨1⟩ : Alias) = ⟨2⟩ := Std.LawfulEqOrd.eq_of_compare rfl
  have hn : (⟨1⟩ : Alias) ≠ ⟨2⟩ := by decide
  exact hn he
private def aliasR : WriteOrder Alias := record (record empty ⟨1⟩) ⟨2⟩
#guard (toList aliasR).map Alias.tag == [1]
#guard aliasR.next == 1
#guard aliasR.positions[(⟨2⟩ : Alias)]?.isSome


-- Both retained parents and repeated saved roots are observed after descendants.
private def restoredInnerAgain := restoredInner
private def restoredOuterAgain := restoredOuter
#guard observe restoredInnerAgain leftW ==
  (3, [(2,1),(7,2)], [(1,2),(2,7)], [(2,none),(7,some 70)], [2,7])
#guard observe restoredOuterAgain w2 ==
  (2, [(2,1),(9,0)], [(0,9),(1,2)], [(2,none),(9,some 90)], [9,2])
#guard observe r2 w2 ==
  (2, [(2,1),(9,0)], [(0,9),(1,2)], [(2,none),(9,some 90)], [9,2])
#guard observe mismatch w0 == (1, [(1,0)], [(0,2)], [], [2])
#guard observe (erase mismatch 1) w0 == (1, [], [], [], [])
#guard observe orphan w0 == (1, [], [(0,2)], [], [2])
#guard observe collision w0 == (0, [(2,0)], [(0,2)], [], [2])
#guard observe (record collision 1) w0 == (1, [(1,0),(2,0)], [(0,1)], [], [1])
#guard observe duplicates w0 == (2, [], [(0,1),(1,1)], [], [1,1])
#guard observe (erase duplicates 1) w0 == (2, [], [(0,1),(1,1)], [], [1,1])

-- WF does not equate the domain of an unrelated value map.
private theorem unrelated_not_agrees : ¬ Agrees r1 w0 := by
  intro h
  have hx := h 9
  have hn : r1.positions[9]?.isSome ≠ w0[9]?.isSome := by decide
  exact hn hx

private def missingReverse : WriteOrder Nat :=
  ⟨1, (∅ : Std.ExtTreeMap Nat Nat).insert 1 0, ∅⟩
private theorem missingReverse_not_wf : ¬ WF missingReverse := by
  intro h
  have hx := (h.1 1 0).mp (by decide)
  have hn : missingReverse.keysByPosition[0]? ≠ some 1 := by decide
  exact hn hx
#guard observe missingReverse w0 == (1, [(1,0)], [], [], [])
#guard observe (record mismatch 1) w0 == observe mismatch w0
#guard observe (erase orphan 1) w0 == observe orphan w0

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
#guard STFSpec.Base.Address.ofBytes? (address 9).toBytes == some addressEqual
#guard STFSpec.Base.FixedBytes.ofBytes? (slot 9).toBytes == some slotEqual
#guard keyObservation (fun a ↦ a.toBytes.toList) addressR addressW ==
  (2, [(pattern 20 2,1),(pattern 20 9,0)], [(0,pattern 20 9),(1,pattern 20 2)],
    [(pattern 20 2,none),(pattern 20 9,some 0)], [pattern 20 9,pattern 20 2])
#guard keyObservation (fun a ↦ a.toBytes.toList) slotR slotW ==
  (2, [(pattern 32 2,1),(pattern 32 9,0)], [(0,pattern 32 9),(1,pattern 32 2)],
    [(pattern 32 2,none),(pattern 32 9,some 0)], [pattern 32 9,pattern 32 2])
#guard keyObservation (fun a ↦ a.toBytes.toList) (erase addressR addressEqual)
  (addressW.erase addressEqual) ==
  (2, [(pattern 20 2,1)], [(1,pattern 20 2)], [(pattern 20 2,none)], [pattern 20 2])
#guard keyObservation (fun a ↦ a.toBytes.toList) (erase slotR slotEqual)
  (slotW.erase slotEqual) ==
  (2, [(pattern 32 2,1)], [(1,pattern 32 2)], [(pattern 32 2,none)], [pattern 32 2])

end STFSpec.Conformance.State.WriteOrderGuards
