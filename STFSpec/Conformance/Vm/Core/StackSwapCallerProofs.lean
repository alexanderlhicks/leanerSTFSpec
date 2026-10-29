/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Public Stack exchange law consumers

Library `EthConformance`. All declarations are private; clients use only the existing
public Stack observer laws and the two exchange laws, with ordinary List reasoning.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7.
-/

namespace STFSpec.Conformance.Vm.Core.StackSwapCallerProofs
open STFSpec.Vm.Core STFSpec.Base Stack

private theorem client_available (s : Stack) (i j : Nat)
    (hi : i < s.size) (hj : j < s.size) : ∃ t, s.swap? i j = some t := by
  cases h : s.swap? i j with
  | none => have := (swap?_eq_none_iff s i j).mp h; omega
  | some t => exact ⟨t, rfl⟩

private theorem client_size (a b : Stack) (i j : Nat)
    (h : a.swap? i j = some b) : b.size = a.size := by
  obtain ⟨x, y, _, _, hm⟩ := (swap?_eq_some_iff a b i j).mp h
  have := congrArg List.length hm
  simpa [← size_eq_length_toList] using this

private theorem client_cells (a b : Stack) (i j k : Nat)
    (h : a.swap? i j = some b) :
    b.toList[k]? = if j = k then a.toList[i]?
      else if i = k then a.toList[j]? else a.toList[k]? := by
  obtain ⟨x, y, hx, hy, hm⟩ := (swap?_eq_some_iff a b i j).mp h
  have hi := (List.getElem?_eq_some_iff.mp hx).1
  have hj := (List.getElem?_eq_some_iff.mp hy).1
  rw [hm]
  simp only [List.getElem?_set, List.length_set, hi, hj, ite_true, hx, hy]

private theorem client_equal_valid (a : Stack) (i : Nat) (hi : i < a.size) :
    a.swap? i i = some a := by
  have h : i < a.toList.length := by simpa [← size_eq_length_toList] using hi
  apply (swap?_eq_some_iff a a i i).mpr
  exact ⟨a.toList[i], a.toList[i], by simp [h], by simp [h], by simp⟩

private theorem list_exchange_comm (l : List U256) (i j : Nat) (x y : U256)
    (hx : l[i]? = some x) (hy : l[j]? = some y) :
    (l.set i y).set j x = (l.set j x).set i y := by
  by_cases h : i = j
  · subst j
    have : x = y := Option.some.inj (hx.symm.trans hy)
    simp [this]
  · exact List.set_comm y x h

private theorem client_comm (a : Stack) (i j : Nat) :
    a.swap? i j = a.swap? j i := by
  cases h : a.swap? i j with
  | none =>
    symm
    apply (swap?_eq_none_iff a j i).mpr
    exact Or.symm ((swap?_eq_none_iff a i j).mp h)
  | some b =>
    symm
    obtain ⟨x, y, hx, hy, hm⟩ := (swap?_eq_some_iff a b i j).mp h
    apply (swap?_eq_some_iff a b j i).mpr
    exact ⟨y, x, hy, hx, hm.trans (list_exchange_comm _ _ _ _ _ hx hy)⟩

private theorem list_exchange_twice (l : List U256) (i j : Nat) (x y : U256)
    (hx : l[i]? = some x) (hy : l[j]? = some y) :
    (((l.set i y).set j x).set i x).set j y = l := by
  have hi := (List.getElem?_eq_some_iff.mp hx).1
  have hj := (List.getElem?_eq_some_iff.mp hy).1
  have heq : i = j → x = y := fun h => Option.some.inj (hx.symm.trans (h ▸ hy))
  apply List.ext_getElem?
  intro k
  by_cases hik : i = k <;> by_cases hjk : j = k <;>
    simp_all

private theorem client_involution (a b : Stack) (i j : Nat)
    (h : a.swap? i j = some b) : b.swap? i j = some a := by
  obtain ⟨x, y, hx, hy, hm⟩ := (swap?_eq_some_iff a b i j).mp h
  apply (swap?_eq_some_iff b a i j).mpr
  have hi := (List.getElem?_eq_some_iff.mp hx).1
  have hj := (List.getElem?_eq_some_iff.mp hy).1
  have heq : i = j → x = y := by
    intro hij
    subst j
    exact Option.some.inj (hx.symm.trans hy)
  refine ⟨y, x, ?_, ?_, ?_⟩
  · rw [hm]
    by_cases hij : i = j
    · subst j
      have hxy := Option.some.inj (hx.symm.trans hy)
      simp only [List.getElem?_set, List.length_set, hi, ite_true]
      exact congrArg some hxy
    · simp only [List.getElem?_set, List.length_set, hi, ite_true,
        Ne.symm hij, ite_false]
  · rw [hm]
    simp only [List.getElem?_set, List.length_set, hj, ite_true]
  · rw [hm]
    exact (list_exchange_twice _ _ _ _ _ hx hy).symm

end STFSpec.Conformance.Vm.Core.StackSwapCallerProofs
