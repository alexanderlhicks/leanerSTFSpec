/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Public bounded Stack law consumers

Library `EthConformance`. Clients use the public model and operation laws.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7.
-/

namespace STFSpec.Conformance.Vm.Core.StackCallerProofs
open STFSpec.Vm.Core STFSpec.Base
open Stack

private theorem empty_size : Stack.empty.size = 0 := by
  rw [Stack.size_eq_length_toList, Stack.toList_empty]
  rfl

private theorem peek_after_push (s t : Stack) (v : U256) (h : s.push v = .ok t) :
    t.peek? 0 = some v := by
  rw [Stack.peek?_eq_getElem?, ((Stack.push_eq_ok_iff s t v).mp h).2]
  rfl

private theorem push_available (s : Stack) (v : U256) (h : s.size < 1024) :
    ∃ t, s.push v = .ok t ∧ t.toList = v :: s.toList := by
  cases hp : s.push v with
  | error e => have := ((push_eq_error_iff s v e).mp hp).1; omega
  | ok t => exact ⟨t, rfl, ((push_eq_ok_iff s t v).mp hp).2⟩

private theorem pop_available (s : Stack) (h : s.toList ≠ []) :
    ∃ v t, s.pop = .ok (v,t) ∧ s.toList = v :: t.toList := by
  cases hp : s.pop with
  | error e => exact False.elim (h (((pop_eq_error_iff s e).mp hp).1))
  | ok result =>
    rcases result with ⟨v,t⟩
    exact ⟨v,t,rfl,(pop_eq_ok_iff s t v).mp hp⟩

private theorem pop_after_push (s t : Stack) (v : U256) (h : s.push v = .ok t) :
    t.pop = .ok (v,s) := by
  exact (pop_eq_ok_iff t s v).mpr ((push_eq_ok_iff s t v).mp h).2

private theorem push_after_pop (s t : Stack) (v : U256) (h : s.pop = .ok (v,t)) :
    t.push v = .ok s := by
  have hm := (pop_eq_ok_iff s t v).mp h
  have hl := congrArg List.length hm
  have hs := size_le s
  rw [← size_eq_length_toList s, List.length_cons, ← size_eq_length_toList t] at hl
  exact (push_eq_ok_iff t s v).mpr ⟨by omega, hm⟩

end STFSpec.Conformance.Vm.Core.StackCallerProofs
