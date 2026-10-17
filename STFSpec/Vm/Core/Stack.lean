/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.U256
import STFSpec.Vm.Core.Exceptions

/-!
# Bounded operand stack

Library `EthVmCore`. Pinned EELS `vm/stack.py:94–131` on typed lists of at most
1024 words. Array storage places the top at the end; the public model is top first.
Only the model observer converts to a List. Frame ownership and allocation costs
remain separate composed obligations.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§2.3/5/7.
-/

namespace STFSpec.Vm.Core
open STFSpec.Base

/-- A bounded operand stack with private top-at-end storage. -/
structure Stack where
  private mk ::
  private data : Array U256
  private bounded : data.size ≤ 1024

namespace Stack
/-- The empty operand stack. -/
def empty : Stack := ⟨#[], by simp⟩
/-- Number of words, without traversing the model. -/
def size (s : Stack) : Nat := s.data.size
/-- Complete ordered word model, with the top first. -/
def toList (s : Stack) : List U256 := s.data.toList.reverse

/-- Remove the top word, or fail before reading an empty stack.
Pinned EELS `src/ethereum/forks/amsterdam/vm/stack.py:94–112`. -/
def pop (s : Stack) : Except ExceptionalHalt (U256 × Stack) :=
  if h : s.data.size = 0 then .error .stackUnderflow
  else .ok (s.data[s.data.size - 1]'(by omega),
    ⟨s.data.pop, by have := s.bounded; simp only [Array.size_pop]; omega⟩)

/-- Append a word, rejecting the full stack before mutation.
Pinned EELS `src/ethereum/forks/amsterdam/vm/stack.py:115–131`. -/
def push (s : Stack) (v : U256) : Except ExceptionalHalt Stack :=
  if h : s.data.size = 1024 then .error .stackOverflow
  else .ok ⟨s.data.push v, by have := s.bounded; simp only [Array.size_push]; omega⟩

/-- Zero-based top-relative observation, guarded before index arithmetic.
Model adapter for indexed reads in pinned EELS
`src/ethereum/forks/amsterdam/vm/instructions/stack.py:106–109,242–243`. -/
def peek? (s : Stack) (i : Nat) : Option U256 :=
  if h : i < s.data.size then
    some (s.data[s.data.size - 1 - i]'(by omega))
  else none

private theorem model_inj {s t : Stack} (h : s.toList = t.toList) : s = t := by
  rcases s with ⟨a, ha⟩
  rcases t with ⟨b, hb⟩
  have hab : a = b := Array.toList_inj.mp (List.reverse_inj.mp h)
  cases hab
  rfl

private def observePop :
    Except ExceptionalHalt (U256 × Stack) → Except ExceptionalHalt (U256 × List U256)
  | .error e => .error e
  | .ok (v, s) => .ok (v, s.toList)
private theorem observePop_inj (x y : Except ExceptionalHalt (U256 × Stack)) :
    observePop x = observePop y ↔ x = y := by
  cases x with
  | error e => cases y <;> simp [observePop]
  | ok a =>
    rcases a with ⟨v,s⟩
    cases y with
    | error e => simp [observePop]
    | ok b =>
      rcases b with ⟨w,t⟩
      simp only [observePop, Except.ok.injEq, Prod.mk.injEq]
      exact ⟨fun ⟨h₁,h₂⟩ => ⟨h₁, model_inj h₂⟩, fun ⟨h₁,h₂⟩ => ⟨h₁, congrArg toList h₂⟩⟩

private theorem pop_model (s : Stack) :
    observePop s.pop = match s.toList with
      | [] => .error .stackUnderflow
      | v :: vs => .ok (v, vs) := by
  rcases s with ⟨a, ha⟩
  by_cases hz : a.size = 0
  · have he : a = #[] := Array.eq_empty_of_size_eq_zero hz
    subst a
    simp [pop, observePop, toList]
  · obtain ⟨b,v,hb⟩ := Array.exists_push_of_ne_empty (xs := a) (by intro he; simp [he] at hz)
    subst a
    simp [pop, observePop, toList, Array.getElem_push]

private def observePush : Except ExceptionalHalt Stack → Except ExceptionalHalt (List U256)
  | .error e => .error e
  | .ok s => .ok s.toList
private theorem observePush_inj (x y : Except ExceptionalHalt Stack) :
    observePush x = observePush y ↔ x = y := by
  cases x with
  | error e => cases y <;> simp [observePush]
  | ok s =>
    cases y with
    | error e => simp [observePush]
    | ok t =>
      simp only [observePush, Except.ok.injEq]
      exact ⟨model_inj, congrArg toList⟩

private theorem push_model (s : Stack) (v : U256) :
    observePush (s.push v) =
      if s.size = 1024 then .error .stackOverflow else .ok (v :: s.toList) := by
  by_cases h : s.data.size = 1024 <;> simp [push, observePush, size, toList, h]

/-- The empty stack has an empty top-first model. -/
theorem toList_empty : empty.toList = [] := rfl
/-- The stored size agrees with the complete public model length. -/
theorem size_eq_length_toList (s : Stack) : s.size = s.toList.length := by
  simp [size, toList]
/-- Every stack contains at most 1024 words. -/
theorem size_le (s : Stack) : s.size ≤ 1024 := s.bounded

/-- Pop fails exactly on an empty model, with stack underflow. -/
theorem pop_eq_error_iff (s : Stack) (e : ExceptionalHalt) :
    s.pop = .error e ↔ s.toList = [] ∧ e = .stackUnderflow := by
  rw [← observePop_inj, pop_model]
  cases h : s.toList <;> simp [observePop, eq_comm]

/-- Pop returns exactly the top word and remaining model. -/
theorem pop_eq_ok_iff (s t : Stack) (v : U256) :
    s.pop = .ok (v,t) ↔ s.toList = v :: t.toList := by
  rw [← observePop_inj, pop_model]
  cases h : s.toList <;> simp [observePop]

/-- Push fails exactly on a full stack, with stack overflow. -/
theorem push_eq_error_iff (s : Stack) (v : U256) (e : ExceptionalHalt) :
    s.push v = .error e ↔ s.size = 1024 ∧ e = .stackOverflow := by
  rw [← observePush_inj, push_model]
  by_cases h : s.size = 1024 <;> simp [h, observePush, eq_comm]

/-- Push succeeds exactly below the bound and prepends to the model. -/
theorem push_eq_ok_iff (s t : Stack) (v : U256) :
    s.push v = .ok t ↔ s.size < 1024 ∧ t.toList = v :: s.toList := by
  rw [← observePush_inj, push_model]
  have := s.size_le
  by_cases h : s.size = 1024
  · simp [h, observePush]
  · have hl : s.size < 1024 := by omega
    simp [h, hl, observePush, eq_comm]

/-- Every Nat depth agrees with optional indexing of the top-first model. -/
theorem peek?_eq_getElem? (s : Stack) (i : Nat) : s.peek? i = s.toList[i]? := by
  by_cases h : i < s.data.size
  · simp only [peek?, h, ↓reduceDIte, toList]
    rw [List.getElem?_reverse (by simpa using h)]
    simp [show s.data.size - 1 - i < s.data.size by omega]
  · have hn : s.toList.length ≤ i := by simp [toList]; omega
    simp [peek?, h, List.getElem?_eq_none hn]

end Stack
end STFSpec.Vm.Core
