/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Complete bounded Stack exchange controls

Library `EthConformance`. Public pushes construct every input. Construction failure
fails a control; observations retain every full word, the held input and result size.
The operand capacity 1024 is independent of the CALL/CREATE depth bound.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Vm.Core.StackSwapGuards
open STFSpec.Vm.Core STFSpec.Base

private def build (xs : List Nat) : Except ExceptionalHalt Stack :=
  xs.reverse.foldlM (fun s n ↦ s.push (U256.ofNat n)) Stack.empty

private def model (s : Stack) : List Nat := s.toList.map U256.toNat

private def check (xs : List Nat) (i j : Nat) (expected : Option (List Nat)) : Bool :=
  match build xs with
  | .error _ => false
  | .ok s =>
    let actual := s.swap? i j
    model s == xs && s.size == xs.length &&
      actual.map model == expected &&
      (s.swap? j i).map model == expected &&
      match actual with
      | none => true
      | some t => t.size == xs.length && (t.swap? i j).map model == some xs

private def huge : Nat := 2 ^ 4096
private def high : Nat := 2 ^ 255
private def maxWord : Nat := 2 ^ 256 - 1
private def mixed : List Nat := [0, maxWord, high, 1, 0x123456789abcdef, high + 17]

#guard check [] 0 0 none
#guard check [] 0 huge none
#guard check [] huge 0 none
#guard check [] huge huge none
#guard check [maxWord] 0 0 (some [maxWord])
#guard check [maxWord] 1 1 none
#guard check [maxWord] 0 1 none
#guard check [maxWord] 1 0 none
#guard check mixed 0 5 (some [high + 17, maxWord, high, 1, 0x123456789abcdef, 0])
#guard check mixed 1 4 (some [0, 0x123456789abcdef, high, 1, maxWord, high + 17])
#guard check mixed 3 3 (some mixed)
#guard check mixed 0 6 none
#guard check mixed 6 0 none
#guard check mixed 6 6 none
#guard check mixed huge 0 none
#guard check mixed 0 huge none
#guard check mixed huge (huge + 1) none
#guard check [high, 7, high, 0, 7] 0 2 (some [high, 7, high, 0, 7])
#guard check [high, 7, high, 0, 7] 1 3 (some [high, 0, high, 7, 7])

-- Independent constructed complete models check every untouched cell at capacity.
private def full : List Nat := (List.range 1024).map (fun n ↦ high + n)
private def fullExchanged : List Nat :=
  [high + 1023] ++ (List.range 1022).map (fun n ↦ high + n + 1) ++ [high]
#guard check full 0 1023 (some fullExchanged)
#guard check full 1023 1023 (some full)
#guard check full 1024 1024 none
#guard check full 0 1024 none
#guard check full 1024 0 none
#guard check full huge 1023 none
#guard check full 1023 huge none
#guard check (List.replicate 1024 maxWord) 0 1023
  (some (List.replicate 1024 maxWord))

-- The 1025th public push overflows, and a failed construction fails the control
-- rather than being skipped.
#guard match build (List.replicate 1025 0) with
  | .error .stackOverflow => true
  | _ => false
#guard !(check (List.replicate 1025 0) 0 1 (some (List.replicate 1025 0)))

end STFSpec.Conformance.Vm.Core.StackSwapGuards
