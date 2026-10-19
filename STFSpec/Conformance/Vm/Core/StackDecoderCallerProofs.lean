/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Public-only scalar decoder clients

Library `EthConformance`. These clients consume all eight ordinary decoder laws,
deriving successful progress, exact errors, bounds and actual input equality.
They unfold neither decoder nor private proof support.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/7.
-/

namespace STFSpec.Conformance.Vm.Core.StackDecoderCallerProofs
open STFSpec.Vm.Core

private theorem single_progress (x : UInt8) (h : ¬ (91 ≤ x.toNat ∧ x.toNat ≤ 127)) :
    ∃ n, decodeSingle x = .ok n := by
  refine ⟨(x.toNat + 145) % 256, ?_⟩
  rw [decodeSingle_eq, ite_eq_right h]

private theorem single_error (x : UInt8) (e : ExceptionalHalt)
    (h : decodeSingle x = .error e) : e = .invalidParameter := by
  rw [decodeSingle_eq] at h
  split at h
  · cases h
    rfl
  · cases h

private theorem single_invalid (x : UInt8) :
    (91 ≤ x.toNat ∧ x.toNat ≤ 127) ↔ decodeSingle x = .error .invalidParameter := by
  exact (decodeSingle_eq_error_iff x).symm

private theorem single_next_fits (x : UInt8) (n : Nat) (h : decodeSingle x = .ok n) :
    17 ≤ n ∧ n + 1 < 256 := by
  have bounds := decodeSingle_bounds x n h
  omega

private theorem single_input_eq (x y : UInt8) (n : Nat)
    (hx : decodeSingle x = .ok n) (hy : decodeSingle y = .ok n) : x = y := by
  exact decodeSingle_injective x y n hx hy

private theorem pair_progress (x : UInt8) (h : ¬ (82 ≤ x.toNat ∧ x.toNat ≤ 127)) :
    ∃ n m, decodePair x = .ok (n,m) := by
  rw [decodePair_eq, ite_eq_right h]
  let k := x.toNat ^^^ 143
  let p := if k / 16 < k % 16 then (k / 16 + 1, k % 16 + 1)
    else (k % 16 + 1, 29 - k / 16)
  exact ⟨p.1, p.2, rfl⟩

private theorem pair_error (x : UInt8) (e : ExceptionalHalt)
    (h : decodePair x = .error e) : e = .invalidParameter := by
  rw [decodePair_eq] at h
  split at h
  · cases h
    rfl
  · cases h

private theorem pair_invalid (x : UInt8) :
    (82 ≤ x.toNat ∧ x.toNat ≤ 127) ↔ decodePair x = .error .invalidParameter := by
  exact (decodePair_eq_error_iff x).symm

private theorem pair_next_fits (x : UInt8) (n m : Nat) (h : decodePair x = .ok (n,m)) :
    1 ≤ n ∧ n ≤ 14 ∧ n < m ∧ m ≤ 30 - n ∧ max n m + 1 < 256 := by
  have bounds := decodePair_bounds x n m h
  simp only [Nat.max_eq_right (Nat.le_of_lt bounds.2.2.1)]
  omega

private theorem pair_input_eq (x y : UInt8) (n m : Nat)
    (hx : decodePair x = .ok (n,m)) (hy : decodePair y = .ok (n,m)) : x = y := by
  exact decodePair_injective x y n m hx hy

end STFSpec.Conformance.Vm.Core.StackDecoderCallerProofs
