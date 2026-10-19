/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core.Exceptions

/-!
# Scalar stack immediate decoders

Library `EthVmCore`. The two pure UInt8 decoders from pinned EELS
`src/ethereum/forks/amsterdam/vm/stack.py:25–91`. Invalid parameters retain the
existing nullary exceptional halt; no stack, gas or program-counter effect occurs.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§2.3/3/7.
-/

namespace STFSpec.Vm.Core

/-- Decode a DUPN/SWAPN byte.
Pinned EELS `src/ethereum/forks/amsterdam/vm/stack.py:25–53`. -/
def decodeSingle (x : UInt8) : Except ExceptionalHalt Nat :=
  if 91 ≤ x.toNat ∧ x.toNat ≤ 127 then .error .invalidParameter
  else .ok ((x.toNat + 145) % 256)

/-- Decode an EXCHANGE byte.
Pinned EELS `src/ethereum/forks/amsterdam/vm/stack.py:56–91`. -/
def decodePair (x : UInt8) : Except ExceptionalHalt (Nat × Nat) :=
  if 82 ≤ x.toNat ∧ x.toNat ≤ 127 then .error .invalidParameter
  else
    let k := x.toNat ^^^ 143
    let q := k / 16
    let r := k % 16
    .ok (if q < r then (q + 1, r + 1) else (r + 1, 29 - q))

/-- Complete single-decoder equation on every UInt8. -/
theorem decodeSingle_eq (x : UInt8) :
    decodeSingle x =
      if 91 ≤ x.toNat ∧ x.toNat ≤ 127 then .error .invalidParameter
      else .ok ((x.toNat + 145) % 256) := rfl

/-- The exact forbidden single-decoder interval. -/
theorem decodeSingle_eq_error_iff (x : UInt8) :
    decodeSingle x = .error .invalidParameter ↔ 91 ≤ x.toNat ∧ x.toNat ≤ 127 := by
  rw [decodeSingle_eq]
  split <;> simp_all

/-- Every successful single index has the prescribed bounds. -/
theorem decodeSingle_bounds (x : UInt8) (n : Nat) (h : decodeSingle x = .ok n) :
    17 ≤ n ∧ n ≤ 235 := by
  have hx := x.toNat_lt
  rw [decodeSingle_eq] at h
  split at h
  · cases h
  · simp only [Except.ok.injEq] at h
    omega

/-- A successful single payload determines its actual input byte. -/
theorem decodeSingle_injective (x y : UInt8) (n : Nat)
    (hx : decodeSingle x = .ok n) (hy : decodeSingle y = .ok n) : x = y := by
  have bx := x.toNat_lt
  have by' := y.toNat_lt
  rw [decodeSingle_eq] at hx hy
  split at hx
  · cases hx
  · split at hy
    · cases hy
    · simp only [Except.ok.injEq] at hx hy
      apply UInt8.toNat_inj.mp
      omega

/-- Complete ordered pair-decoder equation on every UInt8. -/
theorem decodePair_eq (x : UInt8) :
    decodePair x =
      if 82 ≤ x.toNat ∧ x.toNat ≤ 127 then .error .invalidParameter
      else
        let k := x.toNat ^^^ 143
        let q := k / 16
        let r := k % 16
        .ok (if q < r then (q + 1, r + 1) else (r + 1, 29 - q)) := rfl

/-- The exact forbidden pair-decoder interval. -/
theorem decodePair_eq_error_iff (x : UInt8) :
    decodePair x = .error .invalidParameter ↔ 82 ≤ x.toNat ∧ x.toNat ≤ 127 := by
  rw [decodePair_eq]
  split <;> simp_all

-- A small ordinary finite proof establishes bounds and recovers xor143 from the
-- ordered payload. Its second coordinate separates the two branches at 16/17.
set_option maxRecDepth 4096 in
private theorem pair_finite : ∀ x : Fin 256, ¬ (82 ≤ x.val ∧ x.val ≤ 127) →
    let k := x.val ^^^ 143
    let q := k / 16
    let r := k % 16
    let p := if q < r then (q + 1, r + 1) else (r + 1, 29 - q)
    (1 ≤ p.1 ∧ p.1 ≤ 14 ∧ p.1 < p.2 ∧ p.2 ≤ 30 - p.1) ∧
      (if p.2 ≤ 16 then (p.1 - 1) * 16 + (p.2 - 1)
       else (29 - p.2) * 16 + (p.1 - 1)) = k := by
  decide

/-- Every successful ordered pair has all four prescribed bounds. -/
theorem decodePair_bounds (x : UInt8) (n m : Nat) (h : decodePair x = .ok (n,m)) :
    1 ≤ n ∧ n ≤ 14 ∧ n < m ∧ m ≤ 30 - n := by
  rw [decodePair_eq] at h
  split at h
  · cases h
  · rename_i valid
    have facts := pair_finite ⟨x.toNat, x.toNat_lt⟩ valid
    simp only [Except.ok.injEq] at h
    simpa only [h] using facts.1

/-- A successful ordered pair determines its actual input byte. -/
theorem decodePair_injective (x y : UInt8) (n m : Nat)
    (hx : decodePair x = .ok (n,m)) (hy : decodePair y = .ok (n,m)) : x = y := by
  rw [decodePair_eq] at hx hy
  split at hx
  · cases hx
  · rename_i validX
    split at hy
    · cases hy
    · rename_i validY
      have fx := (pair_finite ⟨x.toNat, x.toNat_lt⟩ validX).2
      have fy := (pair_finite ⟨y.toNat, y.toNat_lt⟩ validY).2
      simp only [Except.ok.injEq] at hx hy
      simp only [hx, hy] at fx fy
      have xorEq : x.toNat ^^^ 143 = y.toNat ^^^ 143 := fx.symm.trans fy
      apply UInt8.toNat_inj.mp
      have := congrArg (fun k : Nat ↦ k ^^^ 143) xorEq
      simpa only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] using this

end STFSpec.Vm.Core
