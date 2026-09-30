/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base

/-!
# Numeric helper client proof tests

Library `EthConformance`: callers use public success/failure and rounding laws.
No helper definition is unfolded; unbounded `Uint` is the public `Nat` model itself.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §7.
-/

open STFSpec.Base

example (n m r : Uint) (h : Uint.sub? n m = some r) : m + r = n :=
  (Uint.sub?_eq_some_iff_add n m r).mp h

example (n m : Nat) (h : n < m) : Uint.sub? n m = none :=
  (Uint.sub?_eq_none_iff n m).mpr h

example (n m r : Nat) (h : Uint.sub? n m = some r) : m ≤ n :=
  ((Uint.sub?_eq_some_iff n m r).mp h).1

example (n m : Nat) : Uint.sub? (n + m) m = some n := Uint.sub?_add_cancel n m

example (n : Nat) : ceil32 n % 32 = 0 := ceil32_mod n

example (n : Nat) : n ≤ ceil32 n ∧ ceil32 n < n + 32 :=
  ⟨le_ceil32 n, ceil32_lt_add n⟩

example (n k : Nat) (hn : n ≤ k) (hk : k % 32 = 0) : ceil32 n ≤ k :=
  ceil32_le_of_mod_eq_zero n k hn hk

example (n : Nat) : ceil32 (ceil32 n) = ceil32 n := ceil32_idempotent n

example (n : Nat) : Uint.sub? (n + 32) (n % 32) = some (n + 32 - n % 32) :=
  ceil32_sub?_remainder n

example (n : Nat) : ∃ r, Uint.sub? (ceil32 n) n = some r := by
  refine ⟨ceil32 n - n, (Uint.sub?_eq_some_iff _ _ _).mpr ?_⟩
  exact ⟨le_ceil32 n, rfl⟩

example (n : Nat) (h : n % 32 = 0) : ceil32 n = n :=
  ceil32_eq_self_of_mod_eq_zero n h
