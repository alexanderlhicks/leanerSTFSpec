/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base

/-!
# U256 shift-composition client proofs

Library `EthConformance`: clients depend on public composition and observer laws.
They supply the unsigned sum premise without unfolding word storage or operations.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §7.
-/

open STFSpec.Base

private theorem boundary_sum_lt :
    U256.one.toNat + (U256.ofNat 254).toNat < 2 ^ 256 := by
  rw [U256.toNat_one, U256.toNat_ofNat_of_lt (by decide)]
  decide

private theorem boundary_add : U256.add U256.one (U256.ofNat 254) = U256.ofNat 255 := by
  apply U256.toNat_inj.mp
  rw [U256.toNat_add_of_lt _ _ boundary_sum_lt, U256.toNat_one,
    U256.toNat_ofNat_of_lt (by decide), U256.toNat_ofNat_of_lt (by decide)]

example (s t v : U256) (h : s.toNat + t.toNat < 2 ^ 256) :
    U256.shl t (U256.shl s v) = U256.shl (U256.add s t) v :=
  U256.shl_shl_of_add_lt s t v h

example (s t v : U256) (h : s.toNat + t.toNat < 2 ^ 256) :
    U256.shl t (U256.shl s v) = U256.shl s (U256.shl t v) := by
  rw [U256.shl_shl_of_add_lt s t v h,
    U256.shl_shl_of_add_lt t s v (by omega), U256.add_comm]

example (v : U256) :
    U256.shl (U256.ofNat 254) (U256.shl U256.one v) =
      U256.shl (U256.ofNat 255) v := by
  rw [U256.shl_shl_of_add_lt U256.one (U256.ofNat 254) v boundary_sum_lt,
    boundary_add]

example (s t v : U256) (h : s.toNat + t.toNat < 2 ^ 256) :
    U256.shr t (U256.shr s v) = U256.shr (U256.add s t) v :=
  U256.shr_shr_of_add_lt s t v h

example (s t v : U256) (h : s.toNat + t.toNat < 2 ^ 256) :
    U256.shr t (U256.shr s v) = U256.shr s (U256.shr t v) := by
  rw [U256.shr_shr_of_add_lt s t v h,
    U256.shr_shr_of_add_lt t s v (by omega), U256.add_comm]

example (v : U256) :
    U256.shr (U256.ofNat 254) (U256.shr U256.one v) =
      U256.shr (U256.ofNat 255) v := by
  rw [U256.shr_shr_of_add_lt U256.one (U256.ofNat 254) v boundary_sum_lt,
    boundary_add]

example (s t v : U256) (h : s.toNat + t.toNat < 2 ^ 256) :
    U256.sar t (U256.sar s v) = U256.sar (U256.add s t) v :=
  U256.sar_sar_of_add_lt s t v h

example (s t v : U256) (h : s.toNat + t.toNat < 2 ^ 256) :
    U256.sar t (U256.sar s v) = U256.sar s (U256.sar t v) := by
  rw [U256.sar_sar_of_add_lt s t v h,
    U256.sar_sar_of_add_lt t s v (by omega), U256.add_comm]

example (v : U256) :
    U256.sar (U256.ofNat 254) (U256.sar U256.one v) =
      U256.sar (U256.ofNat 255) v := by
  rw [U256.sar_sar_of_add_lt U256.one (U256.ofNat 254) v boundary_sum_lt,
    boundary_add]
