/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Complete local-settlement controls

Library `EthConformance`. Sixteen closed historical successes and sixteen
target-only controls observe every field. Invalid source calls stay outside the domain.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Vm.Core.SettlementGuards
open STFSpec.Vm.Core STFSpec.Base

private def observe (out : TransactionGasSettlement) : Nat × Nat × Nat × Nat :=
  (out.gasUsed, out.gasLeft, out.executionGasUsed, out.stateGasUsed)

-- Exactly 2^300, factored below the existing constant-folding exponent threshold.
private def wide : Nat := 2 ^ 256 * 2 ^ 44

private def checkWord (T F gL sL : Nat) (r : U256) (s : Int)
    (hR : gL + sL ≤ T) (hS : s.toNat ≤ T - gL - sL) (hF : F ≤ T)
    (expected : Nat × Nat × Nat × Nat) : Bool :=
  observe (settleTransactionGas T F gL sL r s hR hS hF) == expected

-- Checked fixture construction fails a guard on an invalid literal; it adds no API error.
private def check (T F gL sL refund : Nat) (s : Int)
    (hR : gL + sL ≤ T) (hS : s.toNat ≤ T - gL - sL) (hF : F ≤ T)
    (expected : Nat × Nat × Nat × Nat) : Bool :=
  match U256.ofNat? refund with
  | none => false
  | some r => r.toNat == refund && checkWord T F gL sL r s hR hS hF expected

-- S01–S16: complete immutable historical source successes; no source replay.
#guard check 0 0 0 0 0 0 (by decide) (by decide) (by decide) (0, 0, 0, 0)
#guard check 10 0 3 2 0 0 (by decide) (by decide) (by decide) (5, 5, 5, 0)
#guard check 10 0 3 2 1 0 (by decide) (by decide) (by decide) (4, 6, 5, 0)
#guard check 10 0 3 2 2 0 (by decide) (by decide) (by decide) (4, 6, 5, 0)
#guard check 10 0 4 2 2 0 (by decide) (by decide) (by decide) (4, 6, 4, 0)
#guard check 10 5 3 2 1 0 (by decide) (by decide) (by decide) (5, 5, 5, 0)
#guard check 10 8 3 2 1 2 (by decide) (by decide) (by decide) (8, 2, 8, 2)
#guard check 10 0 3 2 0 (-3) (by decide) (by decide) (by decide) (5, 5, 5, 0)
#guard check 10 0 3 2 0 5 (by decide) (by decide) (by decide) (5, 5, 0, 5)
#guard check 10 5 3 2 1 5 (by decide) (by decide) (by decide) (5, 5, 5, 5)
#guard check 10 10 0 0 2 10 (by decide) (by decide) (by decide) (10, 0, 10, 10)
#guard check 10 0 0 0 2 10 (by decide) (by decide) (by decide) (8, 2, 0, 10)
#guard check 10 0 10 0 0 0 (by decide) (by decide) (by decide) (0, 10, 0, 0)
#guard check 100 0 20 30 7 40 (by decide) (by decide) (by decide) (43, 57, 10, 40)
#guard check 100 0 20 30 10 40 (by decide) (by decide) (by decide) (40, 60, 10, 40)
#guard check 100 45 20 30 10 40 (by decide) (by decide) (by decide) (45, 55, 45, 40)

-- G01–G16: complete target-only controls, independent of the closed source schedule.
#guard checkWord 10 0 0 0 U256.max 0 (by decide) (by decide) (by decide) (8, 2, 10, 0)
#guard check 10 0 0 0 (2 ^ 255) 0 (by decide) (by decide) (by decide) (8, 2, 10, 0)
#guard check (wide + 17) 0 wide 0 1 1 (by decide) (by decide) (by decide)
  (16, wide + 1, 16, 1)
#guard check (wide + 17) (wide + 10) wide 0 1 1
  (by decide) (by decide) (by decide) (wide + 10, 7, wide + 10, 1)
#guard check (wide + 17) 0 0 0 0 ((wide : Int) + 17)
  (by decide) (by decide) (by decide) (wide + 17, 0, 0, wide + 17)
#guard checkWord 10 0 0 0 U256.max (-(wide : Int))
  (by decide) (by decide) (by decide) (8, 2, 10, 0)
#guard check 10 10 0 0 0 1 (by decide) (by decide) (by decide) (10, 0, 10, 1)
#guard checkWord 10 7 0 0 U256.max 1 (by decide) (by decide) (by decide) (8, 2, 9, 1)
#guard checkWord 10 8 0 0 U256.max 1 (by decide) (by decide) (by decide) (8, 2, 9, 1)
#guard checkWord 10 9 0 0 U256.max 1 (by decide) (by decide) (by decide) (9, 1, 9, 1)
#guard checkWord 10 10 0 0 U256.max 1 (by decide) (by decide) (by decide) (10, 0, 10, 1)
#guard checkWord 10 0 6 0 U256.max 1 (by decide) (by decide) (by decide) (4, 6, 3, 1)
#guard checkWord 10 0 5 0 U256.max 1 (by decide) (by decide) (by decide) (4, 6, 4, 1)
#guard checkWord 10 0 4 0 U256.max 1 (by decide) (by decide) (by decide) (5, 5, 5, 1)
#guard observe (TransactionGasSettlement.mk 11 23 37 41) == (11, 23, 37, 41)
#guard checkWord (5 * 2 ^ 256) 0 0 0 U256.max 0 (by decide) (by decide) (by decide)
  (4 * 2 ^ 256 + 1, 2 ^ 256 - 1, 5 * 2 ^ 256, 0)

end STFSpec.Conformance.Vm.Core.SettlementGuards
