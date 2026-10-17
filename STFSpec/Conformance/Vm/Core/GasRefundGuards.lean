/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Complete-field state-gas refund guards

Library `EthConformance`. Literal expectations frozen before target execution.
Local numeric compositions use the actual supplied operations, with every intermediate field.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/7.
-/

namespace STFSpec.Conformance.Vm.Core.GasRefundGuards
open STFSpec.Vm.Core

private def fields (m : GasMeter) : Nat × Nat × Nat × Int × Nat × Nat :=
  (m.gasLeft, m.stateGasLeft, m.stateGasBaseline, m.refundCounter,
    m.stateGasSpilled, m.stateGasCommittedSpill)

-- credit-zero
#guard fields (creditStateGasRefund
    ({ gasLeft := 0,
       stateGasLeft := 0,
       stateGasBaseline := 0,
       refundCounter := (0),
       stateGasSpilled := 0,
       stateGasCommittedSpill := 0 })
    0) ==
  (0,
    0,
    0,
    0,
    0,
    0)

-- credit-zero-raw
#guard fields (creditStateGasRefund
    ({ gasLeft := 10,
       stateGasLeft := 4,
       stateGasBaseline := 1,
       refundCounter := (-3),
       stateGasSpilled := 6,
       stateGasCommittedSpill := 7 })
    0) ==
  (10,
    4,
    1,
    (-3),
    6,
    7)

-- credit-less
#guard fields (creditStateGasRefund
    ({ gasLeft := 10,
       stateGasLeft := 4,
       stateGasBaseline := 1,
       refundCounter := (-3),
       stateGasSpilled := 6,
       stateGasCommittedSpill := 7 })
    2) ==
  (12,
    4,
    1,
    (-3),
    4,
    7)

-- credit-equal
#guard fields (creditStateGasRefund
    ({ gasLeft := 10,
       stateGasLeft := 4,
       stateGasBaseline := 1,
       refundCounter := (-3),
       stateGasSpilled := 6,
       stateGasCommittedSpill := 7 })
    6) ==
  (16,
    4,
    1,
    (-3),
    0,
    7)

-- credit-greater
#guard fields (creditStateGasRefund
    ({ gasLeft := 10,
       stateGasLeft := 4,
       stateGasBaseline := 1,
       refundCounter := (-3),
       stateGasSpilled := 6,
       stateGasCommittedSpill := 7 })
    8) ==
  (16,
    6,
    1,
    (-3),
    0,
    7)

-- credit-no-pending
#guard fields (creditStateGasRefund
    ({ gasLeft := 0,
       stateGasLeft := 0,
       stateGasBaseline := 9,
       refundCounter := (4),
       stateGasSpilled := 0,
       stateGasCommittedSpill := 7 })
    8) ==
  (0,
    8,
    9,
    4,
    0,
    7)

-- credit-zero-execution
#guard fields (creditStateGasRefund
    ({ gasLeft := 0,
       stateGasLeft := 0,
       stateGasBaseline := 9,
       refundCounter := (-4),
       stateGasSpilled := 6,
       stateGasCommittedSpill := 7 })
    8) ==
  (6,
    2,
    9,
    (-4),
    0,
    7)

-- repay-zero
#guard fields (repayStateGasSpill
    ({ gasLeft := 0,
       stateGasLeft := 0,
       stateGasBaseline := 0,
       refundCounter := (0),
       stateGasSpilled := 0,
       stateGasCommittedSpill := 0 })
    ) ==
  (0,
    0,
    0,
    0,
    0,
    0)

-- repay-no-reservoir
#guard fields (repayStateGasSpill
    ({ gasLeft := 10,
       stateGasLeft := 0,
       stateGasBaseline := 1,
       refundCounter := (-3),
       stateGasSpilled := 6,
       stateGasCommittedSpill := 7 })
    ) ==
  (10,
    0,
    1,
    (-3),
    6,
    7)

-- repay-no-pending
#guard fields (repayStateGasSpill
    ({ gasLeft := 10,
       stateGasLeft := 4,
       stateGasBaseline := 1,
       refundCounter := (-3),
       stateGasSpilled := 0,
       stateGasCommittedSpill := 7 })
    ) ==
  (10,
    4,
    1,
    (-3),
    0,
    7)

-- repay-less
#guard fields (repayStateGasSpill
    ({ gasLeft := 10,
       stateGasLeft := 4,
       stateGasBaseline := 1,
       refundCounter := (-3),
       stateGasSpilled := 6,
       stateGasCommittedSpill := 7 })
    ) ==
  (14,
    0,
    1,
    (-3),
    2,
    7)

-- repay-equal
#guard fields (repayStateGasSpill
    ({ gasLeft := 10,
       stateGasLeft := 6,
       stateGasBaseline := 1,
       refundCounter := (4),
       stateGasSpilled := 6,
       stateGasCommittedSpill := 7 })
    ) ==
  (16,
    0,
    1,
    4,
    0,
    7)

-- repay-greater-zero-execution
#guard fields (repayStateGasSpill
    ({ gasLeft := 0,
       stateGasLeft := 8,
       stateGasBaseline := 1,
       refundCounter := (-3),
       stateGasSpilled := 6,
       stateGasCommittedSpill := 7 })
    ) ==
  (6,
    2,
    1,
    (-3),
    0,
    7)

-- credit-beyond-word
#guard fields (creditStateGasRefund
    ({ gasLeft := 1361129467683753853853498429727072845824,
       stateGasLeft := 1361129467683753853853498429727072845825,
       stateGasBaseline := 0,
       refundCounter := (-1361129467683753853853498429727072845824),
       stateGasSpilled := 1361129467683753853853498429727072845826,
       stateGasCommittedSpill := 1361129467683753853853498429727072845827 })
    1361129467683753853853498429727072845829) ==
  (2722258935367507707706996859454145691650,
    1361129467683753853853498429727072845828,
    0,
    (-1361129467683753853853498429727072845824),
    0,
    1361129467683753853853498429727072845827)

-- repay-beyond-word
#guard fields (repayStateGasSpill
    ({ gasLeft := 1361129467683753853853498429727072845824,
       stateGasLeft := 1361129467683753853853498429727072845825,
       stateGasBaseline := 0,
       refundCounter := (-1361129467683753853853498429727072845824),
       stateGasSpilled := 1361129467683753853853498429727072845826,
       stateGasCommittedSpill := 1361129467683753853853498429727072845827 })
    ) ==
  (2722258935367507707706996859454145691649,
    0,
    0,
    (-1361129467683753853853498429727072845824),
    1,
    1361129467683753853853498429727072845827)

-- charge-sequence-credit-two
#guard fields (creditStateGasRefund
    ({ gasLeft := 15,
       stateGasLeft := 0,
       stateGasBaseline := 10,
       refundCounter := (-4),
       stateGasSpilled := 5,
       stateGasCommittedSpill := 3 })
    2) ==
  (17,
    0,
    10,
    (-4),
    3,
    3)

-- charge-sequence-credit-six
#guard fields (creditStateGasRefund
    ({ gasLeft := 17,
       stateGasLeft := 0,
       stateGasBaseline := 10,
       refundCounter := (-4),
       stateGasSpilled := 3,
       stateGasCommittedSpill := 3 })
    6) ==
  (20,
    3,
    10,
    (-4),
    0,
    3)

-- credit-sequence-repay
#guard fields (repayStateGasSpill
    ({ gasLeft := 12,
       stateGasLeft := 4,
       stateGasBaseline := 1,
       refundCounter := (-3),
       stateGasSpilled := 4,
       stateGasCommittedSpill := 7 })
    ) ==
  (16,
    0,
    1,
    (-3),
    0,
    7)

-- credit-sequence-repay-again
#guard fields (repayStateGasSpill
    ({ gasLeft := 16,
       stateGasLeft := 0,
       stateGasBaseline := 1,
       refundCounter := (-3),
       stateGasSpilled := 0,
       stateGasCommittedSpill := 7 })
    ) ==
  (16,
    0,
    1,
    (-3),
    0,
    7)

-- counterexample-credit
#guard fields (creditStateGasRefund
    ({ gasLeft := 10,
       stateGasLeft := 2,
       stateGasBaseline := 1,
       refundCounter := (-3),
       stateGasSpilled := 6,
       stateGasCommittedSpill := 7 })
    2) ==
  (12,
    2,
    1,
    (-3),
    4,
    7)

-- Charge/refund/repay composition uses the actual public charge provider.
private def chargeSequence := do
  let charged ← chargeStateGas
    { gasLeft := 20, stateGasLeft := 10, stateGasBaseline := 10,
      refundCounter := -4, stateGasCommittedSpill := 3 } 15
  let credited := creditStateGasRefund charged 2
  let creditedAgain := creditStateGasRefund credited 6
  let repaid := repayStateGasSpill creditedAgain
  .ok (fields charged, fields credited, fields creditedAgain, fields repaid)

#guard (match chargeSequence with
  | .ok result => result == ((15, 0, 10, -4, 5, 3), (17, 0, 10, -4, 3, 3),
      (20, 3, 10, -4, 0, 3), (20, 3, 10, -4, 0, 3))
  | .error _ => false)

private def creditSequence :=
  let credited := creditStateGasRefund
    { gasLeft := 10, stateGasLeft := 4, stateGasBaseline := 1,
      refundCounter := -3, stateGasSpilled := 6, stateGasCommittedSpill := 7 } 2
  let repaid := repayStateGasSpill credited
  (fields credited, fields repaid, fields (repayStateGasSpill repaid))

#guard creditSequence == ((12, 4, 1, -3, 4, 7), (16, 0, 1, -3, 0, 7),
  (16, 0, 1, -3, 0, 7))

-- Initial pending spill invalidates unconditional charge/refund inversion.
private def counterexample := do
  let charged ← chargeStateGas
    { gasLeft := 10, stateGasLeft := 4, stateGasBaseline := 1,
      refundCounter := -3, stateGasSpilled := 6, stateGasCommittedSpill := 7 } 2
  .ok (fields charged, fields (creditStateGasRefund charged 2))

#guard (match counterexample with
  | .ok result => result == ((10, 2, 1, -3, 6, 7), (12, 2, 1, -3, 4, 7)) ∧
      result.2 != (10, 4, 1, -3, 6, 7)
  | .error _ => false)

end STFSpec.Conformance.Vm.Core.GasRefundGuards
