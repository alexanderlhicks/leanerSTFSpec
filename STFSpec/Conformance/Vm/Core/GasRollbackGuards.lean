/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Complete-field gas rollback guards

Library `EthConformance`. Literal expectations frozen before execution cover every local proof
domain.
No caller reachability, child settlement, transaction conservation or fuel claim follows.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/7.
-/

namespace STFSpec.Conformance.Vm.Core.GasRollbackGuards
open STFSpec.Vm.Core

private def fields (m : GasMeter) : Nat × Nat × Nat × Int × Nat × Nat :=
  (m.gasLeft, m.stateGasLeft, m.stateGasBaseline, m.refundCounter,
    m.stateGasSpilled, m.stateGasCommittedSpill)

-- commit-zero
#guard fields (commitStateGas
    ({ gasLeft := 0,
       stateGasLeft := 0,
       stateGasBaseline := 0,
       refundCounter := (0),
       stateGasSpilled := 0,
       stateGasCommittedSpill := 0 })
    (by decide)) ==
  (0,
    0,
    0,
    0,
    0,
    0)

-- commit-equality
#guard fields (commitStateGas
    ({ gasLeft := 7,
       stateGasLeft := 9,
       stateGasBaseline := 9,
       refundCounter := (4),
       stateGasSpilled := 0,
       stateGasCommittedSpill := 3 })
    (by decide)) ==
  (7,
    9,
    9,
    4,
    0,
    3)

-- commit-both-spills-negative
#guard fields (commitStateGas
    ({ gasLeft := 7,
       stateGasLeft := 2,
       stateGasBaseline := 9,
       refundCounter := (-4),
       stateGasSpilled := 5,
       stateGasCommittedSpill := 3 })
    (by decide)) ==
  (7,
    2,
    2,
    (-4),
    0,
    8)

-- commit-zero-execution
#guard fields (commitStateGas
    ({ gasLeft := 0,
       stateGasLeft := 0,
       stateGasBaseline := 9,
       refundCounter := (-4),
       stateGasSpilled := 5,
       stateGasCommittedSpill := 3 })
    (by decide)) ==
  (0,
    0,
    0,
    (-4),
    0,
    8)

-- restore-zero
#guard fields (restoreStateGas
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

-- restore-reservoir-above-baseline
#guard fields (restoreStateGas
    ({ gasLeft := 7,
       stateGasLeft := 12,
       stateGasBaseline := 9,
       refundCounter := (-4),
       stateGasSpilled := 5,
       stateGasCommittedSpill := 3 })
    ) ==
  (12,
    9,
    9,
    0,
    0,
    3)

-- restore-no-pending
#guard fields (restoreStateGas
    ({ gasLeft := 7,
       stateGasLeft := 2,
       stateGasBaseline := 9,
       refundCounter := (4),
       stateGasSpilled := 0,
       stateGasCommittedSpill := 3 })
    ) ==
  (7,
    9,
    9,
    0,
    0,
    3)

-- restore-zero-execution
#guard fields (restoreStateGas
    ({ gasLeft := 0,
       stateGasLeft := 0,
       stateGasBaseline := 9,
       refundCounter := (-4),
       stateGasSpilled := 5,
       stateGasCommittedSpill := 3 })
    ) ==
  (5,
    9,
    9,
    0,
    0,
    3)

-- entry-zero
#guard fields (restoreStateGasToEntry
    ({ gasLeft := 0,
       stateGasLeft := 0,
       stateGasBaseline := 0,
       refundCounter := (0),
       stateGasSpilled := 0,
       stateGasCommittedSpill := 0 })
    0 (by decide) (by decide)) ==
  (0,
    0,
    0,
    0,
    0,
    0)

-- entry-both-spills
#guard fields (restoreStateGasToEntry
    ({ gasLeft := 7,
       stateGasLeft := 2,
       stateGasBaseline := 9,
       refundCounter := (0),
       stateGasSpilled := 5,
       stateGasCommittedSpill := 3 })
    10 (by decide) (by decide)) ==
  (15,
    10,
    10,
    0,
    0,
    0)

-- entry-equality-above-baseline
#guard fields (restoreStateGasToEntry
    ({ gasLeft := 7,
       stateGasLeft := 12,
       stateGasBaseline := 9,
       refundCounter := (0),
       stateGasSpilled := 5,
       stateGasCommittedSpill := 3 })
    9 (by decide) (by decide)) ==
  (15,
    9,
    9,
    0,
    0,
    0)

-- entry-zero-execution
#guard fields (restoreStateGasToEntry
    ({ gasLeft := 0,
       stateGasLeft := 0,
       stateGasBaseline := 0,
       refundCounter := (0),
       stateGasSpilled := 5,
       stateGasCommittedSpill := 3 })
    10 (by decide) (by decide)) ==
  (8,
    10,
    10,
    0,
    0,
    0)

-- commit-beyond-word
#guard fields (commitStateGas
    ({ gasLeft := 1361129467683753853853498429727072845824,
       stateGasLeft := 1361129467683753853853498429727072845824,
       stateGasBaseline := 1361129467683753853853498429727072845825,
       refundCounter := (-1361129467683753853853498429727072845824),
       stateGasSpilled := 1361129467683753853853498429727072845826,
       stateGasCommittedSpill := 1361129467683753853853498429727072845827 })
    (by decide)) ==
  (1361129467683753853853498429727072845824,
    1361129467683753853853498429727072845824,
    1361129467683753853853498429727072845824,
    (-1361129467683753853853498429727072845824),
    0,
    2722258935367507707706996859454145691653)

-- restore-beyond-word
#guard fields (restoreStateGas
    ({ gasLeft := 1361129467683753853853498429727072845824,
       stateGasLeft := 1361129467683753853853498429727072845824,
       stateGasBaseline := 1361129467683753853853498429727072845825,
       refundCounter := (-1361129467683753853853498429727072845824),
       stateGasSpilled := 1361129467683753853853498429727072845826,
       stateGasCommittedSpill := 1361129467683753853853498429727072845827 })
    ) ==
  (2722258935367507707706996859454145691650,
    1361129467683753853853498429727072845825,
    1361129467683753853853498429727072845825,
    0,
    0,
    1361129467683753853853498429727072845827)

-- entry-beyond-word
#guard fields (restoreStateGasToEntry
    ({ gasLeft := 1361129467683753853853498429727072845824,
       stateGasLeft := 1361129467683753853853498429727072845834,
       stateGasBaseline := 1361129467683753853853498429727072845825,
       refundCounter := (0),
       stateGasSpilled := 1361129467683753853853498429727072845826,
       stateGasCommittedSpill := 1361129467683753853853498429727072845827 })
    1361129467683753853853498429727072845826 (by decide) (by decide)) ==
  (4083388403051261561560495289181218537477,
    1361129467683753853853498429727072845826,
    1361129467683753853853498429727072845826,
    0,
    0,
    0)

-- sequence-commit
#guard fields (commitStateGas
    ({ gasLeft := 15,
       stateGasLeft := 0,
       stateGasBaseline := 10,
       refundCounter := (0),
       stateGasSpilled := 5,
       stateGasCommittedSpill := 0 })
    (by decide)) ==
  (15,
    0,
    0,
    0,
    0,
    5)

-- sequence-restore
#guard fields (restoreStateGas
    ({ gasLeft := 12,
       stateGasLeft := 0,
       stateGasBaseline := 0,
       refundCounter := (0),
       stateGasSpilled := 3,
       stateGasCommittedSpill := 5 })
    ) ==
  (15,
    0,
    0,
    0,
    0,
    5)

-- sequence-entry
#guard fields (restoreStateGasToEntry
    ({ gasLeft := 15,
       stateGasLeft := 0,
       stateGasBaseline := 0,
       refundCounter := (0),
       stateGasSpilled := 0,
       stateGasCommittedSpill := 5 })
    10 (by decide) (by decide)) ==
  (20,
    10,
    10,
    0,
    0,
    0)

-- The supplied charges connect the two rollback boundaries, with complete intermediate fields.
private def sequence := do
  let m ← chargeStateGas { gasLeft := 20, stateGasLeft := 10, stateGasBaseline := 10 } 15
  if h : m.stateGasLeft ≤ m.stateGasBaseline then
    let committed := commitStateGas m h
    let charged ← chargeStateGas committed 3
    let restored := restoreStateGas charged
    if h₁ : restored.stateGasBaseline ≤ 10 then
      if h₂ : restored.refundCounter = 0 then
        .ok (fields m, fields committed, fields charged, fields restored,
          fields (restoreStateGasToEntry restored 10 h₁ h₂))
      else .error ExceptionalHalt.outOfGas
    else .error ExceptionalHalt.outOfGas
  else .error ExceptionalHalt.outOfGas

#guard (match sequence with
  | .ok result => result == ((15, 0, 10, 0, 5, 0), (15, 0, 0, 0, 0, 5),
  (12, 0, 0, 0, 3, 5), (15, 0, 0, 0, 0, 5), (20, 10, 10, 0, 0, 0))
  | .error _ => false)

end STFSpec.Conformance.Vm.Core.GasRollbackGuards
