/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Complete gas-transfer controls

Library `EthConformance`. Literal expectations frozen before target execution.
Local algebra establishes no caller reachability, frame settlement or fuel bound.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/7.
-/

namespace STFSpec.Conformance.Vm.Core.GasTransferGuards
open STFSpec.Vm.Core

private def fields (m : GasMeter) : Nat × Nat × Nat × Int × Nat × Nat :=
  (m.gasLeft, m.stateGasLeft, m.stateGasBaseline, m.refundCounter,
    m.stateGasSpilled, m.stateGasCommittedSpill)

-- forfeit-zero
#guard fields (forfeitRemainingGas
    ({ gasLeft := (0),
       stateGasLeft := (0),
       stateGasBaseline := (0),
       refundCounter := (0),
       stateGasSpilled := (0),
       stateGasCommittedSpill := (0) })
    (by rfl)) ==
  ((0),
    (0),
    (0),
    (0),
    (0),
    (0))

-- forfeit-raw
#guard fields (forfeitRemainingGas
    ({ gasLeft := (17),
       stateGasLeft := (9),
       stateGasBaseline := (2),
       refundCounter := (-7),
       stateGasSpilled := (0),
       stateGasCommittedSpill := (11) })
    (by rfl)) ==
  ((0),
    (9),
    (2),
    (-7),
    (0),
    (11))

-- forfeit-zero-execution
#guard fields (forfeitRemainingGas
    ({ gasLeft := (0),
       stateGasLeft := (9),
       stateGasBaseline := (2),
       refundCounter := (7),
       stateGasSpilled := (0),
       stateGasCommittedSpill := (11) })
    (by rfl)) ==
  ((0),
    (9),
    (2),
    (7),
    (0),
    (11))

-- withhold-0
#guard (
  let result := withholdCreateGas
    ({ gasLeft := (0),
       stateGasLeft := (9),
       stateGasBaseline := (2),
       refundCounter := (-7),
       stateGasSpilled := (5),
       stateGasCommittedSpill := (11) });
  (result.1, fields result.2)) ==
  (0,
    ((0),
    (9),
    (2),
    (-7),
    (5),
    (11)))

-- withhold-1
#guard (
  let result := withholdCreateGas
    ({ gasLeft := (1),
       stateGasLeft := (9),
       stateGasBaseline := (2),
       refundCounter := (-7),
       stateGasSpilled := (5),
       stateGasCommittedSpill := (11) });
  (result.1, fields result.2)) ==
  (1,
    ((0),
    (9),
    (2),
    (-7),
    (5),
    (11)))

-- withhold-63
#guard (
  let result := withholdCreateGas
    ({ gasLeft := (63),
       stateGasLeft := (9),
       stateGasBaseline := (2),
       refundCounter := (-7),
       stateGasSpilled := (5),
       stateGasCommittedSpill := (11) });
  (result.1, fields result.2)) ==
  (63,
    ((0),
    (9),
    (2),
    (-7),
    (5),
    (11)))

-- withhold-64
#guard (
  let result := withholdCreateGas
    ({ gasLeft := (64),
       stateGasLeft := (9),
       stateGasBaseline := (2),
       refundCounter := (-7),
       stateGasSpilled := (5),
       stateGasCommittedSpill := (11) });
  (result.1, fields result.2)) ==
  (63,
    ((1),
    (9),
    (2),
    (-7),
    (5),
    (11)))

-- withhold-65
#guard (
  let result := withholdCreateGas
    ({ gasLeft := (65),
       stateGasLeft := (9),
       stateGasBaseline := (2),
       refundCounter := (-7),
       stateGasSpilled := (5),
       stateGasCommittedSpill := (11) });
  (result.1, fields result.2)) ==
  (64,
    ((1),
    (9),
    (2),
    (-7),
    (5),
    (11)))

-- withhold-127
#guard (
  let result := withholdCreateGas
    ({ gasLeft := (127),
       stateGasLeft := (9),
       stateGasBaseline := (2),
       refundCounter := (-7),
       stateGasSpilled := (5),
       stateGasCommittedSpill := (11) });
  (result.1, fields result.2)) ==
  (126,
    ((1),
    (9),
    (2),
    (-7),
    (5),
    (11)))

-- withhold-128
#guard (
  let result := withholdCreateGas
    ({ gasLeft := (128),
       stateGasLeft := (9),
       stateGasBaseline := (2),
       refundCounter := (-7),
       stateGasSpilled := (5),
       stateGasCommittedSpill := (11) });
  (result.1, fields result.2)) ==
  (126,
    ((2),
    (9),
    (2),
    (-7),
    (5),
    (11)))

-- withhold-129
#guard (
  let result := withholdCreateGas
    ({ gasLeft := (129),
       stateGasLeft := (9),
       stateGasBaseline := (2),
       refundCounter := (-7),
       stateGasSpilled := (5),
       stateGasCommittedSpill := (11) });
  (result.1, fields result.2)) ==
  (127,
    ((2),
    (9),
    (2),
    (-7),
    (5),
    (11)))

-- drain-zero
#guard (
  let result := drainStateGasReservoir
    ({ gasLeft := (0),
       stateGasLeft := (0),
       stateGasBaseline := (0),
       refundCounter := (0),
       stateGasSpilled := (0),
       stateGasCommittedSpill := (0) });
  (result.1, fields result.2)) ==
  (0,
    ((0),
    (0),
    (0),
    (0),
    (0),
    (0)))

-- drain-empty
#guard (
  let result := drainStateGasReservoir
    ({ gasLeft := (17),
       stateGasLeft := (0),
       stateGasBaseline := (2),
       refundCounter := (-7),
       stateGasSpilled := (5),
       stateGasCommittedSpill := (11) });
  (result.1, fields result.2)) ==
  (0,
    ((17),
    (0),
    (2),
    (-7),
    (5),
    (11)))

-- drain-raw
#guard (
  let result := drainStateGasReservoir
    ({ gasLeft := (17),
       stateGasLeft := (9),
       stateGasBaseline := (2),
       refundCounter := (-7),
       stateGasSpilled := (5),
       stateGasCommittedSpill := (11) });
  (result.1, fields result.2)) ==
  (9,
    ((17),
    (0),
    (2),
    (-7),
    (5),
    (11)))

-- restore-0-0
#guard fields (restoreChildGas
    ({ gasLeft := (17),
       stateGasLeft := (9),
       stateGasBaseline := (2),
       refundCounter := (-7),
       stateGasSpilled := (5),
       stateGasCommittedSpill := (11) })
    0 0) ==
  ((17),
    (9),
    (2),
    (-7),
    (5),
    (11))

-- restore-0-13
#guard fields (restoreChildGas
    ({ gasLeft := (17),
       stateGasLeft := (9),
       stateGasBaseline := (2),
       refundCounter := (-7),
       stateGasSpilled := (5),
       stateGasCommittedSpill := (11) })
    0 13) ==
  ((17),
    (22),
    (2),
    (-7),
    (5),
    (11))

-- restore-19-0
#guard fields (restoreChildGas
    ({ gasLeft := (17),
       stateGasLeft := (9),
       stateGasBaseline := (2),
       refundCounter := (-7),
       stateGasSpilled := (5),
       stateGasCommittedSpill := (11) })
    19 0) ==
  ((36),
    (9),
    (2),
    (-7),
    (5),
    (11))

-- restore-19-13
#guard fields (restoreChildGas
    ({ gasLeft := (17),
       stateGasLeft := (9),
       stateGasBaseline := (2),
       refundCounter := (-7),
       stateGasSpilled := (5),
       stateGasCommittedSpill := (11) })
    19 13) ==
  ((36),
    (22),
    (2),
    (-7),
    (5),
    (11))

-- forfeit-beyond-word
#guard fields (forfeitRemainingGas
    ({ gasLeft := (18446744073709551616),
       stateGasLeft := (18446744073709551617),
       stateGasBaseline := (3),
       refundCounter := (-18446744073709551618),
       stateGasSpilled := (0),
       stateGasCommittedSpill := (18446744073709551620) })
    (by rfl)) ==
  ((0),
    (18446744073709551617),
    (3),
    (-18446744073709551618),
    (0),
    (18446744073709551620))

-- withhold-beyond-word
#guard (
  let result := withholdCreateGas
    ({ gasLeft := (18446744073709551616),
       stateGasLeft := (18446744073709551617),
       stateGasBaseline := (3),
       refundCounter := (-18446744073709551618),
       stateGasSpilled := (18446744073709551619),
       stateGasCommittedSpill := (18446744073709551620) });
  (result.1, fields result.2)) ==
  (18158513697557839872,
    ((288230376151711744),
    (18446744073709551617),
    (3),
    (-18446744073709551618),
    (18446744073709551619),
    (18446744073709551620)))

-- drain-beyond-word
#guard (
  let result := drainStateGasReservoir
    ({ gasLeft := (18446744073709551616),
       stateGasLeft := (18446744073709551617),
       stateGasBaseline := (3),
       refundCounter := (-18446744073709551618),
       stateGasSpilled := (18446744073709551619),
       stateGasCommittedSpill := (18446744073709551620) });
  (result.1, fields result.2)) ==
  (18446744073709551617,
    ((18446744073709551616),
    (0),
    (3),
    (-18446744073709551618),
    (18446744073709551619),
    (18446744073709551620)))

-- restore-beyond-word
#guard fields (restoreChildGas
    ({ gasLeft := (18446744073709551616),
       stateGasLeft := (18446744073709551617),
       stateGasBaseline := (3),
       refundCounter := (-18446744073709551618),
       stateGasSpilled := (18446744073709551619),
       stateGasCommittedSpill := (18446744073709551620) })
    18446744073709551621 18446744073709551622) ==
  ((36893488147419103237),
    (36893488147419103239),
    (3),
    (-18446744073709551618),
    (18446744073709551619),
    (18446744073709551620))

-- sequence-withhold
#guard (
  let result := withholdCreateGas
    ({ gasLeft := (130),
       stateGasLeft := (9),
       stateGasBaseline := (2),
       refundCounter := (-7),
       stateGasSpilled := (5),
       stateGasCommittedSpill := (11) });
  (result.1, fields result.2)) ==
  (128,
    ((2),
    (9),
    (2),
    (-7),
    (5),
    (11)))

-- sequence-drain
#guard (
  let result := drainStateGasReservoir
    ({ gasLeft := (2),
       stateGasLeft := (9),
       stateGasBaseline := (2),
       refundCounter := (-7),
       stateGasSpilled := (5),
       stateGasCommittedSpill := (11) });
  (result.1, fields result.2)) ==
  (9,
    ((2),
    (0),
    (2),
    (-7),
    (5),
    (11)))

-- sequence-drain-again
#guard (
  let result := drainStateGasReservoir
    ({ gasLeft := (2),
       stateGasLeft := (0),
       stateGasBaseline := (2),
       refundCounter := (-7),
       stateGasSpilled := (5),
       stateGasCommittedSpill := (11) });
  (result.1, fields result.2)) ==
  (0,
    ((2),
    (0),
    (2),
    (-7),
    (5),
    (11)))

-- sequence-restore
#guard fields (restoreChildGas
    ({ gasLeft := (2),
       stateGasLeft := (0),
       stateGasBaseline := (2),
       refundCounter := (-7),
       stateGasSpilled := (5),
       stateGasCommittedSpill := (11) })
    128 9) ==
  ((130),
    (9),
    (2),
    (-7),
    (5),
    (11))

-- sequence-restore-zero
#guard fields (restoreChildGas
    ({ gasLeft := (2),
       stateGasLeft := (0),
       stateGasBaseline := (2),
       refundCounter := (-7),
       stateGasSpilled := (5),
       stateGasCommittedSpill := (11) })
    0 0) ==
  ((2),
    (0),
    (2),
    (-7),
    (5),
    (11))

-- ordinary-rollback-forfeit
#guard fields (forfeitRemainingGas
    ({ gasLeft := (16),
       stateGasLeft := (9),
       stateGasBaseline := (9),
       refundCounter := (0),
       stateGasSpilled := (0),
       stateGasCommittedSpill := (7) })
    (by rfl)) ==
  ((0),
    (9),
    (9),
    (0),
    (0),
    (7))

-- ordinary-forfeit-again
#guard fields (forfeitRemainingGas
    ({ gasLeft := (0),
       stateGasLeft := (9),
       stateGasBaseline := (9),
       refundCounter := (0),
       stateGasSpilled := (0),
       stateGasCommittedSpill := (7) })
    (by rfl)) ==
  ((0),
    (9),
    (9),
    (0),
    (0),
    (7))

-- entry-rollback-forfeit
#guard fields (forfeitRemainingGas
    ({ gasLeft := (23),
       stateGasLeft := (12),
       stateGasBaseline := (12),
       refundCounter := (0),
       stateGasSpilled := (0),
       stateGasCommittedSpill := (0) })
    (by rfl)) ==
  ((0),
    (12),
    (12),
    (0),
    (0),
    (0))

-- Each composition uses the actual public providers and checks every intermediate.
private def roundtrip :=
  let m : GasMeter := {
    gasLeft := 130, stateGasLeft := 9, stateGasBaseline := 2,
    refundCounter := -7, stateGasSpilled := 5, stateGasCommittedSpill := 11 }
  let w := withholdCreateGas m
  let d := drainStateGasReservoir w.2
  let d' := drainStateGasReservoir d.2
  (fields m, (w.1, fields w.2), (d.1, fields d.2), (d'.1, fields d'.2),
    fields (restoreChildGas d.2 w.1 d.1), fields (restoreChildGas d.2 0 0))

#guard roundtrip == ((130,9,2,-7,5,11), (128,(2,9,2,-7,5,11)),
  (9,(2,0,2,-7,5,11)), (0,(2,0,2,-7,5,11)), (130,9,2,-7,5,11), (2,0,2,-7,5,11))

private def ordinary :=
  let m : GasMeter := {
    gasLeft := 10, stateGasLeft := 4, stateGasBaseline := 9,
    refundCounter := -3, stateGasSpilled := 6, stateGasCommittedSpill := 7 }
  let r := restoreStateGas m
  let h := (restoreStateGas_post m).1
  let f := forfeitRemainingGas r h
  have hf : f.stateGasSpilled = 0 := by
    change (forfeitRemainingGas r h).stateGasSpilled = 0
    rw [forfeitRemainingGas_eq]
    exact h
  (fields m, fields r, fields f, fields (forfeitRemainingGas f hf))

#guard ordinary == ((10,4,9,-3,6,7), (16,9,9,0,0,7), (0,9,9,0,0,7), (0,9,9,0,0,7))

private def entry :=
  let m : GasMeter := {
    gasLeft := 10, stateGasLeft := 4, stateGasBaseline := 9,
    refundCounter := 0, stateGasSpilled := 6, stateGasCommittedSpill := 7 }
  let r := restoreStateGasToEntry m 12 (by decide) (by rfl)
  let f := forfeitRemainingGas r (restoreStateGasToEntry_post m 12 (by decide) (by rfl)).1
  (fields m, fields r, fields f)

#guard entry == ((10,4,9,0,6,7), (23,12,12,0,0,0), (0,12,12,0,0,0))

end STFSpec.Conformance.Vm.Core.GasTransferGuards
