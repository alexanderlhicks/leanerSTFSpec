/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Complete signed refund and maximum-grant controls

Library `EthConformance`. Literal full results frozen before first target execution.
These are local record/scalar facts, without caller reachability or settlement claims.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/7.
-/

namespace STFSpec.Conformance.Vm.Core.GasAccountingGuards
open STFSpec.Vm.Core

private def fields (m : GasMeter) : Nat × Nat × Nat × Int × Nat × Nat :=
  (m.gasLeft, m.stateGasLeft, m.stateGasBaseline, m.refundCounter,
    m.stateGasSpilled, m.stateGasCommittedSpill)

-- zero
#guard fields (addRefund
    ({ gasLeft := 0,
       stateGasLeft := 0,
       stateGasBaseline := 0,
       refundCounter := (0),
       stateGasSpilled := 0,
       stateGasCommittedSpill := 0 })
    (0)) ==
  ((0),
    (0),
    (0),
    (0),
    (0),
    (0))

-- raw-zero
#guard fields (addRefund
    ({ gasLeft := 17,
       stateGasLeft := 9,
       stateGasBaseline := 2,
       refundCounter := (-7),
       stateGasSpilled := 5,
       stateGasCommittedSpill := 11 })
    (0)) ==
  ((17),
    (9),
    (2),
    (-7),
    (5),
    (11))

-- negative
#guard fields (addRefund
    ({ gasLeft := 17,
       stateGasLeft := 9,
       stateGasBaseline := 2,
       refundCounter := (3),
       stateGasSpilled := 5,
       stateGasCommittedSpill := 11 })
    (-7)) ==
  ((17),
    (9),
    (2),
    (-4),
    (5),
    (11))

-- positive
#guard fields (addRefund
    ({ gasLeft := 17,
       stateGasLeft := 9,
       stateGasBaseline := 2,
       refundCounter := (-7),
       stateGasSpilled := 5,
       stateGasCommittedSpill := 11 })
    (3)) ==
  ((17),
    (9),
    (2),
    (-4),
    (5),
    (11))

-- cross-positive
#guard fields (addRefund
    ({ gasLeft := 17,
       stateGasLeft := 9,
       stateGasBaseline := 2,
       refundCounter := (-7),
       stateGasSpilled := 5,
       stateGasCommittedSpill := 11 })
    (10)) ==
  ((17),
    (9),
    (2),
    (3),
    (5),
    (11))

-- cross-negative
#guard fields (addRefund
    ({ gasLeft := 17,
       stateGasLeft := 9,
       stateGasBaseline := 2,
       refundCounter := (7),
       stateGasSpilled := 5,
       stateGasCommittedSpill := 11 })
    (-10)) ==
  ((17),
    (9),
    (2),
    (-3),
    (5),
    (11))

-- cancel-positive
#guard fields (addRefund
    ({ gasLeft := 17,
       stateGasLeft := 9,
       stateGasBaseline := 2,
       refundCounter := (7),
       stateGasSpilled := 5,
       stateGasCommittedSpill := 11 })
    (-7)) ==
  ((17),
    (9),
    (2),
    (0),
    (5),
    (11))

-- cancel-negative
#guard fields (addRefund
    ({ gasLeft := 17,
       stateGasLeft := 9,
       stateGasBaseline := 2,
       refundCounter := (-7),
       stateGasSpilled := 5,
       stateGasCommittedSpill := 11 })
    (7)) ==
  ((17),
    (9),
    (2),
    (0),
    (5),
    (11))

-- add-zero
#guard fields (addRefund
    ({ gasLeft := 0,
       stateGasLeft := 9,
       stateGasBaseline := 2,
       refundCounter := (0),
       stateGasSpilled := 5,
       stateGasCommittedSpill := 11 })
    (-1)) ==
  ((0),
    (9),
    (2),
    (-1),
    (5),
    (11))

-- beyond-u256-positive
#guard fields (addRefund
    ({ gasLeft := 17,
       stateGasLeft := 9,
       stateGasBaseline := 2,
       refundCounter :=
         (115792089237316195423570985008687907853269984665640564039457584007913129639936),
       stateGasSpilled := 5,
       stateGasCommittedSpill := 11 })
    (1)) ==
  ((17),
    (9),
    (2),
    (115792089237316195423570985008687907853269984665640564039457584007913129639937),
    (5),
    (11))

-- beyond-u256-negative
#guard fields (addRefund
    ({ gasLeft := 17,
       stateGasLeft := 9,
       stateGasBaseline := 2,
       refundCounter :=
         (-115792089237316195423570985008687907853269984665640564039457584007913129639936),
       stateGasSpilled := 5,
       stateGasCommittedSpill := 11 })
    (-1)) ==
  ((17),
    (9),
    (2),
    (-115792089237316195423570985008687907853269984665640564039457584007913129639937),
    (5),
    (11))

-- large-all-fields
#guard fields (addRefund
    ({ gasLeft := 1361129467683753853853498429727072845824,
       stateGasLeft := 1361129467683753853853498429727072845825,
       stateGasBaseline := 3,
       refundCounter := (-1361129467683753853853498429727072845826),
       stateGasSpilled := 1361129467683753853853498429727072845827,
       stateGasCommittedSpill := 1361129467683753853853498429727072845828 })
    (1361129467683753853853498429727072845829)) ==
  ((1361129467683753853853498429727072845824),
    (1361129467683753853853498429727072845825),
    (3),
    (3),
    (1361129467683753853853498429727072845827),
    (1361129467683753853853498429727072845828))

-- max-0
#guard maxMessageCallGas 0 == 0

-- max-1
#guard maxMessageCallGas 1 == 1

-- max-62
#guard maxMessageCallGas 62 == 62

-- max-63
#guard maxMessageCallGas 63 == 63

-- max-64
#guard maxMessageCallGas 64 == 63

-- max-65
#guard maxMessageCallGas 65 == 64

-- max-127
#guard maxMessageCallGas 127 == 126

-- max-128
#guard maxMessageCallGas 128 == 126

-- max-129
#guard maxMessageCallGas 129 == 127

-- max-4095
#guard maxMessageCallGas 4095 == 4032

-- max-4096
#guard maxMessageCallGas 4096 == 4032

-- max-4097
#guard maxMessageCallGas 4097 == 4033

-- max-18446744073709551616
#guard maxMessageCallGas 18446744073709551616 == 18158513697557839872

-- max-115792089237316195423570985008687907853269984665640564039457584007913129639936
#guard maxMessageCallGas
  115792089237316195423570985008687907853269984665640564039457584007913129639936 ==
  113982837842983129870077688367927159293062641155239930226341059257789486989312

private def composition :=
  let m : GasMeter := {
    gasLeft := 17, stateGasLeft := 9, stateGasBaseline := 2,
    refundCounter := -7, stateGasSpilled := 5, stateGasCommittedSpill := 11 }
  let first := addRefund m 10
  let second := addRefund first (-10)
  let beforeReset := restoreStateGas first
  let reset := restoreStateGas m
  let afterReset := addRefund reset 10
  (fields m, fields first, fields second, fields beforeReset, fields reset, fields afterReset)

#guard composition == ((17,9,2,-7,5,11), (17,9,2,3,5,11), (17,9,2,-7,5,11),
  (22,2,2,0,0,11), (22,2,2,0,0,11), (22,2,2,10,0,11))

end STFSpec.Conformance.Vm.Core.GasAccountingGuards
