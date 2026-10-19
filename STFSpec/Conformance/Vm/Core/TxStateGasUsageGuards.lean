/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Complete transaction state-gas usage guards

Library `EthConformance`. Literal six-field inputs and signed results include
reservoirs above baseline/grant, both spills and beyond-U256 arithmetic.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/7.
-/

namespace STFSpec.Conformance.Vm.Core.TxStateGasUsageGuards
open STFSpec.Vm.Core

private def fields (m : GasMeter) : Nat × Nat × Nat × Int × Nat × Nat :=
  (m.gasLeft, m.stateGasLeft, m.stateGasBaseline, m.refundCounter,
    m.stateGasSpilled, m.stateGasCommittedSpill)

-- all-zero
private def input0 : GasMeter :=
  { gasLeft := 0,
    stateGasLeft := 0,
    stateGasBaseline := 0,
    refundCounter := (0),
    stateGasSpilled := 0,
    stateGasCommittedSpill := 0 }
#guard (fields input0, 0, txStateGasUsed input0 0 (by decide)) ==
  (((0), (0), (0), (0), (0), (0)), 0, (0 : Int))

-- reservoir-draw
private def input1 : GasMeter :=
  { gasLeft := 17,
    stateGasLeft := 7,
    stateGasBaseline := 4,
    refundCounter := (-31),
    stateGasSpilled := 0,
    stateGasCommittedSpill := 0 }
#guard (fields input1, 10, txStateGasUsed input1 10 (by decide)) ==
  (((17), (7), (4), (-31), (0), (0)), 10, (3 : Int))

-- negative-without-spill
private def input2 : GasMeter :=
  { gasLeft := 3,
    stateGasLeft := 19,
    stateGasBaseline := 5,
    refundCounter := (-11),
    stateGasSpilled := 0,
    stateGasCommittedSpill := 0 }
#guard (fields input2, 8, txStateGasUsed input2 8 (by decide)) ==
  (((3), (19), (5), (-11), (0), (0)), 8, (-11 : Int))

-- spill-cancellation
private def input3 : GasMeter :=
  { gasLeft := 7,
    stateGasLeft := 29,
    stateGasBaseline := 4,
    refundCounter := (-71),
    stateGasSpilled := 8,
    stateGasCommittedSpill := 10 }
#guard (fields input3, 11, txStateGasUsed input3 11 (by decide)) ==
  (((7), (29), (4), (-71), (8), (10)), 11, (0 : Int))

-- pending-only
private def input4 : GasMeter :=
  { gasLeft := 2,
    stateGasLeft := 17,
    stateGasBaseline := 8,
    refundCounter := (91),
    stateGasSpilled := 13,
    stateGasCommittedSpill := 0 }
#guard (fields input4, 9, txStateGasUsed input4 9 (by decide)) ==
  (((2), (17), (8), (91), (13), (0)), 9, (5 : Int))

-- committed-only
private def input5 : GasMeter :=
  { gasLeft := 2,
    stateGasLeft := 17,
    stateGasBaseline := 8,
    refundCounter := (91),
    stateGasSpilled := 0,
    stateGasCommittedSpill := 19 }
#guard (fields input5, 9, txStateGasUsed input5 9 (by decide)) ==
  (((2), (17), (8), (91), (0), (19)), 9, (11 : Int))

-- both-spills
private def input6 : GasMeter :=
  { gasLeft := 0,
    stateGasLeft := 17,
    stateGasBaseline := 8,
    refundCounter := (-91),
    stateGasSpilled := 13,
    stateGasCommittedSpill := 19 }
#guard (fields input6, 9, txStateGasUsed input6 9 (by decide)) ==
  (((0), (17), (8), (-91), (13), (19)), 9, (24 : Int))

-- negative-both-spills
private def input7 : GasMeter :=
  { gasLeft := 23,
    stateGasLeft := 51,
    stateGasBaseline := 9,
    refundCounter := (-17),
    stateGasSpilled := 7,
    stateGasCommittedSpill := 11 }
#guard (fields input7, 12, txStateGasUsed input7 12 (by decide)) ==
  (((23), (51), (9), (-17), (7), (11)), 12, (-21 : Int))

-- guidance-negative-witness
private def input8 : GasMeter :=
  { gasLeft := 13,
    stateGasLeft := 21,
    stateGasBaseline := 9,
    refundCounter := (99),
    stateGasSpilled := 3,
    stateGasCommittedSpill := 5 }
#guard (fields input8, 10, txStateGasUsed input8 10 (by decide)) ==
  (((13), (21), (9), (99), (3), (5)), 10, (-3 : Int))

-- ignored-fields-low-baseline
private def input9 : GasMeter :=
  { gasLeft := 0,
    stateGasLeft := 21,
    stateGasBaseline := 0,
    refundCounter := (-999999),
    stateGasSpilled := 3,
    stateGasCommittedSpill := 5 }
#guard (fields input9, 10, txStateGasUsed input9 10 (by decide)) ==
  (((0), (21), (0), (-999999), (3), (5)), 10, (-3 : Int))

-- ignored-fields-exact-baseline
private def input10 : GasMeter :=
  { gasLeft := 999999,
    stateGasLeft := 21,
    stateGasBaseline := 10,
    refundCounter := (0),
    stateGasSpilled := 3,
    stateGasCommittedSpill := 5 }
#guard (fields input10, 10, txStateGasUsed input10 10 (by decide)) ==
  (((999999), (21), (10), (0), (3), (5)), 10, (-3 : Int))

-- grant-increment
private def input11 : GasMeter :=
  { gasLeft := 13,
    stateGasLeft := 21,
    stateGasBaseline := 9,
    refundCounter := (99),
    stateGasSpilled := 3,
    stateGasCommittedSpill := 5 }
#guard (fields input11, 11, txStateGasUsed input11 11 (by decide)) ==
  (((13), (21), (9), (99), (3), (5)), 11, (-2 : Int))

-- reservoir-increment
private def input12 : GasMeter :=
  { gasLeft := 13,
    stateGasLeft := 22,
    stateGasBaseline := 9,
    refundCounter := (99),
    stateGasSpilled := 3,
    stateGasCommittedSpill := 5 }
#guard (fields input12, 10, txStateGasUsed input12 10 (by decide)) ==
  (((13), (22), (9), (99), (3), (5)), 10, (-4 : Int))

-- pending-increment
private def input13 : GasMeter :=
  { gasLeft := 13,
    stateGasLeft := 21,
    stateGasBaseline := 9,
    refundCounter := (99),
    stateGasSpilled := 4,
    stateGasCommittedSpill := 5 }
#guard (fields input13, 10, txStateGasUsed input13 10 (by decide)) ==
  (((13), (21), (9), (99), (4), (5)), 10, (-2 : Int))

-- committed-increment
private def input14 : GasMeter :=
  { gasLeft := 13,
    stateGasLeft := 21,
    stateGasBaseline := 9,
    refundCounter := (99),
    stateGasSpilled := 3,
    stateGasCommittedSpill := 6 }
#guard (fields input14, 10, txStateGasUsed input14 10 (by decide)) ==
  (((13), (21), (9), (99), (3), (6)), 10, (-2 : Int))

-- baseline-is-not-grant
private def input15 : GasMeter :=
  { gasLeft := 0,
    stateGasLeft := 4,
    stateGasBaseline := 99,
    refundCounter := (71),
    stateGasSpilled := 0,
    stateGasCommittedSpill := 0 }
#guard (fields input15, 100, txStateGasUsed input15 100 (by decide)) ==
  (((0), (4), (99), (71), (0), (0)), 100, (96 : Int))

-- beyond-u64-negative
private def input16 : GasMeter :=
  { gasLeft := 18446744073709551617,
    stateGasLeft := 18446744073709551619,
    stateGasBaseline := 18446744073709551615,
    refundCounter := (-18446744073709551618),
    stateGasSpilled := 1,
    stateGasCommittedSpill := 1 }
#guard (fields input16, 18446744073709551616, txStateGasUsed input16 18446744073709551616 (by
    decide)) ==
  (((18446744073709551617), (18446744073709551619), (18446744073709551615),
    (-18446744073709551618), (1), (1)), 18446744073709551616, (-1 : Int))

-- beyond-u256-signed-subtraction
private def input17 : GasMeter :=
  { gasLeft := 115792089237316195423570985008687907853269984665640564039457584007913129639937,
    stateGasLeft := 115792089237316195423570985008687907853269984665640564039457584007913129639953,
    stateGasBaseline :=
      115792089237316195423570985008687907853269984665640564039457584007913129639935,
    refundCounter :=
      (-115792089237316195423570985008687907853269984665640564039457584007913129639937),
    stateGasSpilled := 3,
    stateGasCommittedSpill := 5 }
#guard (fields input17,
    115792089237316195423570985008687907853269984665640564039457584007913129639936, txStateGasUsed
    input17 115792089237316195423570985008687907853269984665640564039457584007913129639936 (by
    decide)) ==
  (((115792089237316195423570985008687907853269984665640564039457584007913129639937),
    (115792089237316195423570985008687907853269984665640564039457584007913129639953),
    (115792089237316195423570985008687907853269984665640564039457584007913129639935),
    (-115792089237316195423570985008687907853269984665640564039457584007913129639937), (3), (5)),
    115792089237316195423570985008687907853269984665640564039457584007913129639936, (-9 : Int))

-- beyond-u256-spill-sum
private def input18 : GasMeter :=
  { gasLeft := 0,
    stateGasLeft := 0,
    stateGasBaseline := 0,
    refundCounter := (-3),
    stateGasSpilled :=
      115792089237316195423570985008687907853269984665640564039457584007913129639936,
    stateGasCommittedSpill :=
      115792089237316195423570985008687907853269984665640564039457584007913129639936 }
#guard (fields input18, 0, txStateGasUsed input18 0 (by decide)) ==
  (((0), (0), (0), (-3),
    (115792089237316195423570985008687907853269984665640564039457584007913129639936),
    (115792089237316195423570985008687907853269984665640564039457584007913129639936)), 0,
    (231584178474632390847141970017375815706539969331281128078915168015826259279872 : Int))

-- beyond-u256-negative-return
private def input19 : GasMeter :=
  { gasLeft := 19,
    stateGasLeft := 115792089237316195423570985008687907853269984665640564039457584007913129639937,
    stateGasBaseline := 0,
    refundCounter :=
      (115792089237316195423570985008687907853269984665640564039457584007913129639936),
    stateGasSpilled := 0,
    stateGasCommittedSpill := 0 }
#guard (fields input19, 0, txStateGasUsed input19 0 (by decide)) ==
  (((19), (115792089237316195423570985008687907853269984665640564039457584007913129639937), (0),
    (115792089237316195423570985008687907853269984665640564039457584007913129639936), (0), (0)), 0,
    (-115792089237316195423570985008687907853269984665640564039457584007913129639937 : Int))

end STFSpec.Conformance.Vm.Core.TxStateGasUsageGuards
