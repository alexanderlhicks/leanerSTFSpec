/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Complete settlement controls

Library `EthConformance`. Fifty handwritten complete ordered controls, including raw eta.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/7 (Q66).
-/

namespace STFSpec.Conformance.Vm.Core.TransactionGasSettlementGuards
open STFSpec.Vm.Core STFSpec.Base

private def tuple (a : TransactionGasSettlement) : Nat × Nat × Nat × Nat :=
  (a.gasUsed, a.gasLeft, a.executionGasUsed, a.stateGasUsed)

-- S01
#guard tuple (settleTransactionGas 0 0 0 0
    (U256.ofNat 0) (0) (by decide) (by decide) (by decide)) == (0, 0, 0, 0)

-- S02
#guard tuple (settleTransactionGas 1 0 0 0
    (U256.ofNat 0) (0) (by decide) (by decide) (by decide)) == (1, 0, 1, 0)

-- S03
#guard tuple (settleTransactionGas 4 0 0 0
    (U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (0) (by decide) (by decide) (by decide)) == (4, 0, 4, 0)

-- S04
#guard tuple (settleTransactionGas 5 0 0 0
    (U256.ofNat 1) (0) (by decide) (by decide) (by decide)) == (4, 1, 5, 0)

-- S05
#guard tuple (settleTransactionGas 6 0 0 0
    (U256.ofNat 1) (0) (by decide) (by decide) (by decide)) == (5, 1, 6, 0)

-- S06
#guard tuple (settleTransactionGas 9 0 0 0
    (U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (0) (by decide) (by decide) (by decide)) == (8, 1, 9, 0)

-- S07
#guard tuple (settleTransactionGas 10 0 0 0
    (U256.ofNat 0) (0) (by decide) (by decide) (by decide)) == (10, 0, 10, 0)

-- S08
#guard tuple (settleTransactionGas 10 0 0 0
    (U256.ofNat 1) (0) (by decide) (by decide) (by decide)) == (9, 1, 10, 0)

-- S09
#guard tuple (settleTransactionGas 10 0 0 0
    (U256.ofNat 2) (0) (by decide) (by decide) (by decide)) == (8, 2, 10, 0)

-- S10
#guard tuple (settleTransactionGas 10 0 0 0
    (U256.ofNat 3) (0) (by decide) (by decide) (by decide)) == (8, 2, 10, 0)

-- S11
#guard tuple (settleTransactionGas 11 0 0 0
    (U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (0) (by decide) (by decide) (by decide)) == (9, 2, 11, 0)

-- S12
#guard tuple (settleTransactionGas 14 0 0 0
    (U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (0) (by decide) (by decide) (by decide)) == (12, 2, 14, 0)

-- S13
#guard tuple (settleTransactionGas 15 0 0 0
    (U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (0) (by decide) (by decide) (by decide)) == (12, 3, 15, 0)

-- S14
#guard tuple (settleTransactionGas 100 0 10 20
    (U256.ofNat 14) (30) (by decide) (by decide) (by decide)) == (56, 44, 40, 30)

-- S15
#guard tuple (settleTransactionGas 100 0 10 20
    (U256.ofNat 13) (30) (by decide) (by decide) (by decide)) == (57, 43, 40, 30)

-- S16
#guard tuple (settleTransactionGas 100 0 10 20
    (U256.ofNat 15) (30) (by decide) (by decide) (by decide)) == (56, 44, 40, 30)

-- S17
#guard tuple (settleTransactionGas 100 55 10 20
    (U256.ofNat 14) (30) (by decide) (by decide) (by decide)) == (56, 44, 55, 30)

-- S18
#guard tuple (settleTransactionGas 100 56 10 20
    (U256.ofNat 14) (30) (by decide) (by decide) (by decide)) == (56, 44, 56, 30)

-- S19
#guard tuple (settleTransactionGas 100 57 10 20
    (U256.ofNat 14) (30) (by decide) (by decide) (by decide)) == (57, 43, 57, 30)

-- S20
#guard tuple (settleTransactionGas 10 10 0 0
    (U256.ofNat 0) (1) (by decide) (by decide) (by decide)) == (10, 0, 10, 1)

-- S21
#guard tuple (settleTransactionGas 10 10 0 0
    (U256.ofNat 2) (10) (by decide) (by decide) (by decide)) == (10, 0, 10, 10)

-- S22
#guard tuple (settleTransactionGas 10 0 0 0
    (U256.ofNat 2) (10) (by decide) (by decide) (by decide)) == (8, 2, 0, 10)

-- S23
#guard tuple (settleTransactionGas 10 1 0 0
    (U256.ofNat 2) (10) (by decide) (by decide) (by decide)) == (8, 2, 1, 10)

-- S24
#guard tuple (settleTransactionGas 10 0 0 0
    (U256.ofNat 2) (-1) (by decide) (by decide) (by decide)) == (8, 2, 10, 0)

-- S25
#guard tuple (settleTransactionGas 10 0 0 0
    (U256.ofNat 2) (-115792089237316195423570985008687907853269984665640564039457584007913129639936) (by decide) (by decide) (by decide)) == (8, 2, 10, 0)

-- S26
#guard tuple (settleTransactionGas 100 0 40 60
    (U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (-1) (by decide) (by decide) (by decide)) == (0, 100, 0, 0)

-- S27
#guard tuple (settleTransactionGas 100 20 40 60
    (U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (0) (by decide) (by decide) (by decide)) == (20, 80, 20, 0)

-- S28
#guard tuple (settleTransactionGas 100 0 100 0
    (U256.ofNat 0) (0) (by decide) (by decide) (by decide)) == (0, 100, 0, 0)

-- S29
#guard tuple (settleTransactionGas 100 0 0 100
    (U256.ofNat 0) (0) (by decide) (by decide) (by decide)) == (0, 100, 0, 0)

-- S30
#guard tuple (settleTransactionGas 100 100 40 60
    (U256.ofNat 0) (0) (by decide) (by decide) (by decide)) == (100, 0, 100, 0)

-- S31
#guard tuple (settleTransactionGas 64 0 0 0
    (U256.ofNat 12) (63) (by decide) (by decide) (by decide)) == (52, 12, 1, 63)

-- S32
#guard tuple (settleTransactionGas 64 1 0 0
    (U256.ofNat 12) (63) (by decide) (by decide) (by decide)) == (52, 12, 1, 63)

-- S33
#guard tuple (settleTransactionGas 64 2 0 0
    (U256.ofNat 12) (63) (by decide) (by decide) (by decide)) == (52, 12, 2, 63)

-- S34
#guard tuple (settleTransactionGas 115792089237316195423570985008687907853269984665640564039457584007913129639936 0 0 0
    (U256.ofNat 0) (0) (by decide) (by decide) (by decide)) == (115792089237316195423570985008687907853269984665640564039457584007913129639936, 0, 115792089237316195423570985008687907853269984665640564039457584007913129639936, 0)

-- S35
#guard tuple (settleTransactionGas 115792089237316195423570985008687907853269984665640564039457584007913129639937 0 115792089237316195423570985008687907853269984665640564039457584007913129639936 0
    (U256.ofNat 0) (1) (by decide) (by decide) (by decide)) == (1, 115792089237316195423570985008687907853269984665640564039457584007913129639936, 0, 1)

-- S36
#guard tuple (settleTransactionGas 115792089237316195423570985008687907853269984665640564039457584007913129639936 115792089237316195423570985008687907853269984665640564039457584007913129639936 0 0
    (U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (115792089237316195423570985008687907853269984665640564039457584007913129639936) (by decide) (by decide) (by decide)) == (115792089237316195423570985008687907853269984665640564039457584007913129639936, 0, 115792089237316195423570985008687907853269984665640564039457584007913129639936, 115792089237316195423570985008687907853269984665640564039457584007913129639936)

-- S37
#guard tuple (settleTransactionGas 18446744073709551626 0 18446744073709551616 0
    (U256.ofNat 2) (5) (by decide) (by decide) (by decide)) == (8, 18446744073709551618, 5, 5)

-- S38
#guard tuple (settleTransactionGas 10 0 0 0
    (U256.ofNat 57896044618658097711785492504343953926634992332820282019728792003956564819968) (0) (by decide) (by decide) (by decide)) == (8, 2, 10, 0)

-- S39
#guard tuple (settleTransactionGas 10 0 0 0
    (U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (0) (by decide) (by decide) (by decide)) == (8, 2, 10, 0)

-- S40
#guard tuple (settleTransactionGas 100 0 20 10
    (U256.ofNat 14) (30) (by decide) (by decide) (by decide)) == (56, 44, 40, 30)

-- S41
#guard tuple (settleTransactionGas 100 0 10 20
    (U256.ofNat 14) (40) (by decide) (by decide) (by decide)) == (56, 44, 30, 40)

-- S42
#guard tuple (settleTransactionGas 100 40 10 20
    (U256.ofNat 14) (30) (by decide) (by decide) (by decide)) == (56, 44, 40, 30)

-- S43
#guard tuple (settleTransactionGas 100 39 10 20
    (U256.ofNat 14) (30) (by decide) (by decide) (by decide)) == (56, 44, 40, 30)

-- S44
#guard tuple (settleTransactionGas 100 41 10 20
    (U256.ofNat 14) (30) (by decide) (by decide) (by decide)) == (56, 44, 41, 30)

-- R01: unrestricted carrier and actual eta reconstruction.
private theorem R01_eta :
    TransactionGasSettlement.mk (TransactionGasSettlement.mk 0 0 0 0).gasUsed
      (TransactionGasSettlement.mk 0 0 0 0).gasLeft
      (TransactionGasSettlement.mk 0 0 0 0).executionGasUsed
      (TransactionGasSettlement.mk 0 0 0 0).stateGasUsed = TransactionGasSettlement.mk 0 0 0 0 :=
  TransactionGasSettlement.eta _
#guard tuple (TransactionGasSettlement.mk 0 0 0 0) == (0, 0, 0, 0)
#guard tuple (TransactionGasSettlement.mk (TransactionGasSettlement.mk 0 0 0 0).gasUsed
    (TransactionGasSettlement.mk 0 0 0 0).gasLeft
    (TransactionGasSettlement.mk 0 0 0 0).executionGasUsed
    (TransactionGasSettlement.mk 0 0 0 0).stateGasUsed) == (0, 0, 0, 0)

-- R02: unrestricted carrier and actual eta reconstruction.
private theorem R02_eta :
    TransactionGasSettlement.mk (TransactionGasSettlement.mk 1 2 3 4).gasUsed
      (TransactionGasSettlement.mk 1 2 3 4).gasLeft
      (TransactionGasSettlement.mk 1 2 3 4).executionGasUsed
      (TransactionGasSettlement.mk 1 2 3 4).stateGasUsed = TransactionGasSettlement.mk 1 2 3 4 :=
  TransactionGasSettlement.eta _
#guard tuple (TransactionGasSettlement.mk 1 2 3 4) == (1, 2, 3, 4)
#guard tuple (TransactionGasSettlement.mk (TransactionGasSettlement.mk 1 2 3 4).gasUsed
    (TransactionGasSettlement.mk 1 2 3 4).gasLeft
    (TransactionGasSettlement.mk 1 2 3 4).executionGasUsed
    (TransactionGasSettlement.mk 1 2 3 4).stateGasUsed) == (1, 2, 3, 4)

-- R03: unrestricted carrier and actual eta reconstruction.
private theorem R03_eta :
    TransactionGasSettlement.mk (TransactionGasSettlement.mk 4 3 2 1).gasUsed
      (TransactionGasSettlement.mk 4 3 2 1).gasLeft
      (TransactionGasSettlement.mk 4 3 2 1).executionGasUsed
      (TransactionGasSettlement.mk 4 3 2 1).stateGasUsed = TransactionGasSettlement.mk 4 3 2 1 :=
  TransactionGasSettlement.eta _
#guard tuple (TransactionGasSettlement.mk 4 3 2 1) == (4, 3, 2, 1)
#guard tuple (TransactionGasSettlement.mk (TransactionGasSettlement.mk 4 3 2 1).gasUsed
    (TransactionGasSettlement.mk 4 3 2 1).gasLeft
    (TransactionGasSettlement.mk 4 3 2 1).executionGasUsed
    (TransactionGasSettlement.mk 4 3 2 1).stateGasUsed) == (4, 3, 2, 1)

-- R04: unrestricted carrier and actual eta reconstruction.
private theorem R04_eta :
    TransactionGasSettlement.mk (TransactionGasSettlement.mk 0 1 0 2).gasUsed
      (TransactionGasSettlement.mk 0 1 0 2).gasLeft
      (TransactionGasSettlement.mk 0 1 0 2).executionGasUsed
      (TransactionGasSettlement.mk 0 1 0 2).stateGasUsed = TransactionGasSettlement.mk 0 1 0 2 :=
  TransactionGasSettlement.eta _
#guard tuple (TransactionGasSettlement.mk 0 1 0 2) == (0, 1, 0, 2)
#guard tuple (TransactionGasSettlement.mk (TransactionGasSettlement.mk 0 1 0 2).gasUsed
    (TransactionGasSettlement.mk 0 1 0 2).gasLeft
    (TransactionGasSettlement.mk 0 1 0 2).executionGasUsed
    (TransactionGasSettlement.mk 0 1 0 2).stateGasUsed) == (0, 1, 0, 2)

-- R05: unrestricted carrier and actual eta reconstruction.
private theorem R05_eta :
    TransactionGasSettlement.mk (TransactionGasSettlement.mk 18446744073709551616 0 115792089237316195423570985008687907853269984665640564039457584007913129639936 1).gasUsed
      (TransactionGasSettlement.mk 18446744073709551616 0 115792089237316195423570985008687907853269984665640564039457584007913129639936 1).gasLeft
      (TransactionGasSettlement.mk 18446744073709551616 0 115792089237316195423570985008687907853269984665640564039457584007913129639936 1).executionGasUsed
      (TransactionGasSettlement.mk 18446744073709551616 0 115792089237316195423570985008687907853269984665640564039457584007913129639936 1).stateGasUsed = TransactionGasSettlement.mk 18446744073709551616 0 115792089237316195423570985008687907853269984665640564039457584007913129639936 1 :=
  TransactionGasSettlement.eta _
#guard tuple (TransactionGasSettlement.mk 18446744073709551616 0 115792089237316195423570985008687907853269984665640564039457584007913129639936 1) == (18446744073709551616, 0, 115792089237316195423570985008687907853269984665640564039457584007913129639936, 1)
#guard tuple (TransactionGasSettlement.mk (TransactionGasSettlement.mk 18446744073709551616 0 115792089237316195423570985008687907853269984665640564039457584007913129639936 1).gasUsed
    (TransactionGasSettlement.mk 18446744073709551616 0 115792089237316195423570985008687907853269984665640564039457584007913129639936 1).gasLeft
    (TransactionGasSettlement.mk 18446744073709551616 0 115792089237316195423570985008687907853269984665640564039457584007913129639936 1).executionGasUsed
    (TransactionGasSettlement.mk 18446744073709551616 0 115792089237316195423570985008687907853269984665640564039457584007913129639936 1).stateGasUsed) == (18446744073709551616, 0, 115792089237316195423570985008687907853269984665640564039457584007913129639936, 1)

-- R06: unrestricted carrier and actual eta reconstruction.
private theorem R06_eta :
    TransactionGasSettlement.mk (TransactionGasSettlement.mk 1 115792089237316195423570985008687907853269984665640564039457584007913129639937 0 18446744073709551616).gasUsed
      (TransactionGasSettlement.mk 1 115792089237316195423570985008687907853269984665640564039457584007913129639937 0 18446744073709551616).gasLeft
      (TransactionGasSettlement.mk 1 115792089237316195423570985008687907853269984665640564039457584007913129639937 0 18446744073709551616).executionGasUsed
      (TransactionGasSettlement.mk 1 115792089237316195423570985008687907853269984665640564039457584007913129639937 0 18446744073709551616).stateGasUsed = TransactionGasSettlement.mk 1 115792089237316195423570985008687907853269984665640564039457584007913129639937 0 18446744073709551616 :=
  TransactionGasSettlement.eta _
#guard tuple (TransactionGasSettlement.mk 1 115792089237316195423570985008687907853269984665640564039457584007913129639937 0 18446744073709551616) == (1, 115792089237316195423570985008687907853269984665640564039457584007913129639937, 0, 18446744073709551616)
#guard tuple (TransactionGasSettlement.mk (TransactionGasSettlement.mk 1 115792089237316195423570985008687907853269984665640564039457584007913129639937 0 18446744073709551616).gasUsed
    (TransactionGasSettlement.mk 1 115792089237316195423570985008687907853269984665640564039457584007913129639937 0 18446744073709551616).gasLeft
    (TransactionGasSettlement.mk 1 115792089237316195423570985008687907853269984665640564039457584007913129639937 0 18446744073709551616).executionGasUsed
    (TransactionGasSettlement.mk 1 115792089237316195423570985008687907853269984665640564039457584007913129639937 0 18446744073709551616).stateGasUsed) == (1, 115792089237316195423570985008687907853269984665640564039457584007913129639937, 0, 18446744073709551616)

end STFSpec.Conformance.Vm.Core.TransactionGasSettlementGuards
