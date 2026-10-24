/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core
import STFSpec.Conformance.Vm.Core.TransactionGasSettlementGuards
import Lean

/-!
# Complete interpreted/native settlement observations

Library `EthConformance`. Fifty actual calls/constructors; fixture support is private.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/7 (Q66).
-/

open STFSpec.Vm.Core STFSpec.Base Lean

private def natJson (n : Nat) : Json := toJson (toString n)
private def intJson (n : Int) : Json := toJson (toString n)
private def settlementJson (a : TransactionGasSettlement) : Json :=
  Json.mkObj [("gasUsed", natJson a.gasUsed), ("gasLeft", natJson a.gasLeft),
    ("executionGasUsed", natJson a.executionGasUsed), ("stateGasUsed", natJson a.stateGasUsed)]
private def inputJson (t f e r : Nat) (refund : U256) (s : Int) : Json :=
  Json.mkObj [("txGas", natJson t), ("calldataFloor", natJson f),
    ("gasLeft", natJson e), ("stateGasLeft", natJson r),
    ("refundUnsigned", natJson refund.toNat), ("stateSigned", intJson s)]
private def emit (value : Json) : IO Unit :=
  (do (← IO.getStdout).putStrLn value.compress)
private def emitHelper (id : String) (t f e r : Nat) (refund : U256) (s : Int)
    (hReturned : e + r ≤ t) (hState : s.toNat ≤ t - e - r) (hFloor : f ≤ t) : IO Unit := do
  let before := inputJson t f e r refund s
  let value := settleTransactionGas t f e r refund s hReturned hState hFloor
  emit (Json.mkObj [("id", toJson id), ("kind", toJson "helper"),
    ("input", before), ("after", inputJson t f e r refund s),
    ("result", settlementJson value)])
private def emitRaw (id : String) (u l x s : Nat) : IO Unit := do
  let value := TransactionGasSettlement.mk u l x s
  let reconstructed := TransactionGasSettlement.mk value.gasUsed value.gasLeft
    value.executionGasUsed value.stateGasUsed
  emit (Json.mkObj [("id", toJson id), ("kind", toJson "raw"),
    ("input", Json.mkObj [("gasUsed", natJson u), ("gasLeft", natJson l),
      ("executionGasUsed", natJson x), ("stateGasUsed", natJson s)]),
    ("after", Json.mkObj [("gasUsed", natJson u), ("gasLeft", natJson l),
      ("executionGasUsed", natJson x), ("stateGasUsed", natJson s)]),
    ("result", settlementJson value), ("reconstructed", settlementJson reconstructed),
    ("equal", toJson (value.gasUsed == reconstructed.gasUsed &&
      value.gasLeft == reconstructed.gasLeft &&
      value.executionGasUsed == reconstructed.executionGasUsed &&
      value.stateGasUsed == reconstructed.stateGasUsed))])

/-- The sole executable entry emits every actual input and complete result. -/
def main : IO UInt32 := do
  try
    emit (Json.mkObj [("schema", toJson "transaction-gas-settlement-v1"),
      ("candidate", toJson "q66-three-bounds-u256"),
      ("catalog", toJson "85e4141895312e8b634aeef4b421da9300826bbdf5c2898ec9fd0992b3e38711"),
      ("mode", toJson "target"), ("count", toJson (50 : Nat))])
    emitHelper "S01" 0 0 0 0
      (U256.ofNat 0) (0) (by decide) (by decide) (by decide)
    emitHelper "S02" 1 0 0 0
      (U256.ofNat 0) (0) (by decide) (by decide) (by decide)
    emitHelper "S03" 4 0 0 0
      (U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (0) (by decide) (by decide) (by decide)
    emitHelper "S04" 5 0 0 0
      (U256.ofNat 1) (0) (by decide) (by decide) (by decide)
    emitHelper "S05" 6 0 0 0
      (U256.ofNat 1) (0) (by decide) (by decide) (by decide)
    emitHelper "S06" 9 0 0 0
      (U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (0) (by decide) (by decide) (by decide)
    emitHelper "S07" 10 0 0 0
      (U256.ofNat 0) (0) (by decide) (by decide) (by decide)
    emitHelper "S08" 10 0 0 0
      (U256.ofNat 1) (0) (by decide) (by decide) (by decide)
    emitHelper "S09" 10 0 0 0
      (U256.ofNat 2) (0) (by decide) (by decide) (by decide)
    emitHelper "S10" 10 0 0 0
      (U256.ofNat 3) (0) (by decide) (by decide) (by decide)
    emitHelper "S11" 11 0 0 0
      (U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (0) (by decide) (by decide) (by decide)
    emitHelper "S12" 14 0 0 0
      (U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (0) (by decide) (by decide) (by decide)
    emitHelper "S13" 15 0 0 0
      (U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (0) (by decide) (by decide) (by decide)
    emitHelper "S14" 100 0 10 20
      (U256.ofNat 14) (30) (by decide) (by decide) (by decide)
    emitHelper "S15" 100 0 10 20
      (U256.ofNat 13) (30) (by decide) (by decide) (by decide)
    emitHelper "S16" 100 0 10 20
      (U256.ofNat 15) (30) (by decide) (by decide) (by decide)
    emitHelper "S17" 100 55 10 20
      (U256.ofNat 14) (30) (by decide) (by decide) (by decide)
    emitHelper "S18" 100 56 10 20
      (U256.ofNat 14) (30) (by decide) (by decide) (by decide)
    emitHelper "S19" 100 57 10 20
      (U256.ofNat 14) (30) (by decide) (by decide) (by decide)
    emitHelper "S20" 10 10 0 0
      (U256.ofNat 0) (1) (by decide) (by decide) (by decide)
    emitHelper "S21" 10 10 0 0
      (U256.ofNat 2) (10) (by decide) (by decide) (by decide)
    emitHelper "S22" 10 0 0 0
      (U256.ofNat 2) (10) (by decide) (by decide) (by decide)
    emitHelper "S23" 10 1 0 0
      (U256.ofNat 2) (10) (by decide) (by decide) (by decide)
    emitHelper "S24" 10 0 0 0
      (U256.ofNat 2) (-1) (by decide) (by decide) (by decide)
    emitHelper "S25" 10 0 0 0
      (U256.ofNat 2) (-115792089237316195423570985008687907853269984665640564039457584007913129639936) (by decide) (by decide) (by decide)
    emitHelper "S26" 100 0 40 60
      (U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (-1) (by decide) (by decide) (by decide)
    emitHelper "S27" 100 20 40 60
      (U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (0) (by decide) (by decide) (by decide)
    emitHelper "S28" 100 0 100 0
      (U256.ofNat 0) (0) (by decide) (by decide) (by decide)
    emitHelper "S29" 100 0 0 100
      (U256.ofNat 0) (0) (by decide) (by decide) (by decide)
    emitHelper "S30" 100 100 40 60
      (U256.ofNat 0) (0) (by decide) (by decide) (by decide)
    emitHelper "S31" 64 0 0 0
      (U256.ofNat 12) (63) (by decide) (by decide) (by decide)
    emitHelper "S32" 64 1 0 0
      (U256.ofNat 12) (63) (by decide) (by decide) (by decide)
    emitHelper "S33" 64 2 0 0
      (U256.ofNat 12) (63) (by decide) (by decide) (by decide)
    emitHelper "S34" 115792089237316195423570985008687907853269984665640564039457584007913129639936 0 0 0
      (U256.ofNat 0) (0) (by decide) (by decide) (by decide)
    emitHelper "S35" 115792089237316195423570985008687907853269984665640564039457584007913129639937 0 115792089237316195423570985008687907853269984665640564039457584007913129639936 0
      (U256.ofNat 0) (1) (by decide) (by decide) (by decide)
    emitHelper "S36" 115792089237316195423570985008687907853269984665640564039457584007913129639936 115792089237316195423570985008687907853269984665640564039457584007913129639936 0 0
      (U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (115792089237316195423570985008687907853269984665640564039457584007913129639936) (by decide) (by decide) (by decide)
    emitHelper "S37" 18446744073709551626 0 18446744073709551616 0
      (U256.ofNat 2) (5) (by decide) (by decide) (by decide)
    emitHelper "S38" 10 0 0 0
      (U256.ofNat 57896044618658097711785492504343953926634992332820282019728792003956564819968) (0) (by decide) (by decide) (by decide)
    emitHelper "S39" 10 0 0 0
      (U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (0) (by decide) (by decide) (by decide)
    emitHelper "S40" 100 0 20 10
      (U256.ofNat 14) (30) (by decide) (by decide) (by decide)
    emitHelper "S41" 100 0 10 20
      (U256.ofNat 14) (40) (by decide) (by decide) (by decide)
    emitHelper "S42" 100 40 10 20
      (U256.ofNat 14) (30) (by decide) (by decide) (by decide)
    emitHelper "S43" 100 39 10 20
      (U256.ofNat 14) (30) (by decide) (by decide) (by decide)
    emitHelper "S44" 100 41 10 20
      (U256.ofNat 14) (30) (by decide) (by decide) (by decide)
    emitRaw "R01" 0 0 0 0
    emitRaw "R02" 1 2 3 4
    emitRaw "R03" 4 3 2 1
    emitRaw "R04" 0 1 0 2
    emitRaw "R05" 18446744073709551616 0 115792089237316195423570985008687907853269984665640564039457584007913129639936 1
    emitRaw "R06" 1 115792089237316195423570985008687907853269984665640564039457584007913129639937 0 18446744073709551616
    emit (Json.mkObj [("end", toJson true), ("count", toJson (50 : Nat)),
      ("catalog", toJson "85e4141895312e8b634aeef4b421da9300826bbdf5c2898ec9fd0992b3e38711")])
    return 0
  catch error =>
    (← IO.getStderr).putStrLn s!"FAIL {error}"
    return 1
