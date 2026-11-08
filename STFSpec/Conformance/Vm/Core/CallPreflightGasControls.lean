/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Complete CALL preflight numeric controls

Library `EthConformance`. Independent literal expectations retain all six meter
fields at every prefix stage. The raw configuration deliberately has ZERO = 7,
a default stipend different from every explicit stipend, and unrelated raw fields.
Source coherence, actual handler effects and child execution remain separate.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/7/10.
-/

namespace STFSpec.Conformance.Vm.Core.CallPreflightGasControls
open STFSpec.Vm.Core STFSpec.Base

private def rawConfig : VmConfig := {
  costs := {
    base := 0
    veryLow := 0
    low := 0
    mid := 0
    high := 0
    warmAccess := 0
    coldAccountAccess := 0
    coldStorageAccess := 0
    storageWrite := 0
    callStipend := 901
    accountWrite := 0
    callValue := 0
    codeInitPerWord := 2
    createAccess := 0
    zero := 7
    memoryPerWord := 0
    fastStep := 0
    refundStorageClear := (-11)
    precompileEcrecover := 0
    precompileP256Verify := 0
    precompileSha256Base := 0
    precompileSha256PerWord := 0
    precompileRipemd160Base := 0
    precompileRipemd160PerWord := 0
    precompileIdentityBase := 0
    precompileIdentityPerWord := 0
    precompileBlake2FPerRound := 0
    precompilePointEvaluation := 0
    precompileBlsG1Add := 0
    precompileBlsG1Mul := 0
    precompileBlsG1Map := 0
    precompileBlsG2Add := 0
    precompileBlsG2Mul := 0
    precompileBlsG2Map := 0
    precompileEcAdd := 0
    precompileEcMul := 0
    precompileEcPairingBase := 0
    precompileEcPairingPerPoint := 0
    perBlob := U64.ofNat 0
    blobScheduleTarget := U64.ofNat 0
    blobTargetGasPerBlock := U64.ofNat 0
    blobBaseCost := 0
    blobScheduleMax := U64.ofNat 0
    blobMinGasPrice := 0
    blobBaseFeeUpdateFraction := 0
    blockAccessListItem := 0
    txBase := 0
    txValueCost := 0
    txDataTokenStandard := 0
    txDataTokenFloor := 0
    txAccessListAddress := 0
    txAccessListStorageKey := 0
    txMaxGasLimit := 0
    txMaxTotalGasLimit := 0
    authTupleBytes := 0
    executionPerAuthBaseCost := 0
    limitAdjustmentFactor := 0
    limitMinimum := 0
    opcodeAdd := 0
    opcodeSub := 0
    opcodeMul := 0
    opcodeDiv := 0
    opcodeSdiv := 0
    opcodeMod := 0
    opcodeSmod := 0
    opcodeAddmod := 0
    opcodeMulmod := 0
    opcodeSignextend := 0
    opcodeLt := 0
    opcodeGt := 0
    opcodeSlt := 0
    opcodeSgt := 0
    opcodeEq := 0
    opcodeIsZero := 0
    opcodeAnd := 0
    opcodeOr := 0
    opcodeXor := 0
    opcodeNot := 0
    opcodeByte := 0
    opcodeShl := 0
    opcodeShr := 0
    opcodeSar := 0
    opcodeClz := 0
    opcodeJump := 0
    opcodeJumpi := 0
    opcodeJumpDest := 0
    opcodeCallDataLoad := 0
    opcodeBlockHash := 0
    opcodeCoinbase := 0
    opcodePop := 0
    opcodeMsize := 0
    opcodePc := 0
    opcodeGas := 0
    opcodeAddress := 0
    opcodeOrigin := 0
    opcodeCaller := 0
    opcodeCallValue := 0
    opcodeCallDataSize := 0
    opcodeCodeSize := 0
    opcodeGasPrice := 0
    opcodeTimestamp := 0
    opcodeNumber := 0
    opcodeGasLimit := 0
    opcodePrevRandao := 0
    opcodeReturnDataSize := 0
    opcodeChainId := 0
    opcodeSelfBalance := 0
    opcodeBaseFee := 0
    opcodeBlobBaseFee := 0
    opcodeSlotNum := 0
    opcodeBlobHash := 0
    opcodePush := 0
    opcodePush0 := 0
    opcodeDup := 0
    opcodeSwap := 0
    opcodeDupn := 0
    opcodeSwapn := 0
    opcodeExchange := 0
    opcodeTload := 0
    opcodeTstore := 0
    opcodeReturnDataCopyBase := 0
    opcodeReturnDataCopyPerWord := 0
    opcodeCallDataCopyBase := 0
    opcodeCodeCopyBase := 0
    opcodeMcopyBase := 0
    opcodeMloadBase := 0
    opcodeMstoreBase := 0
    opcodeMstore8Base := 0
    opcodeCopyPerWord := 0
    opcodeExpBase := 0
    opcodeExpPerByte := 0
    opcodeKeccak256Base := 0
    opcodeKeccak256PerWord := 0
    opcodeLogBase := 0
    opcodeLogDataPerByte := 0
    opcodeLogTopic := 0
    opcodeSelfDestructBase := 0
    blsPairingBase := 0
    blsPairingPerPair := 0
    blsG1KDiscount := #[]
    blsG2KDiscount := #[]
    blsG1MaxDiscount := 0
    blsG2MaxDiscount := 0
    blsMultiplier := 0
  }
  stateCosts := {
    costPerStateByte := 2,
    bytesPerNewAccount := 3,
    bytesPerStorageSet := 4,
    bytesPerAuthBase := 5
  }
  limits := { stackDepthLimit := 7, maxCodeSize := 8, maxInitCodeSize := 9 }
}

private def snapshot (m : GasMeter) : Nat × Nat × Nat × Int × Nat × Nat :=
  (m.gasLeft, m.stateGasLeft, m.stateGasBaseline, m.refundCounter,
    m.stateGasSpilled, m.stateGasCommittedSpill)

private def runPrefix (cfg : VmConfig) (value : U256)
    (requested stipend overhead : Nat) (stateCharge : Option Nat) (credit : Bool)
    (initial : GasMeter) :
    Except ExceptionalHalt ((List (Nat × Nat × Nat × Int × Nat × Nat)) × Nat × Nat × Nat) := do
  let paid ← chargeGas initial overhead
  let current ← match stateCharge with
    | none => .ok paid
    | some amount => chargeStateGas paid amount
  let r := calculateMessageCallGas cfg value requested current.gasLeft 0 0 stipend
  let charged ← chargeGas current r.cost
  let drained := drainStateGasReservoir charged
  let returned := restoreChildGas drained.2 r.subCall drained.1
  let final := if credit then creditStateGasRefund returned (stateCharge.getD 0) else returned
  return ([snapshot paid, snapshot current, snapshot charged, snapshot drained.2,
    snapshot returned, snapshot final], r.cost, r.subCall, drained.1)

private def result (r : Except ExceptionalHalt
    ((List (Nat × Nat × Nat × Int × Nat × Nat)) × Nat × Nat × Nat)) :
    Option ((List (Nat × Nat × Nat × Int × Nat × Nat)) × Nat × Nat × Nat) :=
  match r with
  | .ok value => some value
  | .error _ => none

private def zeroConfig : VmConfig :=
  { rawConfig with costs := { rawConfig.costs with zero := 0 } }

-- No state step, arbitrary reservoir above baseline, signed refund and both spills.
#guard result (runPrefix zeroConfig U256.zero 1000 3 10 none false
    (GasMeter.mk 100 20 3 (-7) 5 11)) == some
  ([(90,20,3,-7,5,11), (90,20,3,-7,5,11), (1,20,3,-7,5,11),
    (1,0,3,-7,5,11), (90,20,3,-7,5,11), (90,20,3,-7,5,11)], 89,89,20)

-- Nonspill charge; full credit also repays preexisting pending spill.
#guard result (runPrefix zeroConfig U256.one 40 3 10 (some 8) true
    (GasMeter.mk 100 20 3 (-7) 5 11)) == some
  ([(90,20,3,-7,5,11), (90,12,3,-7,5,11), (50,12,3,-7,5,11),
    (50,0,3,-7,5,11), (93,12,3,-7,5,11), (98,15,3,-7,0,11)], 40,43,12)

-- Spill thins the exact calculator budget; old and new spill both receive credit.
#guard result (runPrefix zeroConfig U256.one 1000 3 10 (some 25) true
    (GasMeter.mk 100 20 3 (-7) 5 11)) == some
  ([(90,20,3,-7,5,11), (85,0,3,-7,10,11), (1,0,3,-7,10,11),
    (1,0,3,-7,10,11), (88,0,3,-7,10,11), (98,15,3,-7,0,11)], 84,87,0)

-- Spill without a matching credit retains the complete new spill and empty reservoir.
#guard result (runPrefix zeroConfig U256.one 1000 3 10 (some 25) false
    (GasMeter.mk 100 20 3 (-7) 5 11)) == some
  ([(90,20,3,-7,5,11), (85,0,3,-7,10,11), (1,0,3,-7,10,11),
    (1,0,3,-7,10,11), (88,0,3,-7,10,11), (88,0,3,-7,10,11)], 84,87,0)

-- With no preexisting pending spill, a nonspill charge/full-credit restores its reservoir.
#guard result (runPrefix zeroConfig U256.one 40 3 10 (some 8) true
    (GasMeter.mk 100 20 3 9 0 11)) == some
  ([(90,20,3,9,0,11), (90,12,3,9,0,11), (50,12,3,9,0,11),
    (50,0,3,9,0,11), (93,12,3,9,0,11), (93,20,3,9,0,11)], 40,43,12)

-- Charged state path without credit; positive signed refund and zero request.
#guard result (runPrefix zeroConfig U256.zero 0 3 10 (some 8) false
    (GasMeter.mk 100 20 3 9 30 11)) == some
  ([(90,20,3,9,30,11), (90,12,3,9,30,11), (90,12,3,9,30,11),
    (90,0,3,9,30,11), (90,12,3,9,30,11), (90,12,3,9,30,11)], 0,0,12)

-- Matching credit can leave reservoir depleted while paying old spill.
#guard result (runPrefix zeroConfig U256.zero 0 3 10 (some 8) true
    (GasMeter.mk 100 20 3 9 30 11)) == some
  ([(90,20,3,9,30,11), (90,12,3,9,30,11), (90,12,3,9,30,11),
    (90,0,3,9,30,11), (90,12,3,9,30,11), (98,12,3,9,22,11)], 0,0,12)

-- Exact strict financing boundary: t+1 = overhead; full stipend return.
#guard result (runPrefix zeroConfig U256.one 100 3 4 none false
    (GasMeter.mk 10 1 8 5 2 4)) == some
  ([(6,1,8,5,2,4), (6,1,8,5,2,4), (0,1,8,5,2,4),
    (0,0,8,5,2,4), (9,1,8,5,2,4), (9,1,8,5,2,4)], 6,9,1)

-- Nonincrease boundary t = overhead supplies no strict progress.
#guard result (runPrefix zeroConfig U256.one 100 3 3 none false
    (GasMeter.mk 10 1 8 5 2 4)) == some
  ([(7,1,8,5,2,4), (7,1,8,5,2,4), (0,1,8,5,2,4),
    (0,0,8,5,2,4), (10,1,8,5,2,4), (10,1,8,5,2,4)], 7,10,1)

-- Zero overhead and zero effective stipend give complete equality, not progress.
#guard result (runPrefix zeroConfig U256.zero 1000 77 0 none false
    (GasMeter.mk 64 9 1 (-3) 4 8)) == some
  ([(64,9,1,-3,4,8), (64,9,1,-3,4,8), (1,9,1,-3,4,8),
    (1,0,1,-3,4,8), (64,9,1,-3,4,8), (64,9,1,-3,4,8)], 63,63,9)

-- Raw cfg.ZERO stays independent of literal calculator 0 and the passed stipend.
#guard result (runPrefix rawConfig U256.zero 100 99 8 none false
    (GasMeter.mk 10 0 99 (-8) 1 6)) == some
  ([(2,0,99,-8,1,6), (2,0,99,-8,1,6), (0,0,99,-8,1,6),
    (0,0,99,-8,1,6), (9,0,99,-8,1,6), (9,0,99,-8,1,6)], 2,9,0)

-- Exact total state affordability leaves zero execution gas, but returns stipend.
#guard result (runPrefix zeroConfig U256.one 100 3 4 (some 7) true
    (GasMeter.mk 10 1 8 5 2 4)) == some
  ([(6,1,8,5,2,4), (0,0,8,5,8,4), (0,0,8,5,8,4),
    (0,0,8,5,8,4), (3,0,8,5,8,4), (10,0,8,5,1,4)], 0,3,0)

-- One unit beyond execution overhead and total state affordability fail.
#guard match runPrefix zeroConfig U256.zero 100 0 11 none false
    (GasMeter.mk 10 1 8 5 2 4) with
  | .error .outOfGas => true
  | _ => false
#guard match runPrefix zeroConfig U256.zero 100 0 4 (some 8) true
    (GasMeter.mk 10 1 8 5 2 4) with
  | .error .outOfGas => true
  | _ => false

-- Fully consumed overhead is affordable; literal-zero forwarding cannot be short.
#guard result (runPrefix zeroConfig U256.zero 100 77 10 none false
    (GasMeter.mk 10 1 8 5 2 4)) == some
  ([(0,1,8,5,2,4), (0,1,8,5,2,4), (0,1,8,5,2,4),
    (0,0,8,5,2,4), (0,1,8,5,2,4), (0,1,8,5,2,4)], 0,0,1)

-- Independent potential boundaries, using full literal meters above.
#guard (GasMeter.mk 9 1 8 5 2 4).phi + 1 == (GasMeter.mk 10 1 8 5 2 4).phi
#guard (GasMeter.mk 10 1 8 5 2 4).phi == (GasMeter.mk 10 1 8 5 2 4).phi
#guard !((GasMeter.mk 64 9 1 (-3) 4 8).phi + 1 ≤
  (GasMeter.mk 64 9 1 (-3) 4 8).phi)

/-! ### Supplied returned execution and reservoir controls -/

private def runActualReturn (cfg : VmConfig) (value : U256)
    (requested stipend overhead : Nat) (stateCharge : Option Nat) (credit : Bool)
    (initial : GasMeter) (execution reservoir : Nat) :
    Except ExceptionalHalt
      (((List (Nat × Nat × Nat × Int × Nat × Nat)) × Nat × Nat × Nat) ×
        Nat × Nat × Bool × Bool × Bool × Bool × Bool × Bool) := do
  let paid ← chargeGas initial overhead
  let current ← match stateCharge with
    | none => .ok paid
    | some amount => chargeStateGas paid amount
  let r := calculateMessageCallGas cfg value requested current.gasLeft 0 0 stipend
  let charged ← chargeGas current r.cost
  let drained := drainStateGasReservoir charged
  let returned := restoreChildGas drained.2 execution reservoir
  let final := if credit then creditStateGasRefund returned (stateCharge.getD 0) else returned
  let effectiveStipend := if value = U256.zero then cfg.costs.zero else stipend
  return (([snapshot paid, snapshot current, snapshot charged, snapshot drained.2,
    snapshot returned, snapshot final], r.cost, r.subCall, drained.1), initial.phi, final.phi,
    decide (execution ≤ r.subCall), decide (effectiveStipend + 1 ≤ overhead),
    decide (effectiveStipend ≤ overhead), decide (final.phi + 1 ≤ initial.phi),
    decide (final.phi ≤ initial.phi), decide (execution + 1 ≤ overhead + r.cost))

-- Complete mathematical expectations were frozen before these return controls existed.
-- Prefix input templates originate in the accepted parent controls, not EELS execution.

-- Return case 0: zero execution return.
#guard match runActualReturn zeroConfig U256.zero 1000 3 10 none false
    (GasMeter.mk 100 20 3 (-7) 5 11) 0 0 with
  | .ok observed => observed ==
    (([(90,20,3,-7,5,11),
      (90,20,3,-7,5,11),
      (1,20,3,-7,5,11),
      (1,0,3,-7,5,11),
      (1,0,3,-7,5,11),
      (1,0,3,-7,5,11)],
      89, 89, 20),
      116, 17, true, true, true, true, true, true)
  | .error _ => false

-- Return case 1: half execution return.
#guard match runActualReturn zeroConfig U256.zero 1000 3 10 none false
    (GasMeter.mk 100 20 3 (-7) 5 11) 44 20 with
  | .ok observed => observed ==
    (([(90,20,3,-7,5,11),
      (90,20,3,-7,5,11),
      (1,20,3,-7,5,11),
      (1,0,3,-7,5,11),
      (45,20,3,-7,5,11),
      (45,20,3,-7,5,11)],
      89, 89, 20),
      116, 61, true, true, true, true, true, true)
  | .error _ => false

-- Return case 2: full execution return.
#guard match runActualReturn zeroConfig U256.zero 1000 3 10 none false
    (GasMeter.mk 100 20 3 (-7) 5 11) 89 27 with
  | .ok observed => observed ==
    (([(90,20,3,-7,5,11),
      (90,20,3,-7,5,11),
      (1,20,3,-7,5,11),
      (1,0,3,-7,5,11),
      (90,27,3,-7,5,11),
      (90,27,3,-7,5,11)],
      89, 89, 20),
      116, 106, true, true, true, true, true, true)
  | .error _ => false

-- Return case 3: over execution return.
#guard match runActualReturn zeroConfig U256.zero 1000 3 10 none false
    (GasMeter.mk 100 20 3 (-7) 5 11) 90 1361129467683753853853498429727072845827 with
  | .ok observed => observed ==
    (([(90,20,3,-7,5,11),
      (90,20,3,-7,5,11),
      (1,20,3,-7,5,11),
      (1,0,3,-7,5,11),
      (91,1361129467683753853853498429727072845827,3,-7,5,11),
      (91,1361129467683753853853498429727072845827,3,-7,5,11)],
      89, 89, 20),
      116, 107, false, true, true, true, true, true)
  | .error _ => false

-- Return case 4: zero execution return.
#guard match runActualReturn zeroConfig U256.one 40 3 10 (some 8) true
    (GasMeter.mk 100 20 3 (-7) 5 11) 0 0 with
  | .ok observed => observed ==
    (([(90,20,3,-7,5,11),
      (90,12,3,-7,5,11),
      (50,12,3,-7,5,11),
      (50,0,3,-7,5,11),
      (50,0,3,-7,5,11),
      (55,3,3,-7,0,11)],
      40, 43, 12),
      116, 66, true, true, true, true, true, true)
  | .error _ => false

-- Return case 5: half execution return.
#guard match runActualReturn zeroConfig U256.one 40 3 10 (some 8) true
    (GasMeter.mk 100 20 3 (-7) 5 11) 21 12 with
  | .ok observed => observed ==
    (([(90,20,3,-7,5,11),
      (90,12,3,-7,5,11),
      (50,12,3,-7,5,11),
      (50,0,3,-7,5,11),
      (71,12,3,-7,5,11),
      (76,15,3,-7,0,11)],
      40, 43, 12),
      116, 87, true, true, true, true, true, true)
  | .error _ => false

-- Return case 6: full execution return.
#guard match runActualReturn zeroConfig U256.one 40 3 10 (some 8) true
    (GasMeter.mk 100 20 3 (-7) 5 11) 43 19 with
  | .ok observed => observed ==
    (([(90,20,3,-7,5,11),
      (90,12,3,-7,5,11),
      (50,12,3,-7,5,11),
      (50,0,3,-7,5,11),
      (93,19,3,-7,5,11),
      (98,22,3,-7,0,11)],
      40, 43, 12),
      116, 109, true, true, true, true, true, true)
  | .error _ => false

-- Return case 7: over execution return.
#guard match runActualReturn zeroConfig U256.one 40 3 10 (some 8) true
    (GasMeter.mk 100 20 3 (-7) 5 11) 44 1361129467683753853853498429727072845831 with
  | .ok observed => observed ==
    (([(90,20,3,-7,5,11),
      (90,12,3,-7,5,11),
      (50,12,3,-7,5,11),
      (50,0,3,-7,5,11),
      (94,1361129467683753853853498429727072845831,3,-7,5,11),
      (99,1361129467683753853853498429727072845834,3,-7,0,11)],
      40, 43, 12),
      116, 110, false, true, true, true, true, true)
  | .error _ => false

-- Return case 8: zero execution return.
#guard match runActualReturn zeroConfig U256.one 1000 3 10 (some 25) true
    (GasMeter.mk 100 20 3 (-7) 5 11) 0 0 with
  | .ok observed => observed ==
    (([(90,20,3,-7,5,11),
      (85,0,3,-7,10,11),
      (1,0,3,-7,10,11),
      (1,0,3,-7,10,11),
      (1,0,3,-7,10,11),
      (11,15,3,-7,0,11)],
      84, 87, 0),
      116, 22, true, true, true, true, true, true)
  | .error _ => false

-- Return case 9: half execution return.
#guard match runActualReturn zeroConfig U256.one 1000 3 10 (some 25) true
    (GasMeter.mk 100 20 3 (-7) 5 11) 43 0 with
  | .ok observed => observed ==
    (([(90,20,3,-7,5,11),
      (85,0,3,-7,10,11),
      (1,0,3,-7,10,11),
      (1,0,3,-7,10,11),
      (44,0,3,-7,10,11),
      (54,15,3,-7,0,11)],
      84, 87, 0),
      116, 65, true, true, true, true, true, true)
  | .error _ => false

-- Return case 10: full execution return.
#guard match runActualReturn zeroConfig U256.one 1000 3 10 (some 25) true
    (GasMeter.mk 100 20 3 (-7) 5 11) 87 7 with
  | .ok observed => observed ==
    (([(90,20,3,-7,5,11),
      (85,0,3,-7,10,11),
      (1,0,3,-7,10,11),
      (1,0,3,-7,10,11),
      (88,7,3,-7,10,11),
      (98,22,3,-7,0,11)],
      84, 87, 0),
      116, 109, true, true, true, true, true, true)
  | .error _ => false

-- Return case 11: over execution return.
#guard match runActualReturn zeroConfig U256.one 1000 3 10 (some 25) true
    (GasMeter.mk 100 20 3 (-7) 5 11) 88 1361129467683753853853498429727072845835 with
  | .ok observed => observed ==
    (([(90,20,3,-7,5,11),
      (85,0,3,-7,10,11),
      (1,0,3,-7,10,11),
      (1,0,3,-7,10,11),
      (89,1361129467683753853853498429727072845835,3,-7,10,11),
      (99,1361129467683753853853498429727072845850,3,-7,0,11)],
      84, 87, 0),
      116, 110, false, true, true, true, true, true)
  | .error _ => false

-- Return case 12: zero execution return.
#guard match runActualReturn zeroConfig U256.one 1000 3 10 (some 25) false
    (GasMeter.mk 100 20 3 (-7) 5 11) 0 0 with
  | .ok observed => observed ==
    (([(90,20,3,-7,5,11),
      (85,0,3,-7,10,11),
      (1,0,3,-7,10,11),
      (1,0,3,-7,10,11),
      (1,0,3,-7,10,11),
      (1,0,3,-7,10,11)],
      84, 87, 0),
      116, 22, true, true, true, true, true, true)
  | .error _ => false

-- Return case 13: half execution return.
#guard match runActualReturn zeroConfig U256.one 1000 3 10 (some 25) false
    (GasMeter.mk 100 20 3 (-7) 5 11) 43 0 with
  | .ok observed => observed ==
    (([(90,20,3,-7,5,11),
      (85,0,3,-7,10,11),
      (1,0,3,-7,10,11),
      (1,0,3,-7,10,11),
      (44,0,3,-7,10,11),
      (44,0,3,-7,10,11)],
      84, 87, 0),
      116, 65, true, true, true, true, true, true)
  | .error _ => false

-- Return case 14: full execution return.
#guard match runActualReturn zeroConfig U256.one 1000 3 10 (some 25) false
    (GasMeter.mk 100 20 3 (-7) 5 11) 87 7 with
  | .ok observed => observed ==
    (([(90,20,3,-7,5,11),
      (85,0,3,-7,10,11),
      (1,0,3,-7,10,11),
      (1,0,3,-7,10,11),
      (88,7,3,-7,10,11),
      (88,7,3,-7,10,11)],
      84, 87, 0),
      116, 109, true, true, true, true, true, true)
  | .error _ => false

-- Return case 15: over execution return.
#guard match runActualReturn zeroConfig U256.one 1000 3 10 (some 25) false
    (GasMeter.mk 100 20 3 (-7) 5 11) 88 1361129467683753853853498429727072845839 with
  | .ok observed => observed ==
    (([(90,20,3,-7,5,11),
      (85,0,3,-7,10,11),
      (1,0,3,-7,10,11),
      (1,0,3,-7,10,11),
      (89,1361129467683753853853498429727072845839,3,-7,10,11),
      (89,1361129467683753853853498429727072845839,3,-7,10,11)],
      84, 87, 0),
      116, 110, false, true, true, true, true, true)
  | .error _ => false

-- Return case 16: zero execution return.
#guard match runActualReturn zeroConfig U256.one 40 3 10 (some 8) true
    (GasMeter.mk 100 20 3 9 0 11) 0 0 with
  | .ok observed => observed ==
    (([(90,20,3,9,0,11),
      (90,12,3,9,0,11),
      (50,12,3,9,0,11),
      (50,0,3,9,0,11),
      (50,0,3,9,0,11),
      (50,8,3,9,0,11)],
      40, 43, 12),
      111, 61, true, true, true, true, true, true)
  | .error _ => false

-- Return case 17: half execution return.
#guard match runActualReturn zeroConfig U256.one 40 3 10 (some 8) true
    (GasMeter.mk 100 20 3 9 0 11) 21 12 with
  | .ok observed => observed ==
    (([(90,20,3,9,0,11),
      (90,12,3,9,0,11),
      (50,12,3,9,0,11),
      (50,0,3,9,0,11),
      (71,12,3,9,0,11),
      (71,20,3,9,0,11)],
      40, 43, 12),
      111, 82, true, true, true, true, true, true)
  | .error _ => false

-- Return case 18: full execution return.
#guard match runActualReturn zeroConfig U256.one 40 3 10 (some 8) true
    (GasMeter.mk 100 20 3 9 0 11) 43 19 with
  | .ok observed => observed ==
    (([(90,20,3,9,0,11),
      (90,12,3,9,0,11),
      (50,12,3,9,0,11),
      (50,0,3,9,0,11),
      (93,19,3,9,0,11),
      (93,27,3,9,0,11)],
      40, 43, 12),
      111, 104, true, true, true, true, true, true)
  | .error _ => false

-- Return case 19: over execution return.
#guard match runActualReturn zeroConfig U256.one 40 3 10 (some 8) true
    (GasMeter.mk 100 20 3 9 0 11) 44 1361129467683753853853498429727072845843 with
  | .ok observed => observed ==
    (([(90,20,3,9,0,11),
      (90,12,3,9,0,11),
      (50,12,3,9,0,11),
      (50,0,3,9,0,11),
      (94,1361129467683753853853498429727072845843,3,9,0,11),
      (94,1361129467683753853853498429727072845851,3,9,0,11)],
      40, 43, 12),
      111, 105, false, true, true, true, true, true)
  | .error _ => false

-- Return case 20: zero execution return.
#guard match runActualReturn zeroConfig U256.zero 0 3 10 (some 8) false
    (GasMeter.mk 100 20 3 9 30 11) 0 0 with
  | .ok observed => observed ==
    (([(90,20,3,9,30,11),
      (90,12,3,9,30,11),
      (90,12,3,9,30,11),
      (90,0,3,9,30,11),
      (90,0,3,9,30,11),
      (90,0,3,9,30,11)],
      0, 0, 12),
      141, 131, true, true, true, true, true, true)
  | .error _ => false

-- Return case 21: half execution return.
#guard match runActualReturn zeroConfig U256.zero 0 3 10 (some 8) false
    (GasMeter.mk 100 20 3 9 30 11) 0 12 with
  | .ok observed => observed ==
    (([(90,20,3,9,30,11),
      (90,12,3,9,30,11),
      (90,12,3,9,30,11),
      (90,0,3,9,30,11),
      (90,12,3,9,30,11),
      (90,12,3,9,30,11)],
      0, 0, 12),
      141, 131, true, true, true, true, true, true)
  | .error _ => false

-- Return case 22: full execution return.
#guard match runActualReturn zeroConfig U256.zero 0 3 10 (some 8) false
    (GasMeter.mk 100 20 3 9 30 11) 0 19 with
  | .ok observed => observed ==
    (([(90,20,3,9,30,11),
      (90,12,3,9,30,11),
      (90,12,3,9,30,11),
      (90,0,3,9,30,11),
      (90,19,3,9,30,11),
      (90,19,3,9,30,11)],
      0, 0, 12),
      141, 131, true, true, true, true, true, true)
  | .error _ => false

-- Return case 23: over execution return.
#guard match runActualReturn zeroConfig U256.zero 0 3 10 (some 8) false
    (GasMeter.mk 100 20 3 9 30 11) 1 1361129467683753853853498429727072845847 with
  | .ok observed => observed ==
    (([(90,20,3,9,30,11),
      (90,12,3,9,30,11),
      (90,12,3,9,30,11),
      (90,0,3,9,30,11),
      (91,1361129467683753853853498429727072845847,3,9,30,11),
      (91,1361129467683753853853498429727072845847,3,9,30,11)],
      0, 0, 12),
      141, 132, false, true, true, true, true, true)
  | .error _ => false

-- Return case 24: zero execution return.
#guard match runActualReturn zeroConfig U256.zero 0 3 10 (some 8) true
    (GasMeter.mk 100 20 3 9 30 11) 0 0 with
  | .ok observed => observed ==
    (([(90,20,3,9,30,11),
      (90,12,3,9,30,11),
      (90,12,3,9,30,11),
      (90,0,3,9,30,11),
      (90,0,3,9,30,11),
      (98,0,3,9,22,11)],
      0, 0, 12),
      141, 131, true, true, true, true, true, true)
  | .error _ => false

-- Return case 25: half execution return.
#guard match runActualReturn zeroConfig U256.zero 0 3 10 (some 8) true
    (GasMeter.mk 100 20 3 9 30 11) 0 12 with
  | .ok observed => observed ==
    (([(90,20,3,9,30,11),
      (90,12,3,9,30,11),
      (90,12,3,9,30,11),
      (90,0,3,9,30,11),
      (90,12,3,9,30,11),
      (98,12,3,9,22,11)],
      0, 0, 12),
      141, 131, true, true, true, true, true, true)
  | .error _ => false

-- Return case 26: full execution return.
#guard match runActualReturn zeroConfig U256.zero 0 3 10 (some 8) true
    (GasMeter.mk 100 20 3 9 30 11) 0 19 with
  | .ok observed => observed ==
    (([(90,20,3,9,30,11),
      (90,12,3,9,30,11),
      (90,12,3,9,30,11),
      (90,0,3,9,30,11),
      (90,19,3,9,30,11),
      (98,19,3,9,22,11)],
      0, 0, 12),
      141, 131, true, true, true, true, true, true)
  | .error _ => false

-- Return case 27: over execution return.
#guard match runActualReturn zeroConfig U256.zero 0 3 10 (some 8) true
    (GasMeter.mk 100 20 3 9 30 11) 1 1361129467683753853853498429727072845851 with
  | .ok observed => observed ==
    (([(90,20,3,9,30,11),
      (90,12,3,9,30,11),
      (90,12,3,9,30,11),
      (90,0,3,9,30,11),
      (91,1361129467683753853853498429727072845851,3,9,30,11),
      (99,1361129467683753853853498429727072845851,3,9,22,11)],
      0, 0, 12),
      141, 132, false, true, true, true, true, true)
  | .error _ => false

-- Return case 28: zero execution return.
#guard match runActualReturn zeroConfig U256.one 100 3 4 none false
    (GasMeter.mk 10 1 8 5 2 4) 0 0 with
  | .ok observed => observed ==
    (([(6,1,8,5,2,4),
      (6,1,8,5,2,4),
      (0,1,8,5,2,4),
      (0,0,8,5,2,4),
      (0,0,8,5,2,4),
      (0,0,8,5,2,4)],
      6, 9, 1),
      16, 6, true, true, true, true, true, true)
  | .error _ => false

-- Return case 29: half execution return.
#guard match runActualReturn zeroConfig U256.one 100 3 4 none false
    (GasMeter.mk 10 1 8 5 2 4) 4 1 with
  | .ok observed => observed ==
    (([(6,1,8,5,2,4),
      (6,1,8,5,2,4),
      (0,1,8,5,2,4),
      (0,0,8,5,2,4),
      (4,1,8,5,2,4),
      (4,1,8,5,2,4)],
      6, 9, 1),
      16, 10, true, true, true, true, true, true)
  | .error _ => false

-- Return case 30: full execution return.
#guard match runActualReturn zeroConfig U256.one 100 3 4 none false
    (GasMeter.mk 10 1 8 5 2 4) 9 8 with
  | .ok observed => observed ==
    (([(6,1,8,5,2,4),
      (6,1,8,5,2,4),
      (0,1,8,5,2,4),
      (0,0,8,5,2,4),
      (9,8,8,5,2,4),
      (9,8,8,5,2,4)],
      6, 9, 1),
      16, 15, true, true, true, true, true, true)
  | .error _ => false

-- Return case 31: over execution return.
#guard match runActualReturn zeroConfig U256.one 100 3 4 none false
    (GasMeter.mk 10 1 8 5 2 4) 10 1361129467683753853853498429727072845855 with
  | .ok observed => observed ==
    (([(6,1,8,5,2,4),
      (6,1,8,5,2,4),
      (0,1,8,5,2,4),
      (0,0,8,5,2,4),
      (10,1361129467683753853853498429727072845855,8,5,2,4),
      (10,1361129467683753853853498429727072845855,8,5,2,4)],
      6, 9, 1),
      16, 16, false, true, true, false, true, false)
  | .error _ => false

-- Return case 32: zero execution return.
#guard match runActualReturn zeroConfig U256.one 100 3 3 none false
    (GasMeter.mk 10 1 8 5 2 4) 0 0 with
  | .ok observed => observed ==
    (([(7,1,8,5,2,4),
      (7,1,8,5,2,4),
      (0,1,8,5,2,4),
      (0,0,8,5,2,4),
      (0,0,8,5,2,4),
      (0,0,8,5,2,4)],
      7, 10, 1),
      16, 6, true, false, true, true, true, true)
  | .error _ => false

-- Return case 33: half execution return.
#guard match runActualReturn zeroConfig U256.one 100 3 3 none false
    (GasMeter.mk 10 1 8 5 2 4) 5 1 with
  | .ok observed => observed ==
    (([(7,1,8,5,2,4),
      (7,1,8,5,2,4),
      (0,1,8,5,2,4),
      (0,0,8,5,2,4),
      (5,1,8,5,2,4),
      (5,1,8,5,2,4)],
      7, 10, 1),
      16, 11, true, false, true, true, true, true)
  | .error _ => false

-- Return case 34: full execution return.
#guard match runActualReturn zeroConfig U256.one 100 3 3 none false
    (GasMeter.mk 10 1 8 5 2 4) 10 8 with
  | .ok observed => observed ==
    (([(7,1,8,5,2,4),
      (7,1,8,5,2,4),
      (0,1,8,5,2,4),
      (0,0,8,5,2,4),
      (10,8,8,5,2,4),
      (10,8,8,5,2,4)],
      7, 10, 1),
      16, 16, true, false, true, false, true, false)
  | .error _ => false

-- Return case 35: over execution return.
#guard match runActualReturn zeroConfig U256.one 100 3 3 none false
    (GasMeter.mk 10 1 8 5 2 4) 11 1361129467683753853853498429727072845859 with
  | .ok observed => observed ==
    (([(7,1,8,5,2,4),
      (7,1,8,5,2,4),
      (0,1,8,5,2,4),
      (0,0,8,5,2,4),
      (11,1361129467683753853853498429727072845859,8,5,2,4),
      (11,1361129467683753853853498429727072845859,8,5,2,4)],
      7, 10, 1),
      16, 17, false, false, true, false, false, false)
  | .error _ => false

-- Return case 36: zero execution return.
#guard match runActualReturn zeroConfig U256.zero 1000 77 0 none false
    (GasMeter.mk 64 9 1 (-3) 4 8) 0 0 with
  | .ok observed => observed ==
    (([(64,9,1,-3,4,8),
      (64,9,1,-3,4,8),
      (1,9,1,-3,4,8),
      (1,0,1,-3,4,8),
      (1,0,1,-3,4,8),
      (1,0,1,-3,4,8)],
      63, 63, 9),
      76, 13, true, false, true, true, true, true)
  | .error _ => false

-- Return case 37: half execution return.
#guard match runActualReturn zeroConfig U256.zero 1000 77 0 none false
    (GasMeter.mk 64 9 1 (-3) 4 8) 31 9 with
  | .ok observed => observed ==
    (([(64,9,1,-3,4,8),
      (64,9,1,-3,4,8),
      (1,9,1,-3,4,8),
      (1,0,1,-3,4,8),
      (32,9,1,-3,4,8),
      (32,9,1,-3,4,8)],
      63, 63, 9),
      76, 44, true, false, true, true, true, true)
  | .error _ => false

-- Return case 38: full execution return.
#guard match runActualReturn zeroConfig U256.zero 1000 77 0 none false
    (GasMeter.mk 64 9 1 (-3) 4 8) 63 16 with
  | .ok observed => observed ==
    (([(64,9,1,-3,4,8),
      (64,9,1,-3,4,8),
      (1,9,1,-3,4,8),
      (1,0,1,-3,4,8),
      (64,16,1,-3,4,8),
      (64,16,1,-3,4,8)],
      63, 63, 9),
      76, 76, true, false, true, false, true, false)
  | .error _ => false

-- Return case 39: over execution return.
#guard match runActualReturn zeroConfig U256.zero 1000 77 0 none false
    (GasMeter.mk 64 9 1 (-3) 4 8) 64 1361129467683753853853498429727072845863 with
  | .ok observed => observed ==
    (([(64,9,1,-3,4,8),
      (64,9,1,-3,4,8),
      (1,9,1,-3,4,8),
      (1,0,1,-3,4,8),
      (65,1361129467683753853853498429727072845863,1,-3,4,8),
      (65,1361129467683753853853498429727072845863,1,-3,4,8)],
      63, 63, 9),
      76, 77, false, false, true, false, false, false)
  | .error _ => false

-- Return case 40: zero execution return.
#guard match runActualReturn rawConfig U256.zero 100 99 8 none false
    (GasMeter.mk 10 0 99 (-8) 1 6) 0 0 with
  | .ok observed => observed ==
    (([(2,0,99,-8,1,6),
      (2,0,99,-8,1,6),
      (0,0,99,-8,1,6),
      (0,0,99,-8,1,6),
      (0,0,99,-8,1,6),
      (0,0,99,-8,1,6)],
      2, 9, 0),
      17, 7, true, true, true, true, true, true)
  | .error _ => false

-- Return case 41: half execution return.
#guard match runActualReturn rawConfig U256.zero 100 99 8 none false
    (GasMeter.mk 10 0 99 (-8) 1 6) 4 0 with
  | .ok observed => observed ==
    (([(2,0,99,-8,1,6),
      (2,0,99,-8,1,6),
      (0,0,99,-8,1,6),
      (0,0,99,-8,1,6),
      (4,0,99,-8,1,6),
      (4,0,99,-8,1,6)],
      2, 9, 0),
      17, 11, true, true, true, true, true, true)
  | .error _ => false

-- Return case 42: full execution return.
#guard match runActualReturn rawConfig U256.zero 100 99 8 none false
    (GasMeter.mk 10 0 99 (-8) 1 6) 9 7 with
  | .ok observed => observed ==
    (([(2,0,99,-8,1,6),
      (2,0,99,-8,1,6),
      (0,0,99,-8,1,6),
      (0,0,99,-8,1,6),
      (9,7,99,-8,1,6),
      (9,7,99,-8,1,6)],
      2, 9, 0),
      17, 16, true, true, true, true, true, true)
  | .error _ => false

-- Return case 43: over execution return.
#guard match runActualReturn rawConfig U256.zero 100 99 8 none false
    (GasMeter.mk 10 0 99 (-8) 1 6) 10 1361129467683753853853498429727072845867 with
  | .ok observed => observed ==
    (([(2,0,99,-8,1,6),
      (2,0,99,-8,1,6),
      (0,0,99,-8,1,6),
      (0,0,99,-8,1,6),
      (10,1361129467683753853853498429727072845867,99,-8,1,6),
      (10,1361129467683753853853498429727072845867,99,-8,1,6)],
      2, 9, 0),
      17, 17, false, true, true, false, true, false)
  | .error _ => false

-- Return case 44: zero execution return.
#guard match runActualReturn zeroConfig U256.one 100 3 4 (some 7) true
    (GasMeter.mk 10 1 8 5 2 4) 0 0 with
  | .ok observed => observed ==
    (([(6,1,8,5,2,4),
      (0,0,8,5,8,4),
      (0,0,8,5,8,4),
      (0,0,8,5,8,4),
      (0,0,8,5,8,4),
      (7,0,8,5,1,4)],
      0, 3, 0),
      16, 12, true, true, true, true, true, true)
  | .error _ => false

-- Return case 45: half execution return.
#guard match runActualReturn zeroConfig U256.one 100 3 4 (some 7) true
    (GasMeter.mk 10 1 8 5 2 4) 1 0 with
  | .ok observed => observed ==
    (([(6,1,8,5,2,4),
      (0,0,8,5,8,4),
      (0,0,8,5,8,4),
      (0,0,8,5,8,4),
      (1,0,8,5,8,4),
      (8,0,8,5,1,4)],
      0, 3, 0),
      16, 13, true, true, true, true, true, true)
  | .error _ => false

-- Return case 46: full execution return.
#guard match runActualReturn zeroConfig U256.one 100 3 4 (some 7) true
    (GasMeter.mk 10 1 8 5 2 4) 3 7 with
  | .ok observed => observed ==
    (([(6,1,8,5,2,4),
      (0,0,8,5,8,4),
      (0,0,8,5,8,4),
      (0,0,8,5,8,4),
      (3,7,8,5,8,4),
      (10,7,8,5,1,4)],
      0, 3, 0),
      16, 15, true, true, true, true, true, true)
  | .error _ => false

-- Return case 47: over execution return.
#guard match runActualReturn zeroConfig U256.one 100 3 4 (some 7) true
    (GasMeter.mk 10 1 8 5 2 4) 4 1361129467683753853853498429727072845871 with
  | .ok observed => observed ==
    (([(6,1,8,5,2,4),
      (0,0,8,5,8,4),
      (0,0,8,5,8,4),
      (0,0,8,5,8,4),
      (4,1361129467683753853853498429727072845871,8,5,8,4),
      (11,1361129467683753853853498429727072845871,8,5,1,4)],
      0, 3, 0),
      16, 16, false, true, true, false, true, false)
  | .error _ => false

-- Return case 48: unreached execution return.
#guard match runActualReturn zeroConfig U256.zero 100 0 11 none false
    (GasMeter.mk 10 1 8 5 2 4) 0 0 with
  | .error .outOfGas => true
  | _ => false

-- Return case 49: unreached execution return.
#guard match runActualReturn zeroConfig U256.zero 100 0 4 (some 8) true
    (GasMeter.mk 10 1 8 5 2 4) 0 0 with
  | .error .outOfGas => true
  | _ => false

-- Return case 50: zero execution return.
#guard match runActualReturn zeroConfig U256.zero 100 77 10 none false
    (GasMeter.mk 10 1 8 5 2 4) 0 0 with
  | .ok observed => observed ==
    (([(0,1,8,5,2,4),
      (0,1,8,5,2,4),
      (0,1,8,5,2,4),
      (0,0,8,5,2,4),
      (0,0,8,5,2,4),
      (0,0,8,5,2,4)],
      0, 0, 1),
      16, 6, true, true, true, true, true, true)
  | .error _ => false

-- Return case 51: half execution return.
#guard match runActualReturn zeroConfig U256.zero 100 77 10 none false
    (GasMeter.mk 10 1 8 5 2 4) 0 1 with
  | .ok observed => observed ==
    (([(0,1,8,5,2,4),
      (0,1,8,5,2,4),
      (0,1,8,5,2,4),
      (0,0,8,5,2,4),
      (0,1,8,5,2,4),
      (0,1,8,5,2,4)],
      0, 0, 1),
      16, 6, true, true, true, true, true, true)
  | .error _ => false

-- Return case 52: full execution return.
#guard match runActualReturn zeroConfig U256.zero 100 77 10 none false
    (GasMeter.mk 10 1 8 5 2 4) 0 8 with
  | .ok observed => observed ==
    (([(0,1,8,5,2,4),
      (0,1,8,5,2,4),
      (0,1,8,5,2,4),
      (0,0,8,5,2,4),
      (0,8,8,5,2,4),
      (0,8,8,5,2,4)],
      0, 0, 1),
      16, 6, true, true, true, true, true, true)
  | .error _ => false

-- Return case 53: over execution return.
#guard match runActualReturn zeroConfig U256.zero 100 77 10 none false
    (GasMeter.mk 10 1 8 5 2 4) 1 1361129467683753853853498429727072845877 with
  | .ok observed => observed ==
    (([(0,1,8,5,2,4),
      (0,1,8,5,2,4),
      (0,1,8,5,2,4),
      (0,0,8,5,2,4),
      (1,1361129467683753853853498429727072845877,8,5,2,4),
      (1,1361129467683753853853498429727072845877,8,5,2,4)],
      0, 0, 1),
      16, 7, false, true, true, true, true, true)
  | .error _ => false

-- Return case 54: zero execution return.
#guard match runActualReturn rawConfig U256.one 680564733841876926926749214863536422912 3 9
      (some 2722258935367507707706996859454145691649) true
    (GasMeter.mk
      1361129467683753853853498429727072845888
      2722258935367507707706996859454145691648
      10889035741470030830827987437816582766592
      (-1427247692705959881058285969449495136382746624)
      5444517870735015415413993718908291383296
      21778071482940061661655974875633165533184)
    0
    1427247692705959881058285969449495136382746624 with
  | .ok observed => observed ==
    (([
      (1361129467683753853853498429727072845879,
        2722258935367507707706996859454145691648,
        10889035741470030830827987437816582766592,
        -1427247692705959881058285969449495136382746624,
        5444517870735015415413993718908291383296,
        21778071482940061661655974875633165533184),
      (1361129467683753853853498429727072845878,
        0,
        10889035741470030830827987437816582766592,
        -1427247692705959881058285969449495136382746624,
        5444517870735015415413993718908291383297,
        21778071482940061661655974875633165533184),
      (680564733841876926926749214863536422966,
        0,
        10889035741470030830827987437816582766592,
        -1427247692705959881058285969449495136382746624,
        5444517870735015415413993718908291383297,
        21778071482940061661655974875633165533184),
      (680564733841876926926749214863536422966,
        0,
        10889035741470030830827987437816582766592,
        -1427247692705959881058285969449495136382746624,
        5444517870735015415413993718908291383297,
        21778071482940061661655974875633165533184),
      (680564733841876926926749214863536422966,
        1427247692705959881058285969449495136382746624,
        10889035741470030830827987437816582766592,
        -1427247692705959881058285969449495136382746624,
        5444517870735015415413993718908291383297,
        21778071482940061661655974875633165533184),
      (3402823669209384634633746074317682114615,
        1427247692705959881058285969449495136382746624,
        10889035741470030830827987437816582766592,
        -1427247692705959881058285969449495136382746624,
        2722258935367507707706996859454145691648,
        21778071482940061661655974875633165533184)
    ], 680564733841876926926749214863536422912,
      680564733841876926926749214863536422915, 0),
      28583718821358830930923467024268529762368,
      27903154087516954003996717809404993339447,
      true, true, true, true, true, true)
  | .error _ => false

-- Return case 55: half execution return.
#guard match runActualReturn rawConfig U256.one 680564733841876926926749214863536422912 3 9
      (some 2722258935367507707706996859454145691649) true
    (GasMeter.mk
      1361129467683753853853498429727072845888
      2722258935367507707706996859454145691648
      10889035741470030830827987437816582766592
      (-1427247692705959881058285969449495136382746624)
      5444517870735015415413993718908291383296
      21778071482940061661655974875633165533184)
    340282366920938463463374607431768211457
    0 with
  | .ok observed => observed ==
    (([
      (1361129467683753853853498429727072845879,
        2722258935367507707706996859454145691648,
        10889035741470030830827987437816582766592,
        -1427247692705959881058285969449495136382746624,
        5444517870735015415413993718908291383296,
        21778071482940061661655974875633165533184),
      (1361129467683753853853498429727072845878,
        0,
        10889035741470030830827987437816582766592,
        -1427247692705959881058285969449495136382746624,
        5444517870735015415413993718908291383297,
        21778071482940061661655974875633165533184),
      (680564733841876926926749214863536422966,
        0,
        10889035741470030830827987437816582766592,
        -1427247692705959881058285969449495136382746624,
        5444517870735015415413993718908291383297,
        21778071482940061661655974875633165533184),
      (680564733841876926926749214863536422966,
        0,
        10889035741470030830827987437816582766592,
        -1427247692705959881058285969449495136382746624,
        5444517870735015415413993718908291383297,
        21778071482940061661655974875633165533184),
      (1020847100762815390390123822295304634423,
        0,
        10889035741470030830827987437816582766592,
        -1427247692705959881058285969449495136382746624,
        5444517870735015415413993718908291383297,
        21778071482940061661655974875633165533184),
      (3743106036130323098097120681749450326072,
        0,
        10889035741470030830827987437816582766592,
        -1427247692705959881058285969449495136382746624,
        2722258935367507707706996859454145691648,
        21778071482940061661655974875633165533184)
    ], 680564733841876926926749214863536422912,
      680564733841876926926749214863536422915, 0),
      28583718821358830930923467024268529762368,
      28243436454437892467460092416836761550904,
      true, true, true, true, true, true)
  | .error _ => false

-- Return case 56: full execution return.
#guard match runActualReturn rawConfig U256.one 680564733841876926926749214863536422912 3 9
      (some 2722258935367507707706996859454145691649) true
    (GasMeter.mk
      1361129467683753853853498429727072845888
      2722258935367507707706996859454145691648
      10889035741470030830827987437816582766592
      (-1427247692705959881058285969449495136382746624)
      5444517870735015415413993718908291383296
      21778071482940061661655974875633165533184)
    680564733841876926926749214863536422915
    2854495385411919762116571938898990272765493248 with
  | .ok observed => observed ==
    (([
      (1361129467683753853853498429727072845879,
        2722258935367507707706996859454145691648,
        10889035741470030830827987437816582766592,
        -1427247692705959881058285969449495136382746624,
        5444517870735015415413993718908291383296,
        21778071482940061661655974875633165533184),
      (1361129467683753853853498429727072845878,
        0,
        10889035741470030830827987437816582766592,
        -1427247692705959881058285969449495136382746624,
        5444517870735015415413993718908291383297,
        21778071482940061661655974875633165533184),
      (680564733841876926926749214863536422966,
        0,
        10889035741470030830827987437816582766592,
        -1427247692705959881058285969449495136382746624,
        5444517870735015415413993718908291383297,
        21778071482940061661655974875633165533184),
      (680564733841876926926749214863536422966,
        0,
        10889035741470030830827987437816582766592,
        -1427247692705959881058285969449495136382746624,
        5444517870735015415413993718908291383297,
        21778071482940061661655974875633165533184),
      (1361129467683753853853498429727072845881,
        2854495385411919762116571938898990272765493248,
        10889035741470030830827987437816582766592,
        -1427247692705959881058285969449495136382746624,
        5444517870735015415413993718908291383297,
        21778071482940061661655974875633165533184),
      (4083388403051261561560495289181218537530,
        2854495385411919762116571938898990272765493248,
        10889035741470030830827987437816582766592,
        -1427247692705959881058285969449495136382746624,
        2722258935367507707706996859454145691648,
        21778071482940061661655974875633165533184)
    ], 680564733841876926926749214863536422912,
      680564733841876926926749214863536422915, 0),
      28583718821358830930923467024268529762368,
      28583718821358830930923467024268529762362,
      true, true, true, true, true, true)
  | .error _ => false

end STFSpec.Conformance.Vm.Core.CallPreflightGasControls
