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

end STFSpec.Conformance.Vm.Core.CallPreflightGasControls
