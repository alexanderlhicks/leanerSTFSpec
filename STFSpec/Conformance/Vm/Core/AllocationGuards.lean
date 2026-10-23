/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Complete local-allocation controls

Library `EthConformance`. Private raw configurations and complete result pairs
retain 14 closed-source successes, six generic controls and three wide cases.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Vm.Core.AllocationGuards
open STFSpec.Vm.Core
open STFSpec.Base

-- Every existing policy field is supplied; these are raw fixtures, not fork values.
private def policy (cap : Nat) : VmConfig :=
  VmConfig.mk {
    base := 0
    veryLow := 0
    low := 0
    mid := 0
    high := 0
    warmAccess := 0
    coldAccountAccess := 0
    coldStorageAccess := 0
    storageWrite := 0
    callStipend := 0
    accountWrite := 0
    callValue := 0
    codeInitPerWord := 0
    createAccess := 0
    zero := 17
    memoryPerWord := 0
    fastStep := 0
    refundStorageClear := -11
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
    perBlob := U64.zero
    blobScheduleTarget := U64.zero
    blobTargetGasPerBlock := U64.zero
    blobBaseCost := 0
    blobScheduleMax := U64.zero
    blobMinGasPrice := 0
    blobBaseFeeUpdateFraction := 0
    blockAccessListItem := 0
    txBase := 0
    txValueCost := 0
    txDataTokenStandard := 0
    txDataTokenFloor := 0
    txAccessListAddress := 0
    txAccessListStorageKey := 0
    txMaxGasLimit := cap
    txMaxTotalGasLimit := 1
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
  } (StateGasCosts.mk 19 23 29 31) (VmLimits.mk 37 41 43)

private def allocateFixture (cap T I : Nat) (hT : I ≤ T) (hC : I ≤ cap) :
    EvmGasAllocation :=
  allocateEvmGas (policy cap) T I hT hC

private def observe (a : EvmGasAllocation) : Nat × Nat :=
  (a.executionGas, a.stateGasReservoir)

-- P01
#guard observe (allocateFixture 16777216 0 0 (by decide) (by decide)) ==
  (0, 0)
-- P02
#guard observe (allocateFixture 16777216 1 0 (by decide) (by decide)) ==
  (1, 0)
-- P03
#guard observe (allocateFixture 16777216 1 1 (by decide) (by decide)) ==
  (0, 0)
-- P04
#guard observe (allocateFixture 16777216 16777215 0 (by decide) (by decide)) ==
  (16777215, 0)
-- P05
#guard observe (allocateFixture 16777216 16777216 0 (by decide) (by decide)) ==
  (16777216, 0)
-- P06
#guard observe (allocateFixture 16777216 16777217 0 (by decide) (by decide)) ==
  (16777216, 1)
-- P07
#guard observe (allocateFixture 16777216 16777216 1 (by decide) (by decide)) ==
  (16777215, 0)
-- P08
#guard observe (allocateFixture 16777216 16777217 1 (by decide) (by decide)) ==
  (16777215, 1)
-- P09
#guard observe (allocateFixture 16777216 16777215 16777215 (by decide) (by decide)) ==
  (0, 0)
-- P10
#guard observe (allocateFixture 16777216 16777216 16777216 (by decide) (by decide)) ==
  (0, 0)
-- P11
#guard observe (allocateFixture 16777216 16777217 16777216 (by decide) (by decide)) ==
  (0, 1)
-- P12
#guard observe (allocateFixture 16777216 4294967295 16777216 (by decide) (by decide)) ==
  (0, 4278190079)
-- P13
#guard observe (allocateFixture 16777216 4294967296 0 (by decide) (by decide)) ==
  (16777216, 4278190080)
-- P14
#guard observe (allocateFixture 16777216 5 2 (by decide) (by decide)) ==
  (3, 0)
-- G01
#guard observe (allocateFixture 0 0 0 (by decide) (by decide)) ==
  (0, 0)
-- G02
#guard observe (allocateFixture 0 7 0 (by decide) (by decide)) ==
  (0, 7)
-- G03
#guard observe (allocateFixture 7 5 2 (by decide) (by decide)) ==
  (3, 0)
-- G04
#guard observe (allocateFixture 7 9 2 (by decide) (by decide)) ==
  (5, 2)
-- G05
#guard observe (allocateFixture 9 9 2 (by decide) (by decide)) ==
  (7, 0)
-- G06
#guard observe (allocateFixture 7 9 0 (by decide) (by decide)) ==
  (7, 2)
-- W01
#guard observe (allocateFixture (2 ^ 64 + 5) (2 ^ 64 + 9) 3 (by decide) (by decide)) ==
  (18446744073709551618, 4)
-- W02
#guard observe (allocateFixture (2 ^ 256 + 5) (2 ^ 256 + 9) 3 (by decide) (by decide)) ==
  (115792089237316195423570985008687907853269984665640564039457584007913129639938, 4)
-- W03
#guard observe (allocateFixture 7 (2 ^ 256 + 9) 2 (by decide) (by decide)) ==
  (5, 115792089237316195423570985008687907853269984665640564039457584007913129639938)

-- These use the actual G04 allocation to construct every initial meter field.
private def entry : GasMeter :=
  let a := allocateFixture 7 9 2 (by decide) (by decide)
  GasMeter.mk a.executionGas a.stateGasReservoir a.stateGasReservoir 0 0 0

private def observeMeter (m : GasMeter) : Nat × Nat × Nat × Int × Nat × Nat :=
  (m.gasLeft, m.stateGasLeft, m.stateGasBaseline, m.refundCounter,
   m.stateGasSpilled, m.stateGasCommittedSpill)

#guard observeMeter entry == (5, 2, 2, 0, 0, 0)
#guard match chargeGas entry 3 with
  | .ok m => observeMeter m == (2, 2, 2, 0, 0, 0)
  | .error _ => false
#guard match chargeGas entry 6 with
  | .error .outOfGas => true
  | _ => false
#guard txStateGasUsed entry entry.stateGasBaseline (Nat.le_refl _) == 0

end STFSpec.Conformance.Vm.Core.AllocationGuards
