/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-! Complete hand-frozen call/init results and actual six-field charge witnesses.
Library `EthConformance`. No fixture is a production default or coherent fork factory.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7. -/

namespace STFSpec.Conformance.Vm.Core.CallGasGuards
open STFSpec.Vm.Core STFSpec.Base

private def raw_pinned : VmConfig := {
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
    callStipend := 2300
    accountWrite := 0
    callValue := 0
    codeInitPerWord := 2
    createAccess := 0
    zero := 0
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

private def raw_generic : VmConfig := {
  costs := {
    base := 1
    veryLow := 1
    low := 1
    mid := 1
    high := 1
    warmAccess := 1
    coldAccountAccess := 1
    coldStorageAccess := 1
    storageWrite := 1
    callStipend := 19
    accountWrite := 1
    callValue := 1
    codeInitPerWord := 5
    createAccess := 1
    zero := 7
    memoryPerWord := 1
    fastStep := 1
    refundStorageClear := (-11)
    precompileEcrecover := 1
    precompileP256Verify := 1
    precompileSha256Base := 1
    precompileSha256PerWord := 1
    precompileRipemd160Base := 1
    precompileRipemd160PerWord := 1
    precompileIdentityBase := 1
    precompileIdentityPerWord := 1
    precompileBlake2FPerRound := 1
    precompilePointEvaluation := 1
    precompileBlsG1Add := 1
    precompileBlsG1Mul := 1
    precompileBlsG1Map := 1
    precompileBlsG2Add := 1
    precompileBlsG2Mul := 1
    precompileBlsG2Map := 1
    precompileEcAdd := 1
    precompileEcMul := 1
    precompileEcPairingBase := 1
    precompileEcPairingPerPoint := 1
    perBlob := U64.ofNat 1
    blobScheduleTarget := U64.ofNat 1
    blobTargetGasPerBlock := U64.ofNat 1
    blobBaseCost := 1
    blobScheduleMax := U64.ofNat 1
    blobMinGasPrice := 1
    blobBaseFeeUpdateFraction := 1
    blockAccessListItem := 1
    txBase := 1
    txValueCost := 1
    txDataTokenStandard := 1
    txDataTokenFloor := 1
    txAccessListAddress := 1
    txAccessListStorageKey := 1
    txMaxGasLimit := 1
    txMaxTotalGasLimit := 1
    authTupleBytes := 1
    executionPerAuthBaseCost := 1
    limitAdjustmentFactor := 1
    limitMinimum := 1
    opcodeAdd := 1
    opcodeSub := 1
    opcodeMul := 1
    opcodeDiv := 1
    opcodeSdiv := 1
    opcodeMod := 1
    opcodeSmod := 1
    opcodeAddmod := 1
    opcodeMulmod := 1
    opcodeSignextend := 1
    opcodeLt := 1
    opcodeGt := 1
    opcodeSlt := 1
    opcodeSgt := 1
    opcodeEq := 1
    opcodeIsZero := 1
    opcodeAnd := 1
    opcodeOr := 1
    opcodeXor := 1
    opcodeNot := 1
    opcodeByte := 1
    opcodeShl := 1
    opcodeShr := 1
    opcodeSar := 1
    opcodeClz := 1
    opcodeJump := 1
    opcodeJumpi := 1
    opcodeJumpDest := 1
    opcodeCallDataLoad := 1
    opcodeBlockHash := 1
    opcodeCoinbase := 1
    opcodePop := 1
    opcodeMsize := 1
    opcodePc := 1
    opcodeGas := 1
    opcodeAddress := 1
    opcodeOrigin := 1
    opcodeCaller := 1
    opcodeCallValue := 1
    opcodeCallDataSize := 1
    opcodeCodeSize := 1
    opcodeGasPrice := 1
    opcodeTimestamp := 1
    opcodeNumber := 1
    opcodeGasLimit := 1
    opcodePrevRandao := 1
    opcodeReturnDataSize := 1
    opcodeChainId := 1
    opcodeSelfBalance := 1
    opcodeBaseFee := 1
    opcodeBlobBaseFee := 1
    opcodeSlotNum := 1
    opcodeBlobHash := 1
    opcodePush := 1
    opcodePush0 := 1
    opcodeDup := 1
    opcodeSwap := 1
    opcodeDupn := 1
    opcodeSwapn := 1
    opcodeExchange := 1
    opcodeTload := 1
    opcodeTstore := 1
    opcodeReturnDataCopyBase := 1
    opcodeReturnDataCopyPerWord := 1
    opcodeCallDataCopyBase := 1
    opcodeCodeCopyBase := 1
    opcodeMcopyBase := 1
    opcodeMloadBase := 1
    opcodeMstoreBase := 1
    opcodeMstore8Base := 1
    opcodeCopyPerWord := 1
    opcodeExpBase := 1
    opcodeExpPerByte := 1
    opcodeKeccak256Base := 1
    opcodeKeccak256PerWord := 1
    opcodeLogBase := 1
    opcodeLogDataPerByte := 1
    opcodeLogTopic := 1
    opcodeSelfDestructBase := 1
    blsPairingBase := 1
    blsPairingPerPair := 1
    blsG1KDiscount := #[1, 0, 2]
    blsG2KDiscount := #[1, 0, 2]
    blsG1MaxDiscount := 1
    blsG2MaxDiscount := 1
    blsMultiplier := 1
  }
  stateCosts := {
    costPerStateByte := 2,
    bytesPerNewAccount := 3,
    bytesPerStorageSet := 4,
    bytesPerAuthBase := 5
  }
  limits := { stackDepthLimit := 7, maxCodeSize := 8, maxInitCodeSize := 9 }
}

private def raw_zeroWord : VmConfig := {
  costs := {
    base := 1
    veryLow := 1
    low := 1
    mid := 1
    high := 1
    warmAccess := 1
    coldAccountAccess := 1
    coldStorageAccess := 1
    storageWrite := 1
    callStipend := 19
    accountWrite := 1
    callValue := 1
    codeInitPerWord := 0
    createAccess := 1
    zero := 7
    memoryPerWord := 1
    fastStep := 1
    refundStorageClear := (-11)
    precompileEcrecover := 1
    precompileP256Verify := 1
    precompileSha256Base := 1
    precompileSha256PerWord := 1
    precompileRipemd160Base := 1
    precompileRipemd160PerWord := 1
    precompileIdentityBase := 1
    precompileIdentityPerWord := 1
    precompileBlake2FPerRound := 1
    precompilePointEvaluation := 1
    precompileBlsG1Add := 1
    precompileBlsG1Mul := 1
    precompileBlsG1Map := 1
    precompileBlsG2Add := 1
    precompileBlsG2Mul := 1
    precompileBlsG2Map := 1
    precompileEcAdd := 1
    precompileEcMul := 1
    precompileEcPairingBase := 1
    precompileEcPairingPerPoint := 1
    perBlob := U64.ofNat 1
    blobScheduleTarget := U64.ofNat 1
    blobTargetGasPerBlock := U64.ofNat 1
    blobBaseCost := 1
    blobScheduleMax := U64.ofNat 1
    blobMinGasPrice := 1
    blobBaseFeeUpdateFraction := 1
    blockAccessListItem := 1
    txBase := 1
    txValueCost := 1
    txDataTokenStandard := 1
    txDataTokenFloor := 1
    txAccessListAddress := 1
    txAccessListStorageKey := 1
    txMaxGasLimit := 1
    txMaxTotalGasLimit := 1
    authTupleBytes := 1
    executionPerAuthBaseCost := 1
    limitAdjustmentFactor := 1
    limitMinimum := 1
    opcodeAdd := 1
    opcodeSub := 1
    opcodeMul := 1
    opcodeDiv := 1
    opcodeSdiv := 1
    opcodeMod := 1
    opcodeSmod := 1
    opcodeAddmod := 1
    opcodeMulmod := 1
    opcodeSignextend := 1
    opcodeLt := 1
    opcodeGt := 1
    opcodeSlt := 1
    opcodeSgt := 1
    opcodeEq := 1
    opcodeIsZero := 1
    opcodeAnd := 1
    opcodeOr := 1
    opcodeXor := 1
    opcodeNot := 1
    opcodeByte := 1
    opcodeShl := 1
    opcodeShr := 1
    opcodeSar := 1
    opcodeClz := 1
    opcodeJump := 1
    opcodeJumpi := 1
    opcodeJumpDest := 1
    opcodeCallDataLoad := 1
    opcodeBlockHash := 1
    opcodeCoinbase := 1
    opcodePop := 1
    opcodeMsize := 1
    opcodePc := 1
    opcodeGas := 1
    opcodeAddress := 1
    opcodeOrigin := 1
    opcodeCaller := 1
    opcodeCallValue := 1
    opcodeCallDataSize := 1
    opcodeCodeSize := 1
    opcodeGasPrice := 1
    opcodeTimestamp := 1
    opcodeNumber := 1
    opcodeGasLimit := 1
    opcodePrevRandao := 1
    opcodeReturnDataSize := 1
    opcodeChainId := 1
    opcodeSelfBalance := 1
    opcodeBaseFee := 1
    opcodeBlobBaseFee := 1
    opcodeSlotNum := 1
    opcodeBlobHash := 1
    opcodePush := 1
    opcodePush0 := 1
    opcodeDup := 1
    opcodeSwap := 1
    opcodeDupn := 1
    opcodeSwapn := 1
    opcodeExchange := 1
    opcodeTload := 1
    opcodeTstore := 1
    opcodeReturnDataCopyBase := 1
    opcodeReturnDataCopyPerWord := 1
    opcodeCallDataCopyBase := 1
    opcodeCodeCopyBase := 1
    opcodeMcopyBase := 1
    opcodeMloadBase := 1
    opcodeMstoreBase := 1
    opcodeMstore8Base := 1
    opcodeCopyPerWord := 1
    opcodeExpBase := 1
    opcodeExpPerByte := 1
    opcodeKeccak256Base := 1
    opcodeKeccak256PerWord := 1
    opcodeLogBase := 1
    opcodeLogDataPerByte := 1
    opcodeLogTopic := 1
    opcodeSelfDestructBase := 1
    blsPairingBase := 1
    blsPairingPerPair := 1
    blsG1KDiscount := #[1, 0, 2]
    blsG2KDiscount := #[1, 0, 2]
    blsG1MaxDiscount := 1
    blsG2MaxDiscount := 1
    blsMultiplier := 1
  }
  stateCosts := {
    costPerStateByte := 2,
    bytesPerNewAccount := 3,
    bytesPerStorageSet := 4,
    bytesPerAuthBase := 5
  }
  limits := { stackDepthLimit := 7, maxCodeSize := 8, maxInitCodeSize := 9 }
}

-- C01
#guard
  (let r := calculateMessageCallGas raw_pinned
    (U256.ofNat 0) 0 0 0 0;
    (r.cost, r.subCall)) == (0, 0)

-- C02
#guard
  (let r := calculateMessageCallGas raw_pinned
    (U256.ofNat 1) 0 0 0 0;
    (r.cost, r.subCall)) == (0, 2300)

-- C03
#guard
  (let r := calculateMessageCallGas raw_pinned
    (U256.ofNat 1) 100 63 0 0;
    (r.cost, r.subCall)) == (63, 2363)

-- C04
#guard
  (let r := calculateMessageCallGas raw_pinned
    (U256.ofNat 1) 100 64 0 0;
    (r.cost, r.subCall)) == (63, 2363)

-- C05
#guard
  (let r := calculateMessageCallGas raw_pinned
    (U256.ofNat 1) 100 65 0 0;
    (r.cost, r.subCall)) == (64, 2364)

-- C06
#guard
  (let r := calculateMessageCallGas raw_pinned
    (U256.ofNat 0) 5 100 0 0 7;
    (r.cost, r.subCall)) == (5, 5)

-- C07
#guard
  (let r := calculateMessageCallGas raw_pinned
    (U256.ofNat 1) 5 100 0 0 7;
    (r.cost, r.subCall)) == (5, 12)

-- C08
#guard
  (let r := calculateMessageCallGas raw_pinned
    (U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)
    5 100 0 0 0;
    (r.cost, r.subCall)) == (5, 5)

-- C09
#guard
  (let r := calculateMessageCallGas raw_pinned
    (U256.ofNat 1) 10 9 4 6;
    (r.cost, r.subCall)) == (16, 2310)

-- C10
#guard
  (let r := calculateMessageCallGas raw_pinned
    (U256.ofNat 1) 10 10 4 6;
    (r.cost, r.subCall)) == (6, 2300)

-- C11
#guard
  (let r := calculateMessageCallGas raw_pinned
    (U256.ofNat 0) 100 74 4 6;
    (r.cost, r.subCall)) == (69, 63)

-- C12
#guard
  (let r := calculateMessageCallGas raw_pinned
    (U256.ofNat 1) 100 75 4 6 7;
    (r.cost, r.subCall)) == (70, 71)

-- C13
#guard
  (let r := calculateMessageCallGas raw_pinned
    (U256.ofNat 0) 0 4 5 0;
    (r.cost, r.subCall)) == (0, 0)

-- C14
#guard
  (let r := calculateMessageCallGas raw_pinned
    (U256.ofNat 0) 100 63 64 0;
    (r.cost, r.subCall)) == (100, 100)

-- C15
#guard
  (let r := calculateMessageCallGas raw_pinned
    (U256.ofNat 0) 100 64 64 0;
    (r.cost, r.subCall)) == (0, 0)

-- C16
#guard
  (let r := calculateMessageCallGas raw_pinned
    (U256.ofNat 1) 18446744073709551616 18446744073709551616 0 0;
    (r.cost, r.subCall)) == (18158513697557839872, 18158513697557842172)

-- I01
#guard initCodeCost raw_pinned 0 == 0

-- I02
#guard initCodeCost raw_pinned 1 == 2

-- I03
#guard initCodeCost raw_pinned 31 == 2

-- I04
#guard initCodeCost raw_pinned 32 == 2

-- I05
#guard initCodeCost raw_pinned 33 == 4

-- I06
#guard initCodeCost raw_pinned 63 == 4

-- I07
#guard initCodeCost raw_pinned 64 == 4

-- I08
#guard initCodeCost raw_pinned 65 == 6

-- I09
#guard initCodeCost raw_pinned 18446744073709551617 == 1152921504606846978

-- G01
#guard
  (let r := calculateMessageCallGas raw_generic
    (U256.ofNat 0) 0 0 0 0;
    (r.cost, r.subCall)) == (0, 7)

-- G02
#guard
  (let r := calculateMessageCallGas raw_generic
    (U256.ofNat 1) 0 0 0 0;
    (r.cost, r.subCall)) == (0, 19)

-- G03
#guard
  (let r := calculateMessageCallGas raw_generic
    (U256.ofNat 0) 10 64 0 0 0;
    (r.cost, r.subCall)) == (10, 17)

-- G04
#guard
  (let r := calculateMessageCallGas raw_generic
    (U256.ofNat 1) 10 64 0 0 0;
    (r.cost, r.subCall)) == (10, 10)

-- G05
#guard initCodeCost raw_zeroWord 33 == 0

-- G06
#guard initCodeCost raw_generic 1 == 5

-- G07
#guard initCodeCost raw_generic 33 == 10

private def meterFields (m : GasMeter) : Nat × Nat × Nat × Int × Nat × Nat :=
  (m.gasLeft, m.stateGasLeft, m.stateGasBaseline, m.refundCounter,
    m.stateGasSpilled, m.stateGasCommittedSpill)

-- C09: whole-shortage
#guard (match chargeGas ({
    gasLeft := (9),
    stateGasLeft := (17),
    stateGasBaseline := (3),
    refundCounter := (-9),
    stateGasSpilled := (5),
    stateGasCommittedSpill := (7) }) ((calculateMessageCallGas raw_pinned (U256.ofNat 1) 10 9 4
    6).cost + 4) with
  | .error .outOfGas => true
  | _ => false)

-- C10: whole-equality
#guard (match chargeGas ({
    gasLeft := (10),
    stateGasLeft := (17),
    stateGasBaseline := (3),
    refundCounter := (-9),
    stateGasSpilled := (5),
    stateGasCommittedSpill := (7) }) ((calculateMessageCallGas raw_pinned (U256.ofNat 1) 10 10 4
    6).cost + 4) with
  | .ok post => meterFields post == (0, 17, 3, -9, 5, 7)
  | .error _ => false)

-- C13: memory-only-shortage
#guard (match chargeGas ({
    gasLeft := (4),
    stateGasLeft := (17),
    stateGasBaseline := (3),
    refundCounter := (-9),
    stateGasSpilled := (5),
    stateGasCommittedSpill := (7) }) ((calculateMessageCallGas raw_pinned (U256.ofNat 0) 0 4 5
    0).cost + 5) with
  | .error .outOfGas => true
  | _ => false)

-- I05: init-equality
#guard (match chargeGas ({
    gasLeft := (4),
    stateGasLeft := (17),
    stateGasBaseline := (3),
    refundCounter := (-9),
    stateGasSpilled := (5),
    stateGasCommittedSpill := (7) }) (initCodeCost raw_pinned 33) with
  | .ok post => meterFields post == (0, 17, 3, -9, 5, 7)
  | .error _ => false)

-- I05: init-shortage
#guard (match chargeGas ({
    gasLeft := (3),
    stateGasLeft := (17),
    stateGasBaseline := (3),
    refundCounter := (-9),
    stateGasSpilled := (5),
    stateGasCommittedSpill := (7) }) (initCodeCost raw_pinned 33) with
  | .error .outOfGas => true
  | _ => false)

-- G05: zero-price-identity
#guard (match chargeGas ({
    gasLeft := (0),
    stateGasLeft := (17),
    stateGasBaseline := (3),
    refundCounter := (-9),
    stateGasSpilled := (5),
    stateGasCommittedSpill := (7) }) (initCodeCost raw_zeroWord 33) with
  | .ok post => meterFields post == (0, 17, 3, -9, 5, 7)
  | .error _ => false)

end STFSpec.Conformance.Vm.Core.CallGasGuards
