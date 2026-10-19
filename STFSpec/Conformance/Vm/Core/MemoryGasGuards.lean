/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Vm.Core
/-! Complete frozen memory-pricing guards; no returned extent is allocated.
Library `EthConformance`. Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/7. -/
namespace STFSpec.Conformance.Vm.Core.MemoryGasGuards
open STFSpec.Vm.Core STFSpec.Base
private def rawA : VmConfig := {
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
    callStipend := 0
    accountWrite := 0
    callValue := 0
    codeInitPerWord := 0
    createAccess := 0
    zero := 0
    memoryPerWord := 0
    fastStep := 0
    refundStorageClear := (0)
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
    costPerStateByte := 0,
    bytesPerNewAccount := 0,
    bytesPerStorageSet := 0,
    bytesPerAuthBase := 0
  }
  limits := { stackDepthLimit := 0, maxCodeSize := 0, maxInitCodeSize := 0 }
}

private def rawB : VmConfig := {
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
    callStipend := 1
    accountWrite := 1
    callValue := 1
    codeInitPerWord := 1
    createAccess := 1
    zero := 1
    memoryPerWord := 1
    fastStep := 1
    refundStorageClear := (-7)
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

-- C01 pinned-source
#guard
  calculateMemoryGasCost
    ({ rawA with costs := { rawA.costs with memoryPerWord := 3, zero := 0 } })
    0 == 0

-- C02 pinned-source
#guard
  calculateMemoryGasCost
    ({ rawA with costs := { rawA.costs with memoryPerWord := 3, zero := 0 } })
    1 == 3

-- C03 pinned-source
#guard
  calculateMemoryGasCost
    ({ rawA with costs := { rawA.costs with memoryPerWord := 3, zero := 0 } })
    31 == 3

-- C04 pinned-source
#guard
  calculateMemoryGasCost
    ({ rawA with costs := { rawA.costs with memoryPerWord := 3, zero := 0 } })
    32 == 3

-- C05 pinned-source
#guard
  calculateMemoryGasCost
    ({ rawA with costs := { rawA.costs with memoryPerWord := 3, zero := 0 } })
    33 == 6

-- C06 pinned-source
#guard
  calculateMemoryGasCost
    ({ rawA with costs := { rawA.costs with memoryPerWord := 3, zero := 0 } })
    64 == 6

-- C07 pinned-source
#guard
  calculateMemoryGasCost
    ({ rawA with costs := { rawA.costs with memoryPerWord := 3, zero := 0 } })
    704 == 66

-- C08 pinned-source
#guard
  calculateMemoryGasCost
    ({ rawA with costs := { rawA.costs with memoryPerWord := 3, zero := 0 } })
    705 == 70

-- C09 generic-Lean-only
#guard
  calculateMemoryGasCost
    ({ rawA with costs := { rawA.costs with memoryPerWord := 0, zero := 0 } })
    32 == 0

-- C10 generic-Lean-only
#guard
  calculateMemoryGasCost
    ({ rawA with costs := { rawA.costs with memoryPerWord := 0, zero := 0 } })
    704 == 0

-- C11 generic-Lean-only
#guard
  calculateMemoryGasCost
    ({ rawA with costs := { rawA.costs with memoryPerWord := 0, zero := 0 } })
    705 == 1

-- C12 generic-Lean-only
#guard
  calculateMemoryGasCost
    ({ rawA with costs := { rawA.costs with memoryPerWord := 7, zero := 0 } })
    64 == 14

-- P01 pinned-source
#guard
  let m := Memory.empty;
  let r := calculateGasExtendMemory
    ({ rawA with costs := { rawA.costs with memoryPerWord := 3, zero := 0 } })
    m [];
  r.cost == 0 &&
    r.expandBy == 0 &&
    m.toBytes == []

-- P02 pinned-source
#guard
  let m := Memory.empty;
  let r := calculateGasExtendMemory
    ({ rawA with costs := { rawA.costs with memoryPerWord := 3, zero := 0 } })
    m [(U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935,
      U256.ofNat 0)];
  r.cost == 0 &&
    r.expandBy == 0 &&
    m.toBytes == []

-- P03 pinned-source
#guard
  let m := (Memory.empty.expand 32 (by decide));
  let r := calculateGasExtendMemory
    ({ rawA with costs := { rawA.costs with memoryPerWord := 3, zero := 0 } })
    m [(U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935,
      U256.ofNat 0)];
  r.cost == 0 &&
    r.expandBy == 0 &&
    m.toBytes == [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0]

-- P04 pinned-source
#guard
  let m := Memory.empty;
  let r := calculateGasExtendMemory
    ({ rawA with costs := { rawA.costs with memoryPerWord := 3, zero := 0 } })
    m [(U256.ofNat 0,
      U256.ofNat 1)];
  r.cost == 3 &&
    r.expandBy == 32 &&
    m.toBytes == []

-- P05 pinned-source
#guard
  let m := Memory.empty;
  let r := calculateGasExtendMemory
    ({ rawA with costs := { rawA.costs with memoryPerWord := 3, zero := 0 } })
    m [(U256.ofNat 31,
      U256.ofNat 1)];
  r.cost == 3 &&
    r.expandBy == 32 &&
    m.toBytes == []

-- P06 pinned-source
#guard
  let m := Memory.empty;
  let r := calculateGasExtendMemory
    ({ rawA with costs := { rawA.costs with memoryPerWord := 3, zero := 0 } })
    m [(U256.ofNat 31,
      U256.ofNat 2)];
  r.cost == 6 &&
    r.expandBy == 64 &&
    m.toBytes == []

-- P07 pinned-source
#guard
  let m := (Memory.empty.expand 32 (by decide));
  let r := calculateGasExtendMemory
    ({ rawA with costs := { rawA.costs with memoryPerWord := 3, zero := 0 } })
    m [(U256.ofNat 31,
      U256.ofNat 1)];
  r.cost == 0 &&
    r.expandBy == 0 &&
    m.toBytes == [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0]

-- P08 pinned-source
#guard
  let m := (Memory.empty.expand 32 (by decide));
  let r := calculateGasExtendMemory
    ({ rawA with costs := { rawA.costs with memoryPerWord := 3, zero := 0 } })
    m [(U256.ofNat 31,
      U256.ofNat 2)];
  r.cost == 3 &&
    r.expandBy == 32 &&
    m.toBytes == [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0]

-- P09 pinned-source
#guard
  let m := (Memory.empty.expand 64 (by decide));
  let r := calculateGasExtendMemory
    ({ rawA with costs := { rawA.costs with memoryPerWord := 3, zero := 0 } })
    m [(U256.ofNat 32,
      U256.ofNat 33)];
  r.cost == 3 &&
    r.expandBy == 32 &&
    m.toBytes == [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0]

-- P10 pinned-source
#guard
  let m := Memory.empty;
  let r := calculateGasExtendMemory
    ({ rawA with costs := { rawA.costs with memoryPerWord := 3, zero := 0 } })
    m [(U256.ofNat 0,
      U256.ofNat 32),
      (U256.ofNat 0,
      U256.ofNat 64)];
  r.cost == 6 &&
    r.expandBy == 64 &&
    m.toBytes == []

-- P11 pinned-source
#guard
  let m := Memory.empty;
  let r := calculateGasExtendMemory
    ({ rawA with costs := { rawA.costs with memoryPerWord := 3, zero := 0 } })
    m [(U256.ofNat 0,
      U256.ofNat 64),
      (U256.ofNat 0,
      U256.ofNat 32)];
  r.cost == 6 &&
    r.expandBy == 64 &&
    m.toBytes == []

-- P12 pinned-source
#guard
  let m := Memory.empty;
  let r := calculateGasExtendMemory
    ({ rawA with costs := { rawA.costs with memoryPerWord := 3, zero := 0 } })
    m [(U256.ofNat 0,
      U256.ofNat 64),
      (U256.ofNat 0,
      U256.ofNat 64),
      (U256.ofNat 1,
      U256.ofNat 1),
      (U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935,
      U256.ofNat 0)];
  r.cost == 6 &&
    r.expandBy == 64 &&
    m.toBytes == []

-- P13 pinned-source
#guard
  let m := ((Memory.empty.expand 32 (by decide)).write 0 (Bytes.ofList [0,
    128,
    0,
    255,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0]) (by decide));
  let r := calculateGasExtendMemory
    ({ rawA with costs := { rawA.costs with memoryPerWord := 3, zero := 0 } })
    m [(U256.ofNat 0,
      U256.ofNat 32),
      (U256.ofNat 7,
      U256.ofNat 1)];
  r.cost == 0 &&
    r.expandBy == 0 &&
    m.toBytes == [0, 128, 0, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0]

-- P14 pinned-source
#guard
  let m := Memory.empty;
  let r := calculateGasExtendMemory
    ({ rawA with costs := { rawA.costs with memoryPerWord := 3, zero := 0 } })
    m [(U256.ofNat 0,
      U256.ofNat 704),
      (U256.ofNat 704,
      U256.ofNat 1)];
  r.cost == 70 &&
    r.expandBy == 736 &&
    m.toBytes == []

-- P15 pinned-source
#guard
  let m := Memory.empty;
  let r := calculateGasExtendMemory
    ({ rawA with costs := { rawA.costs with memoryPerWord := 3, zero := 0 } })
    m [(U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935,
      U256.ofNat 1)];
  r.cost == 25573364124188608359478044506465618376692515984711443667838213813251045295267028326023940917255906072305793580990624117163312695463878133970985025536 &&
    r.expandBy == 115792089237316195423570985008687907853269984665640564039457584007913129639936 &&
    m.toBytes == []

-- P16 pinned-source
#guard
  let m := Memory.empty;
  let r := calculateGasExtendMemory
    ({ rawA with costs := { rawA.costs with memoryPerWord := 3, zero := 0 } })
    m [(U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935,
      U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)];
  r.cost == 102293456496754433437912178025862473506770063938845774671352855253004181159357096572098977027104064600094191601474374343845645024457215534400228294656 &&
    r.expandBy == 231584178474632390847141970017375815706539969331281128078915168015826259279872 &&
    m.toBytes == []

-- G01 generic-Lean-only
#guard
  let m := Memory.empty;
  let r := calculateGasExtendMemory
    ({ rawA with costs := { rawA.costs with memoryPerWord := 3, zero := 7 } })
    m [];
  r.cost == 7 &&
    r.expandBy == 0 &&
    m.toBytes == []

-- G02 generic-Lean-only
#guard
  let m := Memory.empty;
  let r := calculateGasExtendMemory
    ({ rawA with costs := { rawA.costs with memoryPerWord := 3, zero := 7 } })
    m [(U256.ofNat 0,
      U256.ofNat 32)];
  r.cost == 10 &&
    r.expandBy == 32 &&
    m.toBytes == []

-- G03 generic-Lean-only
#guard
  let m := Memory.empty;
  let r := calculateGasExtendMemory
    ({ rawA with costs := { rawA.costs with memoryPerWord := 3, zero := 7 } })
    m [(U256.ofNat 0,
      U256.ofNat 32),
      (U256.ofNat 0,
      U256.ofNat 64)];
  r.cost == 13 &&
    r.expandBy == 64 &&
    m.toBytes == []

-- G04 generic-Lean-only
#guard
  let m := (Memory.empty.expand 32 (by decide));
  let r := calculateGasExtendMemory
    ({ rawA with costs := { rawA.costs with memoryPerWord := 3, zero := 7 } })
    m [(U256.ofNat 0,
      U256.ofNat 64)];
  r.cost == 10 &&
    r.expandBy == 32 &&
    m.toBytes == [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0]

-- G05 generic-Lean-only
#guard
  let m := Memory.empty;
  let r := calculateGasExtendMemory
    ({ rawA with costs := { rawA.costs with memoryPerWord := 0, zero := 0 } })
    m [(U256.ofNat 0,
      U256.ofNat 32)];
  r.cost == 0 &&
    r.expandBy == 32 &&
    m.toBytes == []

-- G06 generic-Lean-only
#guard
  let m := Memory.empty;
  let r := calculateGasExtendMemory
    ({ rawA with costs := { rawA.costs with memoryPerWord := 0, zero := 0 } })
    m [(U256.ofNat 0,
      U256.ofNat 705)];
  r.cost == 1 &&
    r.expandBy == 736 &&
    m.toBytes == []

-- G07 generic-Lean-only
#guard
  let m := Memory.empty;
  let r := calculateGasExtendMemory
    ({ rawA with costs := { rawA.costs with memoryPerWord := 7, zero := 0 } })
    m [(U256.ofNat 0,
      U256.ofNat 64)];
  r.cost == 14 &&
    r.expandBy == 64 &&
    m.toBytes == []

-- G08 generic-Lean-only
#guard
  let m := Memory.empty;
  let r := calculateGasExtendMemory
    ({ rawA with costs := { rawA.costs with memoryPerWord := 0, zero := 7 } })
    m [(U256.ofNat 0,
      U256.ofNat 32)];
  r.cost == 7 &&
    r.expandBy == 32 &&
    m.toBytes == []

-- E01 generic-Lean-only
#guard
  calculateMemoryGasCost
    ({ rawA with costs := { rawA.costs with memoryPerWord := 0, zero := 0 } })
    736 == 1

-- E02 generic-Lean-only
#guard
  calculateMemoryGasCost
    ({ rawA with costs := { rawA.costs with memoryPerWord := 0, zero := 0 } })
    768 == 1

-- E03 generic-Lean-only
#guard
  let m := (Memory.empty.expand 736 (by decide));
  let r := calculateGasExtendMemory
    ({ rawA with costs := { rawA.costs with memoryPerWord := 0, zero := 0 } })
    m [(U256.ofNat 0,
      U256.ofNat 768)];
  r.cost == 0 &&
    r.expandBy == 32 &&
    m.toBytes == [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

-- E04 generic-Lean-only
#guard
  let m := (Memory.empty.expand 736 (by decide));
  let r := calculateGasExtendMemory
    ({ rawA with costs := { rawA.costs with memoryPerWord := 0, zero := 7 } })
    m [(U256.ofNat 0,
      U256.ofNat 768)];
  r.cost == 7 &&
    r.expandBy == 32 &&
    m.toBytes == [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

-- E05 generic-Lean-only
#guard
  calculateMemoryGasCost
    ({ rawB with costs := { rawB.costs with memoryPerWord := 3, zero := 99 } })
    64 == 6

-- E06 generic-Lean-only
#guard
  let m := Memory.empty;
  let r := calculateGasExtendMemory
    ({ rawB with costs := { rawB.costs with memoryPerWord := 3, zero := 7 } })
    m [(U256.ofNat 0,
      U256.ofNat 32),
      (U256.ofNat 0,
      U256.ofNat 64)];
  r.cost == 13 &&
    r.expandBy == 64 &&
    m.toBytes == []

end STFSpec.Conformance.Vm.Core.MemoryGasGuards
