/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-! Exactly 36 complete allocation controls. All fixtures are private raw data.
Library `EthConformance`; guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7. -/

namespace STFSpec.Conformance.Vm.Core.TransactionGasAllocationGuards
open STFSpec.Vm.Core STFSpec.Base

private def cfgA (cap : Nat) : VmConfig := {
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
    refundStorageClear := 0
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
    txMaxGasLimit := cap
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
  stateCosts := StateGasCosts.mk 0 0 0 0
  limits := VmLimits.mk 0 0 0
}

private def cfgB (cap : Nat) : VmConfig := {
  costs := { (cfgA cap).costs with
    zero := 19
    txMaxTotalGasLimit := 1
    opcodeAdd := 23
    refundStorageClear := (-31)
    blsG1KDiscount := #[0, 2, 2] }
  stateCosts := StateGasCosts.mk 37 0 41 43
  limits := VmLimits.mk 47 53 59
}

private def pair (a : EvmGasAllocation) : Nat × Nat := (a.executionGas, a.stateGasReservoir)

private def entry (a : EvmGasAllocation) : GasMeter :=
  GasMeter.mk a.executionGas a.stateGasReservoir a.stateGasReservoir 0 0 0

private def meterTuple (m : GasMeter) : Nat × Nat × Nat × Int × Nat × Nat :=
  (m.gasLeft, m.stateGasLeft, m.stateGasBaseline, m.refundCounter,
    m.stateGasSpilled, m.stateGasCommittedSpill)

private def grant : EvmGasAllocation := allocateEvmGas (cfgA 7) 9 2 (by decide) (by decide)

-- P01
#guard pair (allocateEvmGas (cfgA 16777216) 0 0 (by decide) (by decide)) == (0, 0)

-- P02
#guard pair (allocateEvmGas (cfgA 16777216) 1 0 (by decide) (by decide)) == (1, 0)

-- P03
#guard pair (allocateEvmGas (cfgA 16777216) 1 1 (by decide) (by decide)) == (0, 0)

-- P04
#guard pair (allocateEvmGas (cfgA 16777216) 16777215 0 (by decide) (by decide)) == (16777215, 0)

-- P05
#guard pair (allocateEvmGas (cfgA 16777216) 16777216 0 (by decide) (by decide)) == (16777216, 0)

-- P06
#guard pair (allocateEvmGas (cfgA 16777216) 16777217 0 (by decide) (by decide)) == (16777216, 1)

-- P07
#guard pair (allocateEvmGas (cfgA 16777216) 16777216 1 (by decide) (by decide)) == (16777215, 0)

-- P08
#guard pair (allocateEvmGas (cfgA 16777216) 16777217 1 (by decide) (by decide)) == (16777215, 1)

-- P09
#guard pair (allocateEvmGas (cfgA 16777216) 16777215 16777215 (by decide) (by decide)) == (0, 0)

-- P10
#guard pair (allocateEvmGas (cfgA 16777216) 16777216 16777216 (by decide) (by decide)) == (0, 0)

-- P11
#guard pair (allocateEvmGas (cfgA 16777216) 16777217 16777216 (by decide) (by decide)) == (0, 1)

-- P12
#guard pair (allocateEvmGas (cfgA 16777216) 4294967295 16777216 (by decide) (by decide)) == (0,
  4278190079)

-- P13
#guard pair (allocateEvmGas (cfgA 16777216) 4294967296 0 (by decide) (by decide)) == (16777216,
  4278190080)

-- P14
#guard pair (allocateEvmGas (cfgA 16777216) 5 2 (by decide) (by decide)) == (3, 0)

-- G01
#guard pair (allocateEvmGas (cfgA 0) 0 0 (by decide) (by decide)) == (0, 0)

-- G02
#guard pair (allocateEvmGas (cfgA 0) 7 0 (by decide) (by decide)) == (0, 7)

-- G03
#guard pair (allocateEvmGas (cfgA 7) 5 2 (by decide) (by decide)) == (3, 0)

-- G04
#guard pair (allocateEvmGas (cfgA 7) 9 2 (by decide) (by decide)) == (5, 2)

-- G05
#guard pair (allocateEvmGas (cfgA 9) 9 2 (by decide) (by decide)) == (7, 0)

-- G06
#guard pair (allocateEvmGas (cfgA 7) 9 0 (by decide) (by decide)) == (7, 2)

-- W01
#guard pair (allocateEvmGas (cfgA 7) 18446744073709551616 2 (by decide) (by decide)) == (5,
  18446744073709551609)

-- W02
#guard pair (allocateEvmGas (cfgA 18446744073709551623) 18446744073709551625 2 (by decide) (by
  decide)) == (18446744073709551621, 2)

-- W03
#guard pair (allocateEvmGas (cfgA
  115792089237316195423570985008687907853269984665640564039457584007913129639943)
  115792089237316195423570985008687907853269984665640564039457584007913129639945 2 (by decide)
  (by decide)) ==
  (115792089237316195423570985008687907853269984665640564039457584007913129639941, 2)

-- W04
#guard pair (allocateEvmGas (cfgA
  115792089237316195423570985008687907853269984665640564039457584007913129639937)
  115792089237316195423570985008687907853269984665640564039457584007913129639937
  115792089237316195423570985008687907853269984665640564039457584007913129639937 (by decide) (by
  decide)) == (0, 0)

-- D01: complete observed and reconstructed coordinates, actual eta equality.
private theorem D01_eta : EvmGasAllocation.mk (EvmGasAllocation.mk 0 0).executionGas
    (EvmGasAllocation.mk 0 0).stateGasReservoir = EvmGasAllocation.mk 0 0 :=
  EvmGasAllocation.eta _
#guard pair (EvmGasAllocation.mk 0 0) == (0, 0) &&
  pair (EvmGasAllocation.mk (EvmGasAllocation.mk 0 0).executionGas
    (EvmGasAllocation.mk 0 0).stateGasReservoir) == (0, 0)

-- D02: complete observed and reconstructed coordinates, actual eta equality.
private theorem D02_eta : EvmGasAllocation.mk (EvmGasAllocation.mk 1 0).executionGas
    (EvmGasAllocation.mk 1 0).stateGasReservoir = EvmGasAllocation.mk 1 0 :=
  EvmGasAllocation.eta _
#guard pair (EvmGasAllocation.mk 1 0) == (1, 0) &&
  pair (EvmGasAllocation.mk (EvmGasAllocation.mk 1 0).executionGas
    (EvmGasAllocation.mk 1 0).stateGasReservoir) == (1, 0)

-- D03: complete observed and reconstructed coordinates, actual eta equality.
private theorem D03_eta : EvmGasAllocation.mk (EvmGasAllocation.mk 0 1).executionGas
    (EvmGasAllocation.mk 0 1).stateGasReservoir = EvmGasAllocation.mk 0 1 :=
  EvmGasAllocation.eta _
#guard pair (EvmGasAllocation.mk 0 1) == (0, 1) &&
  pair (EvmGasAllocation.mk (EvmGasAllocation.mk 0 1).executionGas
    (EvmGasAllocation.mk 0 1).stateGasReservoir) == (0, 1)

-- D04: complete observed and reconstructed coordinates, actual eta equality.
private theorem D04_eta : EvmGasAllocation.mk (EvmGasAllocation.mk
  115792089237316195423570985008687907853269984665640564039457584007913129639937
  18446744073709551617).executionGas
    (EvmGasAllocation.mk
      115792089237316195423570985008687907853269984665640564039457584007913129639937
      18446744073709551617).stateGasReservoir =
      EvmGasAllocation.mk
      115792089237316195423570985008687907853269984665640564039457584007913129639937
      18446744073709551617 :=
  EvmGasAllocation.eta _
#guard pair (EvmGasAllocation.mk
  115792089237316195423570985008687907853269984665640564039457584007913129639937
  18446744073709551617) ==
  (115792089237316195423570985008687907853269984665640564039457584007913129639937,
  18446744073709551617) &&
  pair (EvmGasAllocation.mk (EvmGasAllocation.mk
    115792089237316195423570985008687907853269984665640564039457584007913129639937
    18446744073709551617).executionGas
    (EvmGasAllocation.mk
      115792089237316195423570985008687907853269984665640564039457584007913129639937
      18446744073709551617).stateGasReservoir) ==
      (115792089237316195423570985008687907853269984665640564039457584007913129639937,
      18446744073709551617)

-- E01/E02: both complete results and complete equality flags.
#guard (pair grant, pair (allocateEvmGas (cfgB 7) 9 2 (by decide) (by decide)),
    pair grant == pair (allocateEvmGas (cfgB 7) 9 2 (by decide) (by decide))) ==
  ((5, 2), (5, 2), true)
#guard (pair grant, pair (allocateEvmGas (cfgA 9) 9 2 (by decide) (by decide)),
    pair grant == pair (allocateEvmGas (cfgA 9) 9 2 (by decide) (by decide))) ==
  ((5, 2), (7, 0), false)

-- M01: complete entry, potential and signed observer.
#guard (meterTuple (entry grant), (entry grant).phi,
    txStateGasUsed (entry grant) 2 (by decide)) == ((5, 2, 2, 0, 0, 0), 5, 0)

private def executionObservation (amount : Nat) : Option ((Nat × Nat × Nat × Int × Nat × Nat) ×
  Nat) :=
  match chargeGas (entry grant) amount with
  | .ok m => some (meterTuple m, m.phi)
  | .error _ => none

-- M02/M03/M04: every post-meter coordinate and potential.
#guard executionObservation 0 == some ((5, 2, 2, 0, 0, 0), 5)
#guard executionObservation 3 == some ((2, 2, 2, 0, 0, 0), 2)
#guard executionObservation 5 == some ((0, 2, 2, 0, 0, 0), 0)
-- M05: exact error, without a successful post-meter.
#guard match chargeGas (entry grant) 6 with
  | .error .outOfGas => true
  | _ => false
-- M06: all six fields, potential and signed usage after a spill.
#guard match chargeStateGas (entry grant) 3 with
  | .ok m => if h : m.stateGasBaseline ≤ 2 then
      (meterTuple m, m.phi, txStateGasUsed m 2 h) == ((4, 0, 2, 0, 1, 0), 5, 3)
    else false
  | .error _ => false

end STFSpec.Conformance.Vm.Core.TransactionGasAllocationGuards
