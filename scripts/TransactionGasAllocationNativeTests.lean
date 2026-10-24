/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Conformance.Vm.Core.TransactionGasAllocationGuards
import Lean

/-! Complete 36-group interpreted/native producer. All fixtures are private;
only main is the executable entry. No source module or expected arithmetic model.
Guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7. -/

open STFSpec.Vm.Core STFSpec.Base Lean

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

private def natJson (n : Nat) : Json := toJson (toString n)
private def intJson (n : Int) : Json := toJson (toString n)
private def allocationJson (a : EvmGasAllocation) : Json :=
  Json.mkObj [("executionGas", natJson a.executionGas),
    ("stateGasReservoir", natJson a.stateGasReservoir)]
private def meterJson (m : GasMeter) : Json :=
  Json.mkObj [("gasLeft", natJson m.gasLeft), ("stateGasLeft", natJson m.stateGasLeft),
    ("stateGasBaseline", natJson m.stateGasBaseline), ("refundCounter", intJson m.refundCounter),
    ("stateGasSpilled", natJson m.stateGasSpilled),
    ("stateGasCommittedSpill", natJson m.stateGasCommittedSpill)]
private def emit (id kind : String) (payload : Json) : IO Unit := do
  (← IO.getStdout).putStrLn (Json.mkObj [("id", toJson id), ("kind", toJson kind),
    ("payload", payload)]).compress
private def emitAllocation (id : String) (c t i : Nat) (ht : i ≤ t)
    (hc : i ≤ (cfgA c).costs.txMaxGasLimit) : IO Unit :=
  emit id "allocation" (Json.mkObj [("cap", natJson c), ("txGas", natJson t),
    ("intrinsicExecution", natJson i),
    ("allocation", allocationJson (allocateEvmGas (cfgA c) t i ht hc))])
private def emitRaw (id : String) (e r : Nat) : IO Unit := do
  let a := EvmGasAllocation.mk e r
  let b := EvmGasAllocation.mk a.executionGas a.stateGasReservoir
  emit id "raw" (Json.mkObj [("allocation", allocationJson a),
    ("reconstructed", allocationJson b), ("equal", toJson (pair a == pair b))])
private def emitRelation (id : String) (a b : EvmGasAllocation) : IO Unit :=
  emit id "relation" (Json.mkObj [("left", allocationJson a),
    ("right", allocationJson b), ("equal", toJson (pair a == pair b))])
private def emitCharge (id : String) (result : Except ExceptionalHalt GasMeter)
    (withUsage : Bool) : IO Unit := do
  match result with
  | .error .outOfGas => emit id "charge" (Json.mkObj [("status", toJson "error"),
      ("error", toJson "outOfGas")])
  | .error _ => throw (IO.userError "unexpected charge error")
  | .ok m =>
    let fields := [("status", toJson "ok"), ("meter", meterJson m), ("phi", natJson m.phi)]
    if withUsage then
      if h : m.stateGasBaseline ≤ 2 then
        emit id "charge" (Json.mkObj (fields ++ [("usage", intJson (txStateGasUsed m 2 h))]))
      else throw (IO.userError "observer baseline outside local proof domain")
    else emit id "charge" (Json.mkObj fields)

/-- Reproducible finite executable entry; errors have a distinct nonzero exit. -/
def main : IO UInt32 := do
  try
    (← IO.getStdout).putStrLn (Json.mkObj [("schema", toJson "transaction-gas-allocation-v1"),
      ("mode", toJson "target"), ("count", toJson (36 : Nat))]).compress
    emitAllocation "P01" 16777216 0 0 (by decide) (by decide)
    emitAllocation "P02" 16777216 1 0 (by decide) (by decide)
    emitAllocation "P03" 16777216 1 1 (by decide) (by decide)
    emitAllocation "P04" 16777216 16777215 0 (by decide) (by decide)
    emitAllocation "P05" 16777216 16777216 0 (by decide) (by decide)
    emitAllocation "P06" 16777216 16777217 0 (by decide) (by decide)
    emitAllocation "P07" 16777216 16777216 1 (by decide) (by decide)
    emitAllocation "P08" 16777216 16777217 1 (by decide) (by decide)
    emitAllocation "P09" 16777216 16777215 16777215 (by decide) (by decide)
    emitAllocation "P10" 16777216 16777216 16777216 (by decide) (by decide)
    emitAllocation "P11" 16777216 16777217 16777216 (by decide) (by decide)
    emitAllocation "P12" 16777216 4294967295 16777216 (by decide) (by decide)
    emitAllocation "P13" 16777216 4294967296 0 (by decide) (by decide)
    emitAllocation "P14" 16777216 5 2 (by decide) (by decide)
    emitAllocation "G01" 0 0 0 (by decide) (by decide)
    emitAllocation "G02" 0 7 0 (by decide) (by decide)
    emitAllocation "G03" 7 5 2 (by decide) (by decide)
    emitAllocation "G04" 7 9 2 (by decide) (by decide)
    emitAllocation "G05" 9 9 2 (by decide) (by decide)
    emitAllocation "G06" 7 9 0 (by decide) (by decide)
    emitAllocation "W01" 7 18446744073709551616 2 (by decide) (by decide)
    emitAllocation "W02" 18446744073709551623 18446744073709551625 2 (by decide) (by decide)
    emitAllocation "W03" 115792089237316195423570985008687907853269984665640564039457584007913129639943 115792089237316195423570985008687907853269984665640564039457584007913129639945 2 (by decide) (by decide)
    emitAllocation "W04" 115792089237316195423570985008687907853269984665640564039457584007913129639937 115792089237316195423570985008687907853269984665640564039457584007913129639937 115792089237316195423570985008687907853269984665640564039457584007913129639937 (by decide) (by decide)
    emitRaw "D01" 0 0
    emitRaw "D02" 1 0
    emitRaw "D03" 0 1
    emitRaw "D04" 115792089237316195423570985008687907853269984665640564039457584007913129639937 18446744073709551617
    emitRelation "E01" grant (allocateEvmGas (cfgB 7) 9 2 (by decide) (by decide))
    emitRelation "E02" grant (allocateEvmGas (cfgA 9) 9 2 (by decide) (by decide))
    emit "M01" "entry" (Json.mkObj [("meter", meterJson (entry grant)),
      ("phi", natJson (entry grant).phi),
      ("usage", intJson (txStateGasUsed (entry grant) 2 (by decide)))])
    emitCharge "M02" (chargeGas (entry grant) 0) false
    emitCharge "M03" (chargeGas (entry grant) 3) false
    emitCharge "M04" (chargeGas (entry grant) 5) false
    emitCharge "M05" (chargeGas (entry grant) 6) false
    emitCharge "M06" (chargeStateGas (entry grant) 3) true
    (← IO.getStdout).putStrLn (Json.mkObj [("end", toJson true),
      ("count", toJson (36 : Nat))]).compress
    return 0
  catch error =>
    (← IO.getStderr).putStrLn s!"FAIL {error}"
    return 1
