/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions
import Lean

/-!
# Executed ADD and SUB observations

Complete frame observations use the public providers. The complete-world equality
is proved by ArithmeticCallerProofs; the runtime world observations below are sentinels,
including an unchanged supplied provider action. No EEST guest executes here.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md` §§3/4/7.
-/

open STFSpec.Base STFSpec.State STFSpec.Vm.Core STFSpec.Vm.Instructions Lean

private def costs : GasCosts :=
  {
    base := 1
    veryLow := 2
    low := 3
    mid := 4
    high := 5
    warmAccess := 6
    coldAccountAccess := 7
    coldStorageAccess := 8
    storageWrite := 9
    callStipend := 10
    accountWrite := 11
    callValue := 12
    codeInitPerWord := 13
    createAccess := 14
    zero := 15
    memoryPerWord := 16
    fastStep := 17
    refundStorageClear := 18
    precompileEcrecover := 19
    precompileP256Verify := 20
    precompileSha256Base := 21
    precompileSha256PerWord := 22
    precompileRipemd160Base := 23
    precompileRipemd160PerWord := 24
    precompileIdentityBase := 25
    precompileIdentityPerWord := 26
    precompileBlake2FPerRound := 27
    precompilePointEvaluation := 28
    precompileBlsG1Add := 29
    precompileBlsG1Mul := 30
    precompileBlsG1Map := 31
    precompileBlsG2Add := 32
    precompileBlsG2Mul := 33
    precompileBlsG2Map := 34
    precompileEcAdd := 35
    precompileEcMul := 36
    precompileEcPairingBase := 37
    precompileEcPairingPerPoint := 38
    perBlob := U64.ofNat 39
    blobScheduleTarget := U64.ofNat 40
    blobTargetGasPerBlock := U64.ofNat 41
    blobBaseCost := 42
    blobScheduleMax := U64.ofNat 43
    blobMinGasPrice := 44
    blobBaseFeeUpdateFraction := 45
    blockAccessListItem := 46
    txBase := 47
    txValueCost := 48
    txDataTokenStandard := 49
    txDataTokenFloor := 50
    txAccessListAddress := 51
    txAccessListStorageKey := 52
    txMaxGasLimit := 53
    txMaxTotalGasLimit := 54
    authTupleBytes := 55
    executionPerAuthBaseCost := 56
    limitAdjustmentFactor := 57
    limitMinimum := 58
    opcodeAdd := 59
    opcodeSub := 60
    opcodeMul := 61
    opcodeDiv := 62
    opcodeSdiv := 63
    opcodeMod := 64
    opcodeSmod := 65
    opcodeAddmod := 66
    opcodeMulmod := 67
    opcodeSignextend := 68
    opcodeLt := 69
    opcodeGt := 70
    opcodeSlt := 71
    opcodeSgt := 72
    opcodeEq := 73
    opcodeIsZero := 74
    opcodeAnd := 75
    opcodeOr := 76
    opcodeXor := 77
    opcodeNot := 78
    opcodeByte := 79
    opcodeShl := 80
    opcodeShr := 81
    opcodeSar := 82
    opcodeClz := 83
    opcodeJump := 84
    opcodeJumpi := 85
    opcodeJumpDest := 86
    opcodeCallDataLoad := 87
    opcodeBlockHash := 88
    opcodeCoinbase := 89
    opcodePop := 90
    opcodeMsize := 91
    opcodePc := 92
    opcodeGas := 93
    opcodeAddress := 94
    opcodeOrigin := 95
    opcodeCaller := 96
    opcodeCallValue := 97
    opcodeCallDataSize := 98
    opcodeCodeSize := 99
    opcodeGasPrice := 100
    opcodeTimestamp := 101
    opcodeNumber := 102
    opcodeGasLimit := 103
    opcodePrevRandao := 104
    opcodeReturnDataSize := 105
    opcodeChainId := 106
    opcodeSelfBalance := 107
    opcodeBaseFee := 108
    opcodeBlobBaseFee := 109
    opcodeSlotNum := 110
    opcodeBlobHash := 111
    opcodePush := 112
    opcodePush0 := 113
    opcodeDup := 114
    opcodeSwap := 115
    opcodeDupn := 116
    opcodeSwapn := 117
    opcodeExchange := 118
    opcodeTload := 119
    opcodeTstore := 120
    opcodeReturnDataCopyBase := 121
    opcodeReturnDataCopyPerWord := 122
    opcodeCallDataCopyBase := 123
    opcodeCodeCopyBase := 124
    opcodeMcopyBase := 125
    opcodeMloadBase := 126
    opcodeMstoreBase := 127
    opcodeMstore8Base := 128
    opcodeCopyPerWord := 129
    opcodeExpBase := 130
    opcodeExpPerByte := 131
    opcodeKeccak256Base := 132
    opcodeKeccak256PerWord := 133
    opcodeLogBase := 134
    opcodeLogDataPerByte := 135
    opcodeLogTopic := 136
    opcodeSelfDestructBase := 137
    blsPairingBase := 138
    blsPairingPerPair := 139
    blsG1KDiscount := #[140, 141]
    blsG2KDiscount := #[141, 142]
    blsG1MaxDiscount := 142
    blsG2MaxDiscount := 143
    blsMultiplier := 144
  }

private def addr (n : Nat) := Address.ofNat n
private def hash (n : Nat) := Hash32.ofBytes32 (FixedBytes.ofNat n)
private def blockEnv : BlockEnvironment :=
  ⟨U64.ofNat 11, 13, #[hash 17, hash 19], addr 23, 29, 31,
    U256.ofNat 37, FixedBytes.ofNat 41, U64.ofNat 43, hash 47, U64.ofNat 53⟩
private def txEnv : TransactionEnvironment :=
  ⟨addr 59, addr 61, true, Bytes.ofList [0, 128, 0], U256.ofNat 67, 71, 73,
    79, 83, 89, ∅, ∅, #[], #[], some 0, some (hash 97)⟩

private def ctx (upper : Bool) : FrameCtx :=
  ⟨⟨costs, ⟨0, 7, 2 ^ 300 + 11, 13⟩, ⟨7, 0, 2 ^ 301 + 17⟩⟩,
    blockEnv, txEnv, addr 101, addr 103, U256.max, Bytes.ofList [255, 0, 128],
    some (addr 0), Bytes.ofList [96, 91, 255],
    validJumpDestinations (Bytes.ofList [91, 0, 91]),
    if upper then 1024 else 0, by split <;> decide, true, upper, false, addr 107⟩

private def world : VmWorld Id :=
  let pre : PreState Id := ⟨fun _ ↦ .ok none, fun _ _ ↦ .ok (U256.ofNat 109),
    fun _ ↦ .ok (ByteArray.mk #[0, 255, 128]), fun _ ↦ .ok (hash 113)⟩
  let block : BlockState Id :=
    ⟨pre, ⟨hash 127, hash 131, hash 137, hash 139⟩,
      (∅ : Std.ExtTreeMap Address (Option Account)).insert (addr 149) none,
      ⟨157, ∅, ∅⟩, ∅, ⟨163, ∅, ∅⟩, ∅, ∅, ∅, ∅, ∅, ∅, some (2 ^ 290 + 167)⟩
  let rev : TxRevertible :=
    ⟨∅, ⟨173, ∅, ∅⟩, ∅, ⟨179, ∅, ∅⟩, ∅, ∅, ∅,
      (∅ : Std.ExtTreeMap (Address × Bytes32) U256).insert
        (addr 181, FixedBytes.ofNat 191) (U256.ofNat 193)⟩
  let obs : TxObs :=
    ⟨(∅ : Std.HashSet Address).insert (addr 197), ∅, ∅,
      (∅ : Std.HashSet Address).insert (addr 199)⟩
  ⟨⟨block, rev, obs⟩⟩

private def memory : Memory :=
  let expanded := Memory.empty.expand 32 (by decide)
  expanded.write 2 (Bytes.ofList [0, 128, 255, 1]) (by
    right
    have h : expanded.size = 32 := by
      change (Memory.empty.expand 32 _).size = 32
      rw [← Memory.length_toBytes, Memory.toBytes_expand, Memory.toBytes_empty]
      rfl
    rw [h]
    decide)

private def frame (pc : Nat) (s : Stack) (large : Bool) : Frame :=
  let entry : Log := ⟨addr 256, #[hash 256, hash 1, hash 256], Bytes.ofList [255, 0, 128]⟩
  ⟨pc, s, memory,
    if large then ⟨2 ^ 300 + 3, 101, 2, -17, 5, 11⟩ else ⟨0, 0, 0, -3, 0, 7⟩,
    .concat (.leaf [entry]) (.concat .empty (.leaf [entry])),
    (∅ : AddrSet).insert (addr 256), Bytes.ofList [0, 255, 128, 0],
    (∅ : AddrSet).insert (addr 1),
    ((∅ : SlotSet).insert (addr 1, FixedBytes.ofNat 256)).insert (addr 256, FixedBytes.ofNat 1)⟩

private def bytesJson (b : Bytes) : Json := toJson (b.toList.map UInt8.toNat)
private def frameJson (f : Frame) : Json := Json.mkObj [
  ("pc", toJson f.pc), ("stack", toJson (f.stack.toList.map U256.toNat)),
  ("memory", toJson (f.memory.toBytes.map UInt8.toNat)),
  ("meter", toJson ([Int.ofNat f.gasMeter.gasLeft, Int.ofNat f.gasMeter.stateGasLeft,
    Int.ofNat f.gasMeter.stateGasBaseline, f.gasMeter.refundCounter,
    Int.ofNat f.gasMeter.stateGasSpilled, Int.ofNat f.gasMeter.stateGasCommittedSpill])),
  ("logs", Json.arr (f.logs.toList.map fun l ↦ Json.arr #[
    toJson l.address.toNat, toJson (l.topics.toList.map Hash32.toNat),
    toJson (l.data.toList.map UInt8.toNat)]).toArray),
  ("deleted", toJson (f.accountsToDelete.toList.map Address.toNat)),
  ("returnData", bytesJson f.returnData),
  ("warmAddresses", toJson (f.accessedAddresses.toList.map Address.toNat)),
  ("warmSlots", toJson (f.accessedStorageKeys.toList.map fun (a, k) ↦ (a.toNat, k.toNat)))]

private def worldJson (w : VmWorld Id) : Json :=
  let tx := w.tx
  let storage := match tx.block.preState.getStorage (addr 1) (FixedBytes.ofNat 2) with
    | .ok v => toJson v.toNat
    | .error _ => Json.null
  Json.mkObj [
    ("blockAccountOrder", toJson tx.block.accountOrder.next),
    ("blockStorageOrder", toJson tx.block.storageAddressOrder.next),
    ("revAccountOrder", toJson tx.rev.accountOrder.next),
    ("revStorageOrder", toJson tx.rev.storageAddressOrder.next),
    ("oldestAncestorOffset", toJson tx.block.oldestAncestorOffset),
    ("emptyCodeHash", toJson tx.block.consts.emptyCodeHash.toNat),
    ("storageProviderSample", storage),
    ("created199", toJson (tx.obs.createdAccounts.contains (addr 199))),
    ("read197", toJson (tx.obs.accountReads.contains (addr 197)))]

private def natural (s : String) : IO Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw (IO.userError "invalid natural input")

private def item (values : Array String) (i : Nat) : IO String :=
  match values[i]? with
  | some value => pure value
  | none => throw (IO.userError "missing arithmetic input")

private def inputStack (text : String) : IO Stack := do
  let words ← if text == "-" then pure [] else text.splitOn "," |>.mapM fun s => do
    let n ← natural s
    match U256.ofNat? n with
    | some w => pure w
    | none => throw (IO.userError "word outside U256")
  match words.reverse.foldlM (fun s w => s.push w) Stack.empty with
  | .ok s => pure s
  | .error _ => throw (IO.userError "stack outside typed domain")

/-- Execute the actual public arithmetic handlers on the supplied input-only catalogue. -/
def main (args : List String) : IO Unit := do
  let path ← match args with
    | [path] => pure path
    | _ => throw (IO.userError "expected arithmetic input path")
  let out ← IO.getStdout
  for line in (← IO.FS.readFile path).splitOn "\n" do
    if line.isEmpty then continue
    let values := (line.splitOn "\t").toArray
    if values.size != 9 then throw (IO.userError "arithmetic input arity")
    let i ← natural (← item values 0)
    let op ← item values 1
    let cost ← natural (← item values 2)
    let other ← natural (← item values 3)
    let veryLow ← natural (← item values 4)
    let gas ← natural (← item values 5)
    let pc ← natural (← item values 6)
    let flag ← natural (← item values 7)
    if flag > 1 then throw (IO.userError "invalid context flag")
    let upper := flag == 1
    let s ← inputStack (← item values 8)
    let baseCtx := ctx upper
    let prices := if op == "add" then
      { baseCtx.config.costs with opcodeAdd := cost, opcodeSub := other, veryLow := veryLow }
      else { baseCtx.config.costs with opcodeSub := cost, opcodeAdd := other, veryLow := veryLow }
    let context := { baseCtx with config := { baseCtx.config with costs := prices } }
    let baseFrame := frame pc s true
    let f := { baseFrame with gasMeter := { baseFrame.gasMeter with gasLeft := gas } }
    let action ← if op == "add" then pure (add context f)
      else if op == "sub" then pure (sub context f)
      else throw (IO.userError "unknown arithmetic opcode")
    match (action.run world).run with
    | .error _ => throw (IO.userError "arithmetic returned VmFault")
    | .ok (r, w) =>
      let (after, tag, error) ← match r with
        | .continue after => pure (after, "continue", Json.null)
        | .halt after .stackUnderflow => pure (after, "halt", toJson "stackUnderflow")
        | .halt after .outOfGas => pure (after, "halt", toJson "outOfGas")
        | _ => throw (IO.userError "unexpected arithmetic control")
      out.putStrLn <| (Json.mkObj [
        ("schema", toJson "arithmetic-v1"), ("case", toJson i), ("op", toJson op),
        ("cost", toJson cost), ("otherCost", toJson other), ("veryLow", toJson veryLow),
        ("upper", toJson upper), ("before", frameJson f), ("after", frameJson after),
        ("tag", toJson tag), ("error", error),
        ("phiBefore", toJson f.gasMeter.phi), ("phiAfter", toJson after.gasMeter.phi),
        ("worldBefore", worldJson world), ("worldAfter", worldJson w)]).compress
