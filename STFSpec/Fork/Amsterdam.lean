/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block.SystemAddrs
import STFSpec.Block.TxParams
import STFSpec.Fork.Amsterdam.BlockParams
import STFSpec.Vm.Core.Config
import STFSpec.Vm.Core.Limits

/-!
# Amsterdam block, system and transaction parameters, VM pricing and limits

Library `EthFork`. Complete fixed values for the Block- and Core-owned raw records, in
pinned EELS dependency order. Raw policy fields remain independent in their owning modules.
Spec guidance: `STFSpec/informal/modules/EthFork.md` §§2–7.
-/

namespace STFSpec.Fork.Amsterdam

/-- Complete Amsterdam system addresses and independent call budgets; EELS
`src/ethereum/forks/amsterdam/fork.py:117–141` and
`src/ethereum/forks/amsterdam/requests.py:49` at the pin.
The system caller also matches `src/ethereum/forks/amsterdam/vm/__init__.py:41–43`.
This is fixed data; configuration assembly and address transport are separate. -/
def systemAddrs : Block.SystemAddrs where
  systemAddress := Base.Address.ofNat 0xfffffffffffffffffffffffffffffffffffffffe
  beaconRoots := Base.Address.ofNat 0x000f3df6d732807ef1319fb7b8bb8522d0beac02
  historyStorage := Base.Address.ofNat 0x0000f90827f1c53a10cb7a02335b175320002935
  withdrawalRequests := Base.Address.ofNat 0x00000961ef480eb55e80d19ad83579a64c007002
  consolidationRequests := Base.Address.ofNat 0x0000bbddc7ce488642fb579f8b00f3a590007251
  builderDeposits := Base.Address.ofNat 0x0000bff46984e3725691fa540a8c7589300d8282
  builderExits := Base.Address.ofNat 0x000064d678505ad48f8ccb093bc65613800e8282
  depositContract := Base.Address.ofNat 0x00000000219ab540356cbb839cbe05303d7705fa
  txGas := 30000000
  maxSstoresPerCall := 16

/-- Amsterdam transaction parameters; EELS
`src/ethereum/forks/amsterdam/transactions.py:64,74,82` at the pin.
The floor fields are token counts, separate from VM gas prices. -/
def txParams : Block.TxParams where
  blobCountLimit := 6
  accessListAddressFloorTokens := 80
  accessListStorageKeyFloorTokens := 128

/-- Complete Amsterdam execution and precompile pricing; EELS
`src/ethereum/forks/amsterdam/vm/gas.py:78–259`,
`src/ethereum/forks/amsterdam/vm/precompiled_contracts/bls12_381/__init__.py:37–301`
and
`src/ethereum/forks/amsterdam/vm/precompiled_contracts/bls12_381/bls12_381_pairing.py:46`,
at the pin. Aliases retain their source dependencies. -/
def gasCosts : Vm.Core.GasCosts :=
  let base : Nat := 2
  let veryLow : Nat := 3
  let low : Nat := 5
  let mid : Nat := 8
  let high : Nat := 10
  let warmAccess : Nat := 100
  let coldAccountAccess : Nat := 3000
  let coldStorageAccess : Nat := 2100
  let storageWrite : Nat := 10000
  let callStipend : Nat := 2300
  let accountWrite : Nat := 9000
  let callValue : Nat := accountWrite + callStipend
  let codeInitPerWord : Nat := 2
  let createAccess : Nat := accountWrite + coldAccountAccess
  let gasZero : Nat := 0
  let memoryPerWord : Nat := 3
  let fastStep : Nat := 5
  let refundStorageClear : Int := Int.ofNat (((storageWrite + coldStorageAccess) * 4800) / 5000)
  let precompileEcrecover : Nat := 3000
  let precompileP256Verify : Nat := 6900
  let precompileSha256Base : Nat := 60
  let precompileSha256PerWord : Nat := 12
  let precompileRipemd160Base : Nat := 600
  let precompileRipemd160PerWord : Nat := 120
  let precompileIdentityBase : Nat := 15
  let precompileIdentityPerWord : Nat := 3
  let precompileBlake2FPerRound : Nat := 1
  let precompilePointEvaluation : Nat := 50000
  let precompileBlsG1Add : Nat := 375
  let precompileBlsG1Mul : Nat := 12000
  let precompileBlsG1Map : Nat := 5500
  let precompileBlsG2Add : Nat := 600
  let precompileBlsG2Mul : Nat := 22500
  let precompileBlsG2Map : Nat := 23800
  let precompileEcAdd : Nat := 150
  let precompileEcMul : Nat := 6000
  let precompileEcPairingBase : Nat := 45000
  let precompileEcPairingPerPoint : Nat := 34000
  let perBlob : Base.U64 := Base.U64.ofNat (2 ^ 17)
  let blobScheduleTarget : Base.U64 := Base.U64.ofNat 14
  let blobTargetGasPerBlock : Base.U64 := Base.U64.wrappingMul perBlob blobScheduleTarget
  let blobBaseCost : Nat := 2 ^ 13
  let blobScheduleMax : Base.U64 := Base.U64.ofNat 21
  let blobMinGasPrice : Nat := 1
  let blobBaseFeeUpdateFraction : Nat := 11684671
  let blockAccessListItem : Nat := 2000
  let txBase : Nat := 12000
  let txValueCost : Nat := 6000
  let txDataTokenStandard : Nat := 4
  let txDataTokenFloor : Nat := 16
  let txAccessListAddress : Nat := coldAccountAccess - warmAccess
  let txAccessListStorageKey : Nat := coldStorageAccess - warmAccess
  let txMaxGasLimit : Nat := 16777216
  let txMaxTotalGasLimit : Nat := 4294967295
  let authTupleBytes : Nat := 101
  let executionPerAuthBaseCost : Nat :=
    authTupleBytes * txDataTokenFloor + precompileEcrecover + coldAccountAccess + 2 * warmAccess
  let limitAdjustmentFactor : Nat := 1024
  let limitMinimum : Nat := 5000
  let opcodeAdd : Nat := veryLow
  let opcodeSub : Nat := veryLow
  let opcodeMul : Nat := low
  let opcodeDiv : Nat := low
  let opcodeSdiv : Nat := low
  let opcodeMod : Nat := low
  let opcodeSmod : Nat := low
  let opcodeAddmod : Nat := mid
  let opcodeMulmod : Nat := mid
  let opcodeSignextend : Nat := low
  let opcodeLt : Nat := veryLow
  let opcodeGt : Nat := veryLow
  let opcodeSlt : Nat := veryLow
  let opcodeSgt : Nat := veryLow
  let opcodeEq : Nat := veryLow
  let opcodeIsZero : Nat := veryLow
  let opcodeAnd : Nat := veryLow
  let opcodeOr : Nat := veryLow
  let opcodeXor : Nat := veryLow
  let opcodeNot : Nat := veryLow
  let opcodeByte : Nat := veryLow
  let opcodeShl : Nat := veryLow
  let opcodeShr : Nat := veryLow
  let opcodeSar : Nat := veryLow
  let opcodeClz : Nat := low
  let opcodeJump : Nat := mid
  let opcodeJumpi : Nat := high
  let opcodeJumpDest : Nat := 1
  let opcodeCallDataLoad : Nat := veryLow
  let opcodeBlockHash : Nat := 20
  let opcodeCoinbase : Nat := base
  let opcodePop : Nat := base
  let opcodeMsize : Nat := base
  let opcodePc : Nat := base
  let opcodeGas : Nat := base
  let opcodeAddress : Nat := base
  let opcodeOrigin : Nat := base
  let opcodeCaller : Nat := base
  let opcodeCallValue : Nat := base
  let opcodeCallDataSize : Nat := base
  let opcodeCodeSize : Nat := base
  let opcodeGasPrice : Nat := base
  let opcodeTimestamp : Nat := base
  let opcodeNumber : Nat := base
  let opcodeGasLimit : Nat := base
  let opcodePrevRandao : Nat := base
  let opcodeReturnDataSize : Nat := base
  let opcodeChainId : Nat := base
  let opcodeSelfBalance : Nat := fastStep
  let opcodeBaseFee : Nat := base
  let opcodeBlobBaseFee : Nat := base
  let opcodeSlotNum : Nat := base
  let opcodeBlobHash : Nat := 3
  let opcodePush : Nat := veryLow
  let opcodePush0 : Nat := base
  let opcodeDup : Nat := veryLow
  let opcodeSwap : Nat := veryLow
  let opcodeDupn : Nat := veryLow
  let opcodeSwapn : Nat := veryLow
  let opcodeExchange : Nat := veryLow
  let opcodeTload : Nat := 100
  let opcodeTstore : Nat := 100
  let opcodeReturnDataCopyBase : Nat := veryLow
  let opcodeReturnDataCopyPerWord : Nat := 3
  let opcodeCallDataCopyBase : Nat := veryLow
  let opcodeCodeCopyBase : Nat := veryLow
  let opcodeMcopyBase : Nat := veryLow
  let opcodeMloadBase : Nat := veryLow
  let opcodeMstoreBase : Nat := veryLow
  let opcodeMstore8Base : Nat := veryLow
  let opcodeCopyPerWord : Nat := 3
  let opcodeExpBase : Nat := 10
  let opcodeExpPerByte : Nat := 50
  let opcodeKeccak256Base : Nat := 30
  let opcodeKeccak256PerWord : Nat := 6
  let opcodeLogBase : Nat := 375
  let opcodeLogDataPerByte : Nat := 8
  let opcodeLogTopic : Nat := 375
  let opcodeSelfDestructBase : Nat := 5000
  let blsPairingBase : Nat := 37700
  let blsPairingPerPair : Nat := 32600
  let blsG1KDiscount : Array Nat := #[
    1000, 949, 848, 797, 764, 750, 738, 728, 719, 712, 705, 698, 692, 687, 682, 677,
    673, 669, 665, 661, 658, 654, 651, 648, 645, 642, 640, 637, 635, 632, 630, 627,
    625, 623, 621, 619, 617, 615, 613, 611, 609, 608, 606, 604, 603, 601, 599, 598,
    596, 595, 593, 592, 591, 589, 588, 586, 585, 584, 582, 581, 580, 579, 577, 576,
    575, 574, 573, 572, 570, 569, 568, 567, 566, 565, 564, 563, 562, 561, 560, 559,
    558, 557, 556, 555, 554, 553, 552, 551, 550, 549, 548, 547, 547, 546, 545, 544,
    543, 542, 541, 540, 540, 539, 538, 537, 536, 536, 535, 534, 533, 532, 532, 531,
    530, 529, 528, 528, 527, 526, 525, 525, 524, 523, 522, 522, 521, 520, 520, 519
  ]
  let blsG2KDiscount : Array Nat := #[
    1000, 1000, 923, 884, 855, 832, 812, 796, 782, 770, 759, 749, 740, 732, 724, 717,
    711, 704, 699, 693, 688, 683, 679, 674, 670, 666, 663, 659, 655, 652, 649, 646,
    643, 640, 637, 634, 632, 629, 627, 624, 622, 620, 618, 615, 613, 611, 609, 607,
    606, 604, 602, 600, 598, 597, 595, 593, 592, 590, 589, 587, 586, 584, 583, 582,
    580, 579, 578, 576, 575, 574, 573, 571, 570, 569, 568, 567, 566, 565, 563, 562,
    561, 560, 559, 558, 557, 556, 555, 554, 553, 552, 552, 551, 550, 549, 548, 547,
    546, 545, 545, 544, 543, 542, 541, 541, 540, 539, 538, 537, 537, 536, 535, 535,
    534, 533, 532, 532, 531, 530, 530, 529, 528, 528, 527, 526, 526, 525, 524, 524
  ]
  let blsG1MaxDiscount : Nat := 519
  let blsG2MaxDiscount : Nat := 524
  let blsMultiplier : Nat := 1000
  {
    base := base
    veryLow := veryLow
    low := low
    mid := mid
    high := high
    warmAccess := warmAccess
    coldAccountAccess := coldAccountAccess
    coldStorageAccess := coldStorageAccess
    storageWrite := storageWrite
    callStipend := callStipend
    accountWrite := accountWrite
    callValue := callValue
    codeInitPerWord := codeInitPerWord
    createAccess := createAccess
    zero := gasZero
    memoryPerWord := memoryPerWord
    fastStep := fastStep
    refundStorageClear := refundStorageClear
    precompileEcrecover := precompileEcrecover
    precompileP256Verify := precompileP256Verify
    precompileSha256Base := precompileSha256Base
    precompileSha256PerWord := precompileSha256PerWord
    precompileRipemd160Base := precompileRipemd160Base
    precompileRipemd160PerWord := precompileRipemd160PerWord
    precompileIdentityBase := precompileIdentityBase
    precompileIdentityPerWord := precompileIdentityPerWord
    precompileBlake2FPerRound := precompileBlake2FPerRound
    precompilePointEvaluation := precompilePointEvaluation
    precompileBlsG1Add := precompileBlsG1Add
    precompileBlsG1Mul := precompileBlsG1Mul
    precompileBlsG1Map := precompileBlsG1Map
    precompileBlsG2Add := precompileBlsG2Add
    precompileBlsG2Mul := precompileBlsG2Mul
    precompileBlsG2Map := precompileBlsG2Map
    precompileEcAdd := precompileEcAdd
    precompileEcMul := precompileEcMul
    precompileEcPairingBase := precompileEcPairingBase
    precompileEcPairingPerPoint := precompileEcPairingPerPoint
    perBlob := perBlob
    blobScheduleTarget := blobScheduleTarget
    blobTargetGasPerBlock := blobTargetGasPerBlock
    blobBaseCost := blobBaseCost
    blobScheduleMax := blobScheduleMax
    blobMinGasPrice := blobMinGasPrice
    blobBaseFeeUpdateFraction := blobBaseFeeUpdateFraction
    blockAccessListItem := blockAccessListItem
    txBase := txBase
    txValueCost := txValueCost
    txDataTokenStandard := txDataTokenStandard
    txDataTokenFloor := txDataTokenFloor
    txAccessListAddress := txAccessListAddress
    txAccessListStorageKey := txAccessListStorageKey
    txMaxGasLimit := txMaxGasLimit
    txMaxTotalGasLimit := txMaxTotalGasLimit
    authTupleBytes := authTupleBytes
    executionPerAuthBaseCost := executionPerAuthBaseCost
    limitAdjustmentFactor := limitAdjustmentFactor
    limitMinimum := limitMinimum
    opcodeAdd := opcodeAdd
    opcodeSub := opcodeSub
    opcodeMul := opcodeMul
    opcodeDiv := opcodeDiv
    opcodeSdiv := opcodeSdiv
    opcodeMod := opcodeMod
    opcodeSmod := opcodeSmod
    opcodeAddmod := opcodeAddmod
    opcodeMulmod := opcodeMulmod
    opcodeSignextend := opcodeSignextend
    opcodeLt := opcodeLt
    opcodeGt := opcodeGt
    opcodeSlt := opcodeSlt
    opcodeSgt := opcodeSgt
    opcodeEq := opcodeEq
    opcodeIsZero := opcodeIsZero
    opcodeAnd := opcodeAnd
    opcodeOr := opcodeOr
    opcodeXor := opcodeXor
    opcodeNot := opcodeNot
    opcodeByte := opcodeByte
    opcodeShl := opcodeShl
    opcodeShr := opcodeShr
    opcodeSar := opcodeSar
    opcodeClz := opcodeClz
    opcodeJump := opcodeJump
    opcodeJumpi := opcodeJumpi
    opcodeJumpDest := opcodeJumpDest
    opcodeCallDataLoad := opcodeCallDataLoad
    opcodeBlockHash := opcodeBlockHash
    opcodeCoinbase := opcodeCoinbase
    opcodePop := opcodePop
    opcodeMsize := opcodeMsize
    opcodePc := opcodePc
    opcodeGas := opcodeGas
    opcodeAddress := opcodeAddress
    opcodeOrigin := opcodeOrigin
    opcodeCaller := opcodeCaller
    opcodeCallValue := opcodeCallValue
    opcodeCallDataSize := opcodeCallDataSize
    opcodeCodeSize := opcodeCodeSize
    opcodeGasPrice := opcodeGasPrice
    opcodeTimestamp := opcodeTimestamp
    opcodeNumber := opcodeNumber
    opcodeGasLimit := opcodeGasLimit
    opcodePrevRandao := opcodePrevRandao
    opcodeReturnDataSize := opcodeReturnDataSize
    opcodeChainId := opcodeChainId
    opcodeSelfBalance := opcodeSelfBalance
    opcodeBaseFee := opcodeBaseFee
    opcodeBlobBaseFee := opcodeBlobBaseFee
    opcodeSlotNum := opcodeSlotNum
    opcodeBlobHash := opcodeBlobHash
    opcodePush := opcodePush
    opcodePush0 := opcodePush0
    opcodeDup := opcodeDup
    opcodeSwap := opcodeSwap
    opcodeDupn := opcodeDupn
    opcodeSwapn := opcodeSwapn
    opcodeExchange := opcodeExchange
    opcodeTload := opcodeTload
    opcodeTstore := opcodeTstore
    opcodeReturnDataCopyBase := opcodeReturnDataCopyBase
    opcodeReturnDataCopyPerWord := opcodeReturnDataCopyPerWord
    opcodeCallDataCopyBase := opcodeCallDataCopyBase
    opcodeCodeCopyBase := opcodeCodeCopyBase
    opcodeMcopyBase := opcodeMcopyBase
    opcodeMloadBase := opcodeMloadBase
    opcodeMstoreBase := opcodeMstoreBase
    opcodeMstore8Base := opcodeMstore8Base
    opcodeCopyPerWord := opcodeCopyPerWord
    opcodeExpBase := opcodeExpBase
    opcodeExpPerByte := opcodeExpPerByte
    opcodeKeccak256Base := opcodeKeccak256Base
    opcodeKeccak256PerWord := opcodeKeccak256PerWord
    opcodeLogBase := opcodeLogBase
    opcodeLogDataPerByte := opcodeLogDataPerByte
    opcodeLogTopic := opcodeLogTopic
    opcodeSelfDestructBase := opcodeSelfDestructBase
    blsPairingBase := blsPairingBase
    blsPairingPerPair := blsPairingPerPair
    blsG1KDiscount := blsG1KDiscount
    blsG2KDiscount := blsG2KDiscount
    blsG1MaxDiscount := blsG1MaxDiscount
    blsG2MaxDiscount := blsG2MaxDiscount
    blsMultiplier := blsMultiplier
  }

/-- Four stored Amsterdam state-pricing inputs; EELS
`src/ethereum/forks/amsterdam/vm/gas.py:56–59`. Derived amounts are separate. -/
def stateGasCosts : Vm.Core.StateGasCosts where
  costPerStateByte := 1530
  bytesPerNewAccount := 120
  bytesPerStorageSet := 64
  bytesPerAuthBase := 23

/-- Amsterdam VM limits; EELS `src/ethereum/forks/amsterdam/vm/interpreter.py:84–86`.
The init-code maximum retains its source dependency on the code maximum. -/
def vmLimits : Vm.Core.VmLimits :=
  let maxCodeSize := 0x10000
  { stackDepthLimit := Vm.Core.STACK_DEPTH_LIMIT
    maxCodeSize := maxCodeSize
    maxInitCodeSize := 2 * maxCodeSize }

/-- Group the same complete Amsterdam execution, state and limit records (B8/F8). -/
def vmConfig : Vm.Core.VmConfig := ⟨gasCosts, stateGasCosts, vmLimits⟩

/-- Amsterdam depth is definitionally Core's reducible literal (F8). -/
theorem vmLimits_depth :
    vmConfig.limits.stackDepthLimit = Vm.Core.STACK_DEPTH_LIMIT := rfl

end STFSpec.Fork.Amsterdam
