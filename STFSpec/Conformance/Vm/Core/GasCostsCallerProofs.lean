/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Public gas-policy data clients

Library `EthConformance`. Fully supplied constructor, eta and ext clients, plus
complete selected-cost chargeGas congruence and public success/error consequences.
No raw policy invariants or provider internals are assumed or unfolded.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7.
-/

namespace STFSpec.Conformance.Vm.Core.GasCostsCallerProofs
open STFSpec.Vm.Core

private theorem supplied_constructor_eta
    (base : Nat)
    (veryLow : Nat)
    (low : Nat)
    (mid : Nat)
    (high : Nat)
    (warmAccess : Nat)
    (coldAccountAccess : Nat)
    (coldStorageAccess : Nat)
    (storageWrite : Nat)
    (callStipend : Nat)
    (accountWrite : Nat)
    (callValue : Nat)
    (codeInitPerWord : Nat)
    (createAccess : Nat)
    (zeroCost : Nat)
    (memoryPerWord : Nat)
    (fastStep : Nat)
    (refundStorageClear : Int)
    (precompileEcrecover : Nat)
    (precompileP256Verify : Nat)
    (precompileSha256Base : Nat)
    (precompileSha256PerWord : Nat)
    (precompileRipemd160Base : Nat)
    (precompileRipemd160PerWord : Nat)
    (precompileIdentityBase : Nat)
    (precompileIdentityPerWord : Nat)
    (precompileBlake2FPerRound : Nat)
    (precompilePointEvaluation : Nat)
    (precompileBlsG1Add : Nat)
    (precompileBlsG1Mul : Nat)
    (precompileBlsG1Map : Nat)
    (precompileBlsG2Add : Nat)
    (precompileBlsG2Mul : Nat)
    (precompileBlsG2Map : Nat)
    (precompileEcAdd : Nat)
    (precompileEcMul : Nat)
    (precompileEcPairingBase : Nat)
    (precompileEcPairingPerPoint : Nat)
    (perBlob : STFSpec.Base.U64)
    (blobScheduleTarget : STFSpec.Base.U64)
    (blobTargetGasPerBlock : STFSpec.Base.U64)
    (blobBaseCost : Nat)
    (blobScheduleMax : STFSpec.Base.U64)
    (blobMinGasPrice : Nat)
    (blobBaseFeeUpdateFraction : Nat)
    (blockAccessListItem : Nat)
    (txBase : Nat)
    (txValueCost : Nat)
    (txDataTokenStandard : Nat)
    (txDataTokenFloor : Nat)
    (txAccessListAddress : Nat)
    (txAccessListStorageKey : Nat)
    (txMaxGasLimit : Nat)
    (txMaxTotalGasLimit : Nat)
    (authTupleBytes : Nat)
    (executionPerAuthBaseCost : Nat)
    (limitAdjustmentFactor : Nat)
    (limitMinimum : Nat)
    (opcodeAdd : Nat)
    (opcodeSub : Nat)
    (opcodeMul : Nat)
    (opcodeDiv : Nat)
    (opcodeSdiv : Nat)
    (opcodeMod : Nat)
    (opcodeSmod : Nat)
    (opcodeAddmod : Nat)
    (opcodeMulmod : Nat)
    (opcodeSignextend : Nat)
    (opcodeLt : Nat)
    (opcodeGt : Nat)
    (opcodeSlt : Nat)
    (opcodeSgt : Nat)
    (opcodeEq : Nat)
    (opcodeIsZero : Nat)
    (opcodeAnd : Nat)
    (opcodeOr : Nat)
    (opcodeXor : Nat)
    (opcodeNot : Nat)
    (opcodeByte : Nat)
    (opcodeShl : Nat)
    (opcodeShr : Nat)
    (opcodeSar : Nat)
    (opcodeClz : Nat)
    (opcodeJump : Nat)
    (opcodeJumpi : Nat)
    (opcodeJumpDest : Nat)
    (opcodeCallDataLoad : Nat)
    (opcodeBlockHash : Nat)
    (opcodeCoinbase : Nat)
    (opcodePop : Nat)
    (opcodeMsize : Nat)
    (opcodePc : Nat)
    (opcodeGas : Nat)
    (opcodeAddress : Nat)
    (opcodeOrigin : Nat)
    (opcodeCaller : Nat)
    (opcodeCallValue : Nat)
    (opcodeCallDataSize : Nat)
    (opcodeCodeSize : Nat)
    (opcodeGasPrice : Nat)
    (opcodeTimestamp : Nat)
    (opcodeNumber : Nat)
    (opcodeGasLimit : Nat)
    (opcodePrevRandao : Nat)
    (opcodeReturnDataSize : Nat)
    (opcodeChainId : Nat)
    (opcodeSelfBalance : Nat)
    (opcodeBaseFee : Nat)
    (opcodeBlobBaseFee : Nat)
    (opcodeSlotNum : Nat)
    (opcodeBlobHash : Nat)
    (opcodePush : Nat)
    (opcodePush0 : Nat)
    (opcodeDup : Nat)
    (opcodeSwap : Nat)
    (opcodeDupn : Nat)
    (opcodeSwapn : Nat)
    (opcodeExchange : Nat)
    (opcodeTload : Nat)
    (opcodeTstore : Nat)
    (opcodeReturnDataCopyBase : Nat)
    (opcodeReturnDataCopyPerWord : Nat)
    (opcodeCallDataCopyBase : Nat)
    (opcodeCodeCopyBase : Nat)
    (opcodeMcopyBase : Nat)
    (opcodeMloadBase : Nat)
    (opcodeMstoreBase : Nat)
    (opcodeMstore8Base : Nat)
    (opcodeCopyPerWord : Nat)
    (opcodeExpBase : Nat)
    (opcodeExpPerByte : Nat)
    (opcodeKeccak256Base : Nat)
    (opcodeKeccak256PerWord : Nat)
    (opcodeLogBase : Nat)
    (opcodeLogDataPerByte : Nat)
    (opcodeLogTopic : Nat)
    (opcodeSelfDestructBase : Nat)
    (blsPairingBase : Nat)
    (blsPairingPerPair : Nat)
    (blsG1KDiscount : Array Nat)
    (blsG2KDiscount : Array Nat)
    (blsG1MaxDiscount : Nat)
    (blsG2MaxDiscount : Nat)
    (blsMultiplier : Nat)
    : let c : GasCosts := {
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
        zero := zeroCost
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
      GasCosts.mk
        c.base
        c.veryLow
        c.low
        c.mid
        c.high
        c.warmAccess
        c.coldAccountAccess
        c.coldStorageAccess
        c.storageWrite
        c.callStipend
        c.accountWrite
        c.callValue
        c.codeInitPerWord
        c.createAccess
        c.zero
        c.memoryPerWord
        c.fastStep
        c.refundStorageClear
        c.precompileEcrecover
        c.precompileP256Verify
        c.precompileSha256Base
        c.precompileSha256PerWord
        c.precompileRipemd160Base
        c.precompileRipemd160PerWord
        c.precompileIdentityBase
        c.precompileIdentityPerWord
        c.precompileBlake2FPerRound
        c.precompilePointEvaluation
        c.precompileBlsG1Add
        c.precompileBlsG1Mul
        c.precompileBlsG1Map
        c.precompileBlsG2Add
        c.precompileBlsG2Mul
        c.precompileBlsG2Map
        c.precompileEcAdd
        c.precompileEcMul
        c.precompileEcPairingBase
        c.precompileEcPairingPerPoint
        c.perBlob
        c.blobScheduleTarget
        c.blobTargetGasPerBlock
        c.blobBaseCost
        c.blobScheduleMax
        c.blobMinGasPrice
        c.blobBaseFeeUpdateFraction
        c.blockAccessListItem
        c.txBase
        c.txValueCost
        c.txDataTokenStandard
        c.txDataTokenFloor
        c.txAccessListAddress
        c.txAccessListStorageKey
        c.txMaxGasLimit
        c.txMaxTotalGasLimit
        c.authTupleBytes
        c.executionPerAuthBaseCost
        c.limitAdjustmentFactor
        c.limitMinimum
        c.opcodeAdd
        c.opcodeSub
        c.opcodeMul
        c.opcodeDiv
        c.opcodeSdiv
        c.opcodeMod
        c.opcodeSmod
        c.opcodeAddmod
        c.opcodeMulmod
        c.opcodeSignextend
        c.opcodeLt
        c.opcodeGt
        c.opcodeSlt
        c.opcodeSgt
        c.opcodeEq
        c.opcodeIsZero
        c.opcodeAnd
        c.opcodeOr
        c.opcodeXor
        c.opcodeNot
        c.opcodeByte
        c.opcodeShl
        c.opcodeShr
        c.opcodeSar
        c.opcodeClz
        c.opcodeJump
        c.opcodeJumpi
        c.opcodeJumpDest
        c.opcodeCallDataLoad
        c.opcodeBlockHash
        c.opcodeCoinbase
        c.opcodePop
        c.opcodeMsize
        c.opcodePc
        c.opcodeGas
        c.opcodeAddress
        c.opcodeOrigin
        c.opcodeCaller
        c.opcodeCallValue
        c.opcodeCallDataSize
        c.opcodeCodeSize
        c.opcodeGasPrice
        c.opcodeTimestamp
        c.opcodeNumber
        c.opcodeGasLimit
        c.opcodePrevRandao
        c.opcodeReturnDataSize
        c.opcodeChainId
        c.opcodeSelfBalance
        c.opcodeBaseFee
        c.opcodeBlobBaseFee
        c.opcodeSlotNum
        c.opcodeBlobHash
        c.opcodePush
        c.opcodePush0
        c.opcodeDup
        c.opcodeSwap
        c.opcodeDupn
        c.opcodeSwapn
        c.opcodeExchange
        c.opcodeTload
        c.opcodeTstore
        c.opcodeReturnDataCopyBase
        c.opcodeReturnDataCopyPerWord
        c.opcodeCallDataCopyBase
        c.opcodeCodeCopyBase
        c.opcodeMcopyBase
        c.opcodeMloadBase
        c.opcodeMstoreBase
        c.opcodeMstore8Base
        c.opcodeCopyPerWord
        c.opcodeExpBase
        c.opcodeExpPerByte
        c.opcodeKeccak256Base
        c.opcodeKeccak256PerWord
        c.opcodeLogBase
        c.opcodeLogDataPerByte
        c.opcodeLogTopic
        c.opcodeSelfDestructBase
        c.blsPairingBase
        c.blsPairingPerPair
        c.blsG1KDiscount
        c.blsG2KDiscount
        c.blsG1MaxDiscount
        c.blsG2MaxDiscount
        c.blsMultiplier
        = c := by
  exact GasCosts.eta _

private theorem public_ext (a b : GasCosts)
    (h_base : a.base = b.base)
    (h_veryLow : a.veryLow = b.veryLow)
    (h_low : a.low = b.low)
    (h_mid : a.mid = b.mid)
    (h_high : a.high = b.high)
    (h_warmAccess : a.warmAccess = b.warmAccess)
    (h_coldAccountAccess : a.coldAccountAccess = b.coldAccountAccess)
    (h_coldStorageAccess : a.coldStorageAccess = b.coldStorageAccess)
    (h_storageWrite : a.storageWrite = b.storageWrite)
    (h_callStipend : a.callStipend = b.callStipend)
    (h_accountWrite : a.accountWrite = b.accountWrite)
    (h_callValue : a.callValue = b.callValue)
    (h_codeInitPerWord : a.codeInitPerWord = b.codeInitPerWord)
    (h_createAccess : a.createAccess = b.createAccess)
    (h_zero : a.zero = b.zero)
    (h_memoryPerWord : a.memoryPerWord = b.memoryPerWord)
    (h_fastStep : a.fastStep = b.fastStep)
    (h_refundStorageClear : a.refundStorageClear = b.refundStorageClear)
    (h_precompileEcrecover : a.precompileEcrecover = b.precompileEcrecover)
    (h_precompileP256Verify : a.precompileP256Verify = b.precompileP256Verify)
    (h_precompileSha256Base : a.precompileSha256Base = b.precompileSha256Base)
    (h_precompileSha256PerWord : a.precompileSha256PerWord = b.precompileSha256PerWord)
    (h_precompileRipemd160Base : a.precompileRipemd160Base = b.precompileRipemd160Base)
    (h_precompileRipemd160PerWord : a.precompileRipemd160PerWord = b.precompileRipemd160PerWord)
    (h_precompileIdentityBase : a.precompileIdentityBase = b.precompileIdentityBase)
    (h_precompileIdentityPerWord : a.precompileIdentityPerWord = b.precompileIdentityPerWord)
    (h_precompileBlake2FPerRound : a.precompileBlake2FPerRound = b.precompileBlake2FPerRound)
    (h_precompilePointEvaluation : a.precompilePointEvaluation = b.precompilePointEvaluation)
    (h_precompileBlsG1Add : a.precompileBlsG1Add = b.precompileBlsG1Add)
    (h_precompileBlsG1Mul : a.precompileBlsG1Mul = b.precompileBlsG1Mul)
    (h_precompileBlsG1Map : a.precompileBlsG1Map = b.precompileBlsG1Map)
    (h_precompileBlsG2Add : a.precompileBlsG2Add = b.precompileBlsG2Add)
    (h_precompileBlsG2Mul : a.precompileBlsG2Mul = b.precompileBlsG2Mul)
    (h_precompileBlsG2Map : a.precompileBlsG2Map = b.precompileBlsG2Map)
    (h_precompileEcAdd : a.precompileEcAdd = b.precompileEcAdd)
    (h_precompileEcMul : a.precompileEcMul = b.precompileEcMul)
    (h_precompileEcPairingBase : a.precompileEcPairingBase = b.precompileEcPairingBase)
    (h_precompileEcPairingPerPoint : a.precompileEcPairingPerPoint = b.precompileEcPairingPerPoint)
    (h_perBlob : a.perBlob = b.perBlob)
    (h_blobScheduleTarget : a.blobScheduleTarget = b.blobScheduleTarget)
    (h_blobTargetGasPerBlock : a.blobTargetGasPerBlock = b.blobTargetGasPerBlock)
    (h_blobBaseCost : a.blobBaseCost = b.blobBaseCost)
    (h_blobScheduleMax : a.blobScheduleMax = b.blobScheduleMax)
    (h_blobMinGasPrice : a.blobMinGasPrice = b.blobMinGasPrice)
    (h_blobBaseFeeUpdateFraction : a.blobBaseFeeUpdateFraction = b.blobBaseFeeUpdateFraction)
    (h_blockAccessListItem : a.blockAccessListItem = b.blockAccessListItem)
    (h_txBase : a.txBase = b.txBase)
    (h_txValueCost : a.txValueCost = b.txValueCost)
    (h_txDataTokenStandard : a.txDataTokenStandard = b.txDataTokenStandard)
    (h_txDataTokenFloor : a.txDataTokenFloor = b.txDataTokenFloor)
    (h_txAccessListAddress : a.txAccessListAddress = b.txAccessListAddress)
    (h_txAccessListStorageKey : a.txAccessListStorageKey = b.txAccessListStorageKey)
    (h_txMaxGasLimit : a.txMaxGasLimit = b.txMaxGasLimit)
    (h_txMaxTotalGasLimit : a.txMaxTotalGasLimit = b.txMaxTotalGasLimit)
    (h_authTupleBytes : a.authTupleBytes = b.authTupleBytes)
    (h_executionPerAuthBaseCost : a.executionPerAuthBaseCost = b.executionPerAuthBaseCost)
    (h_limitAdjustmentFactor : a.limitAdjustmentFactor = b.limitAdjustmentFactor)
    (h_limitMinimum : a.limitMinimum = b.limitMinimum)
    (h_opcodeAdd : a.opcodeAdd = b.opcodeAdd)
    (h_opcodeSub : a.opcodeSub = b.opcodeSub)
    (h_opcodeMul : a.opcodeMul = b.opcodeMul)
    (h_opcodeDiv : a.opcodeDiv = b.opcodeDiv)
    (h_opcodeSdiv : a.opcodeSdiv = b.opcodeSdiv)
    (h_opcodeMod : a.opcodeMod = b.opcodeMod)
    (h_opcodeSmod : a.opcodeSmod = b.opcodeSmod)
    (h_opcodeAddmod : a.opcodeAddmod = b.opcodeAddmod)
    (h_opcodeMulmod : a.opcodeMulmod = b.opcodeMulmod)
    (h_opcodeSignextend : a.opcodeSignextend = b.opcodeSignextend)
    (h_opcodeLt : a.opcodeLt = b.opcodeLt)
    (h_opcodeGt : a.opcodeGt = b.opcodeGt)
    (h_opcodeSlt : a.opcodeSlt = b.opcodeSlt)
    (h_opcodeSgt : a.opcodeSgt = b.opcodeSgt)
    (h_opcodeEq : a.opcodeEq = b.opcodeEq)
    (h_opcodeIsZero : a.opcodeIsZero = b.opcodeIsZero)
    (h_opcodeAnd : a.opcodeAnd = b.opcodeAnd)
    (h_opcodeOr : a.opcodeOr = b.opcodeOr)
    (h_opcodeXor : a.opcodeXor = b.opcodeXor)
    (h_opcodeNot : a.opcodeNot = b.opcodeNot)
    (h_opcodeByte : a.opcodeByte = b.opcodeByte)
    (h_opcodeShl : a.opcodeShl = b.opcodeShl)
    (h_opcodeShr : a.opcodeShr = b.opcodeShr)
    (h_opcodeSar : a.opcodeSar = b.opcodeSar)
    (h_opcodeClz : a.opcodeClz = b.opcodeClz)
    (h_opcodeJump : a.opcodeJump = b.opcodeJump)
    (h_opcodeJumpi : a.opcodeJumpi = b.opcodeJumpi)
    (h_opcodeJumpDest : a.opcodeJumpDest = b.opcodeJumpDest)
    (h_opcodeCallDataLoad : a.opcodeCallDataLoad = b.opcodeCallDataLoad)
    (h_opcodeBlockHash : a.opcodeBlockHash = b.opcodeBlockHash)
    (h_opcodeCoinbase : a.opcodeCoinbase = b.opcodeCoinbase)
    (h_opcodePop : a.opcodePop = b.opcodePop)
    (h_opcodeMsize : a.opcodeMsize = b.opcodeMsize)
    (h_opcodePc : a.opcodePc = b.opcodePc)
    (h_opcodeGas : a.opcodeGas = b.opcodeGas)
    (h_opcodeAddress : a.opcodeAddress = b.opcodeAddress)
    (h_opcodeOrigin : a.opcodeOrigin = b.opcodeOrigin)
    (h_opcodeCaller : a.opcodeCaller = b.opcodeCaller)
    (h_opcodeCallValue : a.opcodeCallValue = b.opcodeCallValue)
    (h_opcodeCallDataSize : a.opcodeCallDataSize = b.opcodeCallDataSize)
    (h_opcodeCodeSize : a.opcodeCodeSize = b.opcodeCodeSize)
    (h_opcodeGasPrice : a.opcodeGasPrice = b.opcodeGasPrice)
    (h_opcodeTimestamp : a.opcodeTimestamp = b.opcodeTimestamp)
    (h_opcodeNumber : a.opcodeNumber = b.opcodeNumber)
    (h_opcodeGasLimit : a.opcodeGasLimit = b.opcodeGasLimit)
    (h_opcodePrevRandao : a.opcodePrevRandao = b.opcodePrevRandao)
    (h_opcodeReturnDataSize : a.opcodeReturnDataSize = b.opcodeReturnDataSize)
    (h_opcodeChainId : a.opcodeChainId = b.opcodeChainId)
    (h_opcodeSelfBalance : a.opcodeSelfBalance = b.opcodeSelfBalance)
    (h_opcodeBaseFee : a.opcodeBaseFee = b.opcodeBaseFee)
    (h_opcodeBlobBaseFee : a.opcodeBlobBaseFee = b.opcodeBlobBaseFee)
    (h_opcodeSlotNum : a.opcodeSlotNum = b.opcodeSlotNum)
    (h_opcodeBlobHash : a.opcodeBlobHash = b.opcodeBlobHash)
    (h_opcodePush : a.opcodePush = b.opcodePush)
    (h_opcodePush0 : a.opcodePush0 = b.opcodePush0)
    (h_opcodeDup : a.opcodeDup = b.opcodeDup)
    (h_opcodeSwap : a.opcodeSwap = b.opcodeSwap)
    (h_opcodeDupn : a.opcodeDupn = b.opcodeDupn)
    (h_opcodeSwapn : a.opcodeSwapn = b.opcodeSwapn)
    (h_opcodeExchange : a.opcodeExchange = b.opcodeExchange)
    (h_opcodeTload : a.opcodeTload = b.opcodeTload)
    (h_opcodeTstore : a.opcodeTstore = b.opcodeTstore)
    (h_opcodeReturnDataCopyBase : a.opcodeReturnDataCopyBase = b.opcodeReturnDataCopyBase)
    (h_opcodeReturnDataCopyPerWord : a.opcodeReturnDataCopyPerWord = b.opcodeReturnDataCopyPerWord)
    (h_opcodeCallDataCopyBase : a.opcodeCallDataCopyBase = b.opcodeCallDataCopyBase)
    (h_opcodeCodeCopyBase : a.opcodeCodeCopyBase = b.opcodeCodeCopyBase)
    (h_opcodeMcopyBase : a.opcodeMcopyBase = b.opcodeMcopyBase)
    (h_opcodeMloadBase : a.opcodeMloadBase = b.opcodeMloadBase)
    (h_opcodeMstoreBase : a.opcodeMstoreBase = b.opcodeMstoreBase)
    (h_opcodeMstore8Base : a.opcodeMstore8Base = b.opcodeMstore8Base)
    (h_opcodeCopyPerWord : a.opcodeCopyPerWord = b.opcodeCopyPerWord)
    (h_opcodeExpBase : a.opcodeExpBase = b.opcodeExpBase)
    (h_opcodeExpPerByte : a.opcodeExpPerByte = b.opcodeExpPerByte)
    (h_opcodeKeccak256Base : a.opcodeKeccak256Base = b.opcodeKeccak256Base)
    (h_opcodeKeccak256PerWord : a.opcodeKeccak256PerWord = b.opcodeKeccak256PerWord)
    (h_opcodeLogBase : a.opcodeLogBase = b.opcodeLogBase)
    (h_opcodeLogDataPerByte : a.opcodeLogDataPerByte = b.opcodeLogDataPerByte)
    (h_opcodeLogTopic : a.opcodeLogTopic = b.opcodeLogTopic)
    (h_opcodeSelfDestructBase : a.opcodeSelfDestructBase = b.opcodeSelfDestructBase)
    (h_blsPairingBase : a.blsPairingBase = b.blsPairingBase)
    (h_blsPairingPerPair : a.blsPairingPerPair = b.blsPairingPerPair)
    (h_blsG1KDiscount : a.blsG1KDiscount = b.blsG1KDiscount)
    (h_blsG2KDiscount : a.blsG2KDiscount = b.blsG2KDiscount)
    (h_blsG1MaxDiscount : a.blsG1MaxDiscount = b.blsG1MaxDiscount)
    (h_blsG2MaxDiscount : a.blsG2MaxDiscount = b.blsG2MaxDiscount)
    (h_blsMultiplier : a.blsMultiplier = b.blsMultiplier)
    : a = b := by
  exact GasCosts.ext a b
    h_base
    h_veryLow
    h_low
    h_mid
    h_high
    h_warmAccess
    h_coldAccountAccess
    h_coldStorageAccess
    h_storageWrite
    h_callStipend
    h_accountWrite
    h_callValue
    h_codeInitPerWord
    h_createAccess
    h_zero
    h_memoryPerWord
    h_fastStep
    h_refundStorageClear
    h_precompileEcrecover
    h_precompileP256Verify
    h_precompileSha256Base
    h_precompileSha256PerWord
    h_precompileRipemd160Base
    h_precompileRipemd160PerWord
    h_precompileIdentityBase
    h_precompileIdentityPerWord
    h_precompileBlake2FPerRound
    h_precompilePointEvaluation
    h_precompileBlsG1Add
    h_precompileBlsG1Mul
    h_precompileBlsG1Map
    h_precompileBlsG2Add
    h_precompileBlsG2Mul
    h_precompileBlsG2Map
    h_precompileEcAdd
    h_precompileEcMul
    h_precompileEcPairingBase
    h_precompileEcPairingPerPoint
    h_perBlob
    h_blobScheduleTarget
    h_blobTargetGasPerBlock
    h_blobBaseCost
    h_blobScheduleMax
    h_blobMinGasPrice
    h_blobBaseFeeUpdateFraction
    h_blockAccessListItem
    h_txBase
    h_txValueCost
    h_txDataTokenStandard
    h_txDataTokenFloor
    h_txAccessListAddress
    h_txAccessListStorageKey
    h_txMaxGasLimit
    h_txMaxTotalGasLimit
    h_authTupleBytes
    h_executionPerAuthBaseCost
    h_limitAdjustmentFactor
    h_limitMinimum
    h_opcodeAdd
    h_opcodeSub
    h_opcodeMul
    h_opcodeDiv
    h_opcodeSdiv
    h_opcodeMod
    h_opcodeSmod
    h_opcodeAddmod
    h_opcodeMulmod
    h_opcodeSignextend
    h_opcodeLt
    h_opcodeGt
    h_opcodeSlt
    h_opcodeSgt
    h_opcodeEq
    h_opcodeIsZero
    h_opcodeAnd
    h_opcodeOr
    h_opcodeXor
    h_opcodeNot
    h_opcodeByte
    h_opcodeShl
    h_opcodeShr
    h_opcodeSar
    h_opcodeClz
    h_opcodeJump
    h_opcodeJumpi
    h_opcodeJumpDest
    h_opcodeCallDataLoad
    h_opcodeBlockHash
    h_opcodeCoinbase
    h_opcodePop
    h_opcodeMsize
    h_opcodePc
    h_opcodeGas
    h_opcodeAddress
    h_opcodeOrigin
    h_opcodeCaller
    h_opcodeCallValue
    h_opcodeCallDataSize
    h_opcodeCodeSize
    h_opcodeGasPrice
    h_opcodeTimestamp
    h_opcodeNumber
    h_opcodeGasLimit
    h_opcodePrevRandao
    h_opcodeReturnDataSize
    h_opcodeChainId
    h_opcodeSelfBalance
    h_opcodeBaseFee
    h_opcodeBlobBaseFee
    h_opcodeSlotNum
    h_opcodeBlobHash
    h_opcodePush
    h_opcodePush0
    h_opcodeDup
    h_opcodeSwap
    h_opcodeDupn
    h_opcodeSwapn
    h_opcodeExchange
    h_opcodeTload
    h_opcodeTstore
    h_opcodeReturnDataCopyBase
    h_opcodeReturnDataCopyPerWord
    h_opcodeCallDataCopyBase
    h_opcodeCodeCopyBase
    h_opcodeMcopyBase
    h_opcodeMloadBase
    h_opcodeMstoreBase
    h_opcodeMstore8Base
    h_opcodeCopyPerWord
    h_opcodeExpBase
    h_opcodeExpPerByte
    h_opcodeKeccak256Base
    h_opcodeKeccak256PerWord
    h_opcodeLogBase
    h_opcodeLogDataPerByte
    h_opcodeLogTopic
    h_opcodeSelfDestructBase
    h_blsPairingBase
    h_blsPairingPerPair
    h_blsG1KDiscount
    h_blsG2KDiscount
    h_blsG1MaxDiscount
    h_blsG2MaxDiscount
    h_blsMultiplier

-- The existing numeric charge consumer observes only the selected opcodeAdd cost.
-- Equality is of the whole Except result (including every success meter field).
private theorem selected_charge_congr (a b : GasCosts) (g : GasMeter)
    (h : a.opcodeAdd = b.opcodeAdd) :
    chargeGas g a.opcodeAdd = chargeGas g b.opcodeAdd := by
  exact congrArg (chargeGas g) h

private theorem selected_charge_success (c : GasCosts) (g : GasMeter)
    (h : c.opcodeAdd ≤ g.gasLeft) :
    chargeGas g c.opcodeAdd = .ok { g with gasLeft := g.gasLeft - c.opcodeAdd } := by
  exact chargeGas_of_le g c.opcodeAdd h

private theorem selected_charge_error (c : GasCosts) (g : GasMeter) (e : ExceptionalHalt) :
    chargeGas g c.opcodeAdd = .error e ↔ g.gasLeft < c.opcodeAdd ∧ e = .outOfGas := by
  exact chargeGas_eq_error_iff g c.opcodeAdd e

end STFSpec.Conformance.Vm.Core.GasCostsCallerProofs
