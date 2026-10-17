/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.U64

/-!
# Raw gas policy data

Library `EthVmCore`. The exact class-plus-BLS data boundary from pinned EELS
`src/ethereum/forks/amsterdam/vm/gas.py:72–259` and
`src/ethereum/forks/amsterdam/vm/precompiled_contracts/bls12_381/`.
Fields retain independent raw values; EthFork owns the Amsterdam instantiation.
Short source anchors on projections are relative to these source locations.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7.
-/

namespace STFSpec.Vm.Core

/-- Raw gas-policy data; no defaults, values, supported-config predicate or instances. -/
structure GasCosts where
  /-- `GasCosts.BASE`; pinned EELS `gas.py:78`. -/
  base : Nat
  /-- `GasCosts.VERY_LOW`; pinned EELS `gas.py:79`. -/
  veryLow : Nat
  /-- `GasCosts.LOW`; pinned EELS `gas.py:80`. -/
  low : Nat
  /-- `GasCosts.MID`; pinned EELS `gas.py:81`. -/
  mid : Nat
  /-- `GasCosts.HIGH`; pinned EELS `gas.py:82`. -/
  high : Nat
  /-- `GasCosts.WARM_ACCESS`; pinned EELS `gas.py:85`. -/
  warmAccess : Nat
  /-- `GasCosts.COLD_ACCOUNT_ACCESS`; pinned EELS `gas.py:86`. -/
  coldAccountAccess : Nat
  /-- `GasCosts.COLD_STORAGE_ACCESS`; pinned EELS `gas.py:87`. -/
  coldStorageAccess : Nat
  /-- `GasCosts.STORAGE_WRITE`; pinned EELS `gas.py:90`. -/
  storageWrite : Nat
  /-- `GasCosts.CALL_STIPEND`; pinned EELS `gas.py:93`. -/
  callStipend : Nat
  /-- `GasCosts.ACCOUNT_WRITE`; pinned EELS `gas.py:94`. -/
  accountWrite : Nat
  /-- `GasCosts.CALL_VALUE`; pinned EELS `gas.py:95`. -/
  callValue : Nat
  /-- `GasCosts.CODE_INIT_PER_WORD`; pinned EELS `gas.py:98`. -/
  codeInitPerWord : Nat
  /-- `GasCosts.CREATE_ACCESS`; pinned EELS `gas.py:99`. -/
  createAccess : Nat
  /-- `GasCosts.ZERO`; pinned EELS `gas.py:102`. -/
  zero : Nat
  /-- `GasCosts.MEMORY_PER_WORD`; pinned EELS `gas.py:103`. -/
  memoryPerWord : Nat
  /-- `GasCosts.FAST_STEP`; pinned EELS `gas.py:104`. -/
  fastStep : Nat
  /-- `GasCosts.REFUND_STORAGE_CLEAR`; pinned EELS `gas.py:107–109`. -/
  refundStorageClear : Int
  /-- `GasCosts.PRECOMPILE_ECRECOVER`; pinned EELS `gas.py:112`. -/
  precompileEcrecover : Nat
  /-- `GasCosts.PRECOMPILE_P256VERIFY`; pinned EELS `gas.py:113`. -/
  precompileP256Verify : Nat
  /-- `GasCosts.PRECOMPILE_SHA256_BASE`; pinned EELS `gas.py:114`. -/
  precompileSha256Base : Nat
  /-- `GasCosts.PRECOMPILE_SHA256_PER_WORD`; pinned EELS `gas.py:115`. -/
  precompileSha256PerWord : Nat
  /-- `GasCosts.PRECOMPILE_RIPEMD160_BASE`; pinned EELS `gas.py:116`. -/
  precompileRipemd160Base : Nat
  /-- `GasCosts.PRECOMPILE_RIPEMD160_PER_WORD`; pinned EELS `gas.py:117–119`. -/
  precompileRipemd160PerWord : Nat
  /-- `GasCosts.PRECOMPILE_IDENTITY_BASE`; pinned EELS `gas.py:120`. -/
  precompileIdentityBase : Nat
  /-- `GasCosts.PRECOMPILE_IDENTITY_PER_WORD`; pinned EELS `gas.py:121`. -/
  precompileIdentityPerWord : Nat
  /-- `GasCosts.PRECOMPILE_BLAKE2F_PER_ROUND`; pinned EELS `gas.py:122`. -/
  precompileBlake2FPerRound : Nat
  /-- `GasCosts.PRECOMPILE_POINT_EVALUATION`; pinned EELS `gas.py:123–125`. -/
  precompilePointEvaluation : Nat
  /-- `GasCosts.PRECOMPILE_BLS_G1ADD`; pinned EELS `gas.py:126`. -/
  precompileBlsG1Add : Nat
  /-- `GasCosts.PRECOMPILE_BLS_G1MUL`; pinned EELS `gas.py:127`. -/
  precompileBlsG1Mul : Nat
  /-- `GasCosts.PRECOMPILE_BLS_G1MAP`; pinned EELS `gas.py:128`. -/
  precompileBlsG1Map : Nat
  /-- `GasCosts.PRECOMPILE_BLS_G2ADD`; pinned EELS `gas.py:129`. -/
  precompileBlsG2Add : Nat
  /-- `GasCosts.PRECOMPILE_BLS_G2MUL`; pinned EELS `gas.py:130`. -/
  precompileBlsG2Mul : Nat
  /-- `GasCosts.PRECOMPILE_BLS_G2MAP`; pinned EELS `gas.py:131`. -/
  precompileBlsG2Map : Nat
  /-- `GasCosts.PRECOMPILE_ECADD`; pinned EELS `gas.py:132`. -/
  precompileEcAdd : Nat
  /-- `GasCosts.PRECOMPILE_ECMUL`; pinned EELS `gas.py:133`. -/
  precompileEcMul : Nat
  /-- `GasCosts.PRECOMPILE_ECPAIRING_BASE`; pinned EELS `gas.py:134`. -/
  precompileEcPairingBase : Nat
  /-- `GasCosts.PRECOMPILE_ECPAIRING_PER_POINT`; pinned EELS `gas.py:135–137`. -/
  precompileEcPairingPerPoint : Nat
  /-- `GasCosts.PER_BLOB`; pinned EELS `gas.py:140`. -/
  perBlob : STFSpec.Base.U64
  /-- `GasCosts.BLOB_SCHEDULE_TARGET`; pinned EELS `gas.py:141`. -/
  blobScheduleTarget : STFSpec.Base.U64
  /-- `GasCosts.BLOB_TARGET_GAS_PER_BLOCK`; pinned EELS `gas.py:142`. -/
  blobTargetGasPerBlock : STFSpec.Base.U64
  /-- `GasCosts.BLOB_BASE_COST`; pinned EELS `gas.py:143`. -/
  blobBaseCost : Nat
  /-- `GasCosts.BLOB_SCHEDULE_MAX`; pinned EELS `gas.py:144`. -/
  blobScheduleMax : STFSpec.Base.U64
  /-- `GasCosts.BLOB_MIN_GASPRICE`; pinned EELS `gas.py:145`. -/
  blobMinGasPrice : Nat
  /-- `GasCosts.BLOB_BASE_FEE_UPDATE_FRACTION`; pinned EELS `gas.py:146`. -/
  blobBaseFeeUpdateFraction : Nat
  /-- `GasCosts.BLOCK_ACCESS_LIST_ITEM`; pinned EELS `gas.py:149`. -/
  blockAccessListItem : Nat
  /-- `GasCosts.TX_BASE`; pinned EELS `gas.py:152`. -/
  txBase : Nat
  /-- `GasCosts.TX_VALUE_COST`; pinned EELS `gas.py:153`. -/
  txValueCost : Nat
  /-- `GasCosts.TX_DATA_TOKEN_STANDARD`; pinned EELS `gas.py:154`. -/
  txDataTokenStandard : Nat
  /-- `GasCosts.TX_DATA_TOKEN_FLOOR`; pinned EELS `gas.py:155`. -/
  txDataTokenFloor : Nat
  /-- `GasCosts.TX_ACCESS_LIST_ADDRESS`; pinned EELS `gas.py:156–158`. -/
  txAccessListAddress : Nat
  /-- `GasCosts.TX_ACCESS_LIST_STORAGE_KEY`; pinned EELS `gas.py:159–161`. -/
  txAccessListStorageKey : Nat
  /-- `GasCosts.TX_MAX_GAS_LIMIT`; pinned EELS `gas.py:162`. -/
  txMaxGasLimit : Nat
  /-- `GasCosts.TX_MAX_TOTAL_GAS_LIMIT`; pinned EELS `gas.py:163`. -/
  txMaxTotalGasLimit : Nat
  /-- `GasCosts.AUTH_TUPLE_BYTES`; pinned EELS `gas.py:166`. -/
  authTupleBytes : Nat
  /-- `GasCosts.EXECUTION_PER_AUTH_BASE_COST`; pinned EELS `gas.py:167–172`. -/
  executionPerAuthBaseCost : Nat
  /-- `GasCosts.LIMIT_ADJUSTMENT_FACTOR`; pinned EELS `gas.py:175`. -/
  limitAdjustmentFactor : Nat
  /-- `GasCosts.LIMIT_MINIMUM`; pinned EELS `gas.py:176`. -/
  limitMinimum : Nat
  /-- `GasCosts.OPCODE_ADD`; pinned EELS `gas.py:179`. -/
  opcodeAdd : Nat
  /-- `GasCosts.OPCODE_SUB`; pinned EELS `gas.py:180`. -/
  opcodeSub : Nat
  /-- `GasCosts.OPCODE_MUL`; pinned EELS `gas.py:181`. -/
  opcodeMul : Nat
  /-- `GasCosts.OPCODE_DIV`; pinned EELS `gas.py:182`. -/
  opcodeDiv : Nat
  /-- `GasCosts.OPCODE_SDIV`; pinned EELS `gas.py:183`. -/
  opcodeSdiv : Nat
  /-- `GasCosts.OPCODE_MOD`; pinned EELS `gas.py:184`. -/
  opcodeMod : Nat
  /-- `GasCosts.OPCODE_SMOD`; pinned EELS `gas.py:185`. -/
  opcodeSmod : Nat
  /-- `GasCosts.OPCODE_ADDMOD`; pinned EELS `gas.py:186`. -/
  opcodeAddmod : Nat
  /-- `GasCosts.OPCODE_MULMOD`; pinned EELS `gas.py:187`. -/
  opcodeMulmod : Nat
  /-- `GasCosts.OPCODE_SIGNEXTEND`; pinned EELS `gas.py:188`. -/
  opcodeSignextend : Nat
  /-- `GasCosts.OPCODE_LT`; pinned EELS `gas.py:189`. -/
  opcodeLt : Nat
  /-- `GasCosts.OPCODE_GT`; pinned EELS `gas.py:190`. -/
  opcodeGt : Nat
  /-- `GasCosts.OPCODE_SLT`; pinned EELS `gas.py:191`. -/
  opcodeSlt : Nat
  /-- `GasCosts.OPCODE_SGT`; pinned EELS `gas.py:192`. -/
  opcodeSgt : Nat
  /-- `GasCosts.OPCODE_EQ`; pinned EELS `gas.py:193`. -/
  opcodeEq : Nat
  /-- `GasCosts.OPCODE_ISZERO`; pinned EELS `gas.py:194`. -/
  opcodeIsZero : Nat
  /-- `GasCosts.OPCODE_AND`; pinned EELS `gas.py:195`. -/
  opcodeAnd : Nat
  /-- `GasCosts.OPCODE_OR`; pinned EELS `gas.py:196`. -/
  opcodeOr : Nat
  /-- `GasCosts.OPCODE_XOR`; pinned EELS `gas.py:197`. -/
  opcodeXor : Nat
  /-- `GasCosts.OPCODE_NOT`; pinned EELS `gas.py:198`. -/
  opcodeNot : Nat
  /-- `GasCosts.OPCODE_BYTE`; pinned EELS `gas.py:199`. -/
  opcodeByte : Nat
  /-- `GasCosts.OPCODE_SHL`; pinned EELS `gas.py:200`. -/
  opcodeShl : Nat
  /-- `GasCosts.OPCODE_SHR`; pinned EELS `gas.py:201`. -/
  opcodeShr : Nat
  /-- `GasCosts.OPCODE_SAR`; pinned EELS `gas.py:202`. -/
  opcodeSar : Nat
  /-- `GasCosts.OPCODE_CLZ`; pinned EELS `gas.py:203`. -/
  opcodeClz : Nat
  /-- `GasCosts.OPCODE_JUMP`; pinned EELS `gas.py:204`. -/
  opcodeJump : Nat
  /-- `GasCosts.OPCODE_JUMPI`; pinned EELS `gas.py:205`. -/
  opcodeJumpi : Nat
  /-- `GasCosts.OPCODE_JUMPDEST`; pinned EELS `gas.py:206`. -/
  opcodeJumpDest : Nat
  /-- `GasCosts.OPCODE_CALLDATALOAD`; pinned EELS `gas.py:207`. -/
  opcodeCallDataLoad : Nat
  /-- `GasCosts.OPCODE_BLOCKHASH`; pinned EELS `gas.py:208`. -/
  opcodeBlockHash : Nat
  /-- `GasCosts.OPCODE_COINBASE`; pinned EELS `gas.py:209`. -/
  opcodeCoinbase : Nat
  /-- `GasCosts.OPCODE_POP`; pinned EELS `gas.py:210`. -/
  opcodePop : Nat
  /-- `GasCosts.OPCODE_MSIZE`; pinned EELS `gas.py:211`. -/
  opcodeMsize : Nat
  /-- `GasCosts.OPCODE_PC`; pinned EELS `gas.py:212`. -/
  opcodePc : Nat
  /-- `GasCosts.OPCODE_GAS`; pinned EELS `gas.py:213`. -/
  opcodeGas : Nat
  /-- `GasCosts.OPCODE_ADDRESS`; pinned EELS `gas.py:214`. -/
  opcodeAddress : Nat
  /-- `GasCosts.OPCODE_ORIGIN`; pinned EELS `gas.py:215`. -/
  opcodeOrigin : Nat
  /-- `GasCosts.OPCODE_CALLER`; pinned EELS `gas.py:216`. -/
  opcodeCaller : Nat
  /-- `GasCosts.OPCODE_CALLVALUE`; pinned EELS `gas.py:217`. -/
  opcodeCallValue : Nat
  /-- `GasCosts.OPCODE_CALLDATASIZE`; pinned EELS `gas.py:218`. -/
  opcodeCallDataSize : Nat
  /-- `GasCosts.OPCODE_CODESIZE`; pinned EELS `gas.py:219`. -/
  opcodeCodeSize : Nat
  /-- `GasCosts.OPCODE_GASPRICE`; pinned EELS `gas.py:220`. -/
  opcodeGasPrice : Nat
  /-- `GasCosts.OPCODE_TIMESTAMP`; pinned EELS `gas.py:221`. -/
  opcodeTimestamp : Nat
  /-- `GasCosts.OPCODE_NUMBER`; pinned EELS `gas.py:222`. -/
  opcodeNumber : Nat
  /-- `GasCosts.OPCODE_GASLIMIT`; pinned EELS `gas.py:223`. -/
  opcodeGasLimit : Nat
  /-- `GasCosts.OPCODE_PREVRANDAO`; pinned EELS `gas.py:224`. -/
  opcodePrevRandao : Nat
  /-- `GasCosts.OPCODE_RETURNDATASIZE`; pinned EELS `gas.py:225`. -/
  opcodeReturnDataSize : Nat
  /-- `GasCosts.OPCODE_CHAINID`; pinned EELS `gas.py:226`. -/
  opcodeChainId : Nat
  /-- `GasCosts.OPCODE_SELFBALANCE`; pinned EELS `gas.py:227`. -/
  opcodeSelfBalance : Nat
  /-- `GasCosts.OPCODE_BASEFEE`; pinned EELS `gas.py:228`. -/
  opcodeBaseFee : Nat
  /-- `GasCosts.OPCODE_BLOBBASEFEE`; pinned EELS `gas.py:229`. -/
  opcodeBlobBaseFee : Nat
  /-- `GasCosts.OPCODE_SLOTNUM`; pinned EELS `gas.py:230`. -/
  opcodeSlotNum : Nat
  /-- `GasCosts.OPCODE_BLOBHASH`; pinned EELS `gas.py:231`. -/
  opcodeBlobHash : Nat
  /-- `GasCosts.OPCODE_PUSH`; pinned EELS `gas.py:232`. -/
  opcodePush : Nat
  /-- `GasCosts.OPCODE_PUSH0`; pinned EELS `gas.py:233`. -/
  opcodePush0 : Nat
  /-- `GasCosts.OPCODE_DUP`; pinned EELS `gas.py:234`. -/
  opcodeDup : Nat
  /-- `GasCosts.OPCODE_SWAP`; pinned EELS `gas.py:235`. -/
  opcodeSwap : Nat
  /-- `GasCosts.OPCODE_DUPN`; pinned EELS `gas.py:236`. -/
  opcodeDupn : Nat
  /-- `GasCosts.OPCODE_SWAPN`; pinned EELS `gas.py:237`. -/
  opcodeSwapn : Nat
  /-- `GasCosts.OPCODE_EXCHANGE`; pinned EELS `gas.py:238`. -/
  opcodeExchange : Nat
  /-- `GasCosts.OPCODE_TLOAD`; pinned EELS `gas.py:239`. -/
  opcodeTload : Nat
  /-- `GasCosts.OPCODE_TSTORE`; pinned EELS `gas.py:240`. -/
  opcodeTstore : Nat
  /-- `GasCosts.OPCODE_RETURNDATACOPY_BASE`; pinned EELS `gas.py:243`. -/
  opcodeReturnDataCopyBase : Nat
  /-- `GasCosts.OPCODE_RETURNDATACOPY_PER_WORD`; pinned EELS `gas.py:244`. -/
  opcodeReturnDataCopyPerWord : Nat
  /-- `GasCosts.OPCODE_CALLDATACOPY_BASE`; pinned EELS `gas.py:245`. -/
  opcodeCallDataCopyBase : Nat
  /-- `GasCosts.OPCODE_CODECOPY_BASE`; pinned EELS `gas.py:246`. -/
  opcodeCodeCopyBase : Nat
  /-- `GasCosts.OPCODE_MCOPY_BASE`; pinned EELS `gas.py:247`. -/
  opcodeMcopyBase : Nat
  /-- `GasCosts.OPCODE_MLOAD_BASE`; pinned EELS `gas.py:248`. -/
  opcodeMloadBase : Nat
  /-- `GasCosts.OPCODE_MSTORE_BASE`; pinned EELS `gas.py:249`. -/
  opcodeMstoreBase : Nat
  /-- `GasCosts.OPCODE_MSTORE8_BASE`; pinned EELS `gas.py:250`. -/
  opcodeMstore8Base : Nat
  /-- `GasCosts.OPCODE_COPY_PER_WORD`; pinned EELS `gas.py:251`. -/
  opcodeCopyPerWord : Nat
  /-- `GasCosts.OPCODE_EXP_BASE`; pinned EELS `gas.py:252`. -/
  opcodeExpBase : Nat
  /-- `GasCosts.OPCODE_EXP_PER_BYTE`; pinned EELS `gas.py:253`. -/
  opcodeExpPerByte : Nat
  /-- `GasCosts.OPCODE_KECCAK256_BASE`; pinned EELS `gas.py:254`. -/
  opcodeKeccak256Base : Nat
  /-- `GasCosts.OPCODE_KECCAK256_PER_WORD`; pinned EELS `gas.py:255`. -/
  opcodeKeccak256PerWord : Nat
  /-- `GasCosts.OPCODE_LOG_BASE`; pinned EELS `gas.py:256`. -/
  opcodeLogBase : Nat
  /-- `GasCosts.OPCODE_LOG_DATA_PER_BYTE`; pinned EELS `gas.py:257`. -/
  opcodeLogDataPerByte : Nat
  /-- `GasCosts.OPCODE_LOG_TOPIC`; pinned EELS `gas.py:258`. -/
  opcodeLogTopic : Nat
  /-- `GasCosts.OPCODE_SELFDESTRUCT_BASE`; pinned EELS `gas.py:259`. -/
  opcodeSelfDestructBase : Nat
  /-- Pairing base cost (literal `37700`);
  pinned EELS `bls12_381/bls12_381_pairing.py:46`. -/
  blsPairingBase : Nat
  /-- Per-pair cost (literal `32600`);
  pinned EELS `bls12_381/bls12_381_pairing.py:46`. -/
  blsPairingPerPair : Nat
  /-- `G1_K_DISCOUNT`; pinned EELS `bls12_381/__init__.py:37`. -/
  blsG1KDiscount : Array Nat
  /-- `G2_K_DISCOUNT`; pinned EELS `bls12_381/__init__.py:168`. -/
  blsG2KDiscount : Array Nat
  /-- `G1_MAX_DISCOUNT`; pinned EELS `bls12_381/__init__.py:299`. -/
  blsG1MaxDiscount : Nat
  /-- `G2_MAX_DISCOUNT`; pinned EELS `bls12_381/__init__.py:300`. -/
  blsG2MaxDiscount : Nat
  /-- `MULTIPLIER`; pinned EELS `bls12_381/__init__.py:301`. -/
  blsMultiplier : Nat

/-- Equality of all 144 public projections determines actual record equality. -/
theorem GasCosts.ext (a b : GasCosts)
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
  cases a
  cases b
  congr 1 <;> assumption

/-- Reconstructing all 144 projections returns the actual record. -/
theorem GasCosts.eta (c : GasCosts) :
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
  cases c
  rfl

end STFSpec.Vm.Core
