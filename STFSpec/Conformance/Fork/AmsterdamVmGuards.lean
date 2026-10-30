/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Fork

/-!
# Amsterdam VM complete value controls

Library `EthConformance`. Expected values come from the independently frozen
pinned-source catalogue, not evaluation of the Lean definitions.
Spec guidance: `STFSpec/informal/modules/EthFork.md` §§3–4.
-/

open STFSpec STFSpec.Fork.Amsterdam

#guard gasCosts.base == 2
#guard gasCosts.veryLow == 3
#guard gasCosts.low == 5
#guard gasCosts.mid == 8
#guard gasCosts.high == 10
#guard gasCosts.warmAccess == 100
#guard gasCosts.coldAccountAccess == 3000
#guard gasCosts.coldStorageAccess == 2100
#guard gasCosts.storageWrite == 10000
#guard gasCosts.callStipend == 2300
#guard gasCosts.accountWrite == 9000
#guard gasCosts.callValue == 11300
#guard gasCosts.codeInitPerWord == 2
#guard gasCosts.createAccess == 12000
#guard gasCosts.zero == 0
#guard gasCosts.memoryPerWord == 3
#guard gasCosts.fastStep == 5
#guard gasCosts.refundStorageClear == 11616
#guard gasCosts.precompileEcrecover == 3000
#guard gasCosts.precompileP256Verify == 6900
#guard gasCosts.precompileSha256Base == 60
#guard gasCosts.precompileSha256PerWord == 12
#guard gasCosts.precompileRipemd160Base == 600
#guard gasCosts.precompileRipemd160PerWord == 120
#guard gasCosts.precompileIdentityBase == 15
#guard gasCosts.precompileIdentityPerWord == 3
#guard gasCosts.precompileBlake2FPerRound == 1
#guard gasCosts.precompilePointEvaluation == 50000
#guard gasCosts.precompileBlsG1Add == 375
#guard gasCosts.precompileBlsG1Mul == 12000
#guard gasCosts.precompileBlsG1Map == 5500
#guard gasCosts.precompileBlsG2Add == 600
#guard gasCosts.precompileBlsG2Mul == 22500
#guard gasCosts.precompileBlsG2Map == 23800
#guard gasCosts.precompileEcAdd == 150
#guard gasCosts.precompileEcMul == 6000
#guard gasCosts.precompileEcPairingBase == 45000
#guard gasCosts.precompileEcPairingPerPoint == 34000
#guard gasCosts.perBlob.toNat == 131072
#guard gasCosts.blobScheduleTarget.toNat == 14
#guard gasCosts.blobTargetGasPerBlock.toNat == 1835008
#guard gasCosts.blobBaseCost == 8192
#guard gasCosts.blobScheduleMax.toNat == 21
#guard gasCosts.blobMinGasPrice == 1
#guard gasCosts.blobBaseFeeUpdateFraction == 11684671
#guard gasCosts.blockAccessListItem == 2000
#guard gasCosts.txBase == 12000
#guard gasCosts.txValueCost == 6000
#guard gasCosts.txDataTokenStandard == 4
#guard gasCosts.txDataTokenFloor == 16
#guard gasCosts.txAccessListAddress == 2900
#guard gasCosts.txAccessListStorageKey == 2000
#guard gasCosts.txMaxGasLimit == 16777216
#guard gasCosts.txMaxTotalGasLimit == 4294967295
#guard gasCosts.authTupleBytes == 101
#guard gasCosts.executionPerAuthBaseCost == 7816
#guard gasCosts.limitAdjustmentFactor == 1024
#guard gasCosts.limitMinimum == 5000
#guard gasCosts.opcodeAdd == 3
#guard gasCosts.opcodeSub == 3
#guard gasCosts.opcodeMul == 5
#guard gasCosts.opcodeDiv == 5
#guard gasCosts.opcodeSdiv == 5
#guard gasCosts.opcodeMod == 5
#guard gasCosts.opcodeSmod == 5
#guard gasCosts.opcodeAddmod == 8
#guard gasCosts.opcodeMulmod == 8
#guard gasCosts.opcodeSignextend == 5
#guard gasCosts.opcodeLt == 3
#guard gasCosts.opcodeGt == 3
#guard gasCosts.opcodeSlt == 3
#guard gasCosts.opcodeSgt == 3
#guard gasCosts.opcodeEq == 3
#guard gasCosts.opcodeIsZero == 3
#guard gasCosts.opcodeAnd == 3
#guard gasCosts.opcodeOr == 3
#guard gasCosts.opcodeXor == 3
#guard gasCosts.opcodeNot == 3
#guard gasCosts.opcodeByte == 3
#guard gasCosts.opcodeShl == 3
#guard gasCosts.opcodeShr == 3
#guard gasCosts.opcodeSar == 3
#guard gasCosts.opcodeClz == 5
#guard gasCosts.opcodeJump == 8
#guard gasCosts.opcodeJumpi == 10
#guard gasCosts.opcodeJumpDest == 1
#guard gasCosts.opcodeCallDataLoad == 3
#guard gasCosts.opcodeBlockHash == 20
#guard gasCosts.opcodeCoinbase == 2
#guard gasCosts.opcodePop == 2
#guard gasCosts.opcodeMsize == 2
#guard gasCosts.opcodePc == 2
#guard gasCosts.opcodeGas == 2
#guard gasCosts.opcodeAddress == 2
#guard gasCosts.opcodeOrigin == 2
#guard gasCosts.opcodeCaller == 2
#guard gasCosts.opcodeCallValue == 2
#guard gasCosts.opcodeCallDataSize == 2
#guard gasCosts.opcodeCodeSize == 2
#guard gasCosts.opcodeGasPrice == 2
#guard gasCosts.opcodeTimestamp == 2
#guard gasCosts.opcodeNumber == 2
#guard gasCosts.opcodeGasLimit == 2
#guard gasCosts.opcodePrevRandao == 2
#guard gasCosts.opcodeReturnDataSize == 2
#guard gasCosts.opcodeChainId == 2
#guard gasCosts.opcodeSelfBalance == 5
#guard gasCosts.opcodeBaseFee == 2
#guard gasCosts.opcodeBlobBaseFee == 2
#guard gasCosts.opcodeSlotNum == 2
#guard gasCosts.opcodeBlobHash == 3
#guard gasCosts.opcodePush == 3
#guard gasCosts.opcodePush0 == 2
#guard gasCosts.opcodeDup == 3
#guard gasCosts.opcodeSwap == 3
#guard gasCosts.opcodeDupn == 3
#guard gasCosts.opcodeSwapn == 3
#guard gasCosts.opcodeExchange == 3
#guard gasCosts.opcodeTload == 100
#guard gasCosts.opcodeTstore == 100
#guard gasCosts.opcodeReturnDataCopyBase == 3
#guard gasCosts.opcodeReturnDataCopyPerWord == 3
#guard gasCosts.opcodeCallDataCopyBase == 3
#guard gasCosts.opcodeCodeCopyBase == 3
#guard gasCosts.opcodeMcopyBase == 3
#guard gasCosts.opcodeMloadBase == 3
#guard gasCosts.opcodeMstoreBase == 3
#guard gasCosts.opcodeMstore8Base == 3
#guard gasCosts.opcodeCopyPerWord == 3
#guard gasCosts.opcodeExpBase == 10
#guard gasCosts.opcodeExpPerByte == 50
#guard gasCosts.opcodeKeccak256Base == 30
#guard gasCosts.opcodeKeccak256PerWord == 6
#guard gasCosts.opcodeLogBase == 375
#guard gasCosts.opcodeLogDataPerByte == 8
#guard gasCosts.opcodeLogTopic == 375
#guard gasCosts.opcodeSelfDestructBase == 5000
#guard gasCosts.blsPairingBase == 37700
#guard gasCosts.blsPairingPerPair == 32600
#guard gasCosts.blsG1KDiscount == #[
  1000, 949, 848, 797, 764, 750, 738, 728, 719, 712, 705, 698, 692, 687, 682, 677,
  673, 669, 665, 661, 658, 654, 651, 648, 645, 642, 640, 637, 635, 632, 630, 627,
  625, 623, 621, 619, 617, 615, 613, 611, 609, 608, 606, 604, 603, 601, 599, 598,
  596, 595, 593, 592, 591, 589, 588, 586, 585, 584, 582, 581, 580, 579, 577, 576,
  575, 574, 573, 572, 570, 569, 568, 567, 566, 565, 564, 563, 562, 561, 560, 559,
  558, 557, 556, 555, 554, 553, 552, 551, 550, 549, 548, 547, 547, 546, 545, 544,
  543, 542, 541, 540, 540, 539, 538, 537, 536, 536, 535, 534, 533, 532, 532, 531,
  530, 529, 528, 528, 527, 526, 525, 525, 524, 523, 522, 522, 521, 520, 520, 519
  ]
#guard gasCosts.blsG2KDiscount == #[
  1000, 1000, 923, 884, 855, 832, 812, 796, 782, 770, 759, 749, 740, 732, 724, 717,
  711, 704, 699, 693, 688, 683, 679, 674, 670, 666, 663, 659, 655, 652, 649, 646,
  643, 640, 637, 634, 632, 629, 627, 624, 622, 620, 618, 615, 613, 611, 609, 607,
  606, 604, 602, 600, 598, 597, 595, 593, 592, 590, 589, 587, 586, 584, 583, 582,
  580, 579, 578, 576, 575, 574, 573, 571, 570, 569, 568, 567, 566, 565, 563, 562,
  561, 560, 559, 558, 557, 556, 555, 554, 553, 552, 552, 551, 550, 549, 548, 547,
  546, 545, 545, 544, 543, 542, 541, 541, 540, 539, 538, 537, 537, 536, 535, 535,
  534, 533, 532, 532, 531, 530, 530, 529, 528, 528, 527, 526, 526, 525, 524, 524
  ]
#guard gasCosts.blsG1MaxDiscount == 519
#guard gasCosts.blsG2MaxDiscount == 524
#guard gasCosts.blsMultiplier == 1000
#guard stateGasCosts.costPerStateByte == 1530
#guard stateGasCosts.bytesPerNewAccount == 120
#guard stateGasCosts.bytesPerStorageSet == 64
#guard stateGasCosts.bytesPerAuthBase == 23
#guard vmLimits.stackDepthLimit == 1024
#guard vmLimits.maxCodeSize == 65536
#guard vmLimits.maxInitCodeSize == 131072

private theorem complete_grouping :
    vmConfig = Vm.Core.VmConfig.mk gasCosts stateGasCosts vmLimits := rfl

private theorem depth_literal : vmConfig.limits.stackDepthLimit = 1024 := rfl

private theorem init_code_dependency :
    vmConfig.limits.maxInitCodeSize = 2 * vmConfig.limits.maxCodeSize := rfl

-- Concrete checked-U64 correspondence uses only public construction/observer laws.
private theorem perBlob_range : (131072 : Nat) < 2 ^ 64 := by decide

private theorem perBlob_exact : gasCosts.perBlob.toNat = 131072 := by
  exact Base.U64.toNat_ofNat_of_lt perBlob_range

private theorem blobScheduleTarget_range : (14 : Nat) < 2 ^ 64 := by decide

private theorem blobScheduleTarget_exact : gasCosts.blobScheduleTarget.toNat = 14 := by
  exact Base.U64.toNat_ofNat_of_lt blobScheduleTarget_range

private theorem blobTargetGasPerBlock_range : (1835008 : Nat) < 2 ^ 64 := by decide

private theorem blobTargetGasPerBlock_exact : gasCosts.blobTargetGasPerBlock.toNat = 1835008 := by
  change (Base.U64.wrappingMul gasCosts.perBlob gasCosts.blobScheduleTarget).toNat = _
  rw [Base.U64.toNat_wrappingMul]
  rw [perBlob_exact, blobScheduleTarget_exact]

private theorem blobScheduleMax_range : (21 : Nat) < 2 ^ 64 := by decide

private theorem blobScheduleMax_exact : gasCosts.blobScheduleMax.toNat = 21 := by
  exact Base.U64.toNat_ofNat_of_lt blobScheduleMax_range

private theorem blob_product_checked :
    Base.U64.checkedMul gasCosts.perBlob gasCosts.blobScheduleTarget =
      some gasCosts.blobTargetGasPerBlock := by
  apply (Base.U64.checkedMul_eq_some_iff _ _ _).mpr
  rw [perBlob_exact, blobScheduleTarget_exact, blobTargetGasPerBlock_exact]
  exact ⟨by decide, rfl⟩

-- Public-import clients retain complete records and specialize existing Core consumers.
private theorem public_records :
    vmConfig.costs = gasCosts ∧ vmConfig.stateCosts = stateGasCosts ∧
      vmConfig.limits = vmLimits := ⟨rfl, rfl, rfl⟩
