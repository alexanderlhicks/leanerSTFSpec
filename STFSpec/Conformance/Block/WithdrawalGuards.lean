/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block

/-!
# Complete raw withdrawal controls

Library `EthConformance`. Interpreted guards compare all three unsigned words and
all twenty address bytes. These controls check storage, without a codec or source run.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3–4.
-/

namespace STFSpec.Conformance.Block.WithdrawalGuards

open STFSpec.Base STFSpec.Block

private def observe (w : Withdrawal) : Nat × Nat × List Nat × Nat :=
  (w.index.toNat, w.validatorIndex.toNat, w.address.toBytes.toList.map UInt8.toNat, w.amount.toNat)

private def sample : Withdrawal :=
  Withdrawal.mk (U64.ofNat 17) (U64.ofNat 29)
    (Address.ofNat 0x000102030405060708090a0b0c0d0e0f10111213) (U64.ofNat 43)

#guard observe sample ==
  (17, 29, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19], 43)
#guard observe (Withdrawal.mk U64.zero U64.zero (Address.ofNat 0) U64.zero) ==
  (0, 0, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 0)
#guard observe (Withdrawal.mk U64.max U64.max (Address.ofNat (2 ^ 160 - 1)) U64.max) ==
  (18446744073709551615, 18446744073709551615,
    [255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255],
    18446744073709551615)
#guard observe (Withdrawal.mk U64.zero U64.max
    (Address.ofNat 0x131211100f0e0d0c0b0a09080706050403020100) (U64.ofNat 1)) ==
  (0, 18446744073709551615,
    [19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0], 1)
#guard observe (Withdrawal.mk U64.max (U64.ofNat 1) (Address.ofNat 0) U64.zero) ==
  (18446744073709551615, 1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 0)
#guard observe (Withdrawal.mk (U64.ofNat 1) U64.zero (Address.ofNat 0) U64.max) ==
  (1, 0, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 18446744073709551615)

#guard observe { sample with index := U64.max } ==
  (18446744073709551615, 29,
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19], 43)
#guard observe { sample with validatorIndex := U64.zero } ==
  (17, 0, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19], 43)
#guard observe
    { sample with address := Address.ofNat 0x131211100f0e0d0c0b0a09080706050403020100 } ==
  (17, 29, [19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0], 43)
#guard observe { sample with amount := U64.max } ==
  (17, 29, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19],
    18446744073709551615)

#guard observe (Withdrawal.mk (U64.ofNat 17) (U64.ofNat 29)
    (Address.ofNat 0x8000000000000000000000000000000000000000) (U64.ofNat 43)) ==
  (17, 29, [128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 43)
#guard observe (Withdrawal.mk (U64.ofNat 17) (U64.ofNat 29)
    (Address.ofNat 0x0080000000000000000000000000000000000000) (U64.ofNat 43)) ==
  (17, 29, [0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 43)
#guard observe (Withdrawal.mk (U64.ofNat 17) (U64.ofNat 29)
    (Address.ofNat 0x0000800000000000000000000000000000000000) (U64.ofNat 43)) ==
  (17, 29, [0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 43)
#guard observe (Withdrawal.mk (U64.ofNat 17) (U64.ofNat 29)
    (Address.ofNat 0x0000008000000000000000000000000000000000) (U64.ofNat 43)) ==
  (17, 29, [0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 43)
#guard observe (Withdrawal.mk (U64.ofNat 17) (U64.ofNat 29)
    (Address.ofNat 0x0000000080000000000000000000000000000000) (U64.ofNat 43)) ==
  (17, 29, [0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 43)
#guard observe (Withdrawal.mk (U64.ofNat 17) (U64.ofNat 29)
    (Address.ofNat 0x0000000000800000000000000000000000000000) (U64.ofNat 43)) ==
  (17, 29, [0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 43)
#guard observe (Withdrawal.mk (U64.ofNat 17) (U64.ofNat 29)
    (Address.ofNat 0x0000000000008000000000000000000000000000) (U64.ofNat 43)) ==
  (17, 29, [0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 43)
#guard observe (Withdrawal.mk (U64.ofNat 17) (U64.ofNat 29)
    (Address.ofNat 0x0000000000000080000000000000000000000000) (U64.ofNat 43)) ==
  (17, 29, [0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 43)
#guard observe (Withdrawal.mk (U64.ofNat 17) (U64.ofNat 29)
    (Address.ofNat 0x0000000000000000800000000000000000000000) (U64.ofNat 43)) ==
  (17, 29, [0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 43)
#guard observe (Withdrawal.mk (U64.ofNat 17) (U64.ofNat 29)
    (Address.ofNat 0x0000000000000000008000000000000000000000) (U64.ofNat 43)) ==
  (17, 29, [0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 43)
#guard observe (Withdrawal.mk (U64.ofNat 17) (U64.ofNat 29)
    (Address.ofNat 0x0000000000000000000080000000000000000000) (U64.ofNat 43)) ==
  (17, 29, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0], 43)
#guard observe (Withdrawal.mk (U64.ofNat 17) (U64.ofNat 29)
    (Address.ofNat 0x0000000000000000000000800000000000000000) (U64.ofNat 43)) ==
  (17, 29, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0], 43)
#guard observe (Withdrawal.mk (U64.ofNat 17) (U64.ofNat 29)
    (Address.ofNat 0x0000000000000000000000008000000000000000) (U64.ofNat 43)) ==
  (17, 29, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0], 43)
#guard observe (Withdrawal.mk (U64.ofNat 17) (U64.ofNat 29)
    (Address.ofNat 0x0000000000000000000000000080000000000000) (U64.ofNat 43)) ==
  (17, 29, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0], 43)
#guard observe (Withdrawal.mk (U64.ofNat 17) (U64.ofNat 29)
    (Address.ofNat 0x0000000000000000000000000000800000000000) (U64.ofNat 43)) ==
  (17, 29, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0], 43)
#guard observe (Withdrawal.mk (U64.ofNat 17) (U64.ofNat 29)
    (Address.ofNat 0x0000000000000000000000000000008000000000) (U64.ofNat 43)) ==
  (17, 29, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0], 43)
#guard observe (Withdrawal.mk (U64.ofNat 17) (U64.ofNat 29)
    (Address.ofNat 0x0000000000000000000000000000000080000000) (U64.ofNat 43)) ==
  (17, 29, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0], 43)
#guard observe (Withdrawal.mk (U64.ofNat 17) (U64.ofNat 29)
    (Address.ofNat 0x0000000000000000000000000000000000800000) (U64.ofNat 43)) ==
  (17, 29, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0], 43)
#guard observe (Withdrawal.mk (U64.ofNat 17) (U64.ofNat 29)
    (Address.ofNat 0x0000000000000000000000000000000000008000) (U64.ofNat 43)) ==
  (17, 29, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0], 43)
#guard observe (Withdrawal.mk (U64.ofNat 17) (U64.ofNat 29)
    (Address.ofNat 0x0000000000000000000000000000000000000080) (U64.ofNat 43)) ==
  (17, 29, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128], 43)

end STFSpec.Conformance.Block.WithdrawalGuards
