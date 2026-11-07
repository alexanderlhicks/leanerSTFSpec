/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless

/-!
# Complete raw execution-request controls

Library `EthConformance`. Private controls inspect complete byte/word tuples,
including independent updates, all byte positions, zero and maximum words.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Stateless.RequestItemsGuards

open STFSpec.Base STFSpec.Stateless

private def fixed (n : Nat) (xs : List UInt8) (h : xs.length = n) : FixedBytes n :=
  (FixedBytes.ofBytes? (Bytes.ofList xs)).get (by
    apply Option.isSome_iff_ne_none.mpr
    intro hn
    exact FixedBytes.ofBytes?_eq_none_iff.mp hn (by rw [Bytes.size_ofList, h]))

private def address (xs : List UInt8) (h : xs.length = 20) : Address :=
  (Address.ofBytes? (Bytes.ofList xs)).get (by
    apply Option.isSome_iff_ne_none.mpr
    intro hn
    exact Address.ofBytes?_eq_none_iff.mp hn (by rw [Bytes.size_ofList, h]))

private def depositRequestObserve (r : DepositRequest) :
    List UInt8 × List UInt8 × Nat × List UInt8 × Nat :=
  (r.pubkey.toBytes.toList, r.withdrawalCredentials.toBytes.toList, r.amount.toNat,
    r.signature.toBytes.toList, r.index.toNat)

private def depositRequestPubkey : Bytes48 :=
  fixed 48 [0, 56, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170, 207, 244, 25, 62,
    99, 136, 173, 210, 247, 28, 65, 102, 139, 176, 213, 250, 31, 68, 105, 142,
    179, 216, 253, 34, 71, 108, 145, 182, 219, 0, 37, 74, 111, 148, 185, 0] (by decide)

private def depositRequestWithdrawalCredentials : Bytes32 :=
  fixed 32 [0, 75, 112, 149, 186, 223, 4, 41, 78, 115, 152, 189, 226, 7, 44, 81,
    118, 155, 192, 229, 10, 47, 84, 121, 158, 195, 232, 13, 50, 87, 124, 0] (by decide)

private def depositRequestSignature : Bytes96 :=
  fixed 96 [0, 94, 131, 168, 205, 242, 23, 60, 97, 134, 171, 208, 245, 26, 63, 100,
    137, 174, 211, 248, 29, 66, 103, 140, 177, 214, 251, 32, 69, 106, 143, 180,
    217, 254, 35, 72, 109, 146, 183, 220, 1, 38, 75, 112, 149, 186, 223, 4,
    41, 78, 115, 152, 189, 226, 7, 44, 81, 118, 155, 192, 229, 10, 47, 84,
    121, 158, 195, 232, 13, 50, 87, 124, 161, 198, 235, 16, 53, 90, 127, 164,
    201, 238, 19, 56, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170, 207, 0] (by decide)

private def depositRequest : DepositRequest :=
  ⟨depositRequestPubkey, depositRequestWithdrawalCredentials, U64.ofNat 72623859790382856,
    depositRequestSignature, U64.ofNat 9255003132036915216⟩

#guard depositRequestObserve depositRequest ==
  ([0, 56, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170, 207, 244, 25, 62,
    99, 136, 173, 210, 247, 28, 65, 102, 139, 176, 213, 250, 31, 68, 105, 142,
    179, 216, 253, 34, 71, 108, 145, 182, 219, 0, 37, 74, 111, 148, 185, 0],
    [0, 75, 112, 149, 186, 223, 4, 41, 78, 115, 152, 189, 226, 7, 44, 81,
    118, 155, 192, 229, 10, 47, 84, 121, 158, 195, 232, 13, 50, 87, 124, 0],
    72623859790382856,
    [0, 94, 131, 168, 205, 242, 23, 60, 97, 134, 171, 208, 245, 26, 63, 100,
    137, 174, 211, 248, 29, 66, 103, 140, 177, 214, 251, 32, 69, 106, 143, 180,
    217, 254, 35, 72, 109, 146, 183, 220, 1, 38, 75, 112, 149, 186, 223, 4,
    41, 78, 115, 152, 189, 226, 7, 44, 81, 118, 155, 192, 229, 10, 47, 84,
    121, 158, 195, 232, 13, 50, 87, 124, 161, 198, 235, 16, 53, 90, 127, 164,
    201, 238, 19, 56, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170, 207, 0],
    9255003132036915216)

#guard depositRequestObserve (DepositRequest.mk
  (fixed 48 (List.replicate 48 0) (by decide))
  (fixed 32 (List.replicate 32 0) (by decide))
  (U64.zero)
  (fixed 96 (List.replicate 96 0) (by decide))
  (U64.zero)) ==
  (List.replicate 48 0,
    List.replicate 32 0,
    0,
    List.replicate 96 0,
    0)

#guard depositRequestObserve (DepositRequest.mk
  (fixed 48 (List.replicate 48 255) (by decide))
  (fixed 32 (List.replicate 32 255) (by decide))
  (U64.max)
  (fixed 96 (List.replicate 96 255) (by decide))
  (U64.max)) ==
  (List.replicate 48 255,
    List.replicate 32 255,
    18446744073709551615,
    List.replicate 96 255,
    18446744073709551615)

#guard depositRequestObserve { depositRequest with pubkey := FixedBytes.ofNat 0 } ==
  (List.replicate 48 0,
    [0, 75, 112, 149, 186, 223, 4, 41, 78, 115, 152, 189, 226, 7, 44, 81,
    118, 155, 192, 229, 10, 47, 84, 121, 158, 195, 232, 13, 50, 87, 124, 0],
    72623859790382856,
    [0, 94, 131, 168, 205, 242, 23, 60, 97, 134, 171, 208, 245, 26, 63, 100,
    137, 174, 211, 248, 29, 66, 103, 140, 177, 214, 251, 32, 69, 106, 143, 180,
    217, 254, 35, 72, 109, 146, 183, 220, 1, 38, 75, 112, 149, 186, 223, 4,
    41, 78, 115, 152, 189, 226, 7, 44, 81, 118, 155, 192, 229, 10, 47, 84,
    121, 158, 195, 232, 13, 50, 87, 124, 161, 198, 235, 16, 53, 90, 127, 164,
    201, 238, 19, 56, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170, 207, 0],
    9255003132036915216)

#guard depositRequestObserve { depositRequest with withdrawalCredentials := FixedBytes.ofNat 0 } ==
  ([0, 56, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170, 207, 244, 25, 62,
    99, 136, 173, 210, 247, 28, 65, 102, 139, 176, 213, 250, 31, 68, 105, 142,
    179, 216, 253, 34, 71, 108, 145, 182, 219, 0, 37, 74, 111, 148, 185, 0],
    List.replicate 32 0,
    72623859790382856,
    [0, 94, 131, 168, 205, 242, 23, 60, 97, 134, 171, 208, 245, 26, 63, 100,
    137, 174, 211, 248, 29, 66, 103, 140, 177, 214, 251, 32, 69, 106, 143, 180,
    217, 254, 35, 72, 109, 146, 183, 220, 1, 38, 75, 112, 149, 186, 223, 4,
    41, 78, 115, 152, 189, 226, 7, 44, 81, 118, 155, 192, 229, 10, 47, 84,
    121, 158, 195, 232, 13, 50, 87, 124, 161, 198, 235, 16, 53, 90, 127, 164,
    201, 238, 19, 56, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170, 207, 0],
    9255003132036915216)

#guard (depositRequest.amount.toBitVec).toNat == 72623859790382856
#guard depositRequestObserve { depositRequest with amount := U64.ofNat 0 } ==
  ([0, 56, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170, 207, 244, 25, 62,
    99, 136, 173, 210, 247, 28, 65, 102, 139, 176, 213, 250, 31, 68, 105, 142,
    179, 216, 253, 34, 71, 108, 145, 182, 219, 0, 37, 74, 111, 148, 185, 0],
    [0, 75, 112, 149, 186, 223, 4, 41, 78, 115, 152, 189, 226, 7, 44, 81,
    118, 155, 192, 229, 10, 47, 84, 121, 158, 195, 232, 13, 50, 87, 124, 0],
    0,
    [0, 94, 131, 168, 205, 242, 23, 60, 97, 134, 171, 208, 245, 26, 63, 100,
    137, 174, 211, 248, 29, 66, 103, 140, 177, 214, 251, 32, 69, 106, 143, 180,
    217, 254, 35, 72, 109, 146, 183, 220, 1, 38, 75, 112, 149, 186, 223, 4,
    41, 78, 115, 152, 189, 226, 7, 44, 81, 118, 155, 192, 229, 10, 47, 84,
    121, 158, 195, 232, 13, 50, 87, 124, 161, 198, 235, 16, 53, 90, 127, 164,
    201, 238, 19, 56, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170, 207, 0],
    9255003132036915216)

#guard depositRequestObserve { depositRequest with signature := FixedBytes.ofNat 0 } ==
  ([0, 56, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170, 207, 244, 25, 62,
    99, 136, 173, 210, 247, 28, 65, 102, 139, 176, 213, 250, 31, 68, 105, 142,
    179, 216, 253, 34, 71, 108, 145, 182, 219, 0, 37, 74, 111, 148, 185, 0],
    [0, 75, 112, 149, 186, 223, 4, 41, 78, 115, 152, 189, 226, 7, 44, 81,
    118, 155, 192, 229, 10, 47, 84, 121, 158, 195, 232, 13, 50, 87, 124, 0],
    72623859790382856,
    List.replicate 96 0,
    9255003132036915216)

#guard (depositRequest.index.toBitVec).toNat == 9255003132036915216
#guard depositRequestObserve { depositRequest with index := U64.ofNat 0 } ==
  ([0, 56, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170, 207, 244, 25, 62,
    99, 136, 173, 210, 247, 28, 65, 102, 139, 176, 213, 250, 31, 68, 105, 142,
    179, 216, 253, 34, 71, 108, 145, 182, 219, 0, 37, 74, 111, 148, 185, 0],
    [0, 75, 112, 149, 186, 223, 4, 41, 78, 115, 152, 189, 226, 7, 44, 81,
    118, 155, 192, 229, 10, 47, 84, 121, 158, 195, 232, 13, 50, 87, 124, 0],
    72623859790382856,
    [0, 94, 131, 168, 205, 242, 23, 60, 97, 134, 171, 208, 245, 26, 63, 100,
    137, 174, 211, 248, 29, 66, 103, 140, 177, 214, 251, 32, 69, 106, 143, 180,
    217, 254, 35, 72, 109, 146, 183, 220, 1, 38, 75, 112, 149, 186, 223, 4,
    41, 78, 115, 152, 189, 226, 7, 44, 81, 118, 155, 192, 229, 10, 47, 84,
    121, 158, 195, 232, 13, 50, 87, 124, 161, 198, 235, 16, 53, 90, 127, 164,
    201, 238, 19, 56, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170, 207, 0],
    0)

#guard ((List.range 48).map (fun i ↦ (i, depositRequest.pubkey.toBytes.toList[i]?))) ==
  [(0, some 0), (1, some 56), (2, some 93), (3, some 130), (4, some 167), (5, some 204), (6, some
    241), (7, some 22), (8, some 59), (9, some 96), (10, some 133), (11, some 170), (12, some 207),
    (13, some 244), (14, some 25), (15, some 62),
    (16, some 99), (17, some 136), (18, some 173), (19, some 210), (20, some 247), (21, some 28),
      (22, some 65), (23, some 102), (24, some 139), (25, some 176), (26, some 213),
      (27, some 250), (28, some 31), (29, some 68), (30, some 105), (31, some 142),
    (32, some 179), (33, some 216), (34, some 253), (35, some 34), (36, some 71), (37, some 108),
      (38, some 145), (39, some 182), (40, some 219), (41, some 0), (42, some 37), (43, some 74),
      (44, some 111), (45, some 148), (46, some 185), (47, some 0)]

#guard ((List.range 32).map
    (fun i ↦ (i, depositRequest.withdrawalCredentials.toBytes.toList[i]?))) ==
  [(0, some 0), (1, some 75), (2, some 112), (3, some 149), (4, some 186), (5, some 223), (6, some
    4), (7, some 41), (8, some 78), (9, some 115), (10, some 152), (11, some 189), (12, some 226),
    (13, some 7), (14, some 44), (15, some 81),
    (16, some 118), (17, some 155), (18, some 192), (19, some 229), (20, some 10), (21, some 47),
      (22, some 84), (23, some 121), (24, some 158), (25, some 195), (26, some 232), (27, some 13),
      (28, some 50), (29, some 87), (30, some 124), (31, some 0)]

#guard ((List.range 96).map (fun i ↦ (i, depositRequest.signature.toBytes.toList[i]?))) ==
  [(0, some 0), (1, some 94), (2, some 131), (3, some 168), (4, some 205), (5, some 242), (6, some
    23), (7, some 60), (8, some 97), (9, some 134), (10, some 171), (11, some 208), (12, some 245),
    (13, some 26), (14, some 63), (15, some 100),
    (16, some 137), (17, some 174), (18, some 211), (19, some 248), (20, some 29), (21, some 66),
      (22, some 103), (23, some 140), (24, some 177), (25, some 214), (26, some 251),
      (27, some 32), (28, some 69), (29, some 106), (30, some 143), (31, some 180),
    (32, some 217), (33, some 254), (34, some 35), (35, some 72), (36, some 109), (37, some 146),
      (38, some 183), (39, some 220), (40, some 1), (41, some 38), (42, some 75), (43, some 112),
      (44, some 149), (45, some 186), (46, some 223), (47, some 4),
    (48, some 41), (49, some 78), (50, some 115), (51, some 152), (52, some 189), (53, some 226),
      (54, some 7), (55, some 44), (56, some 81), (57, some 118), (58, some 155), (59, some 192),
      (60, some 229), (61, some 10), (62, some 47), (63, some 84),
    (64, some 121), (65, some 158), (66, some 195), (67, some 232), (68, some 13), (69, some 50),
      (70, some 87), (71, some 124), (72, some 161), (73, some 198), (74, some 235), (75, some 16),
      (76, some 53), (77, some 90), (78, some 127), (79, some 164),
    (80, some 201), (81, some 238), (82, some 19), (83, some 56), (84, some 93), (85, some 130),
      (86, some 167), (87, some 204), (88, some 241), (89, some 22), (90, some 59), (91, some 96),
      (92, some 133), (93, some 170), (94, some 207), (95, some 0)]

private def withdrawalRequestObserve (r : WithdrawalRequest) :
    List UInt8 × List UInt8 × Nat :=
  (r.sourceAddress.toBytes.toList, r.validatorPubkey.toBytes.toList, r.amount.toNat)

private def withdrawalRequestSourceAddress : Address :=
  address [0, 113, 150, 187, 224, 5, 42, 79, 116, 153, 190, 227, 8, 45, 82, 119,
    156, 193, 230, 0] (by decide)

private def withdrawalRequestValidatorPubkey : Bytes48 :=
  fixed 48 [0, 132, 169, 206, 243, 24, 61, 98, 135, 172, 209, 246, 27, 64, 101, 138,
    175, 212, 249, 30, 67, 104, 141, 178, 215, 252, 33, 70, 107, 144, 181, 218,
    255, 36, 73, 110, 147, 184, 221, 2, 39, 76, 113, 150, 187, 224, 5, 0] (by decide)

private def withdrawalRequest : WithdrawalRequest :=
  ⟨withdrawalRequestSourceAddress, withdrawalRequestValidatorPubkey,
    U64.ofNat 18446744073709551615⟩

#guard withdrawalRequestObserve withdrawalRequest ==
  ([0, 113, 150, 187, 224, 5, 42, 79, 116, 153, 190, 227, 8, 45, 82, 119,
    156, 193, 230, 0],
    [0, 132, 169, 206, 243, 24, 61, 98, 135, 172, 209, 246, 27, 64, 101, 138,
    175, 212, 249, 30, 67, 104, 141, 178, 215, 252, 33, 70, 107, 144, 181, 218,
    255, 36, 73, 110, 147, 184, 221, 2, 39, 76, 113, 150, 187, 224, 5, 0],
    18446744073709551615)

#guard withdrawalRequestObserve (WithdrawalRequest.mk
  (address (List.replicate 20 0) (by decide))
  (fixed 48 (List.replicate 48 0) (by decide))
  (U64.zero)) ==
  (List.replicate 20 0,
    List.replicate 48 0,
    0)

#guard withdrawalRequestObserve (WithdrawalRequest.mk
  (address (List.replicate 20 255) (by decide))
  (fixed 48 (List.replicate 48 255) (by decide))
  (U64.max)) ==
  (List.replicate 20 255,
    List.replicate 48 255,
    18446744073709551615)

#guard withdrawalRequestObserve { withdrawalRequest with sourceAddress := Address.ofNat 0 } ==
  (List.replicate 20 0,
    [0, 132, 169, 206, 243, 24, 61, 98, 135, 172, 209, 246, 27, 64, 101, 138,
    175, 212, 249, 30, 67, 104, 141, 178, 215, 252, 33, 70, 107, 144, 181, 218,
    255, 36, 73, 110, 147, 184, 221, 2, 39, 76, 113, 150, 187, 224, 5, 0],
    18446744073709551615)

#guard withdrawalRequestObserve { withdrawalRequest with validatorPubkey := FixedBytes.ofNat 0 } ==
  ([0, 113, 150, 187, 224, 5, 42, 79, 116, 153, 190, 227, 8, 45, 82, 119,
    156, 193, 230, 0],
    List.replicate 48 0,
    18446744073709551615)

#guard (withdrawalRequest.amount.toBitVec).toNat == 18446744073709551615
#guard withdrawalRequestObserve { withdrawalRequest with amount := U64.ofNat 0 } ==
  ([0, 113, 150, 187, 224, 5, 42, 79, 116, 153, 190, 227, 8, 45, 82, 119,
    156, 193, 230, 0],
    [0, 132, 169, 206, 243, 24, 61, 98, 135, 172, 209, 246, 27, 64, 101, 138,
    175, 212, 249, 30, 67, 104, 141, 178, 215, 252, 33, 70, 107, 144, 181, 218,
    255, 36, 73, 110, 147, 184, 221, 2, 39, 76, 113, 150, 187, 224, 5, 0],
    0)

#guard ((List.range 20).map (fun i ↦ (i, withdrawalRequest.sourceAddress.toBytes.toList[i]?))) ==
  [(0, some 0), (1, some 113), (2, some 150), (3, some 187), (4, some 224), (5, some 5), (6, some
    42), (7, some 79), (8, some 116), (9, some 153), (10, some 190), (11, some 227), (12, some 8),
    (13, some 45), (14, some 82), (15, some 119),
    (16, some 156), (17, some 193), (18, some 230), (19, some 0)]

private def consolidationRequestObserve (r : ConsolidationRequest) :
    List UInt8 × List UInt8 × List UInt8 :=
  (r.sourceAddress.toBytes.toList, r.sourcePubkey.toBytes.toList, r.targetPubkey.toBytes.toList)

private def consolidationRequestSourceAddress : Address :=
  address [0, 151, 188, 225, 6, 43, 80, 117, 154, 191, 228, 9, 46, 83, 120, 157,
    194, 231, 12, 0] (by decide)

private def consolidationRequestSourcePubkey : Bytes48 :=
  fixed 48 [0, 170, 207, 244, 25, 62, 99, 136, 173, 210, 247, 28, 65, 102, 139, 176,
    213, 250, 31, 68, 105, 142, 179, 216, 253, 34, 71, 108, 145, 182, 219, 0,
    37, 74, 111, 148, 185, 222, 3, 40, 77, 114, 151, 188, 225, 6, 43, 0] (by decide)

private def consolidationRequestTargetPubkey : Bytes48 :=
  fixed 48 [0, 189, 226, 7, 44, 81, 118, 155, 192, 229, 10, 47, 84, 121, 158, 195,
    232, 13, 50, 87, 124, 161, 198, 235, 16, 53, 90, 127, 164, 201, 238, 19,
    56, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170, 207, 244, 25, 62, 0] (by decide)

private def consolidationRequest : ConsolidationRequest :=
  ⟨consolidationRequestSourceAddress, consolidationRequestSourcePubkey,
    consolidationRequestTargetPubkey⟩

#guard consolidationRequestObserve consolidationRequest ==
  ([0, 151, 188, 225, 6, 43, 80, 117, 154, 191, 228, 9, 46, 83, 120, 157,
    194, 231, 12, 0],
    [0, 170, 207, 244, 25, 62, 99, 136, 173, 210, 247, 28, 65, 102, 139, 176,
    213, 250, 31, 68, 105, 142, 179, 216, 253, 34, 71, 108, 145, 182, 219, 0,
    37, 74, 111, 148, 185, 222, 3, 40, 77, 114, 151, 188, 225, 6, 43, 0],
    [0, 189, 226, 7, 44, 81, 118, 155, 192, 229, 10, 47, 84, 121, 158, 195,
    232, 13, 50, 87, 124, 161, 198, 235, 16, 53, 90, 127, 164, 201, 238, 19,
    56, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170, 207, 244, 25, 62, 0])

#guard consolidationRequestObserve (ConsolidationRequest.mk
  (address (List.replicate 20 0) (by decide))
  (fixed 48 (List.replicate 48 0) (by decide))
  (fixed 48 (List.replicate 48 0) (by decide))) ==
  (List.replicate 20 0,
    List.replicate 48 0,
    List.replicate 48 0)

#guard consolidationRequestObserve (ConsolidationRequest.mk
  (address (List.replicate 20 255) (by decide))
  (fixed 48 (List.replicate 48 255) (by decide))
  (fixed 48 (List.replicate 48 255) (by decide))) ==
  (List.replicate 20 255,
    List.replicate 48 255,
    List.replicate 48 255)

#guard consolidationRequestObserve
    { consolidationRequest with sourceAddress := Address.ofNat 0 } ==
  (List.replicate 20 0,
    [0, 170, 207, 244, 25, 62, 99, 136, 173, 210, 247, 28, 65, 102, 139, 176,
    213, 250, 31, 68, 105, 142, 179, 216, 253, 34, 71, 108, 145, 182, 219, 0,
    37, 74, 111, 148, 185, 222, 3, 40, 77, 114, 151, 188, 225, 6, 43, 0],
    [0, 189, 226, 7, 44, 81, 118, 155, 192, 229, 10, 47, 84, 121, 158, 195,
    232, 13, 50, 87, 124, 161, 198, 235, 16, 53, 90, 127, 164, 201, 238, 19,
    56, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170, 207, 244, 25, 62, 0])

#guard consolidationRequestObserve
    { consolidationRequest with sourcePubkey := FixedBytes.ofNat 0 } ==
  ([0, 151, 188, 225, 6, 43, 80, 117, 154, 191, 228, 9, 46, 83, 120, 157,
    194, 231, 12, 0],
    List.replicate 48 0,
    [0, 189, 226, 7, 44, 81, 118, 155, 192, 229, 10, 47, 84, 121, 158, 195,
    232, 13, 50, 87, 124, 161, 198, 235, 16, 53, 90, 127, 164, 201, 238, 19,
    56, 93, 130, 167, 204, 241, 22, 59, 96, 133, 170, 207, 244, 25, 62, 0])

#guard consolidationRequestObserve
    { consolidationRequest with targetPubkey := FixedBytes.ofNat 0 } ==
  ([0, 151, 188, 225, 6, 43, 80, 117, 154, 191, 228, 9, 46, 83, 120, 157,
    194, 231, 12, 0],
    [0, 170, 207, 244, 25, 62, 99, 136, 173, 210, 247, 28, 65, 102, 139, 176,
    213, 250, 31, 68, 105, 142, 179, 216, 253, 34, 71, 108, 145, 182, 219, 0,
    37, 74, 111, 148, 185, 222, 3, 40, 77, 114, 151, 188, 225, 6, 43, 0],
    List.replicate 48 0)

private def builderDepositRequestObserve (r : BuilderDepositRequest) :
    List UInt8 × List UInt8 × Nat × List UInt8 :=
  (r.pubkey.toBytes.toList, r.withdrawalCredentials.toBytes.toList, r.amount.toNat,
    r.signature.toBytes.toList)

private def builderDepositRequestPubkey : Bytes48 :=
  fixed 48 [0, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103, 140, 177, 214,
    251, 32, 69, 106, 143, 180, 217, 254, 35, 72, 109, 146, 183, 220, 1, 38,
    75, 112, 149, 186, 223, 4, 41, 78, 115, 152, 189, 226, 7, 44, 81, 0] (by decide)

private def builderDepositRequestWithdrawalCredentials : Bytes32 :=
  fixed 32 [0, 227, 8, 45, 82, 119, 156, 193, 230, 11, 48, 85, 122, 159, 196, 233,
    14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 239, 20, 0] (by decide)

private def builderDepositRequestSignature : Bytes96 :=
  fixed 96 [0, 246, 27, 64, 101, 138, 175, 212, 249, 30, 67, 104, 141, 178, 215, 252,
    33, 70, 107, 144, 181, 218, 255, 36, 73, 110, 147, 184, 221, 2, 39, 76,
    113, 150, 187, 224, 5, 42, 79, 116, 153, 190, 227, 8, 45, 82, 119, 156,
    193, 230, 11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236,
    17, 54, 91, 128, 165, 202, 239, 20, 57, 94, 131, 168, 205, 242, 23, 60,
    97, 134, 171, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103, 0] (by decide)

private def builderDepositRequest : BuilderDepositRequest :=
  ⟨builderDepositRequestPubkey, builderDepositRequestWithdrawalCredentials, U64.ofNat 0,
    builderDepositRequestSignature⟩

#guard builderDepositRequestObserve builderDepositRequest ==
  ([0, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103, 140, 177, 214,
    251, 32, 69, 106, 143, 180, 217, 254, 35, 72, 109, 146, 183, 220, 1, 38,
    75, 112, 149, 186, 223, 4, 41, 78, 115, 152, 189, 226, 7, 44, 81, 0],
    [0, 227, 8, 45, 82, 119, 156, 193, 230, 11, 48, 85, 122, 159, 196, 233,
    14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 239, 20, 0],
    0,
    [0, 246, 27, 64, 101, 138, 175, 212, 249, 30, 67, 104, 141, 178, 215, 252,
    33, 70, 107, 144, 181, 218, 255, 36, 73, 110, 147, 184, 221, 2, 39, 76,
    113, 150, 187, 224, 5, 42, 79, 116, 153, 190, 227, 8, 45, 82, 119, 156,
    193, 230, 11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236,
    17, 54, 91, 128, 165, 202, 239, 20, 57, 94, 131, 168, 205, 242, 23, 60,
    97, 134, 171, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103, 0])

#guard builderDepositRequestObserve (BuilderDepositRequest.mk
  (fixed 48 (List.replicate 48 0) (by decide))
  (fixed 32 (List.replicate 32 0) (by decide))
  (U64.zero)
  (fixed 96 (List.replicate 96 0) (by decide))) ==
  (List.replicate 48 0,
    List.replicate 32 0,
    0,
    List.replicate 96 0)

#guard builderDepositRequestObserve (BuilderDepositRequest.mk
  (fixed 48 (List.replicate 48 255) (by decide))
  (fixed 32 (List.replicate 32 255) (by decide))
  (U64.max)
  (fixed 96 (List.replicate 96 255) (by decide))) ==
  (List.replicate 48 255,
    List.replicate 32 255,
    18446744073709551615,
    List.replicate 96 255)

#guard builderDepositRequestObserve { builderDepositRequest with pubkey := FixedBytes.ofNat 0 } ==
  (List.replicate 48 0,
    [0, 227, 8, 45, 82, 119, 156, 193, 230, 11, 48, 85, 122, 159, 196, 233,
    14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 239, 20, 0],
    0,
    [0, 246, 27, 64, 101, 138, 175, 212, 249, 30, 67, 104, 141, 178, 215, 252,
    33, 70, 107, 144, 181, 218, 255, 36, 73, 110, 147, 184, 221, 2, 39, 76,
    113, 150, 187, 224, 5, 42, 79, 116, 153, 190, 227, 8, 45, 82, 119, 156,
    193, 230, 11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236,
    17, 54, 91, 128, 165, 202, 239, 20, 57, 94, 131, 168, 205, 242, 23, 60,
    97, 134, 171, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103, 0])

#guard builderDepositRequestObserve
    { builderDepositRequest with withdrawalCredentials := FixedBytes.ofNat 0 } ==
  ([0, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103, 140, 177, 214,
    251, 32, 69, 106, 143, 180, 217, 254, 35, 72, 109, 146, 183, 220, 1, 38,
    75, 112, 149, 186, 223, 4, 41, 78, 115, 152, 189, 226, 7, 44, 81, 0],
    List.replicate 32 0,
    0,
    [0, 246, 27, 64, 101, 138, 175, 212, 249, 30, 67, 104, 141, 178, 215, 252,
    33, 70, 107, 144, 181, 218, 255, 36, 73, 110, 147, 184, 221, 2, 39, 76,
    113, 150, 187, 224, 5, 42, 79, 116, 153, 190, 227, 8, 45, 82, 119, 156,
    193, 230, 11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236,
    17, 54, 91, 128, 165, 202, 239, 20, 57, 94, 131, 168, 205, 242, 23, 60,
    97, 134, 171, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103, 0])

#guard (builderDepositRequest.amount.toBitVec).toNat == 0
#guard builderDepositRequestObserve
    { builderDepositRequest with amount := U64.ofNat 18364758544493064720 } ==
  ([0, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103, 140, 177, 214,
    251, 32, 69, 106, 143, 180, 217, 254, 35, 72, 109, 146, 183, 220, 1, 38,
    75, 112, 149, 186, 223, 4, 41, 78, 115, 152, 189, 226, 7, 44, 81, 0],
    [0, 227, 8, 45, 82, 119, 156, 193, 230, 11, 48, 85, 122, 159, 196, 233,
    14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 239, 20, 0],
    18364758544493064720,
    [0, 246, 27, 64, 101, 138, 175, 212, 249, 30, 67, 104, 141, 178, 215, 252,
    33, 70, 107, 144, 181, 218, 255, 36, 73, 110, 147, 184, 221, 2, 39, 76,
    113, 150, 187, 224, 5, 42, 79, 116, 153, 190, 227, 8, 45, 82, 119, 156,
    193, 230, 11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236,
    17, 54, 91, 128, 165, 202, 239, 20, 57, 94, 131, 168, 205, 242, 23, 60,
    97, 134, 171, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103, 0])

#guard builderDepositRequestObserve
    { builderDepositRequest with signature := FixedBytes.ofNat 0 } ==
  ([0, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103, 140, 177, 214,
    251, 32, 69, 106, 143, 180, 217, 254, 35, 72, 109, 146, 183, 220, 1, 38,
    75, 112, 149, 186, 223, 4, 41, 78, 115, 152, 189, 226, 7, 44, 81, 0],
    [0, 227, 8, 45, 82, 119, 156, 193, 230, 11, 48, 85, 122, 159, 196, 233,
    14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 239, 20, 0],
    0,
    List.replicate 96 0)

private def builderExitRequestObserve (r : BuilderExitRequest) :
    List UInt8 × List UInt8 :=
  (r.sourceAddress.toBytes.toList, r.pubkey.toBytes.toList)

private def builderExitRequestSourceAddress : Address :=
  address [0, 9, 46, 83, 120, 157, 194, 231, 12, 49, 86, 123, 160, 197, 234, 15,
    52, 89, 126, 0] (by decide)

private def builderExitRequestPubkey : Bytes48 :=
  fixed 48 [0, 28, 65, 102, 139, 176, 213, 250, 31, 68, 105, 142, 179, 216, 253, 34,
    71, 108, 145, 182, 219, 0, 37, 74, 111, 148, 185, 222, 3, 40, 77, 114,
    151, 188, 225, 6, 43, 80, 117, 154, 191, 228, 9, 46, 83, 120, 157, 0] (by decide)

private def builderExitRequest : BuilderExitRequest :=
  ⟨builderExitRequestSourceAddress, builderExitRequestPubkey⟩

#guard builderExitRequestObserve builderExitRequest ==
  ([0, 9, 46, 83, 120, 157, 194, 231, 12, 49, 86, 123, 160, 197, 234, 15,
    52, 89, 126, 0],
    [0, 28, 65, 102, 139, 176, 213, 250, 31, 68, 105, 142, 179, 216, 253, 34,
    71, 108, 145, 182, 219, 0, 37, 74, 111, 148, 185, 222, 3, 40, 77, 114,
    151, 188, 225, 6, 43, 80, 117, 154, 191, 228, 9, 46, 83, 120, 157, 0])

#guard builderExitRequestObserve (BuilderExitRequest.mk
  (address (List.replicate 20 0) (by decide))
  (fixed 48 (List.replicate 48 0) (by decide))) ==
  (List.replicate 20 0,
    List.replicate 48 0)

#guard builderExitRequestObserve (BuilderExitRequest.mk
  (address (List.replicate 20 255) (by decide))
  (fixed 48 (List.replicate 48 255) (by decide))) ==
  (List.replicate 20 255,
    List.replicate 48 255)

#guard builderExitRequestObserve { builderExitRequest with sourceAddress := Address.ofNat 0 } ==
  (List.replicate 20 0,
    [0, 28, 65, 102, 139, 176, 213, 250, 31, 68, 105, 142, 179, 216, 253, 34,
    71, 108, 145, 182, 219, 0, 37, 74, 111, 148, 185, 222, 3, 40, 77, 114,
    151, 188, 225, 6, 43, 80, 117, 154, 191, 228, 9, 46, 83, 120, 157, 0])

#guard builderExitRequestObserve { builderExitRequest with pubkey := FixedBytes.ofNat 0 } ==
  ([0, 9, 46, 83, 120, 157, 194, 231, 12, 49, 86, 123, 160, 197, 234, 15,
    52, 89, 126, 0],
    List.replicate 48 0)

#guard consolidationRequestObserve
    { consolidationRequest with
      sourcePubkey := consolidationRequest.targetPubkey,
      targetPubkey := consolidationRequest.sourcePubkey } !=
  consolidationRequestObserve consolidationRequest

#guard depositRequest.amount.toNat != depositRequest.index.toNat

end STFSpec.Conformance.Stateless.RequestItemsGuards
