/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless

/-!
# Complete raw execution-request aggregate controls

Library `EthConformance`. Private controls compare every item field and every byte
in complete ordered collections, retaining siblings through independent updates.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Stateless.ExecutionRequestsGuards

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

private def depositObserve (r : DepositRequest) :
    List UInt8 × List UInt8 × Nat × List UInt8 × Nat :=
  (r.pubkey.toBytes.toList, r.withdrawalCredentials.toBytes.toList, r.amount.toNat,
    r.signature.toBytes.toList, r.index.toNat)

private def depositZero : DepositRequest :=
  DepositRequest.mk
    (fixed 48 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide))
    (fixed 32 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide))
    (U64.ofNat 0)
    (fixed 96 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide))
    (U64.ofNat 0)

private def depositZeroExpected : List UInt8 × List UInt8 × Nat × List UInt8 × Nat :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    0,
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    0)

#guard depositObserve depositZero == depositZeroExpected

private def depositMax : DepositRequest :=
  DepositRequest.mk
    (fixed 48 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] (by decide))
    (fixed 32 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] (by decide))
    (U64.ofNat 18446744073709551615)
    (fixed 96 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] (by decide))
    (U64.ofNat 18446744073709551615)

private def depositMaxExpected : List UInt8 × List UInt8 × Nat × List UInt8 × Nat :=
  ([255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255],
    [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255],
    18446744073709551615,
    [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255],
    18446744073709551615)

#guard depositObserve depositMax == depositMaxExpected

private def depositA : DepositRequest :=
  DepositRequest.mk
    (fixed 48 [0, 239, 20, 57, 94, 131, 168, 205, 242, 23, 60, 97, 134, 171, 208, 245,
      26, 63, 100, 137, 174, 211, 248, 29, 66, 103, 140, 177, 214, 251, 32, 69,
      106, 143, 180, 217, 254, 35, 72, 109, 146, 183, 220, 1, 38, 75, 112, 0] (by decide))
    (fixed 32 [0, 24, 61, 98, 135, 172, 209, 246, 27, 64, 101, 138, 175, 212, 249, 30,
      67, 104, 141, 178, 215, 252, 33, 70, 107, 144, 181, 218, 255, 36, 73, 0] (by decide))
    (U64.ofNat 72623859790382856)
    (fixed 96 [0, 106, 143, 180, 217, 254, 35, 72, 109, 146, 183, 220, 1, 38, 75, 112,
      149, 186, 223, 4, 41, 78, 115, 152, 189, 226, 7, 44, 81, 118, 155, 192,
      229, 10, 47, 84, 121, 158, 195, 232, 13, 50, 87, 124, 161, 198, 235, 16,
      53, 90, 127, 164, 201, 238, 19, 56, 93, 130, 167, 204, 241, 22, 59, 96,
      133, 170, 207, 244, 25, 62, 99, 136, 173, 210, 247, 28, 65, 102, 139, 176,
      213, 250, 31, 68, 105, 142, 179, 216, 253, 34, 71, 108, 145, 182, 219, 0] (by decide))
    (U64.ofNat 1234567890123456789)

private def depositAExpected : List UInt8 × List UInt8 × Nat × List UInt8 × Nat :=
  ([0, 239, 20, 57, 94, 131, 168, 205, 242, 23, 60, 97, 134, 171, 208, 245,
      26, 63, 100, 137, 174, 211, 248, 29, 66, 103, 140, 177, 214, 251, 32, 69,
      106, 143, 180, 217, 254, 35, 72, 109, 146, 183, 220, 1, 38, 75, 112, 0],
    [0, 24, 61, 98, 135, 172, 209, 246, 27, 64, 101, 138, 175, 212, 249, 30,
      67, 104, 141, 178, 215, 252, 33, 70, 107, 144, 181, 218, 255, 36, 73, 0],
    72623859790382856,
    [0, 106, 143, 180, 217, 254, 35, 72, 109, 146, 183, 220, 1, 38, 75, 112,
      149, 186, 223, 4, 41, 78, 115, 152, 189, 226, 7, 44, 81, 118, 155, 192,
      229, 10, 47, 84, 121, 158, 195, 232, 13, 50, 87, 124, 161, 198, 235, 16,
      53, 90, 127, 164, 201, 238, 19, 56, 93, 130, 167, 204, 241, 22, 59, 96,
      133, 170, 207, 244, 25, 62, 99, 136, 173, 210, 247, 28, 65, 102, 139, 176,
      213, 250, 31, 68, 105, 142, 179, 216, 253, 34, 71, 108, 145, 182, 219, 0],
    1234567890123456789)

#guard depositObserve depositA == depositAExpected

private def depositB : DepositRequest :=
  DepositRequest.mk
    (fixed 48 [0, 54, 91, 128, 165, 202, 239, 20, 57, 94, 131, 168, 205, 242, 23, 60,
      97, 134, 171, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103, 140,
      177, 214, 251, 32, 69, 106, 143, 180, 217, 254, 35, 72, 109, 146, 183, 0] (by decide))
    (fixed 32 [0, 95, 132, 169, 206, 243, 24, 61, 98, 135, 172, 209, 246, 27, 64, 101,
      138, 175, 212, 249, 30, 67, 104, 141, 178, 215, 252, 33, 70, 107, 144, 0] (by decide))
    (U64.ofNat 9255003132036915216)
    (fixed 96 [0, 177, 214, 251, 32, 69, 106, 143, 180, 217, 254, 35, 72, 109, 146, 183,
      220, 1, 38, 75, 112, 149, 186, 223, 4, 41, 78, 115, 152, 189, 226, 7,
      44, 81, 118, 155, 192, 229, 10, 47, 84, 121, 158, 195, 232, 13, 50, 87,
      124, 161, 198, 235, 16, 53, 90, 127, 164, 201, 238, 19, 56, 93, 130, 167,
      204, 241, 22, 59, 96, 133, 170, 207, 244, 25, 62, 99, 136, 173, 210, 247,
      28, 65, 102, 139, 176, 213, 250, 31, 68, 105, 142, 179, 216, 253, 34, 0] (by decide))
    (U64.ofNat 9833440827789222417)

private def depositBExpected : List UInt8 × List UInt8 × Nat × List UInt8 × Nat :=
  ([0, 54, 91, 128, 165, 202, 239, 20, 57, 94, 131, 168, 205, 242, 23, 60,
      97, 134, 171, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103, 140,
      177, 214, 251, 32, 69, 106, 143, 180, 217, 254, 35, 72, 109, 146, 183, 0],
    [0, 95, 132, 169, 206, 243, 24, 61, 98, 135, 172, 209, 246, 27, 64, 101,
      138, 175, 212, 249, 30, 67, 104, 141, 178, 215, 252, 33, 70, 107, 144, 0],
    9255003132036915216,
    [0, 177, 214, 251, 32, 69, 106, 143, 180, 217, 254, 35, 72, 109, 146, 183,
      220, 1, 38, 75, 112, 149, 186, 223, 4, 41, 78, 115, 152, 189, 226, 7,
      44, 81, 118, 155, 192, 229, 10, 47, 84, 121, 158, 195, 232, 13, 50, 87,
      124, 161, 198, 235, 16, 53, 90, 127, 164, 201, 238, 19, 56, 93, 130, 167,
      204, 241, 22, 59, 96, 133, 170, 207, 244, 25, 62, 99, 136, 173, 210, 247,
      28, 65, 102, 139, 176, 213, 250, 31, 68, 105, 142, 179, 216, 253, 34, 0],
    9833440827789222417)

#guard depositObserve depositB == depositBExpected

private def withdrawalObserve (r : WithdrawalRequest) :
    List UInt8 × List UInt8 × Nat :=
  (r.sourceAddress.toBytes.toList, r.validatorPubkey.toBytes.toList, r.amount.toNat)

private def withdrawalZero : WithdrawalRequest :=
  WithdrawalRequest.mk
    (address [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0] (by decide))
    (fixed 48 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide))
    (U64.ofNat 0)

private def withdrawalZeroExpected : List UInt8 × List UInt8 × Nat :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    0)

#guard withdrawalObserve withdrawalZero == withdrawalZeroExpected

private def withdrawalMax : WithdrawalRequest :=
  WithdrawalRequest.mk
    (address [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255] (by decide))
    (fixed 48 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] (by decide))
    (U64.ofNat 18446744073709551615)

private def withdrawalMaxExpected : List UInt8 × List UInt8 × Nat :=
  ([255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255],
    [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255],
    18446744073709551615)

#guard withdrawalObserve withdrawalMax == withdrawalMaxExpected

private def withdrawalA : WithdrawalRequest :=
  WithdrawalRequest.mk
    (address [0, 2, 39, 76, 113, 150, 187, 224, 5, 42, 79, 116, 153, 190, 227, 8,
      45, 82, 119, 0] (by decide))
    (fixed 48 [0, 43, 80, 117, 154, 191, 228, 9, 46, 83, 120, 157, 194, 231, 12, 49,
      86, 123, 160, 197, 234, 15, 52, 89, 126, 163, 200, 237, 18, 55, 92, 129,
      166, 203, 240, 21, 58, 95, 132, 169, 206, 243, 24, 61, 98, 135, 172, 0] (by decide))
    (U64.ofNat 9255003132036915216)

private def withdrawalAExpected : List UInt8 × List UInt8 × Nat :=
  ([0, 2, 39, 76, 113, 150, 187, 224, 5, 42, 79, 116, 153, 190, 227, 8,
      45, 82, 119, 0],
    [0, 43, 80, 117, 154, 191, 228, 9, 46, 83, 120, 157, 194, 231, 12, 49,
      86, 123, 160, 197, 234, 15, 52, 89, 126, 163, 200, 237, 18, 55, 92, 129,
      166, 203, 240, 21, 58, 95, 132, 169, 206, 243, 24, 61, 98, 135, 172, 0],
    9255003132036915216)

#guard withdrawalObserve withdrawalA == withdrawalAExpected

private def withdrawalB : WithdrawalRequest :=
  WithdrawalRequest.mk
    (address [0, 73, 110, 147, 184, 221, 2, 39, 76, 113, 150, 187, 224, 5, 42, 79,
      116, 153, 190, 0] (by decide))
    (fixed 48 [0, 114, 151, 188, 225, 6, 43, 80, 117, 154, 191, 228, 9, 46, 83, 120,
      157, 194, 231, 12, 49, 86, 123, 160, 197, 234, 15, 52, 89, 126, 163, 200,
      237, 18, 55, 92, 129, 166, 203, 240, 21, 58, 95, 132, 169, 206, 243, 0] (by decide))
    (U64.ofNat 1234567890123456789)

private def withdrawalBExpected : List UInt8 × List UInt8 × Nat :=
  ([0, 73, 110, 147, 184, 221, 2, 39, 76, 113, 150, 187, 224, 5, 42, 79,
      116, 153, 190, 0],
    [0, 114, 151, 188, 225, 6, 43, 80, 117, 154, 191, 228, 9, 46, 83, 120,
      157, 194, 231, 12, 49, 86, 123, 160, 197, 234, 15, 52, 89, 126, 163, 200,
      237, 18, 55, 92, 129, 166, 203, 240, 21, 58, 95, 132, 169, 206, 243, 0],
    1234567890123456789)

#guard withdrawalObserve withdrawalB == withdrawalBExpected

private def consolidationObserve (r : ConsolidationRequest) :
    List UInt8 × List UInt8 × List UInt8 :=
  (r.sourceAddress.toBytes.toList, r.sourcePubkey.toBytes.toList, r.targetPubkey.toBytes.toList)

private def consolidationZero : ConsolidationRequest :=
  ConsolidationRequest.mk
    (address [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0] (by decide))
    (fixed 48 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide))
    (fixed 48 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide))

private def consolidationZeroExpected : List UInt8 × List UInt8 × List UInt8 :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])

#guard consolidationObserve consolidationZero == consolidationZeroExpected

private def consolidationMax : ConsolidationRequest :=
  ConsolidationRequest.mk
    (address [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255] (by decide))
    (fixed 48 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] (by decide))
    (fixed 48 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] (by decide))

private def consolidationMaxExpected : List UInt8 × List UInt8 × List UInt8 :=
  ([255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255],
    [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255],
    [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255])

#guard consolidationObserve consolidationMax == consolidationMaxExpected

private def consolidationA : ConsolidationRequest :=
  ConsolidationRequest.mk
    (address [0, 21, 58, 95, 132, 169, 206, 243, 24, 61, 98, 135, 172, 209, 246, 27,
      64, 101, 138, 0] (by decide))
    (fixed 48 [0, 62, 99, 136, 173, 210, 247, 28, 65, 102, 139, 176, 213, 250, 31, 68,
      105, 142, 179, 216, 253, 34, 71, 108, 145, 182, 219, 0, 37, 74, 111, 148,
      185, 222, 3, 40, 77, 114, 151, 188, 225, 6, 43, 80, 117, 154, 191, 0] (by decide))
    (fixed 48 [0, 103, 140, 177, 214, 251, 32, 69, 106, 143, 180, 217, 254, 35, 72, 109,
      146, 183, 220, 1, 38, 75, 112, 149, 186, 223, 4, 41, 78, 115, 152, 189,
      226, 7, 44, 81, 118, 155, 192, 229, 10, 47, 84, 121, 158, 195, 232, 0] (by decide))

private def consolidationAExpected : List UInt8 × List UInt8 × List UInt8 :=
  ([0, 21, 58, 95, 132, 169, 206, 243, 24, 61, 98, 135, 172, 209, 246, 27,
      64, 101, 138, 0],
    [0, 62, 99, 136, 173, 210, 247, 28, 65, 102, 139, 176, 213, 250, 31, 68,
      105, 142, 179, 216, 253, 34, 71, 108, 145, 182, 219, 0, 37, 74, 111, 148,
      185, 222, 3, 40, 77, 114, 151, 188, 225, 6, 43, 80, 117, 154, 191, 0],
    [0, 103, 140, 177, 214, 251, 32, 69, 106, 143, 180, 217, 254, 35, 72, 109,
      146, 183, 220, 1, 38, 75, 112, 149, 186, 223, 4, 41, 78, 115, 152, 189,
      226, 7, 44, 81, 118, 155, 192, 229, 10, 47, 84, 121, 158, 195, 232, 0])

#guard consolidationObserve consolidationA == consolidationAExpected

private def consolidationB : ConsolidationRequest :=
  ConsolidationRequest.mk
    (address [0, 92, 129, 166, 203, 240, 21, 58, 95, 132, 169, 206, 243, 24, 61, 98,
      135, 172, 209, 0] (by decide))
    (fixed 48 [0, 133, 170, 207, 244, 25, 62, 99, 136, 173, 210, 247, 28, 65, 102, 139,
      176, 213, 250, 31, 68, 105, 142, 179, 216, 253, 34, 71, 108, 145, 182, 219,
      0, 37, 74, 111, 148, 185, 222, 3, 40, 77, 114, 151, 188, 225, 6, 0] (by decide))
    (fixed 48 [0, 174, 211, 248, 29, 66, 103, 140, 177, 214, 251, 32, 69, 106, 143, 180,
      217, 254, 35, 72, 109, 146, 183, 220, 1, 38, 75, 112, 149, 186, 223, 4,
      41, 78, 115, 152, 189, 226, 7, 44, 81, 118, 155, 192, 229, 10, 47, 0] (by decide))

private def consolidationBExpected : List UInt8 × List UInt8 × List UInt8 :=
  ([0, 92, 129, 166, 203, 240, 21, 58, 95, 132, 169, 206, 243, 24, 61, 98,
      135, 172, 209, 0],
    [0, 133, 170, 207, 244, 25, 62, 99, 136, 173, 210, 247, 28, 65, 102, 139,
      176, 213, 250, 31, 68, 105, 142, 179, 216, 253, 34, 71, 108, 145, 182, 219,
      0, 37, 74, 111, 148, 185, 222, 3, 40, 77, 114, 151, 188, 225, 6, 0],
    [0, 174, 211, 248, 29, 66, 103, 140, 177, 214, 251, 32, 69, 106, 143, 180,
      217, 254, 35, 72, 109, 146, 183, 220, 1, 38, 75, 112, 149, 186, 223, 4,
      41, 78, 115, 152, 189, 226, 7, 44, 81, 118, 155, 192, 229, 10, 47, 0])

#guard consolidationObserve consolidationB == consolidationBExpected

private def builderDepositObserve (r : BuilderDepositRequest) :
    List UInt8 × List UInt8 × Nat × List UInt8 :=
  (r.pubkey.toBytes.toList, r.withdrawalCredentials.toBytes.toList, r.amount.toNat,
    r.signature.toBytes.toList)

private def builderDepositZero : BuilderDepositRequest :=
  BuilderDepositRequest.mk
    (fixed 48 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide))
    (fixed 32 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide))
    (U64.ofNat 0)
    (fixed 96 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide))

private def builderDepositZeroExpected : List UInt8 × List UInt8 × Nat × List UInt8 :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    0,
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])

#guard builderDepositObserve builderDepositZero == builderDepositZeroExpected

private def builderDepositMax : BuilderDepositRequest :=
  BuilderDepositRequest.mk
    (fixed 48 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] (by decide))
    (fixed 32 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] (by decide))
    (U64.ofNat 18446744073709551615)
    (fixed 96 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] (by decide))

private def builderDepositMaxExpected : List UInt8 × List UInt8 × Nat × List UInt8 :=
  ([255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255],
    [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255],
    18446744073709551615,
    [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255])

#guard builderDepositObserve builderDepositMax == builderDepositMaxExpected

private def builderDepositA : BuilderDepositRequest :=
  BuilderDepositRequest.mk
    (fixed 48 [0, 40, 77, 114, 151, 188, 225, 6, 43, 80, 117, 154, 191, 228, 9, 46,
      83, 120, 157, 194, 231, 12, 49, 86, 123, 160, 197, 234, 15, 52, 89, 126,
      163, 200, 237, 18, 55, 92, 129, 166, 203, 240, 21, 58, 95, 132, 169, 0] (by decide))
    (fixed 32 [0, 81, 118, 155, 192, 229, 10, 47, 84, 121, 158, 195, 232, 13, 50, 87,
      124, 161, 198, 235, 16, 53, 90, 127, 164, 201, 238, 19, 56, 93, 130, 0] (by decide))
    (U64.ofNat 9833440827789222417)
    (fixed 96 [0, 163, 200, 237, 18, 55, 92, 129, 166, 203, 240, 21, 58, 95, 132, 169,
      206, 243, 24, 61, 98, 135, 172, 209, 246, 27, 64, 101, 138, 175, 212, 249,
      30, 67, 104, 141, 178, 215, 252, 33, 70, 107, 144, 181, 218, 255, 36, 73,
      110, 147, 184, 221, 2, 39, 76, 113, 150, 187, 224, 5, 42, 79, 116, 153,
      190, 227, 8, 45, 82, 119, 156, 193, 230, 11, 48, 85, 122, 159, 196, 233,
      14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 239, 20, 0] (by decide))

private def builderDepositAExpected : List UInt8 × List UInt8 × Nat × List UInt8 :=
  ([0, 40, 77, 114, 151, 188, 225, 6, 43, 80, 117, 154, 191, 228, 9, 46,
      83, 120, 157, 194, 231, 12, 49, 86, 123, 160, 197, 234, 15, 52, 89, 126,
      163, 200, 237, 18, 55, 92, 129, 166, 203, 240, 21, 58, 95, 132, 169, 0],
    [0, 81, 118, 155, 192, 229, 10, 47, 84, 121, 158, 195, 232, 13, 50, 87,
      124, 161, 198, 235, 16, 53, 90, 127, 164, 201, 238, 19, 56, 93, 130, 0],
    9833440827789222417,
    [0, 163, 200, 237, 18, 55, 92, 129, 166, 203, 240, 21, 58, 95, 132, 169,
      206, 243, 24, 61, 98, 135, 172, 209, 246, 27, 64, 101, 138, 175, 212, 249,
      30, 67, 104, 141, 178, 215, 252, 33, 70, 107, 144, 181, 218, 255, 36, 73,
      110, 147, 184, 221, 2, 39, 76, 113, 150, 187, 224, 5, 42, 79, 116, 153,
      190, 227, 8, 45, 82, 119, 156, 193, 230, 11, 48, 85, 122, 159, 196, 233,
      14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 239, 20, 0])

#guard builderDepositObserve builderDepositA == builderDepositAExpected

private def builderDepositB : BuilderDepositRequest :=
  BuilderDepositRequest.mk
    (fixed 48 [0, 111, 148, 185, 222, 3, 40, 77, 114, 151, 188, 225, 6, 43, 80, 117,
      154, 191, 228, 9, 46, 83, 120, 157, 194, 231, 12, 49, 86, 123, 160, 197,
      234, 15, 52, 89, 126, 163, 200, 237, 18, 55, 92, 129, 166, 203, 240, 0] (by decide))
    (fixed 32 [0, 152, 189, 226, 7, 44, 81, 118, 155, 192, 229, 10, 47, 84, 121, 158,
      195, 232, 13, 50, 87, 124, 161, 198, 235, 16, 53, 90, 127, 164, 201, 0] (by decide))
    (U64.ofNat 72623859790382856)
    (fixed 96 [0, 234, 15, 52, 89, 126, 163, 200, 237, 18, 55, 92, 129, 166, 203, 240,
      21, 58, 95, 132, 169, 206, 243, 24, 61, 98, 135, 172, 209, 246, 27, 64,
      101, 138, 175, 212, 249, 30, 67, 104, 141, 178, 215, 252, 33, 70, 107, 144,
      181, 218, 255, 36, 73, 110, 147, 184, 221, 2, 39, 76, 113, 150, 187, 224,
      5, 42, 79, 116, 153, 190, 227, 8, 45, 82, 119, 156, 193, 230, 11, 48,
      85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 0] (by decide))

private def builderDepositBExpected : List UInt8 × List UInt8 × Nat × List UInt8 :=
  ([0, 111, 148, 185, 222, 3, 40, 77, 114, 151, 188, 225, 6, 43, 80, 117,
      154, 191, 228, 9, 46, 83, 120, 157, 194, 231, 12, 49, 86, 123, 160, 197,
      234, 15, 52, 89, 126, 163, 200, 237, 18, 55, 92, 129, 166, 203, 240, 0],
    [0, 152, 189, 226, 7, 44, 81, 118, 155, 192, 229, 10, 47, 84, 121, 158,
      195, 232, 13, 50, 87, 124, 161, 198, 235, 16, 53, 90, 127, 164, 201, 0],
    72623859790382856,
    [0, 234, 15, 52, 89, 126, 163, 200, 237, 18, 55, 92, 129, 166, 203, 240,
      21, 58, 95, 132, 169, 206, 243, 24, 61, 98, 135, 172, 209, 246, 27, 64,
      101, 138, 175, 212, 249, 30, 67, 104, 141, 178, 215, 252, 33, 70, 107, 144,
      181, 218, 255, 36, 73, 110, 147, 184, 221, 2, 39, 76, 113, 150, 187, 224,
      5, 42, 79, 116, 153, 190, 227, 8, 45, 82, 119, 156, 193, 230, 11, 48,
      85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 0])

#guard builderDepositObserve builderDepositB == builderDepositBExpected

private def builderExitObserve (r : BuilderExitRequest) :
    List UInt8 × List UInt8 :=
  (r.sourceAddress.toBytes.toList, r.pubkey.toBytes.toList)

private def builderExitZero : BuilderExitRequest :=
  BuilderExitRequest.mk
    (address [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0] (by decide))
    (fixed 48 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide))

private def builderExitZeroExpected : List UInt8 × List UInt8 :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])

#guard builderExitObserve builderExitZero == builderExitZeroExpected

private def builderExitMax : BuilderExitRequest :=
  BuilderExitRequest.mk
    (address [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255] (by decide))
    (fixed 48 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] (by decide))

private def builderExitMaxExpected : List UInt8 × List UInt8 :=
  ([255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255],
    [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255])

#guard builderExitObserve builderExitMax == builderExitMaxExpected

private def builderExitA : BuilderExitRequest :=
  BuilderExitRequest.mk
    (address [0, 59, 96, 133, 170, 207, 244, 25, 62, 99, 136, 173, 210, 247, 28, 65,
      102, 139, 176, 0] (by decide))
    (fixed 48 [0, 100, 137, 174, 211, 248, 29, 66, 103, 140, 177, 214, 251, 32, 69, 106,
      143, 180, 217, 254, 35, 72, 109, 146, 183, 220, 1, 38, 75, 112, 149, 186,
      223, 4, 41, 78, 115, 152, 189, 226, 7, 44, 81, 118, 155, 192, 229, 0] (by decide))

private def builderExitAExpected : List UInt8 × List UInt8 :=
  ([0, 59, 96, 133, 170, 207, 244, 25, 62, 99, 136, 173, 210, 247, 28, 65,
      102, 139, 176, 0],
    [0, 100, 137, 174, 211, 248, 29, 66, 103, 140, 177, 214, 251, 32, 69, 106,
      143, 180, 217, 254, 35, 72, 109, 146, 183, 220, 1, 38, 75, 112, 149, 186,
      223, 4, 41, 78, 115, 152, 189, 226, 7, 44, 81, 118, 155, 192, 229, 0])

#guard builderExitObserve builderExitA == builderExitAExpected

private def builderExitB : BuilderExitRequest :=
  BuilderExitRequest.mk
    (address [0, 130, 167, 204, 241, 22, 59, 96, 133, 170, 207, 244, 25, 62, 99, 136,
      173, 210, 247, 0] (by decide))
    (fixed 48 [0, 171, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103, 140, 177,
      214, 251, 32, 69, 106, 143, 180, 217, 254, 35, 72, 109, 146, 183, 220, 1,
      38, 75, 112, 149, 186, 223, 4, 41, 78, 115, 152, 189, 226, 7, 44, 0] (by decide))

private def builderExitBExpected : List UInt8 × List UInt8 :=
  ([0, 130, 167, 204, 241, 22, 59, 96, 133, 170, 207, 244, 25, 62, 99, 136,
      173, 210, 247, 0],
    [0, 171, 208, 245, 26, 63, 100, 137, 174, 211, 248, 29, 66, 103, 140, 177,
      214, 251, 32, 69, 106, 143, 180, 217, 254, 35, 72, 109, 146, 183, 220, 1,
      38, 75, 112, 149, 186, 223, 4, 41, 78, 115, 152, 189, 226, 7, 44, 0])

#guard builderExitObserve builderExitB == builderExitBExpected

private def observe (r : ExecutionRequests) :=
  (r.deposits.toList.map depositObserve,
    r.withdrawals.toList.map withdrawalObserve,
    r.consolidations.toList.map consolidationObserve,
    r.builderDeposits.toList.map builderDepositObserve,
    r.builderExits.toList.map builderExitObserve)

private def empty : ExecutionRequests :=
  ExecutionRequests.mk #[] #[] #[] #[] #[]

#guard observe empty ==
  ([], [], [], [], [])

private def onlyDeposits : ExecutionRequests :=
  ExecutionRequests.mk #[depositA] #[] #[] #[] #[]

#guard observe onlyDeposits ==
  ([depositAExpected], [], [], [], [])

private def onlyWithdrawals : ExecutionRequests :=
  ExecutionRequests.mk #[] #[withdrawalA] #[] #[] #[]

#guard observe onlyWithdrawals ==
  ([], [withdrawalAExpected], [], [], [])

private def onlyConsolidations : ExecutionRequests :=
  ExecutionRequests.mk #[] #[] #[consolidationA] #[] #[]

#guard observe onlyConsolidations ==
  ([], [], [consolidationAExpected], [], [])

private def onlyBuilderdeposits : ExecutionRequests :=
  ExecutionRequests.mk #[] #[] #[] #[builderDepositA] #[]

#guard observe onlyBuilderdeposits ==
  ([], [], [], [builderDepositAExpected], [])

private def onlyBuilderexits : ExecutionRequests :=
  ExecutionRequests.mk #[] #[] #[] #[] #[builderExitA]

#guard observe onlyBuilderexits ==
  ([], [], [], [], [builderExitAExpected])

private def zero : ExecutionRequests :=
  ExecutionRequests.mk #[depositZero] #[withdrawalZero] #[consolidationZero] #[builderDepositZero]
    #[builderExitZero]

#guard observe zero ==
  ([depositZeroExpected], [withdrawalZeroExpected], [consolidationZeroExpected],
    [builderDepositZeroExpected], [builderExitZeroExpected])

private def maximum : ExecutionRequests :=
  ExecutionRequests.mk #[depositMax] #[withdrawalMax] #[consolidationMax] #[builderDepositMax]
    #[builderExitMax]

#guard observe maximum ==
  ([depositMaxExpected], [withdrawalMaxExpected], [consolidationMaxExpected],
    [builderDepositMaxExpected], [builderExitMaxExpected])

private def mixed : ExecutionRequests :=
  ExecutionRequests.mk #[depositA] #[withdrawalB, withdrawalA] #[consolidationA, consolidationA,
    consolidationB] #[builderDepositB, builderDepositA, builderDepositB, builderDepositZero]
    #[builderExitA, builderExitB, builderExitMax, builderExitZero, builderExitA]

#guard observe mixed ==
  ([depositAExpected], [withdrawalBExpected, withdrawalAExpected], [consolidationAExpected,
    consolidationAExpected, consolidationBExpected], [builderDepositBExpected,
    builderDepositAExpected, builderDepositBExpected, builderDepositZeroExpected],
    [builderExitAExpected, builderExitBExpected, builderExitMaxExpected, builderExitZeroExpected,
    builderExitAExpected])

#guard observe { mixed with deposits := #[depositB, depositA] } ==
  ([depositBExpected, depositAExpected], [withdrawalBExpected, withdrawalAExpected],
    [consolidationAExpected, consolidationAExpected, consolidationBExpected],
    [builderDepositBExpected, builderDepositAExpected, builderDepositBExpected,
    builderDepositZeroExpected], [builderExitAExpected, builderExitBExpected,
    builderExitMaxExpected, builderExitZeroExpected, builderExitAExpected])

#guard observe { mixed with deposits := #[depositA, depositA] } ==
  ([depositAExpected, depositAExpected], [withdrawalBExpected, withdrawalAExpected],
    [consolidationAExpected, consolidationAExpected, consolidationBExpected],
    [builderDepositBExpected, builderDepositAExpected, builderDepositBExpected,
    builderDepositZeroExpected], [builderExitAExpected, builderExitBExpected,
    builderExitMaxExpected, builderExitZeroExpected, builderExitAExpected])

#guard observe { mixed with deposits := #[depositA, depositB] } ==
  ([depositAExpected, depositBExpected], [withdrawalBExpected, withdrawalAExpected],
    [consolidationAExpected, consolidationAExpected, consolidationBExpected],
    [builderDepositBExpected, builderDepositAExpected, builderDepositBExpected,
    builderDepositZeroExpected], [builderExitAExpected, builderExitBExpected,
    builderExitMaxExpected, builderExitZeroExpected, builderExitAExpected])

#guard observe { mixed with deposits := #[depositB, depositA] } ==
  ([depositBExpected, depositAExpected], [withdrawalBExpected, withdrawalAExpected],
    [consolidationAExpected, consolidationAExpected, consolidationBExpected],
    [builderDepositBExpected, builderDepositAExpected, builderDepositBExpected,
    builderDepositZeroExpected], [builderExitAExpected, builderExitBExpected,
    builderExitMaxExpected, builderExitZeroExpected, builderExitAExpected])

#guard observe { mixed with withdrawals := #[withdrawalB, withdrawalA] } ==
  ([depositAExpected], [withdrawalBExpected, withdrawalAExpected], [consolidationAExpected,
    consolidationAExpected, consolidationBExpected], [builderDepositBExpected,
    builderDepositAExpected, builderDepositBExpected, builderDepositZeroExpected],
    [builderExitAExpected, builderExitBExpected, builderExitMaxExpected, builderExitZeroExpected,
    builderExitAExpected])

#guard observe { mixed with withdrawals := #[withdrawalA, withdrawalA] } ==
  ([depositAExpected], [withdrawalAExpected, withdrawalAExpected], [consolidationAExpected,
    consolidationAExpected, consolidationBExpected], [builderDepositBExpected,
    builderDepositAExpected, builderDepositBExpected, builderDepositZeroExpected],
    [builderExitAExpected, builderExitBExpected, builderExitMaxExpected, builderExitZeroExpected,
    builderExitAExpected])

#guard observe { mixed with withdrawals := #[withdrawalA, withdrawalB] } ==
  ([depositAExpected], [withdrawalAExpected, withdrawalBExpected], [consolidationAExpected,
    consolidationAExpected, consolidationBExpected], [builderDepositBExpected,
    builderDepositAExpected, builderDepositBExpected, builderDepositZeroExpected],
    [builderExitAExpected, builderExitBExpected, builderExitMaxExpected, builderExitZeroExpected,
    builderExitAExpected])

#guard observe { mixed with withdrawals := #[withdrawalB, withdrawalA] } ==
  ([depositAExpected], [withdrawalBExpected, withdrawalAExpected], [consolidationAExpected,
    consolidationAExpected, consolidationBExpected], [builderDepositBExpected,
    builderDepositAExpected, builderDepositBExpected, builderDepositZeroExpected],
    [builderExitAExpected, builderExitBExpected, builderExitMaxExpected, builderExitZeroExpected,
    builderExitAExpected])

#guard observe { mixed with consolidations := #[consolidationB, consolidationA] } ==
  ([depositAExpected], [withdrawalBExpected, withdrawalAExpected], [consolidationBExpected,
    consolidationAExpected], [builderDepositBExpected, builderDepositAExpected,
    builderDepositBExpected, builderDepositZeroExpected], [builderExitAExpected,
    builderExitBExpected, builderExitMaxExpected, builderExitZeroExpected, builderExitAExpected])

#guard observe { mixed with consolidations := #[consolidationA, consolidationA] } ==
  ([depositAExpected], [withdrawalBExpected, withdrawalAExpected], [consolidationAExpected,
    consolidationAExpected], [builderDepositBExpected, builderDepositAExpected,
    builderDepositBExpected, builderDepositZeroExpected], [builderExitAExpected,
    builderExitBExpected, builderExitMaxExpected, builderExitZeroExpected, builderExitAExpected])

#guard observe { mixed with consolidations := #[consolidationA, consolidationB] } ==
  ([depositAExpected], [withdrawalBExpected, withdrawalAExpected], [consolidationAExpected,
    consolidationBExpected], [builderDepositBExpected, builderDepositAExpected,
    builderDepositBExpected, builderDepositZeroExpected], [builderExitAExpected,
    builderExitBExpected, builderExitMaxExpected, builderExitZeroExpected, builderExitAExpected])

#guard observe { mixed with consolidations := #[consolidationB, consolidationA] } ==
  ([depositAExpected], [withdrawalBExpected, withdrawalAExpected], [consolidationBExpected,
    consolidationAExpected], [builderDepositBExpected, builderDepositAExpected,
    builderDepositBExpected, builderDepositZeroExpected], [builderExitAExpected,
    builderExitBExpected, builderExitMaxExpected, builderExitZeroExpected, builderExitAExpected])

#guard observe { mixed with builderDeposits := #[builderDepositB, builderDepositA] } ==
  ([depositAExpected], [withdrawalBExpected, withdrawalAExpected], [consolidationAExpected,
    consolidationAExpected, consolidationBExpected], [builderDepositBExpected,
    builderDepositAExpected], [builderExitAExpected, builderExitBExpected, builderExitMaxExpected,
    builderExitZeroExpected, builderExitAExpected])

#guard observe { mixed with builderDeposits := #[builderDepositA, builderDepositA] } ==
  ([depositAExpected], [withdrawalBExpected, withdrawalAExpected], [consolidationAExpected,
    consolidationAExpected, consolidationBExpected], [builderDepositAExpected,
    builderDepositAExpected], [builderExitAExpected, builderExitBExpected, builderExitMaxExpected,
    builderExitZeroExpected, builderExitAExpected])

#guard observe { mixed with builderDeposits := #[builderDepositA, builderDepositB] } ==
  ([depositAExpected], [withdrawalBExpected, withdrawalAExpected], [consolidationAExpected,
    consolidationAExpected, consolidationBExpected], [builderDepositAExpected,
    builderDepositBExpected], [builderExitAExpected, builderExitBExpected, builderExitMaxExpected,
    builderExitZeroExpected, builderExitAExpected])

#guard observe { mixed with builderDeposits := #[builderDepositB, builderDepositA] } ==
  ([depositAExpected], [withdrawalBExpected, withdrawalAExpected], [consolidationAExpected,
    consolidationAExpected, consolidationBExpected], [builderDepositBExpected,
    builderDepositAExpected], [builderExitAExpected, builderExitBExpected, builderExitMaxExpected,
    builderExitZeroExpected, builderExitAExpected])

#guard observe { mixed with builderExits := #[builderExitB, builderExitA] } ==
  ([depositAExpected], [withdrawalBExpected, withdrawalAExpected], [consolidationAExpected,
    consolidationAExpected, consolidationBExpected], [builderDepositBExpected,
    builderDepositAExpected, builderDepositBExpected, builderDepositZeroExpected],
    [builderExitBExpected, builderExitAExpected])

#guard observe { mixed with builderExits := #[builderExitA, builderExitA] } ==
  ([depositAExpected], [withdrawalBExpected, withdrawalAExpected], [consolidationAExpected,
    consolidationAExpected, consolidationBExpected], [builderDepositBExpected,
    builderDepositAExpected, builderDepositBExpected, builderDepositZeroExpected],
    [builderExitAExpected, builderExitAExpected])

#guard observe { mixed with builderExits := #[builderExitA, builderExitB] } ==
  ([depositAExpected], [withdrawalBExpected, withdrawalAExpected], [consolidationAExpected,
    consolidationAExpected, consolidationBExpected], [builderDepositBExpected,
    builderDepositAExpected, builderDepositBExpected, builderDepositZeroExpected],
    [builderExitAExpected, builderExitBExpected])

#guard observe { mixed with builderExits := #[builderExitB, builderExitA] } ==
  ([depositAExpected], [withdrawalBExpected, withdrawalAExpected], [consolidationAExpected,
    consolidationAExpected, consolidationBExpected], [builderDepositBExpected,
    builderDepositAExpected, builderDepositBExpected, builderDepositZeroExpected],
    [builderExitBExpected, builderExitAExpected])

end STFSpec.Conformance.Stateless.ExecutionRequestsGuards
