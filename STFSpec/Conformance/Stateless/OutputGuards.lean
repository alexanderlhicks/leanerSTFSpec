/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Stateless

/-!
# Concrete stateless output literals
Library `EthConformance`. Complete byte expectations frozen independently in WI356;
each root/boolean/chain/schema carrier is supplied directly through public constructors.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §4/§7.
-/
namespace STFSpec.Conformance.Stateless.OutputGuards
open STFSpec.Base STFSpec.Stateless

private def vectors : List (StatelessValidationResult × List UInt8) := [
  ({
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0x0000000000000000000000000000000000000000000000000000000000000000),
    successfulValidation := false,
    chainId := U64.ofNat 0x0000000000000000, schemaId := 0x0000 },
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  ({
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0x0000000000000000000000000000000000000000000000000000000000000000),
    successfulValidation := true,
    chainId := U64.ofNat 0x0000000000000000, schemaId := 0x0000 },
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  ({
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f),
    successfulValidation := false,
    chainId := U64.ofNat 0x0123456789abcdef, schemaId := 0x1234 },
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
     26, 27, 28, 29, 30, 31, 0, 239, 205, 171, 137, 103, 69, 35, 1, 52, 18]),
  ({
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f),
    successfulValidation := true,
    chainId := U64.ofNat 0x0123456789abcdef, schemaId := 0x1234 },
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
     26, 27, 28, 29, 30, 31, 1, 239, 205, 171, 137, 103, 69, 35, 1, 52, 18]),
  ({
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0x1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100),
    successfulValidation := false,
    chainId := U64.ofNat 0x0123456789abcdef, schemaId := 0x1234 },
    [31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8,
     7, 6, 5, 4, 3, 2, 1, 0, 0, 239, 205, 171, 137, 103, 69, 35, 1, 52, 18]),
  ({
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f),
    successfulValidation := false,
    chainId := U64.ofNat 0x0123456789abcdee, schemaId := 0x1234 },
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
     26, 27, 28, 29, 30, 31, 0, 238, 205, 171, 137, 103, 69, 35, 1, 52, 18]),
  ({
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f),
    successfulValidation := false,
    chainId := U64.ofNat 0x0123456789abcdef, schemaId := 0x1235 },
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
     26, 27, 28, 29, 30, 31, 0, 239, 205, 171, 137, 103, 69, 35, 1, 53, 18]),
  ({
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f),
    successfulValidation := true,
    chainId := U64.ofNat 0x0123456789abcdef, schemaId := 0x0000 },
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
     26, 27, 28, 29, 30, 31, 1, 239, 205, 171, 137, 103, 69, 35, 1, 0, 0]),
  ({
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f),
    successfulValidation := false,
    chainId := U64.ofNat 0x0123456789abcdef, schemaId := 0x1501 },
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
     26, 27, 28, 29, 30, 31, 0, 239, 205, 171, 137, 103, 69, 35, 1, 1, 21]),
  ({
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff),
    successfulValidation := true,
    chainId := U64.ofNat 0xffffffffffffffff, schemaId := 0xffff },
    [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
     255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 1, 255, 255, 255, 255,
     255, 255, 255, 255, 255, 255]),
  ({
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0x0d663a7de3d811fbc797f605a65d2745df3a97d9f1994dfb685ff66d2917009f),
    successfulValidation := true,
    chainId := U64.ofNat 0x0000000000000001, schemaId := 0x1501 },
    [13, 102, 58, 125, 227, 216, 17, 251, 199, 151, 246, 5, 166, 93, 39, 69, 223, 58, 151, 217,
     241, 153, 77, 251, 104, 95, 246, 109, 41, 23, 0, 159, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 21]),
  ({
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0x202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f),
    successfulValidation := false,
    chainId := U64.ofNat 0x0123456789abcdef, schemaId := 0x1234 },
    [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54,
     55, 56, 57, 58, 59, 60, 61, 62, 63, 0, 239, 205, 171, 137, 103, 69, 35, 1, 52, 18]),
  ({
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0x404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f),
    successfulValidation := false,
    chainId := U64.ofNat 0x0123456789abcdef, schemaId := 0x1234 },
    [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86,
     87, 88, 89, 90, 91, 92, 93, 94, 95, 0, 239, 205, 171, 137, 103, 69, 35, 1, 52, 18]),
  ({
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0x606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f),
    successfulValidation := false,
    chainId := U64.ofNat 0x0123456789abcdef, schemaId := 0x1234 },
    [96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114,
     115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 0, 239, 205, 171, 137, 103,
     69, 35, 1, 52, 18]),
  ({
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0x808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f),
    successfulValidation := false,
    chainId := U64.ofNat 0x0123456789abcdef, schemaId := 0x1234 },
    [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145,
     146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 0, 239, 205, 171, 137,
     103, 69, 35, 1, 52, 18]),
  ({
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0xa0a1a2a3a4a5a6a7a8a9aaabacadaeafb0b1b2b3b4b5b6b7b8b9babbbcbdbebf),
    successfulValidation := false,
    chainId := U64.ofNat 0x0123456789abcdef, schemaId := 0x1234 },
    [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177,
     178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 0, 239, 205, 171, 137,
     103, 69, 35, 1, 52, 18]),
  ({
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0xc0c1c2c3c4c5c6c7c8c9cacbcccdcecfd0d1d2d3d4d5d6d7d8d9dadbdcdddedf),
    successfulValidation := false,
    chainId := U64.ofNat 0x0123456789abcdef, schemaId := 0x1234 },
    [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209,
     210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 0, 239, 205, 171, 137,
     103, 69, 35, 1, 52, 18]),
  ({
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0xe0e1e2e3e4e5e6e7e8e9eaebecedeeeff0f1f2f3f4f5f6f7f8f9fafbfcfdfeff),
    successfulValidation := false,
    chainId := U64.ofNat 0x0123456789abcdef, schemaId := 0x1234 },
    [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241,
     242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 0, 239, 205, 171, 137,
     103, 69, 35, 1, 52, 18])]

#guard vectors.all fun (result, expected) ↦
  (serializeStatelessOutput result).data.toList == expected
#guard (serializeStatelessOutput zeroSentinel).data.toList == List.replicate 43 0
#guard zeroSentinel.newPayloadRequestRoot.toNat == 0
#guard zeroSentinel.successfulValidation == false
#guard zeroSentinel.chainId.toNat == 0
#guard zeroSentinel.schemaId.toNat == 0

end STFSpec.Conformance.Stateless.OutputGuards
