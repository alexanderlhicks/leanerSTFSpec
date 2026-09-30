/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base

/-!
# Integer byte conversion regression guards

Library `EthConformance`: fixed/minimal/endian boundaries, over-width leading zeros,
unbounded integers and masked address high bits.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §4.
-/

open STFSpec.Base

#guard Bytes.toList (U256.toBeBytes32 (U256.ofNat 0)).toBytes = (List.replicate 32 0)
#guard Bytes.toList (U256.toLeBytes32 (U256.ofNat 0)).toBytes = (List.replicate 32 0)
#guard Bytes.toList (U256.toBeBytes (U256.ofNat 0)) = []
#guard Bytes.toList (U256.toBeBytes32 (U256.ofNat 1)).toBytes = (List.replicate 31 0 ++ [1])
#guard Bytes.toList (U256.toLeBytes32 (U256.ofNat 1)).toBytes = ([1] ++ List.replicate 31 0)
#guard Bytes.toList (U256.toBeBytes (U256.ofNat 1)) = [1]
#guard Bytes.toList (U256.toBeBytes32 (U256.ofNat 255)).toBytes = (List.replicate 31 0 ++ [255])
#guard Bytes.toList (U256.toLeBytes32 (U256.ofNat 255)).toBytes = ([255] ++ List.replicate 31 0)
#guard Bytes.toList (U256.toBeBytes (U256.ofNat 255)) = [255]
#guard Bytes.toList (U256.toBeBytes32 (U256.ofNat 256)).toBytes =
  (List.replicate 30 0 ++ [1, 0])
#guard Bytes.toList (U256.toLeBytes32 (U256.ofNat 256)).toBytes =
  ([0, 1] ++ List.replicate 30 0)
#guard Bytes.toList (U256.toBeBytes (U256.ofNat 256)) = [1, 0]
#guard Bytes.toList (U256.toBeBytes32 (U256.ofNat 257)).toBytes =
  (List.replicate 30 0 ++ [1, 1])
#guard Bytes.toList (U256.toLeBytes32 (U256.ofNat 257)).toBytes =
  ([1, 1] ++ List.replicate 30 0)
#guard Bytes.toList (U256.toBeBytes (U256.ofNat 257)) = [1, 1]
#guard Bytes.toList (U256.toBeBytes32 (U256.ofNat (2 ^ 255))).toBytes =
  ([128] ++ List.replicate 31 0)
#guard Bytes.toList (U256.toLeBytes32 (U256.ofNat (2 ^ 255))).toBytes =
  (List.replicate 31 0 ++ [128])
#guard Bytes.toList (U256.toBeBytes (U256.ofNat (2 ^ 255))) = ([128] ++ List.replicate 31 0)
#guard Bytes.toList (U256.toBeBytes32 (U256.ofNat (2 ^ 256 - 1))).toBytes =
  (List.replicate 32 255)
#guard Bytes.toList (U256.toLeBytes32 (U256.ofNat (2 ^ 256 - 1))).toBytes =
  (List.replicate 32 255)
#guard Bytes.toList (U256.toBeBytes (U256.ofNat (2 ^ 256 - 1))) = (List.replicate 32 255)
#guard Bytes.toList (U256.toBeBytes32 (U256.ofNat
  0x102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20)).toBytes =
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
  26, 27, 28, 29, 30, 31, 32]
#guard Bytes.toList (U256.toLeBytes32 (U256.ofNat
  0x102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20)).toBytes =
  [32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10,
  9, 8, 7, 6, 5, 4, 3, 2, 1]
#guard Bytes.toList (U256.toBeBytes (U256.ofNat
  0x102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20)) =
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
  26, 27, 28, 29, 30, 31, 32]
#guard U256.ofBeBytes? (Bytes.ofList ([] : List UInt8)) = some U256.zero
#guard U256.ofBeBytes? (Bytes.ofList ([0] : List UInt8)) = some U256.zero
#guard U256.ofBeBytes? (Bytes.ofList ((List.replicate 31 0) : List UInt8)) = some U256.zero
#guard U256.ofBeBytes? (Bytes.ofList ((List.replicate 32 0) : List UInt8)) = some U256.zero
#guard U256.ofBeBytes? (Bytes.ofList ((List.replicate 33 0) : List UInt8)) = none
#guard U256.ofBeBytes? (Bytes.ofList ((List.replicate 52 0) : List UInt8)) = none
#guard U256.ofBeBytes? (Bytes.ofList ([1] : List UInt8)) = some (U256.ofNat 1)
#guard U256.ofBeBytes? (Bytes.ofList ([0, 1] : List UInt8)) = some (U256.ofNat 1)
#guard U256.ofBeBytes? (Bytes.ofList ([1, 0] : List UInt8)) = some (U256.ofNat 256)
#guard U256.ofBeBytes? (Bytes.ofList ((List.replicate 32 255) : List UInt8)) =
  some (U256.ofNat (2 ^ 256 - 1))
#guard U256.ofBeBytes? (Bytes.ofList ((List.replicate 31 0 ++ [1]) : List UInt8)) =
  some (U256.ofNat 1)
#guard Bytes.toList (U64.toBeBytes8 (U64.ofNat 0)).toBytes = (List.replicate 8 0)
#guard Bytes.toList (U64.toLeBytes8 (U64.ofNat 0)).toBytes = (List.replicate 8 0)
#guard Bytes.toList (U64.toBeBytes (U64.ofNat 0)) = []
#guard Bytes.toList (U64.toBeBytes8 (U64.ofNat 1)).toBytes = (List.replicate 7 0 ++ [1])
#guard Bytes.toList (U64.toLeBytes8 (U64.ofNat 1)).toBytes = ([1] ++ List.replicate 7 0)
#guard Bytes.toList (U64.toBeBytes (U64.ofNat 1)) = [1]
#guard Bytes.toList (U64.toBeBytes8 (U64.ofNat 255)).toBytes = (List.replicate 7 0 ++ [255])
#guard Bytes.toList (U64.toLeBytes8 (U64.ofNat 255)).toBytes = ([255] ++ List.replicate 7 0)
#guard Bytes.toList (U64.toBeBytes (U64.ofNat 255)) = [255]
#guard Bytes.toList (U64.toBeBytes8 (U64.ofNat 256)).toBytes = (List.replicate 6 0 ++ [1, 0])
#guard Bytes.toList (U64.toLeBytes8 (U64.ofNat 256)).toBytes = ([0, 1] ++ List.replicate 6 0)
#guard Bytes.toList (U64.toBeBytes (U64.ofNat 256)) = [1, 0]
#guard Bytes.toList (U64.toBeBytes8 (U64.ofNat 257)).toBytes = (List.replicate 6 0 ++ [1, 1])
#guard Bytes.toList (U64.toLeBytes8 (U64.ofNat 257)).toBytes = ([1, 1] ++ List.replicate 6 0)
#guard Bytes.toList (U64.toBeBytes (U64.ofNat 257)) = [1, 1]
#guard Bytes.toList (U64.toBeBytes8 (U64.ofNat 9223372036854775808)).toBytes =
  ([128] ++ List.replicate 7 0)
#guard Bytes.toList (U64.toLeBytes8 (U64.ofNat 9223372036854775808)).toBytes =
  (List.replicate 7 0 ++ [128])
#guard Bytes.toList (U64.toBeBytes (U64.ofNat 9223372036854775808)) =
  ([128] ++ List.replicate 7 0)
#guard Bytes.toList (U64.toBeBytes8 (U64.ofNat (2 ^ 64 - 1))).toBytes = (List.replicate 8 255)
#guard Bytes.toList (U64.toLeBytes8 (U64.ofNat (2 ^ 64 - 1))).toBytes = (List.replicate 8 255)
#guard Bytes.toList (U64.toBeBytes (U64.ofNat (2 ^ 64 - 1))) = (List.replicate 8 255)
#guard Bytes.toList (U64.toBeBytes8 (U64.ofNat 72623859790382856)).toBytes =
  [1, 2, 3, 4, 5, 6, 7, 8]
#guard Bytes.toList (U64.toLeBytes8 (U64.ofNat 72623859790382856)).toBytes =
  [8, 7, 6, 5, 4, 3, 2, 1]
#guard Bytes.toList (U64.toBeBytes (U64.ofNat 72623859790382856)) = [1, 2, 3, 4, 5, 6, 7, 8]
#guard U64.ofBeBytes? (Bytes.ofList ([] : List UInt8)) = some U64.zero
#guard U64.ofLeBytes? (Bytes.ofList ([] : List UInt8)) = some U64.zero
#guard U64.ofBeBytes? (Bytes.ofList ([0] : List UInt8)) = some U64.zero
#guard U64.ofLeBytes? (Bytes.ofList ([0] : List UInt8)) = some U64.zero
#guard U64.ofBeBytes? (Bytes.ofList ((List.replicate 7 0) : List UInt8)) = some U64.zero
#guard U64.ofLeBytes? (Bytes.ofList ((List.replicate 7 0) : List UInt8)) = some U64.zero
#guard U64.ofBeBytes? (Bytes.ofList ((List.replicate 8 0) : List UInt8)) = some U64.zero
#guard U64.ofLeBytes? (Bytes.ofList ((List.replicate 8 0) : List UInt8)) = some U64.zero
#guard U64.ofBeBytes? (Bytes.ofList ((List.replicate 9 0) : List UInt8)) = none
#guard U64.ofLeBytes? (Bytes.ofList ((List.replicate 9 0) : List UInt8)) = none
#guard U64.ofBeBytes? (Bytes.ofList ((List.replicate 28 0) : List UInt8)) = none
#guard U64.ofLeBytes? (Bytes.ofList ((List.replicate 28 0) : List UInt8)) = none
#guard U64.ofBeBytes? (Bytes.ofList ([1] : List UInt8)) = some (U64.ofNat 1)
#guard U64.ofLeBytes? (Bytes.ofList ([1] : List UInt8)) = some (U64.ofNat 1)
#guard U64.ofBeBytes? (Bytes.ofList ([0, 1] : List UInt8)) = some (U64.ofNat 1)
#guard U64.ofLeBytes? (Bytes.ofList ([0, 1] : List UInt8)) = some (U64.ofNat 256)
#guard U64.ofBeBytes? (Bytes.ofList ([1, 0] : List UInt8)) = some (U64.ofNat 256)
#guard U64.ofLeBytes? (Bytes.ofList ([1, 0] : List UInt8)) = some (U64.ofNat 1)
#guard U64.ofBeBytes? (Bytes.ofList ((List.replicate 8 255) : List UInt8)) =
  some (U64.ofNat (2 ^ 64 - 1))
#guard U64.ofLeBytes? (Bytes.ofList ((List.replicate 8 255) : List UInt8)) =
  some (U64.ofNat (2 ^ 64 - 1))
#guard U64.ofBeBytes? (Bytes.ofList ((List.replicate 7 0 ++ [1]) : List UInt8)) =
  some (U64.ofNat 1)
#guard U64.ofLeBytes? (Bytes.ofList ((List.replicate 7 0 ++ [1]) : List UInt8)) =
  some (U64.ofNat 72057594037927936)
#guard Bytes.toList (Uint.toBeBytes 0) = []
#guard Uint.ofBeBytes (Uint.toBeBytes 0) = 0
#guard Uint.toBeBytes32? 0 = some (U256.toBeBytes32 (U256.ofNat 0))
#guard Bytes.toList (Uint.toBeBytes 1) = [1]
#guard Uint.ofBeBytes (Uint.toBeBytes 1) = 1
#guard Uint.toBeBytes32? 1 = some (U256.toBeBytes32 (U256.ofNat 1))
#guard Bytes.toList (Uint.toBeBytes 255) = [255]
#guard Uint.ofBeBytes (Uint.toBeBytes 255) = 255
#guard Uint.toBeBytes32? 255 = some (U256.toBeBytes32 (U256.ofNat 255))
#guard Bytes.toList (Uint.toBeBytes 256) = [1, 0]
#guard Uint.ofBeBytes (Uint.toBeBytes 256) = 256
#guard Uint.toBeBytes32? 256 = some (U256.toBeBytes32 (U256.ofNat 256))
#guard Bytes.toList (Uint.toBeBytes 257) = [1, 1]
#guard Uint.ofBeBytes (Uint.toBeBytes 257) = 257
#guard Uint.toBeBytes32? 257 = some (U256.toBeBytes32 (U256.ofNat 257))
#guard Bytes.toList (Uint.toBeBytes (2 ^ 64 - 1)) = (List.replicate 8 255)
#guard Uint.ofBeBytes (Uint.toBeBytes (2 ^ 64 - 1)) = (2 ^ 64 - 1)
#guard Uint.toBeBytes32? (2 ^ 64 - 1) = some (U256.toBeBytes32 (U256.ofNat (2 ^ 64 - 1)))
#guard Bytes.toList (Uint.toBeBytes (2 ^ 64)) = ([1] ++ List.replicate 8 0)
#guard Uint.ofBeBytes (Uint.toBeBytes (2 ^ 64)) = (2 ^ 64)
#guard Uint.toBeBytes32? (2 ^ 64) = some (U256.toBeBytes32 (U256.ofNat (2 ^ 64)))
#guard Bytes.toList (Uint.toBeBytes (2 ^ 256 - 1)) = (List.replicate 32 255)
#guard Uint.ofBeBytes (Uint.toBeBytes (2 ^ 256 - 1)) = (2 ^ 256 - 1)
#guard Uint.toBeBytes32? (2 ^ 256 - 1) = some (U256.toBeBytes32 (U256.ofNat (2 ^ 256 - 1)))
#guard Bytes.toList (Uint.toBeBytes (2 ^ 256)) = ([1] ++ List.replicate 32 0)
#guard Uint.ofBeBytes (Uint.toBeBytes (2 ^ 256)) = (2 ^ 256)
#guard Uint.toBeBytes32? (2 ^ 256) = none
#guard Bytes.toList (Uint.toBeBytes (2 ^ 4096 + 255)) = ([1] ++ List.replicate 511 0 ++ [255])
#guard Uint.ofBeBytes (Uint.toBeBytes (2 ^ 4096 + 255)) = (2 ^ 4096 + 255)
#guard Uint.toBeBytes32? (2 ^ 4096 + 255) = none
#guard Uint.ofBeBytes (Bytes.ofList ([] : List UInt8)) = 0
#guard Uint.ofLeBytes (Bytes.ofList ([] : List UInt8)) = 0
#guard Uint.ofBeBytes (Bytes.ofList ([0] : List UInt8)) = 0
#guard Uint.ofLeBytes (Bytes.ofList ([0] : List UInt8)) = 0
#guard Uint.ofBeBytes (Bytes.ofList ((List.replicate 33 0) : List UInt8)) = 0
#guard Uint.ofLeBytes (Bytes.ofList ((List.replicate 33 0) : List UInt8)) = 0
#guard Uint.ofBeBytes (Bytes.ofList ((List.replicate 64 0 ++ [1]) : List UInt8)) = 1
#guard Uint.ofLeBytes (Bytes.ofList ((List.replicate 64 0 ++ [1]) : List UInt8)) = (2 ^ 512)
#guard Uint.ofBeBytes (Bytes.ofList ([1, 0] : List UInt8)) = 256
#guard Uint.ofLeBytes (Bytes.ofList ([1, 0] : List UInt8)) = 1
#guard Uint.ofBeBytes (Bytes.ofList ([0, 1] : List UInt8)) = 1
#guard Uint.ofLeBytes (Bytes.ofList ([0, 1] : List UInt8)) = 256
#guard Uint.ofBeBytes (Bytes.ofList ((List.replicate 64 255) : List UInt8)) = (2 ^ 512 - 1)
#guard Uint.ofLeBytes (Bytes.ofList ((List.replicate 64 255) : List UInt8)) = (2 ^ 512 - 1)
#guard (Address.ofU256Masked (U256.ofNat 0)).toNat = 0
#guard Bytes.toList (Address.ofU256Masked (U256.ofNat 0)).toBytes = (List.replicate 20 0)
#guard (Address.ofU256Masked (U256.ofNat 1)).toNat = 1
#guard Bytes.toList (Address.ofU256Masked (U256.ofNat 1)).toBytes = (List.replicate 19 0 ++ [1])
#guard (Address.ofU256Masked (U256.ofNat (2 ^ 160 - 1))).toNat = (2 ^ 160 - 1)
#guard Bytes.toList (Address.ofU256Masked (U256.ofNat (2 ^ 160 - 1))).toBytes =
  (List.replicate 20 255)
#guard (Address.ofU256Masked (U256.ofNat (2 ^ 160))).toNat = 0
#guard Bytes.toList (Address.ofU256Masked (U256.ofNat (2 ^ 160))).toBytes =
  (List.replicate 20 0)
#guard (Address.ofU256Masked (U256.ofNat (2 ^ 160 + 1))).toNat = 1
#guard Bytes.toList (Address.ofU256Masked (U256.ofNat (2 ^ 160 + 1))).toBytes =
  (List.replicate 19 0 ++ [1])
#guard (Address.ofU256Masked (U256.ofNat (2 ^ 255 + 17))).toNat = 17
#guard Bytes.toList (Address.ofU256Masked (U256.ofNat (2 ^ 255 + 17))).toBytes =
  (List.replicate 19 0 ++ [17])
#guard (Address.ofU256Masked (U256.ofNat (2 ^ 256 - 1))).toNat = (2 ^ 160 - 1)
#guard Bytes.toList (Address.ofU256Masked (U256.ofNat (2 ^ 256 - 1))).toBytes =
  (List.replicate 20 255)
#guard (Address.ofU256Masked (U256.ofNat
  0x102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f)).toNat =
  0xc0d0e0f101112131415161718191a1b1c1d1e1f
#guard Bytes.toList (Address.ofU256Masked (U256.ofNat
  0x102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f)).toBytes =
  [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]

#guard (FixedBytes.ofNat 0 : FixedBytes 0).toNat = 0
#guard (FixedBytes.ofNat 256 : FixedBytes 1).toBytes.toList = [0]
#guard (FixedBytes.ofLeNat 256 : FixedBytes 0).toBytes.toList = []
#guard (FixedBytes.ofLeNat 0x0102 : FixedBytes 2).toBytes.toList = [2, 1]
#guard (Address.ofNat (2 ^ 160 + 1)).toNat = 1
