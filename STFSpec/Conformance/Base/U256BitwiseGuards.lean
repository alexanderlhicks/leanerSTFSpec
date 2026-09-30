/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base

/-!
# U256 comparison and bitwise regression guards

Library `EthConformance`: deterministic public-API checks for comparisons, bitwise
operations and shifts.
The guards cover operand order, signed boundaries, most-significant byte indexing,
least-significant sign extension, full-word shift guards and CLZ endpoints.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §4.
-/

open STFSpec.Base

#guard (U256.lt U256.zero U256.one).toNat = 1
#guard (U256.lt U256.one U256.zero).toNat = 0
#guard (U256.gt U256.one U256.zero).toNat = 1
#guard (U256.gt U256.zero U256.one).toNat = 0
#guard (U256.lt U256.max U256.zero).toNat = 0
#guard (U256.gt U256.max U256.zero).toNat = 1
#guard (U256.slt U256.max U256.zero).toNat = 1
#guard (U256.sgt U256.max U256.zero).toNat = 0
#guard (U256.sgt U256.zero U256.max).toNat = 1
#guard (U256.slt (U256.ofNat (2 ^ 255)) (U256.ofNat (2 ^ 255 - 1))).toNat = 1
#guard (U256.slt (U256.ofNat (2 ^ 255 - 1)) (U256.ofNat (2 ^ 255))).toNat = 0
#guard (U256.eq U256.one U256.one).toNat = 1
#guard (U256.eq U256.one U256.zero).toNat = 0
#guard (U256.iszero U256.zero).toNat = 1
#guard (U256.iszero U256.max).toNat = 0
#guard U256.ult U256.max U256.zero = false
#guard U256.ule U256.max U256.max = true
#guard U256.ule U256.one U256.zero = false
#guard U256.slt' U256.max U256.zero = true
#guard (U256.and (U256.ofNat 0xaa) (U256.ofNat 0x55)).toNat = 0
#guard (U256.or (U256.ofNat 0xaa) (U256.ofNat 0x55)).toNat = 255
#guard (U256.xor (U256.ofNat 0xff) (U256.ofNat 0x55)).toNat = 0xaa
#guard U256.and U256.max U256.one = U256.one
#guard U256.or U256.max U256.zero = U256.max
#guard U256.xor U256.max U256.max = U256.zero
#guard U256.not U256.zero = U256.max
#guard U256.not U256.max = U256.zero
#guard (U256.byte U256.zero (U256.ofNat (0xab * 2 ^ 248 + 0xcd))).toNat = 0xab
#guard (U256.byte (U256.ofNat 31) (U256.ofNat (0xab * 2 ^ 248 + 0xcd))).toNat = 0xcd
#guard (U256.byte (U256.ofNat 30) (U256.ofNat 0x1234)).toNat = 0x12
#guard U256.byte (U256.ofNat 32) U256.max = U256.zero
#guard U256.byte U256.max U256.max = U256.zero
#guard U256.signextend (U256.ofNat 31) (U256.ofNat (2 ^ 255 + 1)) = U256.ofNat (2 ^ 255 + 1)
#guard U256.signextend (U256.ofNat 32) U256.one = U256.one
#guard U256.signextend U256.max U256.one = U256.one
#guard (U256.signextend U256.zero (U256.ofNat 0x80)).toNat = 2 ^ 256 - 0x80
#guard (U256.signextend U256.zero (U256.ofNat 0x17f)).toNat = 0x7f
#guard (U256.signextend U256.one (U256.ofNat 0x8000)).toNat = 2 ^ 256 - 0x8000
#guard (U256.signextend U256.one (U256.ofNat 0x17fff)).toNat = 0x7fff
#guard U256.shl U256.zero U256.max = U256.max
#guard (U256.shl (U256.ofNat 255) U256.one).toNat = 2 ^ 255
#guard U256.shl (U256.ofNat 255) (U256.ofNat 2) = U256.zero
#guard U256.shl (U256.ofNat 256) U256.one = U256.zero
#guard U256.shl U256.max U256.one = U256.zero
#guard U256.shr U256.zero U256.max = U256.max
#guard (U256.shr (U256.ofNat 255) U256.max).toNat = 1
#guard U256.shr (U256.ofNat 256) U256.max = U256.zero
#guard U256.shr U256.max U256.max = U256.zero
#guard U256.sar U256.zero U256.max = U256.max
#guard U256.sar (U256.ofNat 255) U256.max = U256.max
#guard U256.sar (U256.ofNat 255) (U256.ofNat (2 ^ 255)) = U256.max
#guard U256.sar (U256.ofNat 256) U256.max = U256.max
#guard U256.sar U256.max U256.max = U256.max
#guard U256.sar (U256.ofNat 255) (U256.ofNat (2 ^ 255 - 1)) = U256.zero
#guard U256.sar (U256.ofNat 256) U256.one = U256.zero
#guard U256.sar U256.max U256.one = U256.zero
#guard (U256.sar U256.one (U256.ofNat (2 ^ 256 - 3))).toInt = -2
#guard U256.bitLength U256.zero = 0
#guard U256.bitLength U256.one = 1
#guard U256.bitLength U256.max = 256
#guard (U256.clz U256.zero).toNat = 256
#guard (U256.clz U256.one).toNat = 255
#guard (U256.clz U256.max).toNat = 0
#guard (U256.clz (U256.ofNat (2 ^ 255))).toNat = 0
#guard (U256.clz (U256.ofNat (2 ^ 255 - 1))).toNat = 1
