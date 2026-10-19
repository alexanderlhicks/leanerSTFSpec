/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Complete padded-buffer controls

Library `EthConformance`. Thirty-two frozen whole-byte literals retain zero/high
bytes, clipped tails, empty windows and huge unavailable offsets with small widths.
The huge-start cases do not discriminate wrapped from unbounded stop arithmetic.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Vm.Core.BufferReadGuards
open STFSpec.Vm.Core STFSpec.Base

private def check (input : List UInt8) (start size : Nat) (expected : List UInt8) : Bool :=
  let b := Bytes.ofList input
  let s := U256.ofNat start
  let k := U256.ofNat size
  let result := bufferRead b s k
  (b.toList, s.toNat, k.toNat, result.toList, result.size) ==
    (input, start, size, expected, size)

-- empty-zero
#guard check []
  0 0
  []

-- empty-one
#guard check []
  0 1
  [0]

-- empty-four
#guard check []
  1 4
  [0, 0, 0, 0]

-- empty-huge-zero
#guard check []
  115792089237316195423570985008687907853269984665640564039457584007913129639935 0
  []

-- one-zero-byte
#guard check [0]
  0 1
  [0]

-- one-high-byte
#guard check [255]
  0 1
  [255]

-- one-high-tail
#guard check [255]
  0 4
  [255, 0, 0, 0]

-- one-exact-end
#guard check [255]
  1 1
  [0]

-- zero-prefix
#guard check [0, 1, 127, 128, 255]
  0 2
  [0, 1]

-- whole-mixed
#guard check [0, 1, 127, 128, 255]
  0 5
  [0, 1, 127, 128, 255]

-- contained-mixed
#guard check [0, 1, 127, 128, 255]
  1 3
  [1, 127, 128]

-- contained-high-end
#guard check [0, 1, 127, 128, 255]
  3 2
  [128, 255]

-- partial-last-byte
#guard check [0, 1, 127, 128, 255]
  4 4
  [255, 0, 0, 0]

-- partial-two-bytes
#guard check [0, 1, 127, 128, 255]
  3 4
  [128, 255, 0, 0]

-- whole-plus-zero
#guard check [0, 1, 127, 128, 255]
  0 6
  [0, 1, 127, 128, 255, 0]

-- exact-end-padding
#guard check [0, 1, 127, 128, 255]
  5 4
  [0, 0, 0, 0]

-- beyond-end-padding
#guard check [0, 1, 127, 128, 255]
  6 4
  [0, 0, 0, 0]

-- zero-inside
#guard check [0, 1, 127, 128, 255]
  2 0
  []

-- zero-at-end
#guard check [0, 1, 127, 128, 255]
  5 0
  []

-- zero-beyond-end
#guard check [0, 1, 127, 128, 255]
  9 0
  []

-- interior-zero
#guard check [255, 0, 128, 1]
  0 4
  [255, 0, 128, 1]

-- interior-zero-window
#guard check [255, 0, 128, 1]
  1 2
  [0, 128]

-- u64-before
#guard check [0, 1, 127, 128, 255]
  18446744073709551615 4
  [0, 0, 0, 0]

-- u64-at
#guard check [0, 1, 127, 128, 255]
  18446744073709551616 4
  [0, 0, 0, 0]

-- u64-after
#guard check [0, 1, 127, 128, 255]
  18446744073709551617 4
  [0, 0, 0, 0]

-- u64-after-nonzero-prefix
#guard check [255, 0, 128, 1]
  18446744073709551617 2
  [0, 0]

-- u256-max-zero
#guard check [255, 0, 128, 1]
  115792089237316195423570985008687907853269984665640564039457584007913129639935 0
  []

-- u256-max-one
#guard check [255, 0, 128, 1]
  115792089237316195423570985008687907853269984665640564039457584007913129639935 1
  [0]

-- u256-max-three
#guard check [255, 0, 128, 1]
  115792089237316195423570985008687907853269984665640564039457584007913129639935 3
  [0, 0, 0]

-- word-full
#guard check [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
    12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
    24, 25, 26, 27, 28, 29, 30, 31
  ]
  0 32
  [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
    12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
    24, 25, 26, 27, 28, 29, 30, 31
  ]

-- word-last-high-tail
#guard check [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
    12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
    24, 25, 26, 27, 28, 29, 30, 128
  ]
  30 4
  [30, 128, 0, 0]

-- word-plus-one
#guard check [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
    12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
    24, 25, 26, 27, 28, 29, 30, 31
  ]
  0 33
  [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
    12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
    24, 25, 26, 27, 28, 29, 30, 31, 0
  ]

end STFSpec.Conformance.Vm.Core.BufferReadGuards
