/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Vm.Core

/-!
# Complete small-code jump-destination guards

Library `EthConformance`. These thirty-two complete handwritten controls retain
every code byte, destination, logical bitmap byte and selected/padding/huge probe.
Logical bytes are reconstructed from public membership, not private storage reads.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Vm.Core.JumpdestGuards
open STFSpec.Vm.Core STFSpec.Base

#check_failure JumpdestMap.mk
#check_failure JumpdestMap.bitmap
#check_failure JumpdestMap.codeSize
#check_failure JumpdestMap.ext
#check_failure (⟨0, ByteArray.empty⟩ : JumpdestMap)
#check_failure (inferInstance : BEq JumpdestMap)
#check_failure (inferInstance : DecidableEq JumpdestMap)

private def agrees (code : List UInt8) (expected logical : List Nat)
    (probes : List (Nat × Bool)) : Bool :=
  let c := Bytes.ofList code
  let m := validJumpDestinations c
  let n := (c.size + 7) / 8
  let destinations := (List.range c.size).filter m.contains
  let memberships := (List.range (8 * n)).map m.contains
  let bytes := (List.range n).map fun j ↦
    ((List.range 8).map fun k ↦ if m.contains (j * 8 + k) then 2 ^ k else 0).sum
  destinations == expected && bytes == logical &&
    memberships == (List.range (8 * n)).map expected.contains &&
    probes.all (fun (i, wanted) ↦ m.contains i == wanted) && !m.contains (2 ^ 4096)

-- 01: empty
#guard agrees []
  [] []
  [(0, false), (1, false), (8, false)]

-- 02: single-destination
#guard agrees [91]
  [0] [1]
  [(0, true), (1, false), (7, false), (8, false)]

-- 03: invalid-0c
#guard agrees [12]
  [] [0]
  [(0, false), (1, false), (7, false)]

-- 04: invalid-fe-continues
#guard agrees [254, 91]
  [1] [2]
  [(0, false), (1, true), (2, false), (7, false)]

-- 05: two-invalids-continue
#guard agrees [12, 254, 91]
  [2] [4]
  [(0, false), (1, false), (2, true), (3, false)]

-- 06: stop-does-not-end-scan
#guard agrees [0, 91]
  [1] [2]
  [(0, false), (1, true), (2, false)]

-- 07: return-revert-selfdestruct-do-not-end-scan
#guard agrees [243, 91, 253, 91, 255, 91]
  [1, 3, 5] [42]
  [(0, false), (1, true), (3, true), (5, true), (6, false), (7, false)]

-- 08: push0-has-no-immediate
#guard agrees [95, 91]
  [1] [2]
  [(0, false), (1, true), (2, false)]

-- 09: push1-hides-destination
#guard agrees [96, 91]
  [] [0]
  [(0, false), (1, false), (2, false)]

-- 10: push1-resumes
#guard agrees [96, 91, 91]
  [2] [4]
  [(0, false), (1, false), (2, true), (3, false)]

-- 11: push2-hides-both-bytes
#guard agrees [97, 91, 91]
  [] [0]
  [(0, false), (1, false), (2, false), (3, false)]

-- 12: push2-resumes
#guard agrees [97, 91, 91, 91]
  [3] [8]
  [(1, false), (2, false), (3, true), (4, false)]

-- 13: push-opcode-inside-data-is-not-executed
#guard agrees [97, 96, 91, 91]
  [3] [8]
  [(0, false), (1, false), (2, false), (3, true), (4, false)]

-- 14: push32-byte-hidden-by-push1
#guard agrees [96, 127, 91, 91]
  [2, 3] [12]
  [(0, false), (1, false), (2, true), (3, true), (4, false)]

-- 15: push1-at-end
#guard agrees [96]
  [] [0]
  [(0, false), (1, false), (7, false)]

-- 16: push2-truncated
#guard agrees [97, 91]
  [] [0]
  [(0, false), (1, false), (2, false)]

-- 17: push32-truncated
#guard agrees [127, 91, 91]
  [] [0]
  [(0, false), (1, false), (2, false), (3, false), (32, false)]

-- 18: destination-before-truncated-push32
#guard agrees [91, 127, 91]
  [0] [1]
  [(0, true), (1, false), (2, false), (3, false)]

-- 19: dupn-guidance-example
#guard agrees [230, 91, 96, 91, 91]
  [1, 4] [18]
  [(0, false), (1, true), (2, false), (3, false), (4, true), (5, false)]

-- 20: swapn-guidance-companion
#guard agrees [231, 91, 96, 91, 91]
  [1, 4] [18]
  [(0, false), (1, true), (3, false), (4, true), (5, false)]

-- 21: exchange-guidance-companion
#guard agrees [232, 91, 96, 91, 91]
  [1, 4] [18]
  [(0, false), (1, true), (3, false), (4, true), (5, false)]

-- 22: three-extended-ops-do-not-skip
#guard agrees [230, 91, 231, 91, 232, 91]
  [1, 3, 5] [42]
  [(0, false), (1, true), (2, false), (3, true), (4, false), (5, true), (6, false)]

-- 23: dupn-byte-inside-push-data
#guard agrees [96, 230, 91]
  [2] [4]
  [(0, false), (1, false), (2, true), (3, false)]

-- 24: jump-and-jumpi-do-not-redirect-scan
#guard agrees [86, 91, 87, 91]
  [1, 3] [10]
  [(0, false), (1, true), (2, false), (3, true), (4, false)]

-- 25: bitmap-7-8-15-16-boundaries
#guard agrees [0, 0, 0, 0, 0, 0, 0, 91, 91, 0, 0, 0, 0, 0, 0, 91, 91]
  [7, 8, 15, 16] [128, 129, 1]
  [(6, false), (7, true), (8, true), (9, false), (14, false), (15, true), (16, true), (17,
    false), (23, false), (24, false)]

-- 26: nine-consecutive-destinations
#guard agrees [91, 91, 91, 91, 91, 91, 91, 91, 91]
  [0, 1, 2, 3, 4, 5, 6, 7, 8] [255, 1]
  [(0, true), (7, true), (8, true), (9, false), (15, false), (16, false)]

-- 27: only-final-bit-of-nine
#guard agrees [0, 0, 0, 0, 0, 0, 0, 0, 91]
  [8] [0, 1]
  [(0, false), (7, false), (8, true), (9, false), (15, false), (16, false)]

-- 28: valid-nonpush-nondestinations
#guard agrees [0, 1, 86, 87, 95, 230, 231, 232, 243, 253, 255]
  [] [0, 0]
  [(0, false), (7, false), (8, false), (10, false), (11, false), (15, false), (16, false)]

-- 29: full-push32-then-destination
#guard agrees [127, 91, 91, 91, 91, 91, 91, 91, 91, 91, 91, 91, 91, 91, 91, 91, 91, 91, 91, 91,
    91, 91, 91, 91, 91, 91, 91, 91, 91, 91, 91, 91, 91, 91]
  [33] [0, 0, 0, 0, 2]
  [(0, false), (1, false), (31, false), (32, false), (33, true), (34, false), (39, false), (40,
    false)]

-- 30: two-push1s-then-destination
#guard agrees [96, 91, 96, 91, 91]
  [4] [16]
  [(0, false), (1, false), (2, false), (3, false), (4, true), (5, false)]

-- 31: interleaved-destinations-and-pushes
#guard agrees [91, 96, 91, 91, 97, 91, 91, 91]
  [0, 3, 7] [137]
  [(0, true), (1, false), (2, false), (3, true), (4, false), (5, false), (6, false), (7, true),
    (8, false)]

-- 32: invalid-extended-push0-and-hidden-data
#guard agrees [254, 230, 91, 96, 91, 231, 91, 95, 91, 232, 91]
  [2, 6, 8, 10] [68, 5]
  [(0, false), (1, false), (2, true), (3, false), (4, false), (5, false), (6, true), (7, false),
    (8, true), (9, false), (10, true), (11, false), (15, false), (16, false)]

end STFSpec.Conformance.Vm.Core.JumpdestGuards
