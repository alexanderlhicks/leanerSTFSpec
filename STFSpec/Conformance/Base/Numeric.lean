/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base

/-!
# Numeric helper regression guards

Library `EthConformance`: unbounded checked subtraction and rounding boundaries.
These tests use the public API at 0/1/31/32/33 and values above fixed-word widths.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §4.
-/

open STFSpec.Base

#guard Uint.sub? 0 1 = none
#guard Uint.sub? 0 0 = some 0
#guard Uint.sub? 1 0 = some 1
#guard Uint.sub? 1 1 = some 0
#guard Uint.sub? 31 32 = none
#guard Uint.sub? 32 31 = some 1
#guard Uint.sub? 33 32 = some 1
#guard Uint.sub? (2 ^ 256) 1 = some (2 ^ 256 - 1)
#guard Uint.sub? (2 ^ 256) (2 ^ 256) = some 0
#guard Uint.sub? (2 ^ 256) (2 ^ 256 + 1) = none
#guard Uint.sub? (2 ^ 4096 + 33) (2 ^ 4096 + 1) = some 32
#guard Uint.sub? (2 ^ 4096 + 1) (2 ^ 4096 + 33) = none
#guard Uint.sub? (2 ^ 4096) 0 = some (2 ^ 4096)
#guard ceil32 0 = 0
#guard ceil32 1 = 32
#guard ceil32 31 = 32
#guard ceil32 32 = 32
#guard ceil32 33 = 64
#guard ceil32 63 = 64
#guard ceil32 64 = 64
#guard ceil32 65 = 96
#guard ceil32 (2 ^ 64 - 1) = 2 ^ 64
#guard ceil32 (2 ^ 256 - 1) = 2 ^ 256
#guard ceil32 (2 ^ 256) = 2 ^ 256
#guard ceil32 (2 ^ 256 + 1) = 2 ^ 256 + 32
#guard ceil32 (2 ^ 4096 + 31) = 2 ^ 4096 + 32
#guard ceil32 (2 ^ 4096 + 32) = 2 ^ 4096 + 32
#guard ceil32 (2 ^ 4096 + 33) = 2 ^ 4096 + 64
