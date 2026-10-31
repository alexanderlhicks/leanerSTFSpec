/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block

/-!
# Small calldata-token controls

Library `EthConformance`. Complete scalar results; compiled larger inputs are separate.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §4.
-/

open STFSpec.Block
#guard countTokensInData ByteArray.empty == 0
#guard countTokensInData (ByteArray.mk #[0]) == 1
#guard countTokensInData (ByteArray.mk #[1]) == 4
#guard countTokensInData (ByteArray.mk #[255]) == 4
#guard countTokensInData (ByteArray.mk #[0, 1, 0, 255, 128]) == 14
