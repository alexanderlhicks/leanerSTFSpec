/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.Bytes
import STFSpec.Base.FixedBytes
import STFSpec.Base.IntegerBytes
import STFSpec.Base.Numeric
import STFSpec.Base.U16
import STFSpec.Base.U256
import STFSpec.Base.U256Arithmetic
import STFSpec.Base.U256Bitwise
import STFSpec.Base.U256Exp
import STFSpec.Base.U256ShiftLaws
import STFSpec.Base.U256Signed
import STFSpec.Base.U32
import STFSpec.Base.U64
import STFSpec.Base.U8
import STFSpec.Base.ValueRecords

/-!
# STFSpec.Base

Primitive words, bytes and conversions, fixed byte domains, authorization and state-gas
records, and concrete hash-constant values. No fork policy.

Library `EthBase`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). Implementation status is owned by the
spec guidance document.
Spec guidance: `STFSpec/informal/modules/EthBase.md`.
-/
