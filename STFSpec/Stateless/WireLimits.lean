/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Fork.Amsterdam.WireLimits

/-!
# Stateless input wire-limit aliases

Library `EthStateless`. Consumer names for the Fork-owned Amsterdam values (F8).
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3–7.
-/

namespace STFSpec.Stateless

/-- Alias of the Amsterdam witness header count bound; EELS
`src/ethereum/forks/amsterdam/stateless.py:32` at the pin. -/
abbrev maxWitnessHeaders : Nat := Fork.Amsterdam.MAX_WITNESS_HEADERS

/-- Alias of the Amsterdam witness code byte bound; EELS
`src/ethereum/forks/amsterdam/stateless.py:33` at the pin. -/
abbrev maxBytesPerCode : Nat := Fork.Amsterdam.MAX_BYTES_PER_CODE

/-- Alias of the Amsterdam witness header byte bound; EELS
`src/ethereum/forks/amsterdam/stateless.py:34` at the pin. -/
abbrev maxBytesPerHeader : Nat := Fork.Amsterdam.MAX_BYTES_PER_HEADER

/-- Alias of the Amsterdam witness state-node byte bound; EELS
`src/ethereum/forks/amsterdam/stateless.py:35` at the pin. -/
abbrev maxBytesPerWitnessNode : Nat := Fork.Amsterdam.MAX_BYTES_PER_WITNESS_NODE

/-- Alias of the Amsterdam payload extra-data byte bound; EELS
`src/ethereum/forks/amsterdam/execution_engine/types.py:33` at the pin. -/
abbrev maxExtraDataBytes : Nat := Fork.Amsterdam.MAX_EXTRA_DATA_BYTES

end STFSpec.Stateless
