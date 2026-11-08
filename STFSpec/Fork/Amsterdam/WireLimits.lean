/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import Init

/-!
# Amsterdam input wire limits

Library `EthFork`. Independent fixed bounds for witness members and payload extra data.
Spec guidance: `STFSpec/informal/modules/EthFork.md` §§3–7.
-/

namespace STFSpec.Fork.Amsterdam

/-- Witness header count bound; EELS
`src/ethereum/forks/amsterdam/stateless.py:32,63–66` at the pin. -/
def MAX_WITNESS_HEADERS : Nat := 256

/-- Witness code byte bound; EELS
`src/ethereum/forks/amsterdam/stateless.py:33,55–58` at the pin. -/
def MAX_BYTES_PER_CODE : Nat := 2 ^ 16

/-- Witness header byte bound; EELS
`src/ethereum/forks/amsterdam/stateless.py:34,63–66` at the pin. -/
def MAX_BYTES_PER_HEADER : Nat := 2 ^ 10

/-- Witness state-node byte bound; EELS
`src/ethereum/forks/amsterdam/stateless.py:35,46–49` at the pin. -/
def MAX_BYTES_PER_WITNESS_NODE : Nat := 2 ^ 10

/-- Payload extra-data byte bound; EELS
`src/ethereum/forks/amsterdam/execution_engine/types.py:33,61` at the pin. -/
def MAX_EXTRA_DATA_BYTES : Nat := 32

end STFSpec.Fork.Amsterdam
