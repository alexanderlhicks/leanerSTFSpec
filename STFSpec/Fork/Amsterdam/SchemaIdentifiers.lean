/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import Init

/-!
# Amsterdam stateless input schema identifiers

Library `EthFork`. Selected input schema data, owned here under F8.
Spec guidance: `STFSpec/informal/modules/EthFork.md` §§3–7.
-/

namespace STFSpec.Fork.Amsterdam

/-- Raw selected fork tag; EELS
`src/ethereum/forks/amsterdam/stateless.py:126,129` at the pin. -/
def STATELESS_INPUT_SCHEMA_FORK_INDEX : UInt8 := 0x15

/-- Selected schema revision; EELS
`src/ethereum/forks/amsterdam/stateless.py:130` at the pin. -/
def STATELESS_INPUT_SCHEMA_REVISION : UInt8 := 0x01

/-- Selected schema ID, derived from the owned tag and revision; EELS
`src/ethereum/forks/amsterdam/stateless.py:131–133` at the pin. -/
def STATELESS_INPUT_SCHEMA_ID : UInt16 :=
  (STATELESS_INPUT_SCHEMA_FORK_INDEX.toUInt16 <<< 8) |||
    STATELESS_INPUT_SCHEMA_REVISION.toUInt16

/-- Input schema prefix width; EELS
`src/ethereum/forks/amsterdam/stateless.py:134` at the pin. -/
def STATELESS_INPUT_SCHEMA_ID_SIZE : Nat := 2

/-- Complete two-byte big-endian encoding of the owned schema ID; EELS
`src/ethereum/forks/amsterdam/stateless.py:135–138` at the pin.
The first byte reads the ID's high eight bits, and the second reads its low eight bits. -/
def STATELESS_INPUT_SCHEMA_ID_BYTES : ByteArray :=
  ⟨#[(STATELESS_INPUT_SCHEMA_ID >>> 8).toUInt8, STATELESS_INPUT_SCHEMA_ID.toUInt8]⟩

private theorem schema_bytes_eq : STATELESS_INPUT_SCHEMA_ID_BYTES =
    ⟨#[STATELESS_INPUT_SCHEMA_FORK_INDEX, STATELESS_INPUT_SCHEMA_REVISION]⟩ := by
  decide

private theorem schema_bytes_size :
    STATELESS_INPUT_SCHEMA_ID_BYTES.size = STATELESS_INPUT_SCHEMA_ID_SIZE := rfl

end STFSpec.Fork.Amsterdam
