/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import Init.Data.UInt.Basic

/-!
# Protocol fork identifiers

Library `EthStateless`. Historical identifiers and their stable numeric tags.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3–7.
-/

namespace STFSpec.Stateless

/-- The complete historical identifier inventory in EELS
`src/ethereum/forks/amsterdam/stateless.py:101–126` at the pin. -/
inductive ProtocolFork
  | frontier
  | homestead
  | daoFork
  | tangerineWhistle
  | spuriousDragon
  | byzantium
  | stPetersburg
  | istanbul
  | muirGlacier
  | berlin
  | london
  | arrowGlacier
  | grayGlacier
  | paris
  | shanghai
  | cancun
  | prague
  | osaka
  | bpo1
  | bpo2
  | amsterdam

/-- Forward observation of the explicit EELS `IntEnum` tags in
`src/ethereum/forks/amsterdam/stateless.py:106–126` at the pin. -/
def ProtocolFork.toIndex : ProtocolFork → UInt8
  | .frontier => 0x01
  | .homestead => 0x02
  | .daoFork => 0x03
  | .tangerineWhistle => 0x04
  | .spuriousDragon => 0x05
  | .byzantium => 0x06
  | .stPetersburg => 0x07
  | .istanbul => 0x08
  | .muirGlacier => 0x09
  | .berlin => 0x0a
  | .london => 0x0b
  | .arrowGlacier => 0x0c
  | .grayGlacier => 0x0d
  | .paris => 0x0e
  | .shanghai => 0x0f
  | .cancun => 0x10
  | .prague => 0x11
  | .osaka => 0x12
  | .bpo1 => 0x13
  | .bpo2 => 0x14
  | .amsterdam => 0x15

end STFSpec.Stateless
