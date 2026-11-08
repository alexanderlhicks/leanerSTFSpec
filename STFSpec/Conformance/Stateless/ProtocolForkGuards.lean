/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless

/-!
# Complete protocol fork tag controls

Library `EthConformance`. Every complete UInt8 observation is compared with an
independently written literal from EELS `stateless.py:106–126` at the pin.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3–4.
-/

open STFSpec.Stateless

#guard ProtocolFork.frontier.toIndex.toNat == 0x01
#guard ProtocolFork.homestead.toIndex.toNat == 0x02
#guard ProtocolFork.daoFork.toIndex.toNat == 0x03
#guard ProtocolFork.tangerineWhistle.toIndex.toNat == 0x04
#guard ProtocolFork.spuriousDragon.toIndex.toNat == 0x05
#guard ProtocolFork.byzantium.toIndex.toNat == 0x06
#guard ProtocolFork.stPetersburg.toIndex.toNat == 0x07
#guard ProtocolFork.istanbul.toIndex.toNat == 0x08
#guard ProtocolFork.muirGlacier.toIndex.toNat == 0x09
#guard ProtocolFork.berlin.toIndex.toNat == 0x0a
#guard ProtocolFork.london.toIndex.toNat == 0x0b
#guard ProtocolFork.arrowGlacier.toIndex.toNat == 0x0c
#guard ProtocolFork.grayGlacier.toIndex.toNat == 0x0d
#guard ProtocolFork.paris.toIndex.toNat == 0x0e
#guard ProtocolFork.shanghai.toIndex.toNat == 0x0f
#guard ProtocolFork.cancun.toIndex.toNat == 0x10
#guard ProtocolFork.prague.toIndex.toNat == 0x11
#guard ProtocolFork.osaka.toIndex.toNat == 0x12
#guard ProtocolFork.bpo1.toIndex.toNat == 0x13
#guard ProtocolFork.bpo2.toIndex.toNat == 0x14
#guard ProtocolFork.amsterdam.toIndex.toNat == 0x15
