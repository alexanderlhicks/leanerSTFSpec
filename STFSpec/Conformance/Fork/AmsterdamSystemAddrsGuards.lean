/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block
import STFSpec.Fork

/-!
# Complete Amsterdam system-address controls

Library `EthConformance`. Public-facade type and whole-record controls, retaining all
160 address bytes (including leading zeros) and both independent natural budgets.
Spec guidance: `STFSpec/informal/modules/EthFork.md` §§3–4.
-/

open STFSpec STFSpec.Fork.Amsterdam

private def value_type : Block.SystemAddrs := systemAddrs

private theorem complete_value : systemAddrs = Block.SystemAddrs.mk
    (Base.Address.ofNat 0xfffffffffffffffffffffffffffffffffffffffe)
    (Base.Address.ofNat 0x000f3df6d732807ef1319fb7b8bb8522d0beac02)
    (Base.Address.ofNat 0x0000f90827f1c53a10cb7a02335b175320002935)
    (Base.Address.ofNat 0x00000961ef480eb55e80d19ad83579a64c007002)
    (Base.Address.ofNat 0x0000bbddc7ce488642fb579f8b00f3a590007251)
    (Base.Address.ofNat 0x0000bff46984e3725691fa540a8c7589300d8282)
    (Base.Address.ofNat 0x000064d678505ad48f8ccb093bc65613800e8282)
    (Base.Address.ofNat 0x00000000219ab540356cbb839cbe05303d7705fa)
    30000000 16 := rfl

private def addressBytes (a : Base.Address) : List Nat :=
  a.toBytes.toList.map UInt8.toNat

#guard addressBytes systemAddrs.systemAddress ==
  [255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 254]
#guard addressBytes systemAddrs.beaconRoots ==
  [0, 15, 61, 246, 215, 50, 128, 126, 241, 49, 159, 183, 184, 187, 133, 34, 208, 190, 172, 2]
#guard addressBytes systemAddrs.historyStorage ==
  [0, 0, 249, 8, 39, 241, 197, 58, 16, 203, 122, 2, 51, 91, 23, 83, 32, 0, 41, 53]
#guard addressBytes systemAddrs.withdrawalRequests ==
  [0, 0, 9, 97, 239, 72, 14, 181, 94, 128, 209, 154, 216, 53, 121, 166, 76, 0, 112, 2]
#guard addressBytes systemAddrs.consolidationRequests ==
  [0, 0, 187, 221, 199, 206, 72, 134, 66, 251, 87, 159, 139, 0, 243, 165, 144, 0, 114, 81]
#guard addressBytes systemAddrs.builderDeposits ==
  [0, 0, 191, 244, 105, 132, 227, 114, 86, 145, 250, 84, 10, 140, 117, 137, 48, 13, 130, 130]
#guard addressBytes systemAddrs.builderExits ==
  [0, 0, 100, 214, 120, 80, 90, 212, 143, 140, 203, 9, 59, 198, 86, 19, 128, 14, 130, 130]
#guard addressBytes systemAddrs.depositContract ==
  [0, 0, 0, 0, 33, 154, 181, 64, 53, 108, 187, 131, 156, 190, 5, 48, 61, 119, 5, 250]

#guard systemAddrs.txGas == 30000000
#guard systemAddrs.maxSstoresPerCall == 16
#guard (systemAddrs.txGas, systemAddrs.maxSstoresPerCall) == (30000000, 16)
