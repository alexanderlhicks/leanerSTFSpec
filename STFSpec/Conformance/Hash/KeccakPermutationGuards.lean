/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Hash

/-!
# Reference permutation guards

Library `EthConformance`. The zero-state expected lanes are transcribed from the
Keccak team's round-3 KAT archive, `KeccakKAT/KeccakPermutationIntermediateValues.txt`,
first "Example with the all-zero input" / "State after permutation". Its serialized
bytes are decoded as little-endian lanes in x+5*y order (FIPS 202 §3.1.2).

Source: https://keccak.team/obsolete/KeccakKAT-3.zip
Archive SHA-256: af92d22d23527a0d168a6bbe70b28c840a43bba5bcea828a6d9a5e7ad79378ce
Member SHA-256: db0947545a5d91c20b2105aac75fac430deafe0ccaecb660af60044244df30d4

Other guards are elementary coordinate/bit probes, not host-derived KATs.
Spec guidance: `STFSpec/informal/modules/EthHash.md` §4.
-/

open STFSpec.Hash

private def zeroState : KeccakState := Vector.replicate 25 0
private def asymmetricState : KeccakState := Vector.ofFn fun i ↦ UInt64.ofNat i.val

-- All 25 primary permutation lanes, rather than a truncated digest.
#guard keccakF1600 zeroState =
  #v[0xf1258f7940e1dde7, 0x84d5ccf933c0478a, 0xd598261ea65aa9ee,
     0xbd1547306f80494d, 0x8b284e056253d057, 0xff97a42d7f8e6fd4,
     0x90fee5a0a44647c4, 0x8c5bda0cd6192e76, 0xad30a6f71b19059c,
     0x30935ab7d08ffc64, 0xeb5aa93f2317d635, 0xa9a6e6260d712103,
     0x81a57c16dbcf555f, 0x43b831cd0347c826, 0x01f22f1a11a5569f,
     0x05e5635a21d9ae61, 0x64befef28cc970f2, 0x613670957bc46611,
     0xb87c5a554fd00ecb, 0x8c3ee88a1ccf32c8, 0x940c7922ae3a2614,
     0x1841f924a2c509e4, 0x16f53526e70465c2, 0x75f644e97f30a13b,
     0xeaf1ff7b5ceca249]

#guard keccakLane asymmetricState 0 0 = 0
#guard keccakLane asymmetricState 4 0 = 4
#guard keccakLane asymmetricState 0 1 = 5
#guard keccakLane asymmetricState 4 4 = 24
#guard keccakLane (keccakTheta asymmetricState) 0 0 = 26
#guard keccakLane (keccakRho asymmetricState) 1 0 = 2
#guard keccakLane (keccakPi asymmetricState) 2 3 = 11
#guard keccakLane (keccakChi asymmetricState) 1 0 = 0
#guard keccakLane (keccakIota asymmetricState 0) 0 0 = 1
#guard keccakLane (keccakIota asymmetricState 23) 0 0 = 0x8000000080008008
#guard keccakLane (keccakIota asymmetricState 23) 4 4 = 24
#guard keccakLane (keccakRound zeroState 0) 0 0 = 1
#guard keccakLane (keccakRound zeroState 0) 4 4 = 0
#guard keccakRounds asymmetricState 0 (by decide) = asymmetricState
#guard keccakRounds asymmetricState 1 (by decide) = keccakRound asymmetricState 0
#guard keccakRotl 0x0123456789abcdef 0 = 0x0123456789abcdef
#guard keccakRotl 0x0123456789abcdef 64 = 0x0123456789abcdef
#guard keccakRotl 0x0123456789abcdef 128 = 0x0123456789abcdef
#guard keccakRotl 0x8000000000000000 1 = 1
#guard keccakRotl 1 63 = 0x8000000000000000
#guard keccakRotl 1 65 = 2
#guard keccakRotl 0x0123456789abcdef 8 = 0x23456789abcdef01
#guard (keccakToModel (keccakOfLanes fun _ _ ↦ 0x0102030405060708) (0, 0)).getLsbD 3
#guard !(keccakToModel (keccakOfLanes fun _ _ ↦ 0x0102030405060708) (0, 0)).getLsbD 0
