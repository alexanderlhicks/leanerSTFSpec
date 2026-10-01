/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Hash

/-!
# RIPEMD-160 compression guards

Library `EthConformance`. Primary empty/abc digest facts from the authors' page
https://homes.esat.kuleuven.be/~bosselae/ripemd160.html are decoded into little-endian
chaining words. The inputs below are explicitly supplied padded blocks, using MD4
padding (author pseudocode; RFC 1320 §§3.1–3.2) and little-endian 32-bit parsing.
These are compression KATs; no production digest or parser is exercised.
Other probes check asymmetry, wraparound, branch group boundaries and simultaneous
original-state feedforward. Generated arbitrary-state cases use a separate integer
model and remain evidence outside the checkout.
Spec guidance: `STFSpec/informal/modules/EthHash.md` §§3–4.
-/

namespace STFSpec.Conformance.Hash.Ripemd160CompressionGuards
open STFSpec.Hash

-- Explicit MD4-padded empty input: 0x80 then zeros, low-64-bit trailer zero.
#guard ripemd160Compress ripemd160IV
  #v[0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] =
  #v[0xa585119c, 0x54fce9c5, 0x97082861, 0x48f5e87e, 0x318d25b2]
-- Explicit MD4-padded abc: bytes 61 62 63 80; trailer length 24 bits.
#guard ripemd160Compress ripemd160IV
  #v[0x80636261, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0] =
  #v[0xf708b28e, 0x7a985de0, 0x8e4a049b, 0x87b0c698, 0xfc0b5af1]

#guard ripemd160IV = #v[0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0]
#guard ripemd160Rotl 1 0 = 1
#guard ripemd160Rotl 1 31 = 0x80000000
#guard ripemd160Rotl 0x80000000 1 = 1
#guard ripemd160Rotl 0x12345678 32 = 0x12345678
#guard ripemd160Rotl 1 33 = 2
#guard ripemd160Rotl 0x80000001 64 = 0x80000001
#guard ripemd160F 0 0xf0 0xcc 0xaa = 0x96
#guard ripemd160F 15 0xf0 0xcc 0xaa = 0x96
#guard ripemd160F 16 0xf0 0xcc 0xaa = 0xca
#guard ripemd160F 31 0xf0 0xcc 0xaa = 0xca
#guard ripemd160F 32 0xf0 0xcc 0xaa = 0xffffff59
#guard ripemd160F 47 0xf0 0xcc 0xaa = 0xffffff59
#guard ripemd160F 48 0xf0 0xcc 0xaa = 0xe4
#guard ripemd160F 63 0xf0 0xcc 0xaa = 0xe4
#guard ripemd160F 64 0xf0 0xcc 0xaa = 0xffffff2d
#guard ripemd160F 79 0xf0 0xcc 0xaa = 0xffffff2d
#guard ripemd160Group 15 = 0
#guard ripemd160Group 16 = 1
#guard ripemd160Group 32 = 2
#guard ripemd160Group 48 = 3
#guard ripemd160Group 64 = 4
#guard ripemd160Reverse 0 = 79
#guard ripemd160Reverse 79 = 0
#guard ripemd160LeftOrder[16] = 7
#guard ripemd160RightOrder[16] = 6
#guard ripemd160LeftRotations[79] = 6
#guard ripemd160RightRotations[79] = 11
#guard ripemd160LeftConstants[4] = 0xa953fd4e
#guard ripemd160RightConstants[4] = 0
#guard ripemd160Feedforward #v[1, 10, 100, 1000, 10000]
  ⟨#v[2, 20, 200, 2000, 20000], #v[3, 30, 300, 3000, 30000]⟩ =
  #v[3210, 32100, 21003, 10032, 321]
#guard ripemd160Feedforward #v[0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff]
  ⟨#v[1, 1, 1, 1, 1], #v[1, 1, 1, 1, 1]⟩ = #v[1, 1, 1, 1, 1]
#guard ripemd160Step #v[1, 2, 3, 4, 5] 0 0 0 0 = #v[5, 11, 2, 3072, 4]
#guard ripemd160Rounds ⟨#v[1, 2, 3, 4, 5], #v[6, 7, 8, 9, 10]⟩
  #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] 0 (by decide) =
  ⟨#v[1, 2, 3, 4, 5], #v[6, 7, 8, 9, 10]⟩

end STFSpec.Conformance.Hash.Ripemd160CompressionGuards
