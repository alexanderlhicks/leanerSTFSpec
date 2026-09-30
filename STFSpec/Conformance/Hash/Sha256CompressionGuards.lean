/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Hash

/-!
# Fixed-block SHA-256 compression guards

Library `EthConformance`. These are compression KATs of explicitly supplied words,
not tests of a production padding or digest API. Empty-message digest: NIST CAVP
`shabytetestvectors/SHA256ShortMsg.rsp`, Len=0 (CAVS 11.0, 2011-03-15),
https://csrc.nist.gov/Projects/cryptographic-algorithm-validation-program/Secure-Hashing.
The abc block, intermediate states and digest are selected facts from NIST's
SHA256 worked example, One Block Message Sample, PDF pages 1–3:
https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA256.pdf.
Spec guidance: `STFSpec/informal/modules/EthHash.md` §§3–4.
-/

open STFSpec.Hash STFSpec.Hash.Sha256

namespace STFSpec.Conformance.Hash.Sha256Compression

private def emptyBlock : Vector UInt32 16 := #v[
  0x80000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def abcBlock : Vector UInt32 16 := #v[
  0x61626380, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x18]

#guard sha256Compress initialState emptyBlock = #v[
  0xe3b0c442, 0x98fc1c14, 0x9afbf4c8, 0x996fb924,
  0x27ae41e4, 0x649b934c, 0xa495991b, 0x7852b855]
#guard sha256Compress initialState abcBlock = #v[
  0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223,
  0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad]

-- States AFTER rounds 0,1,16,63, hence prefix lengths 1,2,17,64.
#guard rounds (schedule abcBlock) initialState 1 (by decide) = #v[
  0x5d6aebcd, 0x6a09e667, 0xbb67ae85, 0x3c6ef372,
  0xfa2a4622, 0x510e527f, 0x9b05688c, 0x1f83d9ab]
#guard rounds (schedule abcBlock) initialState 2 (by decide) = #v[
  0x5a6ad9ad, 0x5d6aebcd, 0x6a09e667, 0xbb67ae85,
  0x78ce7989, 0xfa2a4622, 0x510e527f, 0x9b05688c]
#guard rounds (schedule abcBlock) initialState 17 (by decide) = #v[
  0x21da9a9b, 0xb0fa238e, 0xc0645fde, 0xd932eb16,
  0x8034229c, 0x07590dcd, 0x0b92f20c, 0x745a48de]
#guard rounds (schedule abcBlock) initialState 64 (by decide) = #v[
  0x506e3058, 0xd39a2165, 0x04d24d6c, 0xb85e2ce9,
  0x5ef50f24, 0xfb121210, 0x948d25b6, 0x961f4894]

-- Exact arithmetic/rotation probes; expectations follow bit positions and wrapping.
#guard rotr 0x80000001 1 = 0xc0000000
#guard rotr 0x80000001 31 = 3
#guard smallSigma0 0xffffffff ≠ bigSigma0 0xffffffff
#guard ch 0xffffffff 0x12345678 0xdeadbeef = 0x12345678
#guard ch 0 0x12345678 0xdeadbeef = 0xdeadbeef
#guard maj 0x12345678 0x12345678 0xdeadbeef = 0x12345678
#guard feedForward (#v[0xffffffff, 1, 0, 0x80000000, 0, 0, 0, 3])
  (#v[1, 0xffffffff, 1, 0x80000000, 0, 0, 0, 5]) = #v[0, 0, 1, 0, 0, 0, 0, 8]

private def asymmetricBlock : Vector UInt32 16 :=
  Vector.ofFn fun i => UInt32.ofNat (i.val * 0x1020304 + 0x80000001)
private def asymmetricState : Vector UInt32 8 :=
  #v[0, 0xffffffff, 0x80000000, 1, 0x12345678, 0x87654321, 0xa5a5a5a5, 0x5a5a5a5a]

#guard (schedule asymmetricBlock)[0] = asymmetricBlock[0]
#guard (schedule asymmetricBlock)[15] = asymmetricBlock[15]
#guard (schedule asymmetricBlock)[16] = smallSigma1 asymmetricBlock[14] +
  asymmetricBlock[9] + smallSigma0 asymmetricBlock[1] + asymmetricBlock[0]
#guard wordsModel (round asymmetricState 0xffffffff 0xfffffffe) =
  Model.round (wordsModel asymmetricState) 0xffffffff 0xfffffffe
#guard wordsModel (sha256Compress asymmetricState asymmetricBlock) =
  Model.compress (wordsModel asymmetricState) (wordsModel asymmetricBlock)

end STFSpec.Conformance.Hash.Sha256Compression
