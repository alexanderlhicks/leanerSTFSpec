/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Field

/-!
# Complete natural-modulus controls

Library `EthConformance`. Private complete-value controls distinguish every base/scalar
pair and check elementary bounds and residues. They do not prove primality.
Spec guidance: `STFSpec/informal/modules/EthField.md` R1 and §§3–7.
-/

namespace STFSpec.Conformance.Field
open STFSpec.Field

private def moduli : List (String × Nat) :=
  [ ("Bn254.q", Bn254.q),
    ("Bn254.r", Bn254.r),
    ("Bls12381.q", Bls12381.q),
    ("Bls12381.r", Bls12381.r),
    ("Secp256k1.p", Secp256k1.p),
    ("Secp256k1.n", Secp256k1.n),
    ("P256.p", P256.p),
    ("P256.n", P256.n) ]

private def expected : List (String × Nat) :=
  [ ("Bn254.q",
      21888242871839275222246405745257275088696311157297823662689037894645226208583),
    ("Bn254.r",
      21888242871839275222246405745257275088548364400416034343698204186575808495617),
    ("Bls12381.q",
      4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787),
    ("Bls12381.r",
      52435875175126190479447740508185965837690552500527637822603658699938581184513),
    ("Secp256k1.p",
      115792089237316195423570985008687907853269984665640564039457584007908834671663),
    ("Secp256k1.n",
      115792089237316195423570985008687907852837564279074904382605163141518161494337),
    ("P256.p",
      115792089210356248762697446949407573530086143415290314195533631308867097853951),
    ("P256.n",
      115792089210356248762697446949407573529996955224135760342422259061068512044369) ]

#guard moduli == expected
#guard moduli.map (fun row ↦ row.2.log2 + 1) == [254, 254, 381, 255, 256, 256, 256, 256]
#guard moduli.all (fun row ↦ 1 < row.2 && row.2 < 2^384)
#guard moduli.all (fun row ↦ row.1 == "Bls12381.q" || row.2 < 2^256)
#guard moduli.map (fun row ↦ row.2 % 4) == [3, 1, 3, 1, 3, 1, 3, 1]
#guard Bn254.q != Bn254.r && Bls12381.q != Bls12381.r &&
  Secp256k1.p != Secp256k1.n && P256.p != P256.n

end STFSpec.Conformance.Field
