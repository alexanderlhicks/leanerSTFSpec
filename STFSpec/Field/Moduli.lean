/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

/-!
# Exact base and scalar moduli

Library `EthField`. These are natural constants only: no field instances, aliases,
primality certificates, square-root metadata or Montgomery parameters are supplied.
EELS citations are at `e1a316a06fc3d3e0a5da36fdc78580811e9d8a36`; dependency
citations refer to py-ecc 8.0.0 locked by that source's `uv.lock`.
Spec guidance: `STFSpec/informal/modules/EthField.md` R1 and §§3–7.
-/

namespace STFSpec.Field

/-- BN254 base modulus: py-ecc `py_ecc/fields/field_properties.py:24` (`bn128`). -/
def Bn254.q : Nat :=
  21888242871839275222246405745257275088696311157297823662689037894645226208583

/-- BN254 scalar modulus: py-ecc `py_ecc/optimized_bn128/optimized_curve.py:17–19`. -/
def Bn254.r : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- BLS12-381 base modulus: py-ecc `py_ecc/fields/field_properties.py:29` (`bls12_381`). -/
def Bls12381.q : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

/--
BLS12-381 scalar modulus: py-ecc `py_ecc/optimized_bls12_381/optimized_curve.py:17–19`;
EELS `src/ethereum/crypto/kzg.py:59–61` and
`src/ethereum/forks/amsterdam/vm/precompiled_contracts/point_evaluation.py:28`.
-/
def Bls12381.r : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

/-- secp256k1 base modulus: EELS `src/ethereum/crypto/elliptic_curve.py:18–20`. -/
def Secp256k1.p : Nat :=
  0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f

/-- secp256k1 scalar modulus: EELS `src/ethereum/crypto/elliptic_curve.py:21–23`. -/
def Secp256k1.n : Nat :=
  0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

/-- P-256 base modulus: EELS `src/ethereum/crypto/elliptic_curve.py:82–84`. -/
def P256.p : Nat :=
  0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff

/-- P-256 scalar modulus: EELS `src/ethereum/crypto/elliptic_curve.py:79–81`. -/
def P256.n : Nat :=
  0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551

end STFSpec.Field
