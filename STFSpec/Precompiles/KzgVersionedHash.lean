/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Hash.Sha256Digest

/-!
# KZG commitment versioned hashes

Library `EthPrecompiles`. The raw byte helper replaces exactly the first SHA-256
byte with the KZG wire tag; it does not validate a commitment or proof.
Spec guidance: `STFSpec/informal/modules/EthPrecompiles.md` §§3/5/7.
-/

namespace STFSpec.Precompiles.Kzg
open STFSpec.Base

/-- KZG versioned-hash wire tag. Pinned EELS
`src/ethereum/crypto/kzg.py:54`. -/
def versionedHashVersionKzg : UInt8 := 0x01

private def versionedBytes (digest : Bytes32) : Bytes :=
  Bytes.ofList (versionedHashVersionKzg :: digest.toBytes.toList.drop 1)

private theorem size_versionedBytes (digest : Bytes32) :
    (versionedBytes digest).size = 32 := by
  rw [versionedBytes, Bytes.size_ofList, List.length_cons, List.length_drop,
    Bytes.length_toList, FixedBytes.size_toBytes]

private def packVersionedHash (digest : Bytes32) : VersionedHash :=
  (Hash32.ofBytes? (versionedBytes digest)).get (by
    apply Option.isSome_iff_ne_none.mpr
    intro h
    exact Hash32.ofBytes?_eq_none_iff.mp h (size_versionedBytes digest))

private theorem toBytes_packVersionedHash (digest : Bytes32) :
    (packVersionedHash digest).toBytes = versionedBytes digest := by
  apply (Hash32.ofBytes?_eq_some_iff.mp ?_).2
  exact (Option.some_get (x := Hash32.ofBytes? (versionedBytes digest)) _).symm

/-- Hash arbitrary commitment bytes once and retain SHA-256 bytes 1 through 31
in order after the wire tag. Pinned EELS
`src/ethereum/crypto/kzg.py:65–74`. There is no 48-byte admission or proof check.
Q46 supplies the total SHA extension; source/FIPS correspondence additionally
requires `8 * commitment.size < 2^64` and successful host/hash/constructor operations. -/
def commitmentToVersionedHash (commitment : ByteArray) : VersionedHash :=
  packVersionedHash (Hash.sha256 commitment)

/-- Complete result equation, including every suffix byte and any zero bytes.
Discarding SHA byte zero supplies no injectivity or cryptographic binding claim. -/
theorem commitmentToVersionedHash_toBytes (commitment : ByteArray) :
    (commitmentToVersionedHash commitment).toBytes.toList =
      versionedHashVersionKzg :: (STFSpec.Hash.sha256 commitment).toBytes.toList.drop 1 := by
  rw [commitmentToVersionedHash, toBytes_packVersionedHash, versionedBytes,
    Bytes.toList_ofList]

end STFSpec.Precompiles.Kzg
