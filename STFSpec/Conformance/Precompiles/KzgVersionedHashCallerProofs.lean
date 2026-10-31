/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Precompiles

/-!
# Public KZG result-law clients

Library `EthConformance`. These clients use only public Base/Hash/Kzg contracts.
Spec guidance: `STFSpec/informal/modules/EthPrecompiles.md` §§3/7.
-/

open STFSpec.Base STFSpec.Precompiles.Kzg

private theorem result_size (commitment : ByteArray) :
    (commitmentToVersionedHash commitment).toBytes.size = 32 :=
  Hash32.size_toBytes _

private theorem result_prefix (commitment : ByteArray) :
    (commitmentToVersionedHash commitment).toBytes.toList[0]? = some 0x01 := by
  rw [commitmentToVersionedHash_toBytes]
  rfl

private theorem result_suffix (commitment : ByteArray) (i : Nat) :
    (commitmentToVersionedHash commitment).toBytes.toList[i + 1]? =
      (STFSpec.Hash.sha256 commitment).toBytes.toList[i + 1]? := by
  rw [commitmentToVersionedHash_toBytes]
  simp only [List.getElem?_cons_succ, List.getElem?_drop, Nat.add_comm]

private theorem result_determined (commitment : ByteArray) (result : VersionedHash)
    (h : result.toBytes.toList =
      versionedHashVersionKzg :: (STFSpec.Hash.sha256 commitment).toBytes.toList.drop 1) :
    result = commitmentToVersionedHash commitment := by
  apply Hash32.toBytes_inj.mp
  apply Bytes.ext
  rw [h, commitmentToVersionedHash_toBytes]
