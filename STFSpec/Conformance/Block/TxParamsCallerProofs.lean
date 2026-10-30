/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block

/-!
# Public raw transaction parameter clients

Library `EthConformance`. Complete raw construction, reconstruction and updates
through the public Block facade.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3–7.
-/

open STFSpec.Block

private def constructorType : Nat → Nat → Nat → TxParams := TxParams.mk
private def blobType : TxParams → Nat := TxParams.blobCountLimit
private def addressType : TxParams → Nat := TxParams.accessListAddressFloorTokens
private def storageType : TxParams → Nat := TxParams.accessListStorageKeyFloorTokens

private theorem blob_projection (b a s : Nat) : (TxParams.mk b a s).blobCountLimit = b := rfl

private theorem address_projection (b a s : Nat) :
    (TxParams.mk b a s).accessListAddressFloorTokens = a := rfl

private theorem storage_projection (b a s : Nat) :
    (TxParams.mk b a s).accessListStorageKeyFloorTokens = s := rfl

private theorem reconstruct (p : TxParams) :
    TxParams.mk p.blobCountLimit p.accessListAddressFloorTokens
      p.accessListStorageKeyFloorTokens = p := rfl

private theorem update_blob (p : TxParams) (b : Nat) :
    let q := { p with blobCountLimit := b }
    (q.blobCountLimit, q.accessListAddressFloorTokens, q.accessListStorageKeyFloorTokens) =
      (b, p.accessListAddressFloorTokens, p.accessListStorageKeyFloorTokens) := rfl

private theorem update_address (p : TxParams) (a : Nat) :
    let q := { p with accessListAddressFloorTokens := a }
    (q.blobCountLimit, q.accessListAddressFloorTokens, q.accessListStorageKeyFloorTokens) =
      (p.blobCountLimit, a, p.accessListStorageKeyFloorTokens) := rfl

private theorem update_storage (p : TxParams) (s : Nat) :
    let q := { p with accessListStorageKeyFloorTokens := s }
    (q.blobCountLimit, q.accessListAddressFloorTokens, q.accessListStorageKeyFloorTokens) =
      (p.blobCountLimit, p.accessListAddressFloorTokens, s) := rfl

private def observe (p : TxParams) : Nat × Nat × Nat :=
  (p.blobCountLimit, p.accessListAddressFloorTokens, p.accessListStorageKeyFloorTokens)

#guard observe (TxParams.mk 0 0 0) == (0, 0, 0)
#guard observe (TxParams.mk 17 29 43) == (17, 29, 43)
#guard observe (TxParams.mk (2 ^ 256) 0 (2 ^ 512 + 1)) == (2 ^ 256, 0, 2 ^ 512 + 1)
#guard observe (TxParams.mk 0 (2 ^ 300 + 7) 3) == (0, 2 ^ 300 + 7, 3)
