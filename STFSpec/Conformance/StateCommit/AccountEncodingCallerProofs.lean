/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateCommit

/-!
# Ordinary account encoder callers
Library `EthConformance`. Whole-field/all-input public contracts, including unbounded nonce.
Spec guidance: `STFSpec/informal/modules/EthStateCommit.md` SC1/§7.
-/
namespace STFSpec.Conformance.StateCommit.AccountEncodingCallerProofs
open STFSpec.Base STFSpec.Codec STFSpec.State STFSpec.StateCommit

private theorem defining (acc : Account) (root : Hash32) :
    encodeAccount acc root =
      Rlp.encode (.list [Rlp.ofNat acc.nonce, .bytes (U256.toBeBytes acc.balance).toByteArray,
        .bytes root.toBytes.toByteArray, .bytes acc.codeHash.toBytes.toByteArray]) :=
  encodeAccount_eq acc root

private theorem complete_reference (acc : Account) (root : Hash32) :
    (encodeAccount acc root).data.toList = Rlp.encodeModel (.list [
      .bytes (Uint.toBeBytesReference acc.nonce).toByteArray,
      .bytes (Uint.toBeBytesReference acc.balance.toNat).toByteArray,
      .bytes root.toBytes.toByteArray, .bytes acc.codeHash.toBytes.toByteArray]) := by
  rw [encodeAccount_eq, Rlp.toList_encode]
  simp only [Rlp.ofNat, U256.toBeBytes_eq, Uint.toBeBytes_eq_reference]

private theorem supplied_root (n : Nat) (b : U256) (code root : Hash32) :
    encodeAccount (Account.mk n b code) root =
      Rlp.encode (.list [Rlp.ofNat n, .bytes (U256.toBeBytes b).toByteArray,
        .bytes root.toBytes.toByteArray, .bytes code.toBytes.toByteArray]) :=
  encodeAccount_eq _ _

end STFSpec.Conformance.StateCommit.AccountEncodingCallerProofs
