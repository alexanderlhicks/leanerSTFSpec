/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.Account

/-!
# Complete Account value guards

Library `EthConformance`: deterministic complete-field observations, including
arbitrary supplied constants and absence versus a present empty account.
Spec guidance: `STFSpec/informal/modules/EthState.md`.
-/

namespace STFSpec.Conformance.State.AccountGuards

open STFSpec.Base STFSpec.State

private def hashOfNat (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)

private def observe (x : State.Account) : Nat × Nat × List UInt8 :=
  (x.nonce, x.balance.toNat, x.codeHash.toBytes.toList)

private def leadingHash : Hash32 := hashOfNat (2 ^ 248)
private def trailingHash : Hash32 := hashOfNat 1
private def zeroHash : Hash32 := hashOfNat 0
private def allHash : Hash32 := hashOfNat (2 ^ 256 - 1)

private def leadingConsts : HashConsts :=
  ⟨leadingHash, trailingHash, zeroHash, allHash⟩
private def trailingConsts : HashConsts :=
  ⟨trailingHash, leadingHash, allHash, zeroHash⟩

private def zeroAccount : State.Account := ⟨0, U256.zero, zeroHash⟩
private def hugeAccount : State.Account := ⟨2 ^ 1024 + 17, U256.max, leadingHash⟩
private def otherNonce : State.Account := ⟨2 ^ 1024 + 18, U256.max, leadingHash⟩
private def otherBalance : State.Account := ⟨2 ^ 1024 + 17, U256.zero, leadingHash⟩
private def otherHash : State.Account := ⟨2 ^ 1024 + 17, U256.max, trailingHash⟩

#guard observe zeroAccount = (0, 0, List.replicate 32 0)
#guard observe hugeAccount = (2 ^ 1024 + 17, 2 ^ 256 - 1, 1 :: List.replicate 31 0)
#guard observe (emptyAccount leadingConsts) = (0, 0, 1 :: List.replicate 31 0)
#guard observe (emptyAccount trailingConsts) = (0, 0, List.replicate 31 0 ++ [1])
#guard (emptyAccount leadingConsts).codeHash.toBytes.toList ≠
  (emptyAccount trailingConsts).codeHash.toBytes.toList
#guard hugeAccount = State.Account.mk hugeAccount.nonce hugeAccount.balance hugeAccount.codeHash
#guard hugeAccount ≠ otherNonce
#guard hugeAccount ≠ otherBalance
#guard hugeAccount ≠ otherHash
#guard (none : Option State.Account) ≠ some (emptyAccount leadingConsts)
#guard (some (emptyAccount leadingConsts) : Option State.Account) ≠ none
#guard observe (emptyAccount HashConsts.literals) =
  (0, 0, [0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c,
    0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0,
    0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b,
    0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70])

end STFSpec.Conformance.State.AccountGuards
