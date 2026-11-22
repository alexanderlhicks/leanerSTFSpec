/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Defaulted current account guards

Private interpreted controls distinguish a present zero account from absence under
arbitrary supplied constants. Complete finite native/interpreted controls are in
`scripts/AccountDefaultNativeTests.lean`.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/4/7.1.
-/

namespace STFSpec.Conformance.State.AccountDefaultGuards

open STFSpec.State STFSpec.Base

private def provider : PreState Id where
  getAccount? := fun _ ↦ .ok none
  getStorage := fun _ _ ↦ .ok U256.zero
  getCode := fun _ ↦ .ok ByteArray.empty
  stateRoot := fun _ ↦ .ok HashConsts.literals.emptyTrieRoot

private def initial (hash : Nat) (value : Option Account) : TxState Id :=
  let a := Address.ofNat 7
  ⟨BlockState.new provider { HashConsts.literals with
      emptyCodeHash := Hash32.ofBytes32 (FixedBytes.ofNat hash) },
    ⟨(∅ : Std.ExtTreeMap Address (Option Account)).insert a value,
      ⟨0, ∅, ∅⟩, ∅, ⟨0, ∅, ∅⟩, ∅, ∅, ∅, ∅⟩,
    ⟨∅, ∅, ∅, ∅⟩⟩

private def answer (hash : Nat) (value : Option Account) : Option (List Nat) :=
  match ((getAccount (Address.ofNat 7)).run (initial hash value)).run with
  | .ok (a, _) => some [a.nonce, a.balance.toNat, a.codeHash.toBytes32.toNat]
  | .error _ => none

#guard answer 17 none = some [0, 0, 17]
#guard answer 0 none = some [0, 0, 0]
#guard answer (2 ^ 256 - 1) none = some [0, 0, 2 ^ 256 - 1]
#guard answer 17 (some (emptyAccount HashConsts.literals)) =
  some [0, 0, 89477152217924674838424037953991966239322087453347756267410168184682657981552]
#guard answer 17 (some ⟨2 ^ 420 + 3, U256.ofNat (2 ^ 256 - 1),
    Hash32.ofBytes32 (FixedBytes.ofNat (2 ^ 255 + 1))⟩) =
  some [2 ^ 420 + 3, 2 ^ 256 - 1, 2 ^ 255 + 1]

end STFSpec.Conformance.State.AccountDefaultGuards
