/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit.Root
import STFSpec.State.MathState
import STFSpec.StateCommit.Account
import STFSpec.StateCommit.Storage

/-!
# Mathematical state roots

Library `EthStateCommit`. Prepare storage and account leaves in ascending
raw key order, then use the canonical root on the prepared maps.
Spec guidance: `STFSpec/informal/modules/EthStateCommit.md` SC4, §§5 and 7.2.
-/

namespace STFSpec.StateCommit

open STFSpec.Base STFSpec.Commit STFSpec.Hash STFSpec.State

variable {m : Type → Type} [Monad m] [KeccakQuery m]

private abbrev Prepared := Std.ExtTreeMap Nibbles ByteArray

private def prepareSlots : List (Bytes32 × U256) → Prepared → m Prepared
  | [], prepared => pure prepared
  | (slot, value) :: rest, prepared =>
    if value = U256.zero then prepareSlots rest prepared
    else do
      let digest ← KeccakQuery.keccak slot.toBytes.toByteArray
      let path := bytesToNibbleList digest.toBytes.toByteArray
      prepareSlots rest (prepared.insert path (encodeStorage value))

/-- Prepare the selected address's nonzero slots in ascending slot order (Q100).
Repeated digest paths retain the later leaf. The source preparation is
EELS `src/ethereum/merkle_patricia_trie.py:407–475`. -/
def storageTrieMap (σ : MathState) (a : Address) : m (Std.ExtTreeMap Nibbles ByteArray) :=
  match σ.storage[a]? with
  | none => pure ∅
  | some slots => prepareSlots slots.toList ∅

/-- Compute the selected storage root using the caller's empty trie constant. -/
def storageRoot (consts : HashConsts) (σ : MathState) (a : Address) : m Hash32 := do
  let prepared ← storageTrieMap σ a
  mathRoot consts.emptyTrieRoot prepared

private def prepareAccounts (storage : Address → m Hash32) :
    List (Address × Account) → Prepared → m Prepared
  | [], prepared => pure prepared
  | (address, account) :: rest, prepared => do
    let root ← storage address
    let leaf := encodeAccount account root
    let digest ← KeccakQuery.keccak address.toBytes.toByteArray
    let path := bytesToNibbleList digest.toBytes.toByteArray
    prepareAccounts storage rest (prepared.insert path leaf)

/-- Prepare present accounts in ascending address order (Q100). Each account's
storage root precedes the address query, and the later leaf wins at a shared path.
The source callback is EELS `src/ethereum/state_mpt.py:113–118`. -/
def accountTrieMap (consts : HashConsts) (σ : MathState) : m (Std.ExtTreeMap Nibbles ByteArray) :=
  prepareAccounts (storageRoot consts σ) σ.accounts.toList ∅

/-- Compute the root of the prepared account map using the caller's empty trie constant. -/
def mathStateRoot (consts : HashConsts) (σ : MathState) : m Hash32 := do
  let prepared ← accountTrieMap consts σ
  mathRoot consts.emptyTrieRoot prepared

end STFSpec.StateCommit
