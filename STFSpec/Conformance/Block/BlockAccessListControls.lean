/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block

/-!
# Raw block access list clients

Library `EthConformance`. Private clients use the Block facade to check each raw
field and compare complete ordered values.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3–5.
-/

namespace STFSpec.Conformance.Block.BlockAccessListControls

open STFSpec.Base STFSpec.Block

private def storageConstructor : U32 → U256 → StorageChange := StorageChange.mk
private def storageIndex : StorageChange → U32 := StorageChange.blockAccessIndex
private def storageValue : StorageChange → U256 := StorageChange.newValue
private def balanceConstructor : U32 → U256 → BalanceChange := BalanceChange.mk
private def balanceIndex : BalanceChange → U32 := BalanceChange.blockAccessIndex
private def balanceValue : BalanceChange → U256 := BalanceChange.postBalance
private def nonceConstructor : U32 → U64 → NonceChange := NonceChange.mk
private def nonceIndex : NonceChange → U32 := NonceChange.blockAccessIndex
private def nonceValue : NonceChange → U64 := NonceChange.newNonce
private def codeConstructor : U32 → ByteArray → CodeChange := CodeChange.mk
private def codeIndex : CodeChange → U32 := CodeChange.blockAccessIndex
private def codeValue : CodeChange → ByteArray := CodeChange.newCode
private def slotConstructor : U256 → List StorageChange → SlotChanges := SlotChanges.mk
private def slotKey : SlotChanges → U256 := SlotChanges.slot
private def slotUpdates : SlotChanges → List StorageChange := SlotChanges.changes
private def accountConstructor :
    Address → List SlotChanges → List U256 → List BalanceChange → List NonceChange →
      List CodeChange → AccountChanges := AccountChanges.mk
private def accountAddress : AccountChanges → Address := AccountChanges.address
private def accountStorage : AccountChanges → List SlotChanges := AccountChanges.storageChanges
private def accountReads : AccountChanges → List U256 := AccountChanges.storageReads
private def accountBalances : AccountChanges → List BalanceChange :=
  AccountChanges.balanceChanges
private def accountNonces : AccountChanges → List NonceChange := AccountChanges.nonceChanges
private def accountCode : AccountChanges → List CodeChange := AccountChanges.codeChanges
private def blockEntries : BlockAccessList → Array AccountChanges := id
private def ofBlockEntries : Array AccountChanges → BlockAccessList := id

private def storageFields (change : StorageChange) : U32 × U256 :=
  (change.blockAccessIndex, change.newValue)

private def balanceFields (change : BalanceChange) : U32 × U256 :=
  (change.blockAccessIndex, change.postBalance)

private def nonceFields (change : NonceChange) : U32 × U64 :=
  (change.blockAccessIndex, change.newNonce)

private def codeFields (change : CodeChange) : U32 × ByteArray :=
  (change.blockAccessIndex, change.newCode)

private def slotFields (slot : SlotChanges) : U256 × List StorageChange :=
  (slot.slot, slot.changes)

private def accountFields (account : AccountChanges) :
    Address × List SlotChanges × List U256 × List BalanceChange × List NonceChange ×
      List CodeChange :=
  (account.address, account.storageChanges, account.storageReads, account.balanceChanges,
    account.nonceChanges, account.codeChanges)

private theorem storage_fields (index : U32) (value : U256) :
    storageFields (StorageChange.mk index value) = (index, value) := rfl

private theorem balance_fields (index : U32) (value : U256) :
    balanceFields (BalanceChange.mk index value) = (index, value) := rfl

private theorem nonce_fields (index : U32) (value : U64) :
    nonceFields (NonceChange.mk index value) = (index, value) := rfl

private theorem code_fields (index : U32) (value : ByteArray) :
    codeFields (CodeChange.mk index value) = (index, value) := rfl

private theorem slot_fields (key : U256) (updates : List StorageChange) :
    slotFields (SlotChanges.mk key updates) = (key, updates) := rfl

private theorem account_fields (address : Address) (storage : List SlotChanges)
    (reads : List U256) (balances : List BalanceChange) (nonces : List NonceChange)
    (code : List CodeChange) :
    accountFields (AccountChanges.mk address storage reads balances nonces code) =
      (address, storage, reads, balances, nonces, code) := rfl

private theorem storage_reconstruction (change : StorageChange) :
    StorageChange.mk change.blockAccessIndex change.newValue = change := rfl

private theorem balance_reconstruction (change : BalanceChange) :
    BalanceChange.mk change.blockAccessIndex change.postBalance = change := rfl

private theorem nonce_reconstruction (change : NonceChange) :
    NonceChange.mk change.blockAccessIndex change.newNonce = change := rfl

private theorem code_reconstruction (change : CodeChange) :
    CodeChange.mk change.blockAccessIndex change.newCode = change := rfl

private theorem slot_reconstruction (slot : SlotChanges) :
    SlotChanges.mk slot.slot slot.changes = slot := rfl

private theorem account_reconstruction (account : AccountChanges) :
    AccountChanges.mk account.address account.storageChanges account.storageReads
      account.balanceChanges account.nonceChanges account.codeChanges = account := rfl

private theorem storage_update_index (change : StorageChange) (index : U32) :
    storageFields { change with blockAccessIndex := index } = (index, change.newValue) := rfl

private theorem storage_update_value (change : StorageChange) (value : U256) :
    storageFields { change with newValue := value } = (change.blockAccessIndex, value) := rfl

private theorem balance_update_index (change : BalanceChange) (index : U32) :
    balanceFields { change with blockAccessIndex := index } = (index, change.postBalance) := rfl

private theorem balance_update_value (change : BalanceChange) (value : U256) :
    balanceFields { change with postBalance := value } = (change.blockAccessIndex, value) := rfl

private theorem nonce_update_index (change : NonceChange) (index : U32) :
    nonceFields { change with blockAccessIndex := index } = (index, change.newNonce) := rfl

private theorem nonce_update_value (change : NonceChange) (value : U64) :
    nonceFields { change with newNonce := value } = (change.blockAccessIndex, value) := rfl

private theorem code_update_index (change : CodeChange) (index : U32) :
    codeFields { change with blockAccessIndex := index } = (index, change.newCode) := rfl

private theorem code_update_value (change : CodeChange) (value : ByteArray) :
    codeFields { change with newCode := value } = (change.blockAccessIndex, value) := rfl

private theorem slot_update_key (slot : SlotChanges) (key : U256) :
    slotFields { slot with slot := key } = (key, slot.changes) := rfl

private theorem slot_update_changes (slot : SlotChanges) (updates : List StorageChange) :
    slotFields { slot with changes := updates } = (slot.slot, updates) := rfl

private theorem account_update_address (account : AccountChanges) (address : Address) :
    accountFields { account with address := address } =
      (address, account.storageChanges, account.storageReads, account.balanceChanges,
        account.nonceChanges, account.codeChanges) := rfl

private theorem account_update_storage (account : AccountChanges) (storage : List SlotChanges) :
    accountFields { account with storageChanges := storage } =
      (account.address, storage, account.storageReads, account.balanceChanges,
        account.nonceChanges, account.codeChanges) := rfl

private theorem account_update_reads (account : AccountChanges) (reads : List U256) :
    accountFields { account with storageReads := reads } =
      (account.address, account.storageChanges, reads, account.balanceChanges,
        account.nonceChanges, account.codeChanges) := rfl

private theorem account_update_balances (account : AccountChanges)
    (balances : List BalanceChange) :
    accountFields { account with balanceChanges := balances } =
      (account.address, account.storageChanges, account.storageReads, balances,
        account.nonceChanges, account.codeChanges) := rfl

private theorem account_update_nonces (account : AccountChanges) (nonces : List NonceChange) :
    accountFields { account with nonceChanges := nonces } =
      (account.address, account.storageChanges, account.storageReads, account.balanceChanges,
        nonces, account.codeChanges) := rfl

private theorem account_update_code (account : AccountChanges) (code : List CodeChange) :
    accountFields { account with codeChanges := code } =
      (account.address, account.storageChanges, account.storageReads, account.balanceChanges,
        account.nonceChanges, code) := rfl

private def observeStorage (change : StorageChange) : Nat × Nat :=
  (change.blockAccessIndex.toNat, change.newValue.toNat)

private def observeBalance (change : BalanceChange) : Nat × Nat :=
  (change.blockAccessIndex.toNat, change.postBalance.toNat)

private def observeNonce (change : NonceChange) : Nat × Nat :=
  (change.blockAccessIndex.toNat, change.newNonce.toNat)

private def observeCode (change : CodeChange) : Nat × List UInt8 :=
  (change.blockAccessIndex.toNat, (Bytes.ofByteArray change.newCode).toList)

private def observeSlot (slot : SlotChanges) : Nat × List (Nat × Nat) :=
  (slot.slot.toNat, slot.changes.map observeStorage)

private abbrev AccountView :=
  List UInt8 × List (Nat × List (Nat × Nat)) × List Nat × List (Nat × Nat) ×
    List (Nat × Nat) × List (Nat × List UInt8)

private def observeAccount (account : AccountChanges) : AccountView :=
  (account.address.toBytes.toList, account.storageChanges.map observeSlot,
    account.storageReads.map U256.toNat, account.balanceChanges.map observeBalance,
    account.nonceChanges.map observeNonce, account.codeChanges.map observeCode)

private def observeBlock (accounts : BlockAccessList) : List AccountView :=
  accounts.toList.map observeAccount

private def emptyAccount : AccountChanges := ⟨Address.ofNat 0, [], [], [], [], []⟩

private def longCode : ByteArray :=
  ⟨#[0, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
    32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
    48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 255]⟩

private def largestSlot : SlotChanges :=
  ⟨U256.max, [⟨U32.max, U256.max⟩, ⟨U32.zero, U256.zero⟩, ⟨U32.max, U256.max⟩]⟩

private def account : AccountChanges :=
  ⟨Address.ofNat 0x000102030405060708090a0b0c0d0e0f10111213,
    [largestSlot, ⟨U256.zero, []⟩, largestSlot],
    [U256.max, U256.zero, U256.max],
    [⟨U32.max, U256.max⟩, ⟨U32.zero, U256.zero⟩, ⟨U32.max, U256.max⟩],
    [⟨U32.max, U64.max⟩, ⟨U32.zero, U64.zero⟩, ⟨U32.max, U64.max⟩],
    [⟨U32.max, longCode⟩, ⟨U32.zero, ByteArray.empty⟩, ⟨U32.max, longCode⟩]⟩

private def expectedEmpty : AccountView :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [], [], [], [], [])

private def expectedAccount : AccountView :=
  let maxIndex := 4294967295
  let maxWord := 2 ^ 256 - 1
  let maxNonce := 18446744073709551615
  let wordChanges := [(maxIndex, maxWord), (0, 0), (maxIndex, maxWord)]
  let slotEntry := (maxWord, wordChanges)
  let middleBytes := (List.range 61).map (fun n ↦ UInt8.ofNat (n + 2))
  let codeBytes : List UInt8 := [0, 0] ++ middleBytes ++ [255]
  ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19],
    [slotEntry, (0, []), slotEntry], [maxWord, 0, maxWord], wordChanges,
    [(maxIndex, maxNonce), (0, 0), (maxIndex, maxNonce)],
    [(maxIndex, codeBytes), (0, []), (maxIndex, codeBytes)])

#guard observeBlock #[] == []
#guard observeAccount emptyAccount == expectedEmpty
#guard observeAccount account == expectedAccount
#guard observeBlock #[account, emptyAccount, account] ==
  [expectedAccount, expectedEmpty, expectedAccount]

end STFSpec.Conformance.Block.BlockAccessListControls
