/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateCommit

/-!
# Mathematical state root controls

Library `EthConformance`. Compare complete roots with pinned EELS for concrete
Keccak and for synthetic collisions at storage or account keys.
Spec guidance: `STFSpec/informal/modules/EthStateCommit.md` SC4 and §7.2.
-/

namespace STFSpec.Conformance.StateCommit.MathStateRootGuards

open STFSpec.Base STFSpec.Hash STFSpec.State STFSpec.StateCommit

private def hash (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)

private def rawState
    (accounts : List (Nat × Account)) (slots : List (Nat × Nat × Nat))
    (code : List (Hash32 × ByteArray)) : MathState :=
  let accountMap := accounts.foldl (fun (table : Std.ExtTreeMap Address Account) (a, value) ↦
    table.insert (Address.ofNat a) value) ∅
  let storageMap := slots.foldl
    (fun (table : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)) (a, k, v) ↦
      let address := Address.ofNat a
      let previous : Std.ExtTreeMap Bytes32 U256 := table[address]?.getD ∅
      table.insert address (previous.insert (FixedBytes.ofNat k) (U256.ofNat v))) ∅
  let codeMap := code.foldl (fun (table : Std.ExtTreeMap Hash32 ByteArray) (key, bytes) ↦
    table.insert key bytes) ∅
  ⟨accountMap, storageMap, codeMap⟩

private def consts : HashConsts := HashConsts.literals
private def firstCodeHash : Hash32 :=
  hash 0xc7b1358b5104e7bb933bd1c7f41e564c12611e004ea7c377c50a786b16bf804a
private def secondCodeHash : Hash32 :=
  hash 0x8bad9ba94613fec1e809fab581b571a885374d55530adda2718a1d613e9a5c60
private def firstAccount : Account := ⟨1, U256.ofNat (2^252 + 1), firstCodeHash⟩
private def secondAccount : Account := ⟨2^65 + 1, U256.ofNat 53, secondCodeHash⟩
private def accounts : List (Nat × Account) := [(17, firstAccount), (33, secondAccount)]
private def slots : List (Nat × Nat × Nat) := [(17, 5, 7), (17, 11, 2^255 + 13), (33, 7, 1)]
private def codes : List (Hash32 × ByteArray) :=
  [(firstCodeHash, ⟨#[0, 255, 23]⟩), (secondCodeHash, ⟨#[95, 0]⟩)]

private def root (σ : MathState) : Hash32 := Id.run (mathStateRoot consts σ)

#guard root (rawState [] [] []) ==
  hash 0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421
#guard root (rawState [(231, emptyAccount consts)] [] []) ==
  hash 0xbe18cca60509a8061c3fc2541dfda401ec2fc4242fc5ef867ad5f29de65152af
#guard root (rawState [(17, firstAccount)] [(17, 5, 7)] []) ==
  hash 0xb2bb3d94dd5d2b11653ea7da70a1e9b1bc58414221303b636875a911bf438a2d

private def twoAccountRoot : Hash32 :=
  hash 0x0d5f0ad85a3d6426089e111aaf51bf4c7c6c218a917db033d1b45821be49f5e6

#guard root (rawState accounts slots []) == twoAccountRoot
#guard root (rawState accounts.reverse slots.reverse []) == twoAccountRoot
#guard root (rawState accounts slots codes) == twoAccountRoot
#guard root (rawState accounts (slots ++ [(49, 19, 23)]) []) == twoAccountRoot
#guard root (rawState accounts (slots ++ [(17, 5, 0)]) []) ==
  hash 0xadd20172e90803befa632d10f9415f8cc8361ced611224078f1a2a91fa92efa3

private def collidingRoot (keys : List ByteArray) (σ : MathState) : Hash32 :=
  let oracle : KeccakQuery Id := ⟨fun input ↦
    if keys.contains input then
      hash 0x5555555555555555555555555555555555555555555555555555555555555555
    else KeccakQuery.keccak (m := Id) input⟩
  Id.run (@mathStateRoot Id inferInstance oracle consts σ)

private def collisionAccounts : List (Nat × Account) :=
  [(17, ⟨1, U256.ofNat 19, firstCodeHash⟩), (33, ⟨2, U256.ofNat 53, secondCodeHash⟩)]
private def collisionSlots : List (Nat × Nat × Nat) := [(17, 5, 7), (17, 11, 13)]
private def accountKeys : List ByteArray := [17, 33].map (fun n ↦ (Address.ofNat n).toBytes.toByteArray)
private def slotKeys : List ByteArray :=
  [5, 11].map (fun n ↦ (FixedBytes.ofNat n : Bytes32).toBytes.toByteArray)
private def ascendingAccountRoot : Hash32 :=
  hash 0xd03ca24dc73164d0ae76214e0994bfd832224a7c924af373827c39db866337eb
private def reverseAccountRoot : Hash32 :=
  hash 0x43a2d4367efecb156659dec241acb16dfe5d99b10cbc56b11df0c6bdf2312d8a
private def ascendingStorageRoot : Hash32 :=
  hash 0xc8a275d5f639db6b0c7f5c5bb1d9094dc22877e24c2e3ed02a1aa93d23ad5c92
private def reverseStorageRoot : Hash32 :=
  hash 0xd8ec60ad41c031dfaa8d1294a8bb1a5d47cd575c6d2fe46342686730d9da9eb0

#guard collidingRoot accountKeys (rawState collisionAccounts [] []) == ascendingAccountRoot
#guard collidingRoot accountKeys (rawState collisionAccounts.reverse [] []) == ascendingAccountRoot
#guard collidingRoot accountKeys (rawState collisionAccounts.reverse [] []) != reverseAccountRoot
#guard collidingRoot slotKeys (rawState (collisionAccounts.take 1) collisionSlots []) == ascendingStorageRoot
#guard collidingRoot slotKeys (rawState (collisionAccounts.take 1) collisionSlots.reverse []) ==
  ascendingStorageRoot
#guard collidingRoot slotKeys (rawState (collisionAccounts.take 1) collisionSlots.reverse []) !=
  reverseStorageRoot

end STFSpec.Conformance.StateCommit.MathStateRootGuards
