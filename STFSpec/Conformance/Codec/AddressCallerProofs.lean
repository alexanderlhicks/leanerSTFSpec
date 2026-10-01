/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Public address caller proofs

Library `EthConformance`. Consumers compose the public query, Id, suffix and
transformer contracts without unfolding private conversion or provider storage.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3/7/8.
-/

namespace STFSpec.Conformance.Codec.AddressCallerProofs

open STFSpec.Base STFSpec.Hash STFSpec.Codec

example (hash : Hash32) : (Address.ofNat hash.toNat).toBytes.toList =
    hash.toBytes.toList.drop 12 := by
  rw [toBytes_address_of_hash, Bytes.toList_ofList]

example (hash : Hash32) : (hash.toBytes.toList.drop 12).length = 20 := by
  rw [List.length_drop, Bytes.length_toList, Hash32.size_toBytes]

example (hash : Hash32) :
    Bytes.leftPadZero (Bytes.ofList (hash.toBytes.toList.drop 12)) 20 =
      Bytes.ofList (hash.toBytes.toList.drop 12) := by
  apply Bytes.ext
  rw [Bytes.toList_leftPadZero, Bytes.size_ofList, List.length_drop,
    Bytes.length_toList, Hash32.size_toBytes]
  simp

example (sender : Address) (nonce : Nat) :
    computeContractAddress sender nonce = computeContractAddressQ (m := Id) sender nonce :=
  computeContractAddress_id sender nonce

example (sender : Address) (salt : Bytes32) (code : ByteArray) :
    computeCreate2ContractAddress sender salt code =
      computeCreate2ContractAddressQ (m := Id) sender salt code :=
  computeCreate2ContractAddress_id sender salt code

example (sender : Address) (nonce : Nat) :
    (computeContractAddress sender nonce).toBytes.toList =
      (keccak256 (Rlp.encode (.list [.bytes sender.toBytes.toByteArray,
        Rlp.ofNat nonce]))).toBytes.toList.drop 12 := by
  rw [toBytes_computeContractAddress, Bytes.toList_ofList]

example (sender : Address) (salt : Bytes32) (code : ByteArray) :
    (computeCreate2ContractAddress sender salt code).toBytes.size = 20 :=
  Address.size_toBytes _

example (sender : Address) (salt : Bytes32) (code : ByteArray) :
    (computeCreate2ContractAddress sender salt code).toBytes.toList =
      (keccak256 (⟨#[0xff]⟩ ++ sender.toBytes.toByteArray ++ salt.toBytes.toByteArray ++
        (keccak256 code).toBytes.toByteArray)).toBytes.toList.drop 12 := by
  rw [toBytes_computeCreate2ContractAddress, Bytes.toList_ofList]

-- Zero nonce is the empty typed leaf, rather than a singleton zero byte.
example (sender : Address) :
    (Rlp.encode (.list [.bytes sender.toBytes.toByteArray, Rlp.ofNat 0])).data.toList =
      Rlp.lengthPrefixModel 192 247
        ((Rlp.encode (.bytes sender.toBytes.toByteArray)).size + 1) ++
          (Rlp.encode (.bytes sender.toBytes.toByteArray)).data.toList ++ [128] := by
  rw [Rlp.toList_encode_list, Rlp.encodePayloadModel_cons, Rlp.encodePayloadModel_cons,
    Rlp.encodePayloadModel_nil, List.append_nil, ← Rlp.toList_encode]
  have hz : Rlp.encodeModel (Rlp.ofNat 0) = [128] := by decide
  rw [hz, List.length_append, Array.length_toList, List.length_cons, List.length_nil,
    Nat.zero_add, List.append_assoc, ← ByteArray.size_data]

section Generic
variable {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]

example (sender : Address) (nonce : Nat) :
    (do let result ← computeContractAddressQ (m := m) sender nonce
        pure result.toBytes : m Bytes) = (do
      let hash ← KeccakQuery.keccak
        (Rlp.encode (.list [.bytes sender.toBytes.toByteArray, Rlp.ofNat nonce]))
      pure (Bytes.ofList (hash.toBytes.toList.drop 12))) :=
  toBytes_computeContractAddressQ sender nonce

example (sender : Address) (salt : Bytes32) (code : ByteArray) :
    (do let result ← computeCreate2ContractAddressQ (m := m) sender salt code
        pure result.toBytes : m Bytes) = (do
      let codeHash ← KeccakQuery.keccak code
      let hash ← KeccakQuery.keccak
        (⟨#[0xff]⟩ ++ sender.toBytes.toByteArray ++ salt.toBytes.toByteArray ++
          codeHash.toBytes.toByteArray)
      pure (Bytes.ofList (hash.toBytes.toList.drop 12))) :=
  toBytes_computeCreate2ContractAddressQ sender salt code

example (sender : Address) (nonce : Nat) (hash : Hash32)
    (h : KeccakQuery.keccak (m := m)
      (Rlp.encode (.list [.bytes sender.toBytes.toByteArray, Rlp.ofNat nonce])) = pure hash) :
    (do let result ← computeContractAddressQ (m := m) sender nonce
        pure result.toBytes : m Bytes) = pure (Bytes.ofList (hash.toBytes.toList.drop 12)) := by
  rw [computeContractAddressQ_of_pure_answer sender nonce hash h]
  simp only [pure_bind, toBytes_address_of_hash]

example {σ : Type} (sender : Address) (nonce : Nat) (s : σ) :
    (computeContractAddressQ (m := StateT σ m) sender nonce).run s =
      (do let result ← computeContractAddressQ (m := m) sender nonce
          pure (result, s)) := run_computeContractAddressQ_stateT sender nonce s

example {σ : Type} (sender : Address) (salt : Bytes32) (code : ByteArray) (s : σ) :
    (computeCreate2ContractAddressQ (m := StateT σ m) sender salt code).run s =
      (do let result ← computeCreate2ContractAddressQ (m := m) sender salt code
          pure (result, s)) := run_computeCreate2ContractAddressQ_stateT sender salt code s

example {ε : Type} (sender : Address) (nonce : Nat) :
    (computeContractAddressQ (m := ExceptT ε m) sender nonce).run =
      (do let result ← computeContractAddressQ (m := m) sender nonce
          pure (.ok result : Except ε Address)) := run_computeContractAddressQ_exceptT sender nonce

example {ε : Type} (sender : Address) (salt : Bytes32) (code : ByteArray) :
    (computeCreate2ContractAddressQ (m := ExceptT ε m) sender salt code).run =
      (do let result ← computeCreate2ContractAddressQ (m := m) sender salt code
          pure (.ok result : Except ε Address)) :=
  run_computeCreate2ContractAddressQ_exceptT sender salt code
end Generic

section Failure
variable {m : Type → Type} {ε : Type} [Monad m] [LawfulMonad m]
  [KeccakQuery (ExceptT ε m)]

example (sender : Address) (salt : Bytes32) (code : ByteArray) (error : ε)
    (h : KeccakQuery.keccak (m := ExceptT ε m) code = ExceptT.mk (pure (.error error))) :
    (computeCreate2ContractAddressQ (m := ExceptT ε m) sender salt code).run =
      pure (.error error) := run_computeCreate2ContractAddressQ_error_code sender salt code error h

example (sender : Address) (salt : Bytes32) (code : ByteArray) (hash : Hash32) (error : ε)
    (hcode : KeccakQuery.keccak (m := ExceptT ε m) code = pure hash)
    (hhash : KeccakQuery.keccak (m := ExceptT ε m)
      (⟨#[0xff]⟩ ++ sender.toBytes.toByteArray ++ salt.toBytes.toByteArray ++
        hash.toBytes.toByteArray) = ExceptT.mk (pure (.error error))) :
    (computeCreate2ContractAddressQ (m := ExceptT ε m) sender salt code).run =
      pure (.error error) :=
  run_computeCreate2ContractAddressQ_error_hash sender salt code hash error hcode hhash
end Failure

end STFSpec.Conformance.Codec.AddressCallerProofs
