/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.RlpEncode
import STFSpec.Hash.KeccakQuery

/-!
# Contract address derivation

Library `EthCodec`. CREATE and CREATE2 preserve the exact supplied oracle answers
and ordered query effects. Pure execution is their definitional `Id` specialization.
The CREATE preimage is `Rlp.Encodable` for every nonce below 2^256 (Q47); the
Nat encoder remains total at every nonce. VM creation/state/gas rules are separate.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§2–8.
-/

namespace STFSpec.Codec

open STFSpec.Base STFSpec.Hash

-- Alias for the numeric conversion whose exact suffix law belongs to `EthBase`.
private def lastBytes20 (hash : Hash32) : Address := Address.ofNat hash.toNat

private theorem size_encode_bytes_le (b : ByteArray) (h : b.size ≤ 32) :
    (Rlp.encode (.bytes b)).size ≤ 33 := by
  have hs := Rlp.size_encodeBytes b
  rw [Rlp.encodeBytes] at hs
  rw [hs]
  split <;> (try split) <;> omega

/-- Every sender and nonce below 2^256 has a standard-domain CREATE preimage.
This discharges Q47's `Rlp.Encodable` premise without capping the total Nat API. -/
theorem encodable_computeContractAddress_preimage (sender : Address) (nonce : Nat)
    (h : nonce < 2 ^ 256) :
    Rlp.Encodable (.list [.bytes sender.toBytes.toByteArray, Rlp.ofNat nonce]) := by
  have hs : (Uint.toBeBytes nonce).size ≤ 32 := (Uint.size_toBeBytes_le_iff _ _).mpr h
  have ha : sender.toBytes.toByteArray.size = 20 := by
    rw [Bytes.size_toByteArray, Address.size_toBytes]
  have hn : (Uint.toBeBytes nonce).toByteArray.size ≤ 32 := by
    rw [Bytes.size_toByteArray]
    exact hs
  rw [Rlp.encodable_list_iff]
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [Rlp.encodable_bytes_iff, ha]
      decide
    · unfold Rlp.ofNat
      rw [Rlp.encodable_bytes_iff]
      omega
  · rw [Rlp.encodePayloadModel_cons, Rlp.encodePayloadModel_cons, Rlp.encodePayloadModel_nil,
      ← Rlp.toList_encode, ← Rlp.toList_encode]
    simp only [List.append_nil, List.length_append, Array.length_toList, ByteArray.size_data]
    have hsender := size_encode_bytes_le sender.toBytes.toByteArray (by omega)
    have hnonce := size_encode_bytes_le (Uint.toBeBytes nonce).toByteArray hn
    unfold Rlp.ofNat
    omega

/-- CREATE returns the last twenty bytes of the oracle answer to
`keccak256(rlp([sender, nonce]))`, with the nonce minimally encoded. EELS
`src/ethereum/forks/amsterdam/utils/address.py:42–63` at the pin. -/
def computeContractAddressQ {m : Type → Type} [Monad m] [KeccakQuery m]
    (sender : Address) (nonce : Nat) : m Address := do
  let hash ← KeccakQuery.keccak
    (Rlp.encode (.list [.bytes sender.toBytes.toByteArray, Rlp.ofNat nonce]))
  pure (lastBytes20 hash)

/-- CREATE2 returns the last twenty bytes of the answer to
`keccak256(0xff ‖ sender ‖ salt ‖ keccak256(initCode))`. Query init code first,
then include all thirty-two bytes of that answer in the outer preimage. EELS
`src/ethereum/forks/amsterdam/utils/address.py:66–93` at the pin. -/
def computeCreate2ContractAddressQ {m : Type → Type} [Monad m] [KeccakQuery m]
    (sender : Address) (salt : Bytes32) (initCode : ByteArray) : m Address := do
  let codeHash ← KeccakQuery.keccak initCode
  let hash ← KeccakQuery.keccak
    (⟨#[0xff]⟩ ++ sender.toBytes.toByteArray ++ salt.toBytes.toByteArray ++
      codeHash.toBytes.toByteArray)
  pure (lastBytes20 hash)

/-- Concrete CREATE is the definitional identity specialization of the query API. -/
def computeContractAddress (sender : Address) (nonce : Nat) : Address :=
  computeContractAddressQ (m := Id) sender nonce

/-- Concrete CREATE2 is the definitional identity specialization of the query API. -/
def computeCreate2ContractAddress (sender : Address) (salt : Bytes32)
    (initCode : ByteArray) : Address :=
  computeCreate2ContractAddressQ (m := Id) sender salt initCode

/-- Public one-query expansion: every oracle answer contributes its low 160 bits.
No concrete-answer or security premise is assumed. -/
theorem computeContractAddressQ_eq {m : Type → Type} [Monad m] [KeccakQuery m]
    (sender : Address) (nonce : Nat) :
    computeContractAddressQ (m := m) sender nonce = (do
      let hash ← KeccakQuery.keccak
        (Rlp.encode (.list [.bytes sender.toBytes.toByteArray, Rlp.ofNat nonce]))
      pure (Address.ofNat hash.toNat) : m Address) := rfl

/-- Public two-query expansion pins order, exact preimages and dependence on the
complete first answer. The lawful `ExceptT` error laws below establish that
an earlier query failure suppresses later queries. -/
theorem computeCreate2ContractAddressQ_eq {m : Type → Type} [Monad m] [KeccakQuery m]
    (sender : Address) (salt : Bytes32) (initCode : ByteArray) :
    computeCreate2ContractAddressQ (m := m) sender salt initCode = (do
      let codeHash ← KeccakQuery.keccak initCode
      let hash ← KeccakQuery.keccak
        (⟨#[0xff]⟩ ++ sender.toBytes.toByteArray ++ salt.toBytes.toByteArray ++
          codeHash.toBytes.toByteArray)
      pure (Address.ofNat hash.toNat) : m Address) := rfl

/-- Observing CREATE bytes preserves the sole query and returns its exact suffix. -/
theorem toBytes_computeContractAddressQ {m : Type → Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m] (sender : Address) (nonce : Nat) :
    (do let address ← computeContractAddressQ (m := m) sender nonce
        pure address.toBytes : m Bytes) = (do
      let hash ← KeccakQuery.keccak
        (Rlp.encode (.list [.bytes sender.toBytes.toByteArray, Rlp.ofNat nonce]))
      pure (Bytes.ofList (hash.toBytes.toList.drop 12))) := by
  rw [computeContractAddressQ_eq]
  simp only [bind_assoc, pure_bind, Address.toBytes_ofNat_toNat]

/-- Observing CREATE2 bytes preserves both queries and the first answer dependence,
then returns the exact twenty-byte suffix of the second answer. -/
theorem toBytes_computeCreate2ContractAddressQ {m : Type → Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m] (sender : Address) (salt : Bytes32)
    (initCode : ByteArray) :
    (do let address ← computeCreate2ContractAddressQ (m := m) sender salt initCode
        pure address.toBytes : m Bytes) = (do
      let codeHash ← KeccakQuery.keccak initCode
      let hash ← KeccakQuery.keccak
        (⟨#[0xff]⟩ ++ sender.toBytes.toByteArray ++ salt.toBytes.toByteArray ++
          codeHash.toBytes.toByteArray)
      pure (Bytes.ofList (hash.toBytes.toList.drop 12))) := by
  rw [computeCreate2ContractAddressQ_eq]
  simp only [bind_assoc, pure_bind, Address.toBytes_ofNat_toNat]

/-- The pure CREATE endpoint is definitionally its identity query computation. -/
theorem computeContractAddress_id (sender : Address) (nonce : Nat) :
    computeContractAddress sender nonce =
      computeContractAddressQ (m := Id) sender nonce := rfl

/-- The pure CREATE2 endpoint is definitionally its identity query computation. -/
theorem computeCreate2ContractAddress_id (sender : Address) (salt : Bytes32)
    (initCode : ByteArray) : computeCreate2ContractAddress sender salt initCode =
      computeCreate2ContractAddressQ (m := Id) sender salt initCode := rfl

/-- CREATE's concrete formula uses exactly the public RLP preimage. -/
theorem computeContractAddress_eq (sender : Address) (nonce : Nat) :
    computeContractAddress sender nonce = Address.ofNat
      (keccak256 (Rlp.encode (.list
        [.bytes sender.toBytes.toByteArray, Rlp.ofNat nonce]))).toNat := rfl

/-- CREATE2's concrete formula preserves both complete digests in source order. -/
theorem computeCreate2ContractAddress_eq (sender : Address) (salt : Bytes32)
    (initCode : ByteArray) : computeCreate2ContractAddress sender salt initCode =
      Address.ofNat (keccak256 (⟨#[0xff]⟩ ++ sender.toBytes.toByteArray ++
        salt.toBytes.toByteArray ++ (keccak256 initCode).toBytes.toByteArray)).toNat := rfl

/-- CREATE returns exactly the last twenty digest bytes. -/
theorem toBytes_computeContractAddress (sender : Address) (nonce : Nat) :
    (computeContractAddress sender nonce).toBytes = Bytes.ofList
      ((keccak256 (Rlp.encode (.list
        [.bytes sender.toBytes.toByteArray, Rlp.ofNat nonce]))).toBytes.toList.drop 12) := by
  rw [computeContractAddress_eq, Address.toBytes_ofNat_toNat]

/-- CREATE2 returns exactly the last twenty outer digest bytes. -/
theorem toBytes_computeCreate2ContractAddress (sender : Address) (salt : Bytes32)
    (initCode : ByteArray) : (computeCreate2ContractAddress sender salt initCode).toBytes =
      Bytes.ofList ((keccak256 (⟨#[0xff]⟩ ++ sender.toBytes.toByteArray ++
        salt.toBytes.toByteArray ++
        (keccak256 initCode).toBytes.toByteArray)).toBytes.toList.drop 12) := by
  rw [computeCreate2ContractAddress_eq, Address.toBytes_ofNat_toNat]

/-- Arbitrary pure CREATE answers are retained, without a concrete digest premise. -/
theorem computeContractAddressQ_of_pure_answer {m : Type → Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m] (sender : Address) (nonce : Nat)
    (hash : Hash32) (h : KeccakQuery.keccak (m := m)
      (Rlp.encode (.list [.bytes sender.toBytes.toByteArray, Rlp.ofNat nonce])) = pure hash) :
    computeContractAddressQ (m := m) sender nonce = pure (Address.ofNat hash.toNat) := by
  rw [computeContractAddressQ_eq, h]
  simp only [pure_bind]

/-- Both arbitrary pure CREATE2 answers are retained; the outer preimage includes
all thirty-two bytes of the first answer. -/
theorem computeCreate2ContractAddressQ_of_pure_answers {m : Type → Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m] (sender : Address) (salt : Bytes32)
    (initCode : ByteArray) (codeHash hash : Hash32)
    (hcode : KeccakQuery.keccak (m := m) initCode = pure codeHash)
    (hhash : KeccakQuery.keccak (m := m)
      (⟨#[0xff]⟩ ++ sender.toBytes.toByteArray ++ salt.toBytes.toByteArray ++
        codeHash.toBytes.toByteArray) = pure hash) :
    computeCreate2ContractAddressQ (m := m) sender salt initCode =
      pure (Address.ofNat hash.toNat) := by
  rw [computeCreate2ContractAddressQ_eq, hcode]
  simp only [pure_bind]
  rw [hhash]
  simp only [pure_bind]

/-- State forwarding preserves the additional state and underlying oracle effects. -/
theorem run_computeContractAddressQ_stateT {m : Type → Type} {σ : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m] (sender : Address) (nonce : Nat) (s : σ) :
    (computeContractAddressQ (m := StateT σ m) sender nonce).run s =
      (do let address ← computeContractAddressQ (m := m) sender nonce
          pure (address, s)) := by
  simp [computeContractAddressQ, KeccakQuery.keccak_stateT]

/-- CREATE2 state forwarding preserves the extra state through both queries. -/
theorem run_computeCreate2ContractAddressQ_stateT {m : Type → Type} {σ : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m] (sender : Address) (salt : Bytes32)
    (initCode : ByteArray) (s : σ) :
    (computeCreate2ContractAddressQ (m := StateT σ m) sender salt initCode).run s =
      (do let address ← computeCreate2ContractAddressQ (m := m) sender salt initCode
          pure (address, s)) := by
  simp [computeCreate2ContractAddressQ, KeccakQuery.keccak_stateT]

/-- Exception forwarding wraps the underlying CREATE success without a handler. -/
theorem run_computeContractAddressQ_exceptT {m : Type → Type} {ε : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m] (sender : Address) (nonce : Nat) :
    (computeContractAddressQ (m := ExceptT ε m) sender nonce).run =
      (do let address ← computeContractAddressQ (m := m) sender nonce
          pure (.ok address : Except ε Address)) := by
  simp only [computeContractAddressQ, KeccakQuery.keccak_exceptT,
    ExceptT.run_map, ExceptT.run_lift, Functor.map_map, Except.map, bind_pure_comp]

/-- Exception forwarding preserves both CREATE2 queries and adds no handler. -/
theorem run_computeCreate2ContractAddressQ_exceptT {m : Type → Type} {ε : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m] (sender : Address) (salt : Bytes32)
    (initCode : ByteArray) :
    (computeCreate2ContractAddressQ (m := ExceptT ε m) sender salt initCode).run =
      (do let address ← computeCreate2ContractAddressQ (m := m) sender salt initCode
          pure (.ok address : Except ε Address)) := by
  simp only [computeCreate2ContractAddressQ, KeccakQuery.keccak_exceptT, ExceptT.run_bind,
    ExceptT.run_map, ExceptT.run_lift, bind_map_left, Functor.map_map, Except.map,
    map_bind, bind_pure_comp]

/-- A failed CREATE query preserves its original error without constructing an address. -/
theorem run_computeContractAddressQ_error {m : Type → Type} {ε : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery (ExceptT ε m)] (sender : Address)
    (nonce : Nat) (error : ε)
    (h : KeccakQuery.keccak (m := ExceptT ε m)
      (Rlp.encode (.list [.bytes sender.toBytes.toByteArray, Rlp.ofNat nonce])) =
        ExceptT.mk (pure (.error error))) :
    (computeContractAddressQ (m := ExceptT ε m) sender nonce).run = pure (.error error) := by
  rw [computeContractAddressQ_eq, h]
  simp only [ExceptT.run_bind, ExceptT.run_mk, pure_bind]

/-- A failed CREATE2 code query returns its original error, without an outer query. -/
theorem run_computeCreate2ContractAddressQ_error_code {m : Type → Type} {ε : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery (ExceptT ε m)] (sender : Address)
    (salt : Bytes32) (initCode : ByteArray) (error : ε)
    (h : KeccakQuery.keccak (m := ExceptT ε m) initCode = ExceptT.mk (pure (.error error))) :
    (computeCreate2ContractAddressQ (m := ExceptT ε m) sender salt initCode).run =
      pure (.error error) := by
  rw [computeCreate2ContractAddressQ_eq, h]
  simp only [ExceptT.run_bind, ExceptT.run_mk, pure_bind]

/-- A failed CREATE2 outer query preserves its exact error after the first answer. -/
theorem run_computeCreate2ContractAddressQ_error_hash {m : Type → Type} {ε : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery (ExceptT ε m)] (sender : Address)
    (salt : Bytes32) (initCode : ByteArray) (codeHash : Hash32) (error : ε)
    (hcode : KeccakQuery.keccak (m := ExceptT ε m) initCode = pure codeHash)
    (hhash : KeccakQuery.keccak (m := ExceptT ε m)
      (⟨#[0xff]⟩ ++ sender.toBytes.toByteArray ++ salt.toBytes.toByteArray ++
        codeHash.toBytes.toByteArray) = ExceptT.mk (pure (.error error))) :
    (computeCreate2ContractAddressQ (m := ExceptT ε m) sender salt initCode).run =
      pure (.error error) := by
  rw [computeCreate2ContractAddressQ_eq, hcode]
  simp only [pure_bind]
  rw [hhash]
  simp only [ExceptT.run_bind, ExceptT.run_mk, pure_bind]

end STFSpec.Codec
