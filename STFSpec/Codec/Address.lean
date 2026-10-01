/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.RlpEncode
import STFSpec.Hash.KeccakQuery

/-!
# Contract address derivation

Library `EthCodec`. CREATE and CREATE2 preserve the exact supplied oracle answers
and ordered query effects. Pure execution is their definitional `Id` specialization.
Standard CREATE preimage correspondence retains `Rlp.Encodable` (Q47); the Nat
encoder remains total outside that domain. VM creation/state/gas rules are separate.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§2–8.
-/

namespace STFSpec.Codec

open STFSpec.Base STFSpec.Hash

private def lastBytes20 (hash : Hash32) : Address := Address.ofNat hash.toNat

/-- The numeric conversion retains exactly the final twenty public hash bytes,
including leading zeros. Only public Base conversion contracts are used. -/
theorem toBytes_address_of_hash (hash : Hash32) :
    (Address.ofNat hash.toNat).toBytes = Bytes.ofList (hash.toBytes.toList.drop 12) := by
  have h : Address.ofNat hash.toNat =
      Address.ofU256Masked (U256.ofBeBytes32 hash.toBytes32) := by
    apply Address.toNat_inj.mp
    rw [Address.toNat_ofNat, Address.toNat_ofU256Masked, U256.toNat_ofBeBytes32,
      Hash32.toNat_toBytes32]
  rw [h, Address.toBytes_ofU256Masked, U256.toBeBytes32_ofBeBytes32,
    Hash32.toBytes_toBytes32]

/-- One exact RLP sender/minimal-nonce query; EELS
`src/ethereum/forks/amsterdam/utils/address.py:42–63` at the pin. -/
def computeContractAddressQ {m : Type → Type} [Monad m] [KeccakQuery m]
    (sender : Address) (nonce : Nat) : m Address := do
  let hash ← KeccakQuery.keccak
    (Rlp.encode (.list [.bytes sender.toBytes.toByteArray, Rlp.ofNat nonce]))
  pure (lastBytes20 hash)

/-- Two ordered queries: init code, then ff/sender/salt/that answer; EELS
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
complete first answer. An earlier monadic failure suppresses later queries. -/
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
  simp only [bind_assoc, pure_bind, toBytes_address_of_hash]

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
  simp only [bind_assoc, pure_bind, toBytes_address_of_hash]

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
  rw [computeContractAddress_eq, toBytes_address_of_hash]

/-- CREATE2 returns exactly the last twenty outer digest bytes. -/
theorem toBytes_computeCreate2ContractAddress (sender : Address) (salt : Bytes32)
    (initCode : ByteArray) : (computeCreate2ContractAddress sender salt initCode).toBytes =
      Bytes.ofList ((keccak256 (⟨#[0xff]⟩ ++ sender.toBytes.toByteArray ++
        salt.toBytes.toByteArray ++ (keccak256 initCode).toBytes.toByteArray)).toBytes.toList.drop
          12) := by
  rw [computeCreate2ContractAddress_eq, toBytes_address_of_hash]

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
