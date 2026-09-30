/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.FixedBytes
import STFSpec.Base.U256
import STFSpec.Base.U64
import STFSpec.Base.U8

/-!
# Primitive records and concrete hash-constant values

Library `EthBase`: value records only, without hashing or fork policy. Authorization and
state-gas charging follow pinned EELS `src/ethereum/forks/amsterdam/fork_types.py:45,58,62,87`.
`HashConsts.literals` records the concrete `Id` vectors; generic consumers receive an
explicit record acquired by EthHash (D5/F20), rather than substituting these literals.
Spec guidance: `STFSpec/informal/modules/EthBase.md`.
-/

namespace STFSpec.Base

/-- Keccak-derived values acquired through EthHash and threaded by callers (D5/F20). -/
structure HashConsts where
  /-- Empty code hash value; EELS `src/ethereum/state.py:36`. -/
  emptyCodeHash : Hash32
  /-- Empty trie root value; EELS `src/ethereum/merkle_patricia_trie.py:71`. -/
  emptyTrieRoot : Hash32
  /-- Empty ommer hash value; EELS `src/ethereum/forks/amsterdam/fork.py:116`. -/
  emptyOmmerHash : Hash32
  /-- Transfer event topic value; EELS `src/ethereum/forks/amsterdam/vm/__init__.py:40`. -/
  transferTopic : Hash32

namespace HashConsts

/-- Construction preserves the `emptyCodeHash` field. -/
theorem emptyCodeHash_mk (emptyCodeHash : Hash32) (emptyTrieRoot : Hash32)
    (emptyOmmerHash : Hash32) (transferTopic : Hash32) :
    (HashConsts.mk emptyCodeHash emptyTrieRoot emptyOmmerHash transferTopic).emptyCodeHash =
      emptyCodeHash := rfl

/-- Construction preserves the `emptyTrieRoot` field. -/
theorem emptyTrieRoot_mk (emptyCodeHash : Hash32) (emptyTrieRoot : Hash32)
    (emptyOmmerHash : Hash32) (transferTopic : Hash32) :
    (HashConsts.mk emptyCodeHash emptyTrieRoot emptyOmmerHash transferTopic).emptyTrieRoot =
      emptyTrieRoot := rfl

/-- Construction preserves the `emptyOmmerHash` field. -/
theorem emptyOmmerHash_mk (emptyCodeHash : Hash32) (emptyTrieRoot : Hash32)
    (emptyOmmerHash : Hash32) (transferTopic : Hash32) :
    (HashConsts.mk emptyCodeHash emptyTrieRoot emptyOmmerHash transferTopic).emptyOmmerHash =
      emptyOmmerHash := rfl

/-- Construction preserves the `transferTopic` field. -/
theorem transferTopic_mk (emptyCodeHash : Hash32) (emptyTrieRoot : Hash32)
    (emptyOmmerHash : Hash32) (transferTopic : Hash32) :
    (HashConsts.mk emptyCodeHash emptyTrieRoot emptyOmmerHash transferTopic).transferTopic =
      transferTopic := rfl

/-- Public projections determine the complete record. -/
theorem ext {x y : HashConsts}
    (h0 : x.emptyCodeHash = y.emptyCodeHash)
    (h1 : x.emptyTrieRoot = y.emptyTrieRoot)
    (h2 : x.emptyOmmerHash = y.emptyOmmerHash)
    (h3 : x.transferTopic = y.transferTopic) : x = y := by
  cases x
  cases y
  cases h0
  cases h1
  cases h2
  cases h3
  rfl

/-- Reconstructing the public fields returns the original record. -/
theorem eta (x : HashConsts) :
    HashConsts.mk x.emptyCodeHash x.emptyTrieRoot x.emptyOmmerHash x.transferTopic = x := by
  cases x
  rfl

end HashConsts

/-- Authorization value, with exact EELS `src/ethereum/forks/amsterdam/fork_types.py:87` fields. -/
structure Authorization where
  /-- Source field at EELS `src/ethereum/forks/amsterdam/fork_types.py:92`. -/
  chainId : U256
  /-- Source field at EELS `src/ethereum/forks/amsterdam/fork_types.py:93`. -/
  address : Address
  /-- Source field at EELS `src/ethereum/forks/amsterdam/fork_types.py:94`. -/
  nonce : U64
  /-- Source field at EELS `src/ethereum/forks/amsterdam/fork_types.py:95`. -/
  yParity : U8
  /-- Source field at EELS `src/ethereum/forks/amsterdam/fork_types.py:96`. -/
  r : U256
  /-- Source field at EELS `src/ethereum/forks/amsterdam/fork_types.py:97`. -/
  s : U256

namespace Authorization

/-- Construction preserves the `chainId` field. -/
theorem chainId_mk (chainId : U256)
    (address : Address) (nonce : U64) (yParity : U8) (r : U256) (s : U256) :
    (Authorization.mk chainId address nonce yParity r s).chainId = chainId := rfl

/-- Construction preserves the `address` field. -/
theorem address_mk (chainId : U256)
    (address : Address) (nonce : U64) (yParity : U8) (r : U256) (s : U256) :
    (Authorization.mk chainId address nonce yParity r s).address = address := rfl

/-- Construction preserves the `nonce` field. -/
theorem nonce_mk (chainId : U256)
    (address : Address) (nonce : U64) (yParity : U8) (r : U256) (s : U256) :
    (Authorization.mk chainId address nonce yParity r s).nonce = nonce := rfl

/-- Construction preserves the `yParity` field. -/
theorem yParity_mk (chainId : U256)
    (address : Address) (nonce : U64) (yParity : U8) (r : U256) (s : U256) :
    (Authorization.mk chainId address nonce yParity r s).yParity = yParity := rfl

/-- Construction preserves the `r` field. -/
theorem r_mk (chainId : U256)
    (address : Address) (nonce : U64) (yParity : U8) (r : U256) (s : U256) :
    (Authorization.mk chainId address nonce yParity r s).r = r := rfl

/-- Construction preserves the `s` field. -/
theorem s_mk (chainId : U256)
    (address : Address) (nonce : U64) (yParity : U8) (r : U256) (s : U256) :
    (Authorization.mk chainId address nonce yParity r s).s = s := rfl

/-- Public projections determine the complete record. -/
theorem ext {x y : Authorization}
    (h0 : x.chainId = y.chainId)
    (h1 : x.address = y.address)
    (h2 : x.nonce = y.nonce)
    (h3 : x.yParity = y.yParity)
    (h4 : x.r = y.r)
    (h5 : x.s = y.s) : x = y := by
  cases x
  cases y
  cases h0
  cases h1
  cases h2
  cases h3
  cases h4
  cases h5
  rfl

/-- Reconstructing the public fields returns the original record. -/
theorem eta (x : Authorization) :
    Authorization.mk x.chainId x.address x.nonce x.yParity x.r x.s = x := by
  cases x
  rfl

end Authorization

/-- State-growth rate; EELS `src/ethereum/forks/amsterdam/fork_types.py:45`.
The Amsterdam rate value belongs to EthFork, rather than this primitive type. -/
structure StateGasPerByte where
  /-- Unbounded rate; EELS `src/ethereum/forks/amsterdam/fork_types.py:56`. -/
  rate : Nat

namespace StateGasPerByte

/-- Construction preserves the `rate` field. -/
theorem rate_mk (rate : Nat) :
    (StateGasPerByte.mk rate).rate = rate := rfl

/-- Public projections determine the complete record. -/
theorem ext {x y : StateGasPerByte}
    (h0 : x.rate = y.rate) : x = y := by
  cases x
  cases y
  cases h0
  rfl

/-- Reconstructing the public fields returns the original record. -/
theorem eta (x : StateGasPerByte) :
    StateGasPerByte.mk x.rate = x := by
  cases x
  rfl

/-- Charge an unbounded byte count; EELS `src/ethereum/forks/amsterdam/fork_types.py:58,62`.
Both source operand orders multiply the same unbounded rate and byte count. -/
def charge (g : StateGasPerByte) (numBytes : Nat) : Nat := g.rate * numBytes

/-- The charging model is exact unbounded natural multiplication. -/
theorem charge_eq (g : StateGasPerByte) (numBytes : Nat) :
    g.charge numBytes = g.rate * numBytes := rfl

/-- The reverse source operand order has the same charging observation. -/
theorem charge_eq_mul_rate (g : StateGasPerByte) (numBytes : Nat) :
    g.charge numBytes = numBytes * g.rate := Nat.mul_comm _ _

/-- No bytes incur no state-gas charge. -/
theorem charge_zero (g : StateGasPerByte) : g.charge 0 = 0 := Nat.mul_zero _

/-- A zero rate incurs no charge for any byte count. -/
theorem charge_mk_zero (numBytes : Nat) : (StateGasPerByte.mk 0).charge numBytes = 0 :=
  Nat.zero_mul _

end StateGasPerByte

namespace HashConsts

private def checkedHash (b : Bytes) (h : b.size = 32) : Hash32 :=
  (Hash32.ofBytes? b).get (Option.isSome_iff_ne_none.mpr (by
    intro hn
    exact (Hash32.ofBytes?_eq_none_iff.mp hn) h))

private theorem toBytes_checkedHash (b : Bytes) (h : b.size = 32) :
    (checkedHash b h).toBytes = b :=
  (Hash32.ofBytes?_eq_some_iff.mp (Option.eq_some_of_isSome _)).2

/-- Concrete `Id` hash values for the four pinned source constants:
EELS `src/ethereum/state.py:36`, `merkle_patricia_trie.py:71`,
`forks/amsterdam/fork.py:116`, `forks/amsterdam/vm/__init__.py:40`.
These bytes perform no hashing and impose no invariant on an arbitrary `HashConsts` record.
EthHash owns the future query-to-literals equality and runtime acquisition (D5/F20). -/
def literals : HashConsts where
  emptyCodeHash := checkedHash (Bytes.ofList ([
    0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c,
    0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0,
    0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b,
    0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70
  ] : List UInt8)) (by decide)
  emptyTrieRoot := checkedHash (Bytes.ofList ([
    0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6,
    0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e,
    0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0,
    0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21
  ] : List UInt8)) (by decide)
  emptyOmmerHash := checkedHash (Bytes.ofList ([
    0x1d, 0xcc, 0x4d, 0xe8, 0xde, 0xc7, 0x5d, 0x7a,
    0xab, 0x85, 0xb5, 0x67, 0xb6, 0xcc, 0xd4, 0x1a,
    0xd3, 0x12, 0x45, 0x1b, 0x94, 0x8a, 0x74, 0x13,
    0xf0, 0xa1, 0x42, 0xfd, 0x40, 0xd4, 0x93, 0x47
  ] : List UInt8)) (by decide)
  transferTopic := checkedHash (Bytes.ofList ([
    0xdd, 0xf2, 0x52, 0xad, 0x1b, 0xe2, 0xc8, 0x9b,
    0x69, 0xc2, 0xb0, 0x68, 0xfc, 0x37, 0x8d, 0xaa,
    0x95, 0x2b, 0xa7, 0xf1, 0x63, 0xc4, 0xa1, 0x16,
    0x28, 0xf5, 0x5a, 0x4d, 0xf5, 0x23, 0xb3, 0xef
  ] : List UInt8)) (by decide)

/-- The concrete `emptyCodeHash` vector, through the public byte model. -/
theorem toBytes_literals_emptyCodeHash :
    literals.emptyCodeHash.toBytes = (Bytes.ofList ([
      0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c,
      0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0,
      0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b,
      0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70
    ] : List UInt8)) :=
  toBytes_checkedHash _ _

/-- The concrete `emptyTrieRoot` vector, through the public byte model. -/
theorem toBytes_literals_emptyTrieRoot :
    literals.emptyTrieRoot.toBytes = (Bytes.ofList ([
      0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6,
      0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e,
      0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0,
      0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21
    ] : List UInt8)) :=
  toBytes_checkedHash _ _

/-- The concrete `emptyOmmerHash` vector, through the public byte model. -/
theorem toBytes_literals_emptyOmmerHash :
    literals.emptyOmmerHash.toBytes = (Bytes.ofList ([
      0x1d, 0xcc, 0x4d, 0xe8, 0xde, 0xc7, 0x5d, 0x7a,
      0xab, 0x85, 0xb5, 0x67, 0xb6, 0xcc, 0xd4, 0x1a,
      0xd3, 0x12, 0x45, 0x1b, 0x94, 0x8a, 0x74, 0x13,
      0xf0, 0xa1, 0x42, 0xfd, 0x40, 0xd4, 0x93, 0x47
    ] : List UInt8)) :=
  toBytes_checkedHash _ _

/-- The concrete `transferTopic` vector, through the public byte model. -/
theorem toBytes_literals_transferTopic :
    literals.transferTopic.toBytes = (Bytes.ofList ([
      0xdd, 0xf2, 0x52, 0xad, 0x1b, 0xe2, 0xc8, 0x9b,
      0x69, 0xc2, 0xb0, 0x68, 0xfc, 0x37, 0x8d, 0xaa,
      0x95, 0x2b, 0xa7, 0xf1, 0x63, 0xc4, 0xa1, 0x16,
      0x28, 0xf5, 0x5a, 0x4d, 0xf5, 0x23, 0xb3, 0xef
    ] : List UInt8)) :=
  toBytes_checkedHash _ _

end HashConsts

end STFSpec.Base
