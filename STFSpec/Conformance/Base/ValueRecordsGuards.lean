/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base

/-!
# Primitive record regression guards

Library `EthConformance`: exact fields, arbitrary constant records, concrete pinned
vectors and unbounded state-gas charge boundaries. No hashing or codecs are exercised.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §§3–4.
-/

open STFSpec.Base

private def zeroAddress : Address :=
  (Address.ofBytes? (Bytes.ofList (List.replicate 20 0))).get (by decide)

private def firstAuth : Authorization :=
  ⟨U256.zero, zeroAddress, U64.zero, U8.zero, U256.zero, U256.one⟩

private def lastAuth : Authorization :=
  ⟨U256.max, zeroAddress, U64.max, U8.max, U256.one, U256.max⟩

#guard firstAuth.chainId.toNat = 0
#guard firstAuth.address.toBytes = (Bytes.ofList (List.replicate 20 0))
#guard firstAuth.nonce.toNat = 0
#guard firstAuth.yParity.toNat = 0
#guard firstAuth.r.toNat = 0
#guard firstAuth.s.toNat = 1
#guard lastAuth.chainId.toNat = 2 ^ 256 - 1
#guard lastAuth.address.toNat = 0
#guard lastAuth.nonce.toNat = 2 ^ 64 - 1
#guard lastAuth.yParity.toNat = 255
#guard lastAuth.r.toNat = 1
#guard lastAuth.s.toNat = 2 ^ 256 - 1
#guard ({lastAuth with nonce := U64.one}).nonce.toNat = 1
#guard ({lastAuth with yParity := U8.one}).nonce.toNat = 2 ^ 64 - 1
#guard ({lastAuth with yParity := U8.one}).yParity.toNat = 1
#guard ({lastAuth with r := U256.zero}).s.toNat = 2 ^ 256 - 1

-- Concrete vectors correspond to source keccak-derived constants, never to sha3-256.
#guard HashConsts.literals.emptyCodeHash.toNat =
  0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470
#guard HashConsts.literals.emptyTrieRoot.toNat =
  0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421
#guard HashConsts.literals.emptyOmmerHash.toNat =
  0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347
#guard HashConsts.literals.transferTopic.toNat =
  0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef
#guard HashConsts.literals.emptyCodeHash.toBytes.size = 32
#guard HashConsts.literals.emptyTrieRoot.toBytes.size = 32
#guard HashConsts.literals.emptyOmmerHash.toBytes.size = 32
#guard HashConsts.literals.transferTopic.toBytes.size = 32

-- An arbitrary record does not assert the concrete Id interpretation.
private def permutedConsts : HashConsts :=
  ⟨HashConsts.literals.transferTopic, HashConsts.literals.emptyOmmerHash,
   HashConsts.literals.emptyTrieRoot, HashConsts.literals.emptyCodeHash⟩
#guard permutedConsts.emptyCodeHash = HashConsts.literals.transferTopic
#guard permutedConsts.emptyTrieRoot = HashConsts.literals.emptyOmmerHash
#guard permutedConsts.emptyOmmerHash = HashConsts.literals.emptyTrieRoot
#guard permutedConsts.transferTopic = HashConsts.literals.emptyCodeHash
#guard permutedConsts.emptyCodeHash ≠ HashConsts.literals.emptyCodeHash
#guard ({permutedConsts with transferTopic := permutedConsts.emptyTrieRoot}).transferTopic =
  HashConsts.literals.emptyOmmerHash

#guard (StateGasPerByte.mk 0).rate = 0
#guard (StateGasPerByte.mk (2 ^ 4096)).rate = 2 ^ 4096
#guard (StateGasPerByte.mk 0).charge 0 = 0
#guard (StateGasPerByte.mk 0).charge (2 ^ 8192) = 0
#guard (StateGasPerByte.mk (2 ^ 8192)).charge 0 = 0
#guard (StateGasPerByte.mk 1).charge 1 = 1
#guard (StateGasPerByte.mk 1).charge (2 ^ 256) = 2 ^ 256
#guard (StateGasPerByte.mk (2 ^ 64 - 1)).charge 2 = 2 ^ 65 - 2
#guard (StateGasPerByte.mk (2 ^ 256)).charge (2 ^ 256) = 2 ^ 512
#guard (StateGasPerByte.mk (2 ^ 4096)).charge (2 ^ 4096) = 2 ^ 8192
#guard (StateGasPerByte.mk (2 ^ 4096 + 1)).charge (2 ^ 4096 + 2) =
  2 ^ 8192 + 3 * 2 ^ 4096 + 2
