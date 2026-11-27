/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block

/-!
# Block access list hash controls

Library `EthConformance`. Private proofs use the Block facade. Interpreted
controls compare complete preimages and digests from the pinned EELS source.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3–5.
-/

namespace STFSpec.Conformance.Block.BlockAccessListHashControls

open STFSpec.Base STFSpec.Block STFSpec.Codec STFSpec.Hash

private theorem hashAction {m : Type → Type} [Monad m] [KeccakQuery m]
    (bal : BlockAccessList) :
    hashBlockAccessList (m := m) bal = KeccakQuery.keccak (Rlp.encodeOf bal.toList) := rfl

private theorem hashId (bal : BlockAccessList) :
    hashBlockAccessList (m := Id) bal = keccak256 (Rlp.encodeOf bal.toList) := rfl

private abbrev Trace := StateM (List ByteArray)

@[instance_reducible]
private def recorder (answer : Hash32) : KeccakQuery Trace where
  keccak input := fun previous ↦ (answer, input :: previous)

private theorem hashTrace (bal : BlockAccessList) (answer : Hash32) (previous : List ByteArray) :
    letI := recorder answer
    (hashBlockAccessList (m := Trace) bal).run previous =
      (answer, Rlp.encodeOf bal.toList :: previous) := rfl

private def matchesSource (bal : BlockAccessList) (wire digest : List UInt8) : Bool :=
  let expectedAnswer := HashConsts.literals.emptyCodeHash
  letI := recorder expectedAnswer
  let previous := [ByteArray.mk #[0x42, 0xa0]]
  let (answer, trace) := (hashBlockAccessList (m := Trace) bal).run previous
  answer == expectedAnswer && trace == ByteArray.mk wire.toArray :: previous &&
    (hashBlockAccessList (m := Id) bal).toBytes.toList == digest

private def blank : AccountChanges :=
  AccountChanges.mk (Address.ofNat 0) [] [] [] [] []

private def rich : AccountChanges :=
  AccountChanges.mk (Address.ofNat 0x001122330044ff0066778899aabbccddeeff0001)
    [⟨U256.ofNat 2, [⟨U32.ofNat 5, U256.ofNat 256⟩, ⟨U32.zero, U256.zero⟩]⟩]
    [U256.ofNat 2, U256.ofNat 1, U256.ofNat 2]
    [⟨U32.ofNat 128, U256.ofNat 1⟩] [⟨U32.zero, U64.max⟩]
    [⟨U32.ofNat 5, ⟨#[0xff, 0x00, 0x9a]⟩⟩, ⟨U32.zero, ⟨#[0]⟩⟩,
     ⟨U32.ofNat 5, ByteArray.empty⟩]

private def blankWire : List UInt8 :=
  [0xda, 0x94] ++ List.replicate 20 0 ++ List.replicate 5 0xc0

private def richWire : List UInt8 :=
  [0xf8, 0x43, 0x94, 0x00, 0x11, 0x22, 0x33, 0x00, 0x44, 0xff, 0x00, 0x66,
   0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff, 0x00, 0x01,
   0xcb, 0xca, 0x02, 0xc8, 0xc4, 0x05, 0x82, 0x01, 0x00, 0xc2, 0x80, 0x80,
   0xc3, 0x02, 0x01, 0x02, 0xc4, 0xc3, 0x81, 0x80, 0x01, 0xcb, 0xca, 0x80,
   0x88, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xcc, 0xc5, 0x05,
   0x83, 0xff, 0x00, 0x9a, 0xc2, 0x80, 0x00, 0xc2, 0x05, 0x80]

#guard matchesSource #[] [0xc0]
  [0x1d, 0xcc, 0x4d, 0xe8, 0xde, 0xc7, 0x5d, 0x7a, 0xab, 0x85, 0xb5, 0x67,
   0xb6, 0xcc, 0xd4, 0x1a, 0xd3, 0x12, 0x45, 0x1b, 0x94, 0x8a, 0x74, 0x13,
   0xf0, 0xa1, 0x42, 0xfd, 0x40, 0xd4, 0x93, 0x47]

#guard matchesSource #[blank] (0xdb :: blankWire)
  [0x6f, 0x30, 0x5d, 0xb0, 0xbb, 0x6e, 0xfc, 0x6f, 0x66, 0x87, 0x13, 0x71,
   0x24, 0x96, 0x9a, 0x3b, 0x85, 0x29, 0xab, 0xb4, 0x55, 0xc8, 0x8f, 0x50,
   0xec, 0x9e, 0x9b, 0xdf, 0x88, 0x8f, 0xe9, 0x6d]

#guard matchesSource #[rich, rich, blank] ([0xf8, 0xa5] ++ richWire ++ richWire ++ blankWire)
  [0x41, 0x04, 0x16, 0x68, 0xe6, 0xa9, 0x75, 0x57, 0xec, 0xf0, 0x36, 0x7d,
   0xb3, 0xe3, 0xce, 0x6d, 0x64, 0x59, 0x81, 0x94, 0xb3, 0x5f, 0x1d, 0xe9,
   0xb6, 0x14, 0x1a, 0xd4, 0xea, 0x83, 0x44, 0x64]

end STFSpec.Conformance.Block.BlockAccessListHashControls
