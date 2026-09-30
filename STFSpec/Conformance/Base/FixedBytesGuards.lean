/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.FixedBytes

/-!
# Fixed-width byte regression guards

Library `EthConformance`: exact/short/long lengths, including zero, leading zeros,
endian markers, ordering boundaries, distinct domain conversions and slot-key pairs.
These guards execute actual `ByteArray` construction and observations.

Spec guidance: `STFSpec/informal/modules/EthBase.md`.
-/

namespace STFSpec.Conformance.Base.FixedBytesGuards

open STFSpec.Base

private def zeros (n : Nat) : Bytes := (List.replicate n (0 : UInt8)).toByteArray
private def filled (n : Nat) (b : UInt8) : Bytes := (List.replicate n b).toByteArray
private def indexed (n : Nat) : Bytes := ((List.range n).map UInt8.ofNat).toByteArray
private def marker (n : Nat) (b : UInt8) : Bytes :=
  ((List.replicate (n-1) (0 : UInt8)) ++ [b]).toByteArray
private def order? (n : Nat) (a b : Bytes) : Option Ordering := do
  let x ← FixedBytes.ofBytes? (n := n) a
  let y ← FixedBytes.ofBytes? (n := n) b
  pure (compare x y)
private def addressOrder? (a b : Bytes) : Option Ordering := do
  let x ← Address.ofBytes? a
  let y ← Address.ofBytes? b
  pure (compare x y)
private def hashOrder? (a b : Bytes) : Option Ordering := do
  let x ← Hash32.ofBytes? a
  let y ← Hash32.ofBytes? b
  pure (compare x y)
private def pairOrder? (a b c d : Bytes) : Option Ordering := do
  let x ← Address.ofBytes? a
  let y ← FixedBytes.ofBytes? (n := 32) b
  let z ← Address.ofBytes? c
  let w ← FixedBytes.ofBytes? (n := 32) d
  pure (compare (x, y) (z, w))

/-! The byte models are public; raw storage and domain coercions are private. -/
#check_failure FixedBytes.val
#check_failure FixedBytes.ofBitVecRaw
#check_failure fun (x : FixedBytes 2) ↦ x.1
#check_failure (⟨0⟩ : FixedBytes 2)
#check_failure ({ val := 0 } : FixedBytes 2)
#check_failure Address.val
#check_failure Address.ofBitVecRaw
#check_failure Address.toFixed
#check_failure Address.ofFixed
#check_failure fun (x : Address) ↦ x.1
#check_failure (⟨0⟩ : Address)
#check_failure ({ val := 0 } : Address)
#check_failure Hash32.val
#check_failure Hash32.ofBitVecRaw
#check_failure Hash32.toFixed
#check_failure Hash32.ofFixed
#check_failure fun (x : Hash32) ↦ x.1
#check_failure (⟨0⟩ : Hash32)
#check_failure ({ val := 0 } : Hash32)
#check_failure (inferInstance : Coe Hash32 Bytes32)
#check_failure (inferInstance : Coe Bytes32 Hash32)

-- Wrong length rejects before computing a radix or decoding contents.
#guard (FixedBytes.ofBytes? (n := 2 ^ 4096) ByteArray.empty) = none

/-! Every declared width plus generic widths zero, one and two. -/
#guard (FixedBytes.ofBytes? (n := 0) (zeros 0)).map FixedBytes.toBytes = some (zeros 0)
#guard (FixedBytes.ofBytes? (n := 0) (filled 0 255)).map FixedBytes.toBytes = some (filled 0 255)
#guard (FixedBytes.ofBytes? (n := 0) (indexed 0)).map FixedBytes.toBytes = some (indexed 0)
#guard (FixedBytes.ofBytes? (n := 0) (zeros 0)).map FixedBytes.toNat = some 0
#guard (FixedBytes.ofBytes? (n := 0) (zeros 1)) = none
#guard order? 0 (indexed 0) (indexed 0) = some .eq
#guard (FixedBytes.ofBytes? (n := 1) (zeros 1)).map FixedBytes.toBytes = some (zeros 1)
#guard (FixedBytes.ofBytes? (n := 1) (filled 1 255)).map FixedBytes.toBytes = some (filled 1 255)
#guard (FixedBytes.ofBytes? (n := 1) (indexed 1)).map FixedBytes.toBytes = some (indexed 1)
#guard (FixedBytes.ofBytes? (n := 1) (zeros 1)).map FixedBytes.toNat = some 0
#guard (FixedBytes.ofBytes? (n := 1) (zeros 0)) = none
#guard (FixedBytes.ofBytes? (n := 1) (marker 1 1)).map FixedBytes.toNat = some 1
#guard order? 1 (zeros 1) (filled 1 255) = some .lt
#guard order? 1 (filled 1 255) (zeros 1) = some .gt
#guard (FixedBytes.ofBytes? (n := 1) (zeros 2)) = none
#guard order? 1 (indexed 1) (indexed 1) = some .eq
#guard (FixedBytes.ofBytes? (n := 2) (zeros 2)).map FixedBytes.toBytes = some (zeros 2)
#guard (FixedBytes.ofBytes? (n := 2) (filled 2 255)).map FixedBytes.toBytes = some (filled 2 255)
#guard (FixedBytes.ofBytes? (n := 2) (indexed 2)).map FixedBytes.toBytes = some (indexed 2)
#guard (FixedBytes.ofBytes? (n := 2) (zeros 2)).map FixedBytes.toNat = some 0
#guard (FixedBytes.ofBytes? (n := 2) (zeros 1)) = none
#guard (FixedBytes.ofBytes? (n := 2) (marker 2 1)).map FixedBytes.toNat = some 1
#guard order? 2 (zeros 2) (filled 2 255) = some .lt
#guard order? 2 (filled 2 255) (zeros 2) = some .gt
#guard (FixedBytes.ofBytes? (n := 2) (zeros 3)) = none
#guard order? 2 (indexed 2) (indexed 2) = some .eq
#guard (FixedBytes.ofBytes? (n := 8) (zeros 8)).map FixedBytes.toBytes = some (zeros 8)
#guard (FixedBytes.ofBytes? (n := 8) (filled 8 255)).map FixedBytes.toBytes = some (filled 8 255)
#guard (FixedBytes.ofBytes? (n := 8) (indexed 8)).map FixedBytes.toBytes = some (indexed 8)
#guard (FixedBytes.ofBytes? (n := 8) (zeros 8)).map FixedBytes.toNat = some 0
#guard (FixedBytes.ofBytes? (n := 8) (zeros 7)) = none
#guard (FixedBytes.ofBytes? (n := 8) (marker 8 1)).map FixedBytes.toNat = some 1
#guard order? 8 (zeros 8) (filled 8 255) = some .lt
#guard order? 8 (filled 8 255) (zeros 8) = some .gt
#guard (FixedBytes.ofBytes? (n := 8) (zeros 9)) = none
#guard order? 8 (indexed 8) (indexed 8) = some .eq
#guard (FixedBytes.ofBytes? (n := 20) (zeros 20)).map FixedBytes.toBytes = some (zeros 20)
#guard (FixedBytes.ofBytes? (n := 20) (filled 20 255)).map FixedBytes.toBytes = some (filled 20 255)
#guard (FixedBytes.ofBytes? (n := 20) (indexed 20)).map FixedBytes.toBytes = some (indexed 20)
#guard (FixedBytes.ofBytes? (n := 20) (zeros 20)).map FixedBytes.toNat = some 0
#guard (FixedBytes.ofBytes? (n := 20) (zeros 19)) = none
#guard (FixedBytes.ofBytes? (n := 20) (marker 20 1)).map FixedBytes.toNat = some 1
#guard order? 20 (zeros 20) (filled 20 255) = some .lt
#guard order? 20 (filled 20 255) (zeros 20) = some .gt
#guard (FixedBytes.ofBytes? (n := 20) (zeros 21)) = none
#guard order? 20 (indexed 20) (indexed 20) = some .eq
#guard (FixedBytes.ofBytes? (n := 32) (zeros 32)).map FixedBytes.toBytes = some (zeros 32)
#guard (FixedBytes.ofBytes? (n := 32) (filled 32 255)).map FixedBytes.toBytes = some (filled 32 255)
#guard (FixedBytes.ofBytes? (n := 32) (indexed 32)).map FixedBytes.toBytes = some (indexed 32)
#guard (FixedBytes.ofBytes? (n := 32) (zeros 32)).map FixedBytes.toNat = some 0
#guard (FixedBytes.ofBytes? (n := 32) (zeros 31)) = none
#guard (FixedBytes.ofBytes? (n := 32) (marker 32 1)).map FixedBytes.toNat = some 1
#guard order? 32 (zeros 32) (filled 32 255) = some .lt
#guard order? 32 (filled 32 255) (zeros 32) = some .gt
#guard (FixedBytes.ofBytes? (n := 32) (zeros 33)) = none
#guard order? 32 (indexed 32) (indexed 32) = some .eq
#guard (FixedBytes.ofBytes? (n := 48) (zeros 48)).map FixedBytes.toBytes = some (zeros 48)
#guard (FixedBytes.ofBytes? (n := 48) (filled 48 255)).map FixedBytes.toBytes = some (filled 48 255)
#guard (FixedBytes.ofBytes? (n := 48) (indexed 48)).map FixedBytes.toBytes = some (indexed 48)
#guard (FixedBytes.ofBytes? (n := 48) (zeros 48)).map FixedBytes.toNat = some 0
#guard (FixedBytes.ofBytes? (n := 48) (zeros 47)) = none
#guard (FixedBytes.ofBytes? (n := 48) (marker 48 1)).map FixedBytes.toNat = some 1
#guard order? 48 (zeros 48) (filled 48 255) = some .lt
#guard order? 48 (filled 48 255) (zeros 48) = some .gt
#guard (FixedBytes.ofBytes? (n := 48) (zeros 49)) = none
#guard order? 48 (indexed 48) (indexed 48) = some .eq
#guard (FixedBytes.ofBytes? (n := 64) (zeros 64)).map FixedBytes.toBytes = some (zeros 64)
#guard (FixedBytes.ofBytes? (n := 64) (filled 64 255)).map FixedBytes.toBytes = some (filled 64 255)
#guard (FixedBytes.ofBytes? (n := 64) (indexed 64)).map FixedBytes.toBytes = some (indexed 64)
#guard (FixedBytes.ofBytes? (n := 64) (zeros 64)).map FixedBytes.toNat = some 0
#guard (FixedBytes.ofBytes? (n := 64) (zeros 63)) = none
#guard (FixedBytes.ofBytes? (n := 64) (marker 64 1)).map FixedBytes.toNat = some 1
#guard order? 64 (zeros 64) (filled 64 255) = some .lt
#guard order? 64 (filled 64 255) (zeros 64) = some .gt
#guard (FixedBytes.ofBytes? (n := 64) (zeros 65)) = none
#guard order? 64 (indexed 64) (indexed 64) = some .eq
#guard (FixedBytes.ofBytes? (n := 96) (zeros 96)).map FixedBytes.toBytes = some (zeros 96)
#guard (FixedBytes.ofBytes? (n := 96) (filled 96 255)).map FixedBytes.toBytes = some (filled 96 255)
#guard (FixedBytes.ofBytes? (n := 96) (indexed 96)).map FixedBytes.toBytes = some (indexed 96)
#guard (FixedBytes.ofBytes? (n := 96) (zeros 96)).map FixedBytes.toNat = some 0
#guard (FixedBytes.ofBytes? (n := 96) (zeros 95)) = none
#guard (FixedBytes.ofBytes? (n := 96) (marker 96 1)).map FixedBytes.toNat = some 1
#guard order? 96 (zeros 96) (filled 96 255) = some .lt
#guard order? 96 (filled 96 255) (zeros 96) = some .gt
#guard (FixedBytes.ofBytes? (n := 96) (zeros 97)) = none
#guard order? 96 (indexed 96) (indexed 96) = some .eq
#guard (FixedBytes.ofBytes? (n := 256) (zeros 256)).map FixedBytes.toBytes = some (zeros 256)
#guard (FixedBytes.ofBytes? (n := 256) (filled 256 255)).map FixedBytes.toBytes =
  some (filled 256 255)
#guard (FixedBytes.ofBytes? (n := 256) (indexed 256)).map FixedBytes.toBytes = some (indexed 256)
#guard (FixedBytes.ofBytes? (n := 256) (zeros 256)).map FixedBytes.toNat = some 0
#guard (FixedBytes.ofBytes? (n := 256) (zeros 255)) = none
#guard (FixedBytes.ofBytes? (n := 256) (marker 256 1)).map FixedBytes.toNat = some 1
#guard order? 256 (zeros 256) (filled 256 255) = some .lt
#guard order? 256 (filled 256 255) (zeros 256) = some .gt
#guard (FixedBytes.ofBytes? (n := 256) (zeros 257)) = none
#guard order? 256 (indexed 256) (indexed 256) = some .eq

/-! Byte order markers that would reverse under little-endian interpretation. -/
#guard (FixedBytes.ofBytes? (n := 2) ([1, 0] : List UInt8).toByteArray).map
  FixedBytes.toNat = some 256
#guard (FixedBytes.ofBytes? (n := 2) ([0, 255] : List UInt8).toByteArray).map
  FixedBytes.toNat = some 255
#guard order? 2 ([1, 0] : List UInt8).toByteArray ([0, 255] : List UInt8).toByteArray =
  some .gt
#guard order? 2 ([0, 255] : List UInt8).toByteArray ([1, 0] : List UInt8).toByteArray =
  some .lt
#guard order? 2 (zeros 1) (zeros 2) = none
#guard (FixedBytes.ofBytes? (n := 0) ByteArray.empty).map FixedBytes.toBytes =
  some ByteArray.empty
#guard (FixedBytes.ofBytes? (n := 0) ([1] : List UInt8).toByteArray) = none

/-! Aliases elaborate to their specified widths and share the fixed-byte contract. -/
#guard ((FixedBytes.ofBytes? (zeros 8) : Option Bytes8).map FixedBytes.toBytes) = some (zeros 8)
#guard ((FixedBytes.ofBytes? (zeros 32) : Option Bytes32).map FixedBytes.toBytes) = some (zeros 32)
#guard ((FixedBytes.ofBytes? (zeros 48) : Option Bytes48).map FixedBytes.toBytes) = some (zeros 48)
#guard ((FixedBytes.ofBytes? (zeros 64) : Option Bytes64).map FixedBytes.toBytes) = some (zeros 64)
#guard ((FixedBytes.ofBytes? (zeros 96) : Option Bytes96).map FixedBytes.toBytes) = some (zeros 96)
#guard ((FixedBytes.ofBytes? (zeros 256) : Option Bloom).map FixedBytes.toBytes) = some (zeros 256)
#guard ((FixedBytes.ofBytes? (indexed 64) : Option Hash64).map FixedBytes.toBytes) =
  some (indexed 64)

/-! Distinct address/hash domains preserve content and reject by exact length. -/
#guard (Address.ofBytes? (zeros 20)).map Address.toBytes = some (zeros 20)
#guard (Address.ofBytes? (indexed 20)).map Address.toBytes = some (indexed 20)
#guard Address.ofBytes? (zeros 19) = none
#guard Address.ofBytes? (zeros 21) = none
#guard (Address.ofBytes? (marker 20 1)).map Address.toNat = some 1
#guard (Address.ofBytes? (filled 20 255)).map Address.toNat = some (2^160-1)
#guard addressOrder? (marker 20 1) (marker 20 255) = some .lt
#guard addressOrder? (filled 20 255) (zeros 20) = some .gt
#guard addressOrder? (indexed 20) (indexed 20) = some .eq
#guard (Hash32.ofBytes? (zeros 32)).map Hash32.toBytes = some (zeros 32)
#guard (Hash32.ofBytes? (indexed 32)).map Hash32.toBytes = some (indexed 32)
#guard Hash32.ofBytes? (zeros 31) = none
#guard Hash32.ofBytes? (zeros 33) = none
#guard (Hash32.ofBytes? (marker 32 1)).map Hash32.toNat = some 1
#guard (Hash32.ofBytes? (filled 32 255)).map Hash32.toNat = some (2^256-1)
#guard hashOrder? (marker 32 1) (marker 32 255) = some .lt
#guard hashOrder? (filled 32 255) (zeros 32) = some .gt
#guard hashOrder? (indexed 32) (indexed 32) = some .eq
#guard ((Hash32.ofBytes? (indexed 32)).map Hash32.toBytes32).map FixedBytes.toBytes =
  some (indexed 32)
#guard ((FixedBytes.ofBytes? (n := 32) (indexed 32)).map Hash32.ofBytes32).map Hash32.toBytes =
  some (indexed 32)
#guard ((Hash32.ofBytes? (zeros 32) : Option Root).map Hash32.toBytes) = some (zeros 32)
#guard ((Hash32.ofBytes? (zeros 32) : Option VersionedHash).map Hash32.toBytes) = some (zeros 32)

/-! Lexical pair ordering: address dominates reversed slots; equal address uses slot. -/
#guard pairOrder? (zeros 20) (filled 32 255) (marker 20 1) (zeros 32) = some .lt
#guard pairOrder? (marker 20 1) (zeros 32) (zeros 20) (filled 32 255) = some .gt
#guard pairOrder? (zeros 20) (zeros 32) (zeros 20) (marker 32 1) = some .lt
#guard pairOrder? (zeros 20) (marker 32 1) (zeros 20) (zeros 32) = some .gt
#guard pairOrder? (indexed 20) (indexed 32) (indexed 20) (indexed 32) = some .eq
#guard pairOrder? (zeros 19) (zeros 32) (zeros 20) (zeros 32) = none

end STFSpec.Conformance.Base.FixedBytesGuards
