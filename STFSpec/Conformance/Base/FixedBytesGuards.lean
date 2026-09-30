/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.FixedBytes

/-!
# Fixed-width byte regression guards

Library `EthConformance`: exact/short/long lengths, including zero, leading zeros,
endian markers, ordering boundaries, distinct domain conversions and slot-key pairs.
These guards use explicit byte construction and public observations.

Spec guidance: `STFSpec/informal/modules/EthBase.md`.
-/

namespace STFSpec.Conformance.Base.FixedBytesGuards

open STFSpec.Base

private def zeros (n : Nat) : Bytes := Bytes.ofList (List.replicate n (0 : UInt8))
private def filled (n : Nat) (b : UInt8) : Bytes := Bytes.ofList (List.replicate n b)
private def indexed (n : Nat) : Bytes := Bytes.ofList ((List.range n).map UInt8.ofNat)
private def marker (n : Nat) (b : UInt8) : Bytes :=
  Bytes.ofList (List.replicate (n - 1) (0 : UInt8) ++ [b])
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
#guard (FixedBytes.ofBytes? (n := 2 ^ 4096) Bytes.empty) = none

private def widthGuards (n : Nat) : Bool :=
  decide ((FixedBytes.ofBytes? (n := n) (zeros n)).map FixedBytes.toBytes = some (zeros n)) &&
  decide ((FixedBytes.ofBytes? (n := n) (filled n 255)).map FixedBytes.toBytes =
    some (filled n 255)) &&
  decide ((FixedBytes.ofBytes? (n := n) (indexed n)).map FixedBytes.toBytes =
    some (indexed n)) &&
  decide ((FixedBytes.ofBytes? (n := n) (zeros n)).map FixedBytes.toNat = some 0) &&
  decide (FixedBytes.ofBytes? (n := n) (zeros (n + 1)) = none) &&
  decide (order? n (indexed n) (indexed n) = some .eq) &&
  if n = 0 then true else
    decide (FixedBytes.ofBytes? (n := n) (zeros (n - 1)) = none) &&
    decide ((FixedBytes.ofBytes? (n := n) (marker n 1)).map FixedBytes.toNat = some 1) &&
    decide (order? n (zeros n) (filled n 255) = some .lt) &&
    decide (order? n (filled n 255) (zeros n) = some .gt)

/-! Every declared width plus generic widths zero, one and two. -/
#guard widthGuards 0
#guard widthGuards 1
#guard widthGuards 2
#guard widthGuards 8
#guard widthGuards 20
#guard widthGuards 32
#guard widthGuards 48
#guard widthGuards 64
#guard widthGuards 96
#guard widthGuards 256

/-! Byte order markers that would reverse under little-endian interpretation. -/
#guard (FixedBytes.ofBytes? (n := 2) (Bytes.ofList [1, 0])).map
  FixedBytes.toNat = some 256
#guard (FixedBytes.ofBytes? (n := 2) (Bytes.ofList [0, 255])).map
  FixedBytes.toNat = some 255
#guard order? 2 (Bytes.ofList [1, 0]) (Bytes.ofList [0, 255]) =
  some .gt
#guard order? 2 (Bytes.ofList [0, 255]) (Bytes.ofList [1, 0]) =
  some .lt
#guard order? 2 (zeros 1) (zeros 2) = none
#guard (FixedBytes.ofBytes? (n := 0) Bytes.empty).map FixedBytes.toBytes =
  some Bytes.empty
#guard (FixedBytes.ofBytes? (n := 0) (Bytes.ofList [1])) = none

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
#guard (Address.ofBytes? (filled 20 255)).map Address.toNat = some (2 ^ 160 - 1)
#guard addressOrder? (marker 20 1) (marker 20 255) = some .lt
#guard addressOrder? (filled 20 255) (zeros 20) = some .gt
#guard addressOrder? (indexed 20) (indexed 20) = some .eq
#guard (Hash32.ofBytes? (zeros 32)).map Hash32.toBytes = some (zeros 32)
#guard (Hash32.ofBytes? (indexed 32)).map Hash32.toBytes = some (indexed 32)
#guard Hash32.ofBytes? (zeros 31) = none
#guard Hash32.ofBytes? (zeros 33) = none
#guard (Hash32.ofBytes? (marker 32 1)).map Hash32.toNat = some 1
#guard (Hash32.ofBytes? (filled 32 255)).map Hash32.toNat = some (2 ^ 256 - 1)
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
