/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.StateCommit

/-!
# Complete canonical storage bytes
Library `EthConformance`. Deterministic whole-byte reference/instance controls;
the source driver compares actual original U256 dispatch separately.
Spec guidance: `STFSpec/informal/modules/EthStateCommit.md` SC2/Q53/§4.
-/
namespace STFSpec.Conformance.StateCommit.StorageEncodingGuards
open STFSpec.Base STFSpec.Codec STFSpec.Commit STFSpec.StateCommit

private def reference (v : U256) : List UInt8 :=
  Rlp.encodeModel (.bytes (Uint.toBeBytesReference v.toNat).toByteArray)
private def boundaryValues : List Nat :=
  [0, 1, 127, 128, 255, 256] ++ (List.range 32).flatMap fun i ↦
    let n := 256 ^ (i + 1)
    [n - 1] ++ if n < 2 ^ 256 then [n, n + 1] else []
private def patternedValues : List Nat :=
  (List.range 32).flatMap fun i ↦
    let k := i + 1
    [(2 ^ (8 * k) - 1) / 3, 2 ^ (8 * k - 1), 2 ^ (8 * k - 1) + 1,
      Uint.ofBeBytes (Bytes.ofList (List.replicate k 170)),
      Uint.ofBeBytes (Bytes.ofList (List.replicate k 85)),
      Uint.ofBeBytes (Bytes.ofList ((List.range k).map fun j ↦ UInt8.ofNat (j * 31 + 7)))]
private def generatedValues : List Nat :=
  (List.range 512).map fun i ↦
    (i * 123456789012345678901234567890123456789 +
      2 ^ (i % 256) + i * 256 ^ 16) % 2 ^ 256
private def values : List Nat := boundaryValues ++ patternedValues ++ generatedValues
private def check (n : Nat) : Bool :=
  let v := U256.ofNat n
  let raw := encodeStorage v
  decide (n < 2 ^ 256) && raw.data.toList == reference v &&
    raw.size > 0 && raw.size ≤ 33 && TrieValue.encode v == raw

#guard values.all check
#guard (encodeStorage U256.zero).data.toList == [128]
#guard (encodeStorage (U256.ofNat 1)).data.toList == [1]
#guard (encodeStorage (U256.ofNat 127)).data.toList == [127]
#guard (encodeStorage (U256.ofNat 128)).data.toList == [129, 128]
#guard (encodeStorage (U256.ofNat 255)).data.toList == [129, 255]
#guard (encodeStorage (U256.ofNat 256)).data.toList == [130, 1, 0]
#guard (encodeStorage U256.max).data.toList == 160 :: List.replicate 32 255
#guard (List.range 32).all fun i ↦
  let v := U256.ofNat (2^(8 * (i + 1) - 1))
  (encodeStorage v).data.toList == UInt8.ofNat (128 + i + 1) :: 128 :: List.replicate i 0
-- Leading fixed-width zero bytes are interpreted as integers, not padded payloads.
#guard (encodeStorage (U256.ofBeBytes32 (FixedBytes.ofNat 1))).data.toList == [1]
#guard (encodeStorage (U256.ofBeBytes32 (FixedBytes.ofNat 0))).data.toList == [128]
#guard (encodeStorage (U256.ofNat (256 ^ 31 : Nat))).data.toList == 160 :: 1 :: List.replicate 31 0

private def emit : IO Unit := do
  for (n, i) in values.zipIdx do
    let raw := encodeStorage (U256.ofNat n)
    IO.println s!"\{\"case\":{i},\"value\":{n},\"encoded\":{raw.data.toList.map UInt8.toNat}}"
end STFSpec.Conformance.StateCommit.StorageEncodingGuards
