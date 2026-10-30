/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block
import STFSpec.Base.Bytes
import STFSpec.Conformance.Block.CalldataTokensGuards
import Lean

/-!
# Complete compiled calldata-token observations

Library `EthConformance`. The finite independent catalog has 266 inputs.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3/4/7.
-/

open STFSpec.Block STFSpec.Base Lean

private def digit (n : Nat) : Char := Char.ofNat (if n < 10 then 48 + n else 87 + n)
private def hex (data : ByteArray) : String :=
  String.ofList (data.data.toList.flatMap fun b ↦ [digit (b.toNat / 16), digit (b.toNat % 16)])
private def generated (n : Nat) (f : Nat → UInt8) : ByteArray :=
  (Bytes.generate n f).toByteArray
private def emit (value : Json) : IO Unit := do (← IO.getStdout).putStrLn value.compress
private def emitCase (id : String) (data : ByteArray) : IO Unit :=
  emit (Json.mkObj [("id", toJson id), ("hex", toJson (hex data)),
    ("actual", toJson (countTokensInData data))])

/-- Emit actual complete input/result rows, with a bounded catalog frame. -/
def main : IO Unit := do
  emit (Json.mkObj [("schema", toJson "calldata-tokens-v1"), ("count", toJson (266 : Nat))])
  emitCase "empty" ByteArray.empty
  emitCase "zero2" (ByteArray.mk #[0, 0])
  emitCase "nonzero2" (ByteArray.mk #[1, 128])
  emitCase "mixed" (ByteArray.mk #[0, 1, 0, 255, 128])
  emitCase "all_bytes" (generated 256 UInt8.ofNat)
  emitCase "all_nonzero" (generated 255 (fun i ↦ UInt8.ofNat (i + 1)))
  emitCase "zeros_10240" (generated 10240 (fun _ ↦ 0))
  emitCase "nonzero_10240" (generated 10240 (fun _ ↦ 255))
  emitCase "alternating_513" (generated 1026 (fun i ↦ if i % 2 = 0 then 0 else 255))
  emitCase "endpoint_zero" (generated 1025 (fun i ↦ if i = 0 ∨ i = 1024 then 0 else 171))
  for i in List.range 256 do
    let pad := if i < 10 then "00" else if i < 100 then "0" else ""
    emitCase ("singleton_" ++ pad ++ toString i) (ByteArray.mk #[UInt8.ofNat i])
  emit (Json.mkObj [("end", toJson true), ("count", toJson (266 : Nat))])
