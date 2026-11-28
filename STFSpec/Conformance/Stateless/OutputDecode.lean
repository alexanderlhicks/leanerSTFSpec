/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.IntegerBytes
import STFSpec.Stateless.Output

/-!
# Stateless result deserialization

Library `EthConformance`. The fixed-width host decoder and its left inverse.
Spec guidance is in `STFSpec/informal/modules/EthConformance.md` (R10, L-host-inverse).
-/

namespace STFSpec.Conformance

open STFSpec.Base STFSpec.Codec STFSpec.Stateless

private def decodeFlag (byte : UInt8) : Except SszError Bool :=
  if byte = 0 then .ok false else if byte = 1 then .ok true else .error .boolByte

/-- Decode the four fields of the SSZ result used by the host.
EELS `src/ethereum/forks/amsterdam/stateless_host.py:41–43` at the pin. -/
def deserializeStatelessOutput (input : ByteArray) : Except SszError StatelessValidationResult :=
  if input.size = 43 then do
    let bytes := Bytes.ofByteArray input
    let some flag := input[32]? | .error .length
    let success ← decodeFlag flag
    let some root := Hash32.ofBytes? (bytes.extract 0 32) | .error .length
    let some chain := U64.ofLeBytes? (bytes.extract 33 41) | .error .length
    let schema := UInt16.ofNat (Uint.ofLeBytes (bytes.extract 41 43))
    pure ⟨root, success, chain, schema⟩
  else
    .error .length

private def digits (width value : Nat) : List UInt8 :=
  (List.range width).map fun i ↦ UInt8.ofNat ((value / 256 ^ i) % 256)

private theorem digits_eq_fixed (width value : Nat) :
    Bytes.ofList (digits width value) = (FixedBytes.ofLeNat (n := width) value).toBytes := by
  apply Bytes.ext
  rw [FixedBytes.toBytes_ofLeNat, Bytes.toList_ofList, Bytes.toList_generate, digits]
  apply List.map_congr_left
  intro i _
  rw [Nat.shiftRight_eq_div_pow, Nat.pow_mul]
  exact UInt8.toNat.inj (by simp)

private theorem schema_roundtrip (schema : UInt16) :
    UInt16.ofNat (Uint.ofLeBytes (Bytes.ofList (digits 2 schema.toNat))) = schema := by
  rw [digits_eq_fixed, Uint.ofLeBytes_eq_reverse, FixedBytes.toBytes_ofLeNat_eq_reverse,
    Bytes.toList_ofList, List.reverse_reverse, Bytes.ofList_toList,
    Uint.ofBeBytes_eq_fold, ← FixedBytes.toNat_eq_fold,
    FixedBytes.toNat_ofNat_of_lt _ schema.toNat_lt]
  apply UInt16.toNat.inj
  rw [UInt16.toNat_ofNat']
  exact Nat.mod_eq_of_lt schema.toNat_lt

/-- Deserializing a serialized stateless result recovers all four fields. -/
theorem deserializeStatelessOutput_serializeStatelessOutput (result : StatelessValidationResult) :
    deserializeStatelessOutput (serializeStatelessOutput result) = .ok result := by
  let input := serializeStatelessOutput result
  let bytes := Bytes.ofByteArray input
  let root := result.newPayloadRequestRoot.toBytes.toList
  let flag : UInt8 := if result.successfulValidation then 1 else 0
  let chain := digits 8 result.chainId.toNat
  let schema := digits 2 result.schemaId.toNat
  have layout : bytes.toList = root ++ flag :: (chain ++ schema) := by
    change (serializeStatelessOutput result).data.toList = _
    simpa only [root, flag, chain, schema, digits, List.append_assoc, List.cons_append,
      List.nil_append] using
      serializeStatelessOutput_eq result
  have width : input.size = 43 := serializeStatelessOutput_size result
  have rootLength : root.length = 32 := by
    change result.newPayloadRequestRoot.toBytes.toList.length = 32
    rw [Bytes.length_toList, Hash32.size_toBytes]
  have chainLength : chain.length = 8 := by simp [chain, digits]
  have dropRoot : bytes.toList.drop 32 = flag :: (chain ++ schema) := by
    rw [layout, List.drop_left' rootLength]
  have dropFlag : bytes.toList.drop 33 = chain ++ schema := by
    rw [← List.drop_drop (j := 32) (i := 1), dropRoot, List.drop_succ_cons, List.drop_zero]
  have flagAtIndex : input[32]? = some flag := by
    have packedToList : input[32]? = bytes.toList[32]? := by
      rw [show bytes.toList = input.data.toList from Bytes.toList_ofByteArray input,
        Array.getElem?_toList]
      simp only [getElem?_def, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    rw [packedToList, layout, List.getElem?_append_right (show root.length ≤ 32 by omega),
      rootLength, Nat.sub_self, List.getElem?_cons_zero]
  have rootBytes : (Bytes.ofByteArray input).extract 0 32 = result.newPayloadRequestRoot.toBytes := by
    change bytes.extract 0 32 = _
    apply Bytes.ext
    rw [Bytes.toList_extract, layout, List.drop_zero, Nat.sub_zero, List.take_left' rootLength]
  have chainBytes :
      (Bytes.ofByteArray input).extract 33 41 = (U64.toLeBytes8 result.chainId).toBytes := by
    change bytes.extract 33 41 = _
    rw [U64.toLeBytes8, ← digits_eq_fixed]
    apply Bytes.ext
    rw [Bytes.toList_extract, dropFlag, List.take_left' chainLength, Bytes.toList_ofList]
  have schemaBytes : (Bytes.ofByteArray input).extract 41 43 = Bytes.ofList schema := by
    change bytes.extract 41 43 = _
    have schemaLength : schema.length = 2 := by simp [schema, digits]
    apply Bytes.ext
    rw [Bytes.toList_extract, ← List.drop_drop (j := 33) (i := 8), dropFlag,
      List.drop_left' chainLength, show 43 - 41 = 2 by decide, ← schemaLength,
      List.take_length, Bytes.toList_ofList]
  have flagRoundtrip : decodeFlag flag = .ok result.successfulValidation := by
    cases h : result.successfulValidation <;> simp [flag, h, decodeFlag]
  change deserializeStatelessOutput input = .ok result
  rw [deserializeStatelessOutput, ite_eq_left width, flagAtIndex]
  simp only [flagRoundtrip, rootBytes, chainBytes, schemaBytes, Hash32.ofBytes?_toBytes,
    U64.ofLeBytes?_toLeBytes8, schema, schema_roundtrip]
  rfl

end STFSpec.Conformance
