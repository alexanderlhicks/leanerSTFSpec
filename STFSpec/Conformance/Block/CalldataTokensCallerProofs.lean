/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block

/-!
# Private clients of the complete calldata-token law

Library `EthConformance`. Only the public operation and its result equation are used.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3/4/5/7.
-/

namespace STFSpec.Conformance.Block.CalldataTokensCallerProofs
open STFSpec.Block

private theorem empty : countTokensInData ByteArray.empty = 0 := by
  rw [countTokensInData_eq]
  rfl

private theorem bounds (data : ByteArray) :
    data.size ≤ countTokensInData data ∧ countTokensInData data ≤ 4 * data.size := by
  rw [countTokensInData_eq]
  have h := List.length_filter_le (fun byte : UInt8 ↦ byte == 0) data.data.toList
  have hs : data.data.toList.length = data.size := rfl
  omega

private theorem append (a b : ByteArray) :
    countTokensInData (a ++ b) = countTokensInData a + countTokensInData b := by
  simp only [countTokensInData_eq, ByteArray.toList_data_append, List.filter_append,
    List.length_append, ByteArray.size_append]
  have ha := List.length_filter_le (fun byte : UInt8 ↦ byte == 0) a.data.toList
  have hb := List.length_filter_le (fun byte : UInt8 ↦ byte == 0) b.data.toList
  have hsa : a.data.toList.length = a.size := rfl
  have hsb : b.data.toList.length = b.size := rfl
  omega

end STFSpec.Conformance.Block.CalldataTokensCallerProofs
