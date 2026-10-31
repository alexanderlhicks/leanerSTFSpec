/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block

/-!
# Private facade clients of complete deposit extraction laws

Library `EthConformance`. Clients use public equations and Base byte contracts;
no implementation or private worker is unfolded.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3/4/5/7.
-/

namespace STFSpec.Conformance.Block.DepositDataCallerProofs
open STFSpec.Block STFSpec.Base

private theorem complete_equation (data : ByteArray) :
    extractDepositData data =
      let bytes := Bytes.ofByteArray data
      let word := fun start ↦ Uint.ofBeBytes (bytes.extract start (start + 32))
      if data.size ≠ 576 then .error .length
      else if word 0 ≠ 160 then .error .pubkeyOffset
      else if word 32 ≠ 256 then .error .wcOffset
      else if word 64 ≠ 320 then .error .amountOffset
      else if word 96 ≠ 384 then .error .signatureOffset
      else if word 128 ≠ 512 then .error .indexOffset
      else if word 160 ≠ 48 then .error .pubkeySize
      else if word 256 ≠ 32 then .error .wcSize
      else if word 320 ≠ 8 then .error .amountSize
      else if word 384 ≠ 96 then .error .signatureSize
      else if word 512 ≠ 8 then .error .indexSize
      else .ok ((bytes.extract 192 240 ++ bytes.extract 288 320 ++
        bytes.extract 352 360 ++ bytes.extract 416 512 ++ bytes.extract 544 552).toByteArray)
    := extractDepositData_eq data


private theorem wrong_length (data : ByteArray) (h : data.size ≠ 576) :
    extractDepositData data = .error .length := by
  rw [extractDepositData_eq]
  simp [h]

private theorem first_offset (data : ByteArray) (length : data.size = 576)
    (bad : Uint.ofBeBytes ((Bytes.ofByteArray data).extract 0 32) ≠ 160) :
    extractDepositData data = .error .pubkeyOffset := by
  rw [extractDepositData_eq]
  simp [length, bad]

private theorem offsets_before_sizes (data : ByteArray) (length : data.size = 576)
    (h0 : Uint.ofBeBytes ((Bytes.ofByteArray data).extract 0 32) = 160)
    (h1 : Uint.ofBeBytes ((Bytes.ofByteArray data).extract 32 64) = 256)
    (h2 : Uint.ofBeBytes ((Bytes.ofByteArray data).extract 64 96) = 320)
    (h3 : Uint.ofBeBytes ((Bytes.ofByteArray data).extract 96 128) = 384)
    (bad : Uint.ofBeBytes ((Bytes.ofByteArray data).extract 128 160) ≠ 512) :
    extractDepositData data = .error .indexOffset := by
  rw [extractDepositData_eq]
  simp [length, h0, h1, h2, h3, bad]

private theorem successful_size (data result : ByteArray)
    (h : extractDepositData data = .ok result) : result.size = 192 :=
  size_extractDepositData data result h

end STFSpec.Conformance.Block.DepositDataCallerProofs
