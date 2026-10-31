/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.IntegerBytes

/-!
# Fixed deposit-event ABI extraction

Library `EthBlock`. Pinned EELS `src/ethereum/forks/amsterdam/requests.py:170–271`.
The eleven guards retain source order and full unsigned word values. Only the
five admitted byte windows are returned; padding and field contents are ignored.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§2.10/3/4/5/7.
-/

namespace STFSpec.Block
open STFSpec.Base

/-- The eleven distinct rejection sites of `extract_deposit_data` at pinned EELS
`src/ethereum/forks/amsterdam/requests.py:185–265`, in their checking order. -/
inductive DepositError where
  | length | pubkeyOffset | wcOffset | amountOffset | signatureOffset
  | indexOffset | pubkeySize | wcSize | amountSize | signatureSize | indexSize

/-- Strip fixed ABI framing on every finite byte array; pinned EELS
`src/ethereum/forks/amsterdam/requests.py:170–271`. After admitting all five
offsets, their size-word locations and data windows are fixed natural offsets.
Word windows have at most 32 bytes; assembled output buffers have at most
192 bytes. These are per-buffer bounds, not a total allocation-volume claim. -/
def extractDepositData (data : ByteArray) : Except DepositError ByteArray :=
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

/-- Complete ordered guard/result equation, including every error identity and
all successful output bytes. Words are unbounded big-endian reads of full
32-byte windows; no narrowing, padding check or content validation is implied.
Source intermediate allocations and host-resource failures remain separate. -/
theorem extractDepositData_eq (data : ByteArray) :
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
    := rfl

/-- Every successful extraction has exactly 192 bytes. This follows from the
admitted event length and five complete windows, independently of contents. -/
theorem size_extractDepositData (data result : ByteArray)
    (h : extractDepositData data = .ok result) : result.size = 192 := by
  rw [extractDepositData_eq] at h
  simp only [] at h
  by_cases h0 : data.size = 576
  case neg => simp [h0] at h
  simp [h0] at h
  by_cases h1 : Uint.ofBeBytes ((Bytes.ofByteArray data).extract 0 (0 + 32)) = 160
  case neg => simp [h1] at h
  simp [h1] at h
  by_cases h2 : Uint.ofBeBytes ((Bytes.ofByteArray data).extract 32 (32 + 32)) = 256
  case neg => simp [h2] at h
  simp [h2] at h
  by_cases h3 : Uint.ofBeBytes ((Bytes.ofByteArray data).extract 64 (64 + 32)) = 320
  case neg => simp [h3] at h
  simp [h3] at h
  by_cases h4 : Uint.ofBeBytes ((Bytes.ofByteArray data).extract 96 (96 + 32)) = 384
  case neg => simp [h4] at h
  simp [h4] at h
  by_cases h5 : Uint.ofBeBytes ((Bytes.ofByteArray data).extract 128 (128 + 32)) = 512
  case neg => simp [h5] at h
  simp [h5] at h
  by_cases h6 : Uint.ofBeBytes ((Bytes.ofByteArray data).extract 160 (160 + 32)) = 48
  case neg => simp [h6] at h
  simp [h6] at h
  by_cases h7 : Uint.ofBeBytes ((Bytes.ofByteArray data).extract 256 (256 + 32)) = 32
  case neg => simp [h7] at h
  simp [h7] at h
  by_cases h8 : Uint.ofBeBytes ((Bytes.ofByteArray data).extract 320 (320 + 32)) = 8
  case neg => simp [h8] at h
  simp [h8] at h
  by_cases h9 : Uint.ofBeBytes ((Bytes.ofByteArray data).extract 384 (384 + 32)) = 96
  case neg => simp [h9] at h
  simp [h9] at h
  by_cases h10 : Uint.ofBeBytes ((Bytes.ofByteArray data).extract 512 (512 + 32)) = 8
  case neg => simp [h10] at h
  simp [h10] at h
  cases h
  simp only [Bytes.size_toByteArray, Bytes.size_append, Bytes.size_extract,
    Bytes.size_ofByteArray]
  omega

end STFSpec.Block
