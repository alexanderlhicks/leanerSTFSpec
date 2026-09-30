/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.Bytes

/-!
# Byte padding and padded-read regression guards

Library `EthConformance`: empty, equal, shorter, oversize and zero-length cases;
partly and wholly unavailable windows; huge natural offsets without huge allocation.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §4.
-/

open STFSpec.Base

-- Storage and implicit representation conversions are unavailable to callers.
#check_failure Bytes.raw
#check_failure Bytes.ofByteArrayRaw
#check_failure fun (b : Bytes) ↦ b.1
#check_failure (⟨ByteArray.empty⟩ : Bytes)
#check_failure ({ raw := ByteArray.empty } : Bytes)
#check_failure (inferInstance : Coe Bytes ByteArray)
#check_failure (inferInstance : Coe ByteArray Bytes)

#guard Bytes.ofList [] = Bytes.empty
#guard (Bytes.ofList [0, 128, 255]).size = 3
#guard (Bytes.ofList [0, 128, 255])[1]'(by decide) = 128
#guard (Bytes.ofList [0, 128, 255])[3]? = none
#guard Bytes.toList (Bytes.ofByteArray ([0, 128, 255] : List UInt8).toByteArray) =
  [0, 128, 255]
#guard (Bytes.ofList [0, 128, 255]).toByteArray.data.toList = [0, 128, 255]
#guard (Bytes.ofList [0, 128, 255]).toByteArray.size = 3
#guard Bytes.ofByteArray (Bytes.ofList [0, 128, 255]).toByteArray = Bytes.ofList [0, 128, 255]
#guard (Bytes.ofByteArray ByteArray.empty).toByteArray = ByteArray.empty
#guard Bytes.toList (Bytes.empty.push 128) = [128]
#guard Bytes.toList (Bytes.ofList [1, 2] ++ Bytes.ofList [3]) = [1, 2, 3]
#guard Bytes.toList ((Bytes.ofList [1, 2, 3]).extract 1 7) = [2, 3]
#guard Bytes.toList ((Bytes.ofList [1, 2, 3]).extract 7 9) = []
#guard Bytes.toList (Bytes.generate 0 UInt8.ofNat) = []
#guard Bytes.toList (Bytes.generate 5 (fun i ↦ UInt8.ofNat (i + 128))) =
  [128, 129, 130, 131, 132]
#guard Bytes.foldl (fun n b ↦ 256 * n + b.toNat) 0 (Bytes.ofList [1, 128, 255]) = 98559

private def sample : Bytes := Bytes.ofList [1, 128, 255]
private def empty : Bytes := Bytes.empty

#guard Bytes.toList empty = []
#guard Bytes.toList sample = [1, 128, 255]
#guard Bytes.ofList (Bytes.toList sample) = sample
#guard Bytes.leftPadZero empty 0 = empty
#guard Bytes.rightPadZero empty 0 = empty
#guard Bytes.toList (Bytes.leftPadZero empty 3) = [0, 0, 0]
#guard Bytes.toList (Bytes.rightPadZero empty 3) = [0, 0, 0]
#guard Bytes.leftPadZero sample 0 = sample
#guard Bytes.rightPadZero sample 0 = sample
#guard Bytes.leftPadZero sample 2 = sample
#guard Bytes.rightPadZero sample 2 = sample
#guard Bytes.leftPadZero sample 3 = sample
#guard Bytes.rightPadZero sample 3 = sample
#guard Bytes.toList (Bytes.leftPadZero sample 5) = [0, 0, 1, 128, 255]
#guard Bytes.toList (Bytes.rightPadZero sample 5) = [1, 128, 255, 0, 0]
#guard (Bytes.leftPadZero sample 5).size = 5
#guard (Bytes.rightPadZero sample 2).size = 3
#guard Bytes.leftPadZero (Bytes.leftPadZero sample 5) 5 = Bytes.leftPadZero sample 5
#guard Bytes.rightPadZero (Bytes.rightPadZero sample 5) 5 = Bytes.rightPadZero sample 5
#guard Bytes.leftPadZero (Bytes.ofList (List.replicate 21 7)) 20 =
  (Bytes.ofList (List.replicate 21 7))
#guard Bytes.rightPadZero (Bytes.ofList (List.replicate 21 7)) 20 =
  (Bytes.ofList (List.replicate 21 7))
#guard Bytes.extractPadded empty 0 0 = empty
#guard Bytes.toList (Bytes.extractPadded empty 0 3) = [0, 0, 0]
#guard Bytes.extractPadded sample 0 0 = empty
#guard Bytes.toList (Bytes.extractPadded sample 0 3) = [1, 128, 255]
#guard Bytes.toList (Bytes.extractPadded sample 1 2) = [128, 255]
#guard Bytes.toList (Bytes.extractPadded sample 1 4) = [128, 255, 0, 0]
#guard Bytes.toList (Bytes.extractPadded sample 2 3) = [255, 0, 0]
#guard Bytes.toList (Bytes.extractPadded sample 3 2) = [0, 0]
#guard Bytes.toList (Bytes.extractPadded sample 4 2) = [0, 0]
#guard Bytes.extractPadded sample (2 ^ 256 - 1) 0 = empty
#guard Bytes.toList (Bytes.extractPadded sample (2 ^ 256 - 1) 3) = [0, 0, 0]
#guard Bytes.extractPadded sample (2 ^ 4096) 0 = empty
#guard Bytes.toList (Bytes.extractPadded sample (2 ^ 4096) 3) = [0, 0, 0]
#guard (Bytes.extractPadded sample (2 ^ 4096) 2).size = 2
#guard Bytes.toList (Bytes.extractPadded sample 0 5) = [1, 128, 255, 0, 0]
#guard Bytes.toList (Bytes.extractPadded (Bytes.rightPadZero sample 5) 1 4) = [128, 255, 0, 0]
#guard (Bytes.toList (Bytes.leftPadZero sample 5))[0]? = some 0
#guard (Bytes.toList (Bytes.leftPadZero sample 5))[2]? = some 1
#guard (Bytes.toList (Bytes.leftPadZero sample 5))[5]? = none
#guard (Bytes.toList (Bytes.rightPadZero sample 5))[2]? = some 255
#guard (Bytes.toList (Bytes.rightPadZero sample 5))[3]? = some 0
#guard (Bytes.toList (Bytes.rightPadZero sample 5))[5]? = none

-- Native-index wrap sentinels: these offsets have low bits inside the source.
#guard Bytes.toList (Bytes.extractPadded sample (2 ^ 64) 3) = [0, 0, 0]
#guard Bytes.toList (Bytes.extractPadded sample (2 ^ 64 + 1) 3) = [0, 0, 0]
#guard Bytes.toList (Bytes.extractPadded sample (2 ^ 256) 3) = [0, 0, 0]
#guard Bytes.toList (Bytes.extractPadded sample (2 ^ 256 + 1) 3) = [0, 0, 0]
#guard Bytes.toList (Bytes.leftPadZero Bytes.empty 7) = List.replicate 7 0
#guard Bytes.toList (Bytes.rightPadZero sample 8) = [1, 128, 255, 0, 0, 0, 0, 0]
#guard (Bytes.extractPadded sample 1 (2 ^ 16)).size = 2 ^ 16

-- Public unpadded slicing clips before the native packed primitive too.
#guard (sample.extract (2 ^ 64) (2 ^ 64 + 3)) = Bytes.empty
#guard (sample.extract (2 ^ 64 + 1) (2 ^ 64 + 3)) = Bytes.empty
#guard (sample.extract (2 ^ 256 + 1) (2 ^ 256 + 3)) = Bytes.empty
#guard (sample.extract 1 (2 ^ 256)) = Bytes.ofList [128, 255]
#guard (sample.extract (2 ^ 256) 1) = Bytes.empty
