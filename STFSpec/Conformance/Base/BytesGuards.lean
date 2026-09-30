/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base

/-!
# Byte padding and padded-read regression guards

Library `EthConformance`: empty, equal, shorter, oversize and zero-length cases;
partly and wholly unavailable windows; huge natural offsets without huge allocation.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §4.
-/

open STFSpec.Base

private def sample : Bytes := ([1, 128, 255] : List UInt8).toByteArray
private def empty : Bytes := ByteArray.empty

#guard Bytes.toList empty = []
#guard Bytes.toList sample = [1, 128, 255]
#guard (Bytes.toList sample).toByteArray = sample
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
#guard Bytes.leftPadZero (List.replicate 21 (7 : UInt8)).toByteArray 20 =
  (List.replicate 21 (7 : UInt8)).toByteArray
#guard Bytes.rightPadZero (List.replicate 21 (7 : UInt8)).toByteArray 20 =
  (List.replicate 21 (7 : UInt8)).toByteArray
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
