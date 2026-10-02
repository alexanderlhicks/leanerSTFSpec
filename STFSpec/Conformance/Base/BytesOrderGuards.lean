/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.BytesOrder
import Std.Data.TreeMap

/-!
# Byte-content ordering regression guards

Library `EthConformance`. Proper prefixes, empty values, significant zeros,
unsigned boundaries and 4096-byte shared prefixes exercise evaluated ordering.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §3/§4.
-/

namespace STFSpec.Conformance.Base.BytesOrderGuards

open STFSpec.Base

#check_failure Bytes.byteAt
#check_failure Bytes.compareScan
#check_failure (inferInstance : Ord ByteArray)
#check_failure (inferInstance : LT Bytes)
#check_failure (inferInstance : LE Bytes)
#check_failure (inferInstance : Hashable Bytes)

#guard compare Bytes.empty Bytes.empty = .eq
#guard compare Bytes.empty (Bytes.ofList [0]) = .lt
#guard compare (Bytes.ofList [0]) Bytes.empty = .gt
#guard compare (Bytes.ofList [0]) (Bytes.ofList [0, 0]) = .lt
#guard compare (Bytes.ofList [0, 0]) (Bytes.ofList [0]) = .gt
#guard compare (Bytes.ofList [0, 1]) (Bytes.ofList [1]) = .lt
#guard compare (Bytes.ofList [255]) (Bytes.ofList [0, 0]) = .gt
#guard compare (Bytes.ofList [1, 255]) (Bytes.ofList [2]) = .lt
#guard compare (Bytes.ofList [127]) (Bytes.ofList [128]) = .lt
#guard compare (Bytes.ofList [128]) (Bytes.ofList [255]) = .lt
#guard compare (Bytes.ofList [255, 0]) (Bytes.ofList [255, 1]) = .lt
-- RLP ordinal zero is 0x80; ordinal one is 0x01. Byte order is not ordinal order.
#guard compare (Bytes.ofList [128]) (Bytes.ofList [1]) = .gt

/-- Every singleton pair exercises unsigned order, including the upper half. -/
private def allUnsignedPairs : Bool := (List.range 256).all fun i ↦
  (List.range 256).all fun j ↦
    compare (Bytes.ofList [UInt8.ofNat i]) (Bytes.ofList [UInt8.ofNat j]) == compare i j

#guard allUnsignedPairs
#guard compare (Bytes.ofList (List.replicate 4096 255 ++ [0]))
  (Bytes.ofList (List.replicate 4096 255 ++ [1])) = .lt
#guard compare (Bytes.ofList (List.replicate 4096 0))
  (Bytes.ofList (List.replicate 4096 0 ++ [0])) = .lt
#guard compare (Bytes.ofList (List.replicate 4096 255))
  (Bytes.ofList (List.replicate 4096 255)) = .eq
#guard compare (Bytes.ofList (0 :: List.replicate 4096 255))
  (Bytes.ofList (1 :: List.replicate 4096 255)) = .lt
#guard (Bytes.ofList (List.replicate 4096 0 ++ [128, 255])).toByteArray.toList =
  List.replicate 4096 0 ++ [128, 255]
#guard (Bytes.ofList [0, 0, 128, 255]).toByteArray.toList = [0, 0, 128, 255]
#guard Bytes.empty.toByteArray.toList = []
#guard (((∅ : Std.TreeMap Bytes Nat).insert (Bytes.ofList [0]) 1).insert
  (Bytes.ofList [0]) 2)[Bytes.ofList [0]]? = some 2
#guard (((∅ : Std.TreeMap Bytes Nat).insert (Bytes.ofList [0]) 1).insert
  (Bytes.ofList [0, 0]) 2)[Bytes.ofList [0]]? = some 1

end STFSpec.Conformance.Base.BytesOrderGuards
