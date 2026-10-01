/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Typed RLP leaf regression guards

Library `EthConformance`. Model leaves only, no raw wire decoder. Integer zero
width and generic union callbacks are model cases; matching dependency targets
are exercised by `rlp_typed_differential.py`. No instances on nested `RlpItem`.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–4.
-/

open STFSpec.Codec STFSpec.Codec.Rlp STFSpec.Base

/-- Observe diagnostics without introducing instances for nested model items. -/
private def error? {α : Type} : Except RlpError α → Option RlpError
  | .error e => some e
  | .ok _ => none

#guard (toNat (RlpItem.bytes (ByteArray.mk ([] : List UInt8).toArray))).toOption = some 0
#guard (toNat (RlpItem.bytes (ByteArray.mk ([1] : List UInt8).toArray))).toOption = some 1
#guard (toNat (RlpItem.bytes (ByteArray.mk ([127] : List UInt8).toArray))).toOption = some 127
#guard (toNat (RlpItem.bytes (ByteArray.mk ([128] : List UInt8).toArray))).toOption = some 128
#guard (toNat (RlpItem.bytes (ByteArray.mk ([1, 0] : List UInt8).toArray))).toOption = some 256
#guard error? (toNat (RlpItem.bytes (ByteArray.mk ([0] : List UInt8).toArray))) = some (.nonCanonical "integer leading zero")
#guard error? (toNat (RlpItem.bytes (ByteArray.mk ([0, 1] : List UInt8).toArray))) = some (.nonCanonical "integer leading zero")
#guard error? (toNat (RlpItem.bytes (ByteArray.mk ([0, 0, 1] : List UInt8).toArray))) = some (.nonCanonical "integer leading zero")
#guard (toNat (.list [])).toOption = none
#guard (toNatBounded 8 (RlpItem.bytes (ByteArray.mk ([] : List UInt8).toArray))).toOption = some 0
#guard (toNatBounded 8 (RlpItem.bytes (ByteArray.mk ([1] : List UInt8).toArray))).toOption = some 1
#guard (toNatBounded 8 (RlpItem.bytes (ByteArray.mk ([127] : List UInt8).toArray))).toOption = some 127
#guard (toNatBounded 8 (RlpItem.bytes (ByteArray.mk ([128] : List UInt8).toArray))).toOption = some 128
#guard (toNatBounded 8 (RlpItem.bytes (ByteArray.mk ([1, 0] : List UInt8).toArray))).toOption = some 256
#guard error? (toNatBounded 8 (RlpItem.bytes (ByteArray.mk ([0] : List UInt8).toArray))) = some (.nonCanonical "integer leading zero")
#guard error? (toNatBounded 8 (RlpItem.bytes (ByteArray.mk ([0, 1] : List UInt8).toArray))) = some (.nonCanonical "integer leading zero")
#guard error? (toNatBounded 8 (RlpItem.bytes (ByteArray.mk ([0, 0, 1] : List UInt8).toArray))) = some (.nonCanonical "integer leading zero")
#guard (toNatBounded 8 (.list [])).toOption = none
#guard (toNatBounded 32 (RlpItem.bytes (ByteArray.mk ([] : List UInt8).toArray))).toOption = some 0
#guard (toNatBounded 32 (RlpItem.bytes (ByteArray.mk ([1] : List UInt8).toArray))).toOption = some 1
#guard (toNatBounded 32 (RlpItem.bytes (ByteArray.mk ([127] : List UInt8).toArray))).toOption = some 127
#guard (toNatBounded 32 (RlpItem.bytes (ByteArray.mk ([128] : List UInt8).toArray))).toOption = some 128
#guard (toNatBounded 32 (RlpItem.bytes (ByteArray.mk ([1, 0] : List UInt8).toArray))).toOption = some 256
#guard error? (toNatBounded 32 (RlpItem.bytes (ByteArray.mk ([0] : List UInt8).toArray))) = some (.nonCanonical "integer leading zero")
#guard error? (toNatBounded 32 (RlpItem.bytes (ByteArray.mk ([0, 1] : List UInt8).toArray))) = some (.nonCanonical "integer leading zero")
#guard error? (toNatBounded 32 (RlpItem.bytes (ByteArray.mk ([0, 0, 1] : List UInt8).toArray))) = some (.nonCanonical "integer leading zero")
#guard (toNatBounded 32 (.list [])).toOption = none
#guard error? (toNatBounded 0 (RlpItem.bytes (ByteArray.mk ([0] : List UInt8).toArray))) = some (.nonCanonical "integer leading zero")
#guard error? (toNatBounded 0 (RlpItem.bytes (ByteArray.mk ([1] : List UInt8).toArray))) = some (.shape "integer width")
#guard error? (toNatBounded 8 (RlpItem.bytes (ByteArray.mk ([0, 0, 0, 0, 0, 0, 0, 0, 0] : List UInt8).toArray))) = some (.nonCanonical "integer leading zero")
#guard error? (toNatBounded 8 (RlpItem.bytes (ByteArray.mk ([1, 0, 0, 0, 0, 0, 0, 0, 0] : List UInt8).toArray))) = some (.shape "integer width")
#guard error? (toNatBounded 32 (RlpItem.bytes (ByteArray.mk ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List UInt8).toArray))) = some (.nonCanonical "integer leading zero")
#guard error? (toNatBounded 32 (RlpItem.bytes (ByteArray.mk ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List UInt8).toArray))) = some (.shape "integer width")
#guard (toNatBounded 0 (RlpItem.bytes (ByteArray.mk ([] : List UInt8).toArray))).toOption = some 0
#guard (toNatBounded 8 (RlpItem.bytes (ByteArray.mk ([255, 255, 255, 255, 255, 255, 255, 255] : List UInt8).toArray))).toOption = some 18446744073709551615
#guard (toBool (RlpItem.bytes (ByteArray.mk ([] : List UInt8).toArray))).toOption = some false
#guard (toBool (RlpItem.bytes (ByteArray.mk ([1] : List UInt8).toArray))).toOption = some true
#guard (toBool (RlpItem.bytes (ByteArray.mk ([0] : List UInt8).toArray))).toOption = none
#guard (toBool (RlpItem.bytes (ByteArray.mk ([2] : List UInt8).toArray))).toOption = none
#guard (toBool (RlpItem.bytes (ByteArray.mk ([1, 1] : List UInt8).toArray))).toOption = none
#guard (toBool (RlpItem.bytes (ByteArray.mk ([255] : List UInt8).toArray))).toOption = none
#guard (toBool (.list [])).toOption = none
#guard ((toFixed 0 (RlpItem.bytes (ByteArray.mk ([] : List UInt8).toArray))).map (fun v => v.toBytes.toByteArray.data.toList)).toOption = some []
#guard ((toFixed 0 (RlpItem.bytes (ByteArray.mk ([17] : List UInt8).toArray))).map (fun v => v.toBytes.toByteArray.data.toList)).toOption = none
#guard (toFixed 0 (.list [])).toOption.isSome = false
#guard ((toFixed 20 (RlpItem.bytes (ByteArray.mk ([] : List UInt8).toArray))).map (fun v => v.toBytes.toByteArray.data.toList)).toOption = none
#guard ((toFixed 20 (RlpItem.bytes (ByteArray.mk ([17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17] : List UInt8).toArray))).map (fun v => v.toBytes.toByteArray.data.toList)).toOption = none
#guard ((toFixed 20 (RlpItem.bytes (ByteArray.mk ([17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17] : List UInt8).toArray))).map (fun v => v.toBytes.toByteArray.data.toList)).toOption = some [17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17]
#guard ((toFixed 20 (RlpItem.bytes (ByteArray.mk ([17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17] : List UInt8).toArray))).map (fun v => v.toBytes.toByteArray.data.toList)).toOption = none
#guard (toFixed 20 (.list [])).toOption.isSome = false
#guard ((toFixed 32 (RlpItem.bytes (ByteArray.mk ([] : List UInt8).toArray))).map (fun v => v.toBytes.toByteArray.data.toList)).toOption = none
#guard ((toFixed 32 (RlpItem.bytes (ByteArray.mk ([17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17] : List UInt8).toArray))).map (fun v => v.toBytes.toByteArray.data.toList)).toOption = none
#guard ((toFixed 32 (RlpItem.bytes (ByteArray.mk ([17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17] : List UInt8).toArray))).map (fun v => v.toBytes.toByteArray.data.toList)).toOption = some [17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17]
#guard ((toFixed 32 (RlpItem.bytes (ByteArray.mk ([17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17] : List UInt8).toArray))).map (fun v => v.toBytes.toByteArray.data.toList)).toOption = none
#guard (toFixed 32 (.list [])).toOption.isSome = false
#guard ((toBytes (RlpItem.bytes (ByteArray.mk ([0, 1, 255] : List UInt8).toArray))).map (fun b => b.data.toList)).toOption = some [0,1,255]
#guard (toBytes (.list [])).toOption = none
#guard ((toList (.list [.bytes ByteArray.empty, .list []])).map List.length).toOption = some 2
#guard (toList (RlpItem.bytes (ByteArray.mk ([] : List UInt8).toArray))).toOption.isSome = false
#guard ((toFields 0 (.list [])).map (fun v => v.toList.length)).toOption = some 0
#guard ((toFields 0 (.list [.bytes ByteArray.empty])).map (fun v => v.toList.length)).toOption = none
#guard ((toFields 0 (.list [.bytes ByteArray.empty, .bytes ByteArray.empty])).map (fun v => v.toList.length)).toOption = none
#guard ((toFields 1 (.list [])).map (fun v => v.toList.length)).toOption = none
#guard ((toFields 1 (.list [.bytes ByteArray.empty])).map (fun v => v.toList.length)).toOption = some 1
#guard ((toFields 1 (.list [.bytes ByteArray.empty, .bytes ByteArray.empty])).map (fun v => v.toList.length)).toOption = none
#guard ((toFields 2 (.list [])).map (fun v => v.toList.length)).toOption = none
#guard ((toFields 2 (.list [.bytes ByteArray.empty])).map (fun v => v.toList.length)).toOption = none
#guard ((toFields 2 (.list [.bytes ByteArray.empty, .bytes ByteArray.empty])).map (fun v => v.toList.length)).toOption = some 2
#guard (toFields 0 (.bytes ByteArray.empty)).toOption.isSome = false
#guard error? (union2 (fun _ => .ok (7 : Nat)) (fun _ => .ok 7) (.list [])) = some (.shape "multiple union variants")
#guard error? (union2 (fun _ => .ok (7 : Nat)) (fun _ => .ok 8) (.list [])) = some (.shape "multiple union variants")
#guard error? (union2 (fun _ => .error (.shape "a")) (fun _ => .error (.shape "b")) (.list []) : Except RlpError Nat) = some (.shape "no union variant")
#guard (union2 (fun _ => .error (.shape "a")) (fun _ => .ok (8 : Nat)) (.list [])).toOption = some 8
#guard (union2 (fun _ => .ok (7 : Nat)) (fun _ => .error (.shape "b")) (.list [])).toOption = some 7
