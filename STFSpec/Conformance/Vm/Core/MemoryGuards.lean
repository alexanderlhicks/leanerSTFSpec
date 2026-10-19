/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Vm.Core
import Lean
/-!
# Complete Memory observations
Library `EthConformance`. Public construction and complete actual memories, immutable
reads and retained snapshots for thirty-three frozen controls.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/7.
-/
open STFSpec.Vm.Core STFSpec.Base Lean
-- These listed private names and uninstalled instances are unavailable publicly.
-- The transparent structure is not an opacity or constructor-elimination guarantee.
#check_failure Memory.mk
#check_failure Memory.raw
#check_failure Memory.aligned
#check_failure Memory.ofBytes
#check_failure Memory.ext
#check_failure Memory.overwrite
#check_failure (⟨ByteArray.empty, by decide⟩ : Memory)
#check_failure (inferInstance : BEq Memory)
#check_failure (inferInstance : DecidableEq Memory)
private def byteHex (b : UInt8) : String :=
  let digit := fun n ↦ if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  String.ofList [digit (b.toNat / 16), digit (b.toNat % 16)]
private def fullBytes (size : Nat) (xs : List UInt8) : Json :=
  Json.mkObj [("size", toJson size), ("hex", toJson (String.join (xs.map byteHex)))]
private def memoryJson (m : Memory) : Json := fullBytes m.size m.toBytes
private def bytesJson (b : Bytes) : Json := fullBytes b.size b.toList
-- 01-empty
private def m01 : Memory := Memory.empty
-- 02-empty-expand-zero
private def m02 : Memory := m01.expand 0 (by decide)
-- 03-expand32
private def m03 : Memory := m01.expand 32 (by decide)
-- 04-expand-zero32
private def m04 : Memory := m03.expand 0 (by decide)
-- 05-expand32-again
private def m05 : Memory := m03.expand 32 (by decide)
-- 06-full-write
private def v06 : Bytes := Bytes.ofList [0 , 1 , 2 , 3 , 4 , 5 , 6 , 7 , 8 , 9 , 10 , 11 , 12 , 13
  , 14 , 15 , 16 , 17 , 18 , 19 , 20 , 21 , 22 , 23 , 24 , 25 , 26 , 27 , 28 , 29 , 30 , 31 , 32 ,
  33 , 34 , 35 , 36 , 37 , 38 , 39 , 40 , 41 , 42 , 43 , 44 , 45 , 46 , 47 , 48 , 49 , 50 , 51 , 52
  , 53 , 54 , 55 , 56 , 57 , 58 , 59 , 60 , 61 , 62 , 63]
private def m06 : Memory := m05.write 0 v06 (by right; decide)
-- 07-high-interior-zero-full-write
private def v07 : Bytes := Bytes.ofList [0 , 128 , 255 , 1 , 0 , 127 , 85 , 170 , 0 , 128 , 255 , 1
  , 0 , 127 , 85 , 170 , 0 , 128 , 255 , 1 , 0 , 127 , 85 , 170 , 0 , 128 , 255 , 1 , 0 , 127 , 85
  , 170]
private def m07 : Memory := m03.write 0 v07 (by right; decide)
-- 08-read-all
private def m08 : Memory := m06
private def r08 : Bytes := m08.readBytes 0 64 (by right; decide)
-- 09-save-cross-window
private def m09 : Memory := m06
private def r09 : Bytes := m09.readBytes 28 8 (by right; decide)
-- 10-cross-word-write
private def v10 : Bytes := Bytes.ofList [254, 0, 128, 255, 1, 0, 127, 85]
private def m10 : Memory := m06.write 28 v10 (by right; decide)
-- 11-cross-word-read
private def m11 : Memory := m10
private def r11 : Bytes := m11.readBytes 28 8 (by right; decide)
-- 12-whole-prefix
private def m12 : Memory := m10
private def r12 : Bytes := m12.readBytes 0 28 (by right; decide)
-- 13-whole-suffix
private def m13 : Memory := m10
private def r13 : Bytes := m13.readBytes 36 28 (by right; decide)
-- 14-left-overlap
private def v14 : Bytes := r09
private def m14 : Memory := m06.write 26 v14 (by right; decide)
-- 15-right-overlap
private def v15 : Bytes := r09
private def m15 : Memory := m06.write 30 v15 (by right; decide)
-- 16-self-copy
private def v16 : Bytes := r09
private def m16 : Memory := m06.write 28 v16 (by right; decide)
-- 17-retained-original-and-read
private def m17 : Memory := m10
-- 18-expand-written32
private def m18 : Memory := m10.expand 32 (by decide)
-- 19-exact-end-write
private def v19 : Bytes := Bytes.ofList [0, 128, 255, 0]
private def m19 : Memory := m06.write 60 v19 (by right; decide)
-- 20-exact-end-read
private def m20 : Memory := m19
private def r20 : Bytes := m20.readBytes 60 4 (by right; decide)
-- 21-empty-end-read
private def m21 : Memory := m06
private def r21 : Bytes := m21.readBytes 64 0 (Or.inl rfl)
-- 22-empty-read-inside-write
private def m22 : Memory := m10
private def r22 : Bytes := m22.readBytes 30 0 (Or.inl rfl)
-- 23-empty-write-inside-read
private def v23 : Bytes := Bytes.ofList []
private def m23 : Memory := m06.write 30 v23 (Or.inl (by decide))
private def r23 : Bytes := m23.readBytes 28 8 (by right; decide)
-- 24-adjacent-prefix
private def m24 : Memory := m10
private def r24 : Bytes := m24.readBytes 28 0 (Or.inl rfl)
-- 25-adjacent-left
private def m25 : Memory := m10
private def r25 : Bytes := m25.readBytes 24 4 (by right; decide)
-- 26-adjacent-right
private def m26 : Memory := m10
private def r26 : Bytes := m26.readBytes 36 4 (by right; decide)
-- 27-empty-read-2p64
private def m27 : Memory := m06
private def r27 : Bytes := m27.readBytes 18446744073709551616 0 (Or.inl rfl)
-- 28-empty-write-2p64
private def v28 : Bytes := Bytes.ofList []
private def m28 : Memory := m06.write 18446744073709551616 v28 (Or.inl (by decide))
-- 29-empty-read-u256max
private def m29 : Memory := m06
private def r29 : Bytes := m29.readBytes
  115792089237316195423570985008687907853269984665640564039457584007913129639935 0 (Or.inl rfl)
-- 30-empty-write-u256max
private def v30 : Bytes := Bytes.ofList []
private def m30 : Memory := m06.write
  115792089237316195423570985008687907853269984665640564039457584007913129639935 v30 (Or.inl (by
  decide))
-- 31-lean-only-empty-read-2p4096
private def m31 : Memory := m06
private def r31 : Bytes := m31.readBytes (2^4096) 0 (Or.inl rfl)
-- 32-lean-only-empty-write-2p4096
private def v32 : Bytes := Bytes.ofList []
private def m32 : Memory := m06.write (2^4096) v32 (Or.inl (by decide))
-- 33-both-empty
private def v33 : Bytes := Bytes.ofList []
private def m33 : Memory := m01.write 18446744073709551616 v33 (Or.inl (by decide))
private def r33 : Bytes := m33.readBytes 0 0 (Or.inl rfl)
private def observations : List Json := [
  Json.mkObj [( "id" , toJson "01-empty" ) , ( "op" , toJson "observe" ) , ( "before" , memoryJson
    Memory.empty) , ( "input" , Json.mkObj []) , ( "after" , memoryJson m01) , ( "reads" ,
    Json.mkObj []) , ( "savedMemories" , Json.mkObj []) , ( "savedBytes" , Json.mkObj []) , (
    "returnClass" , toJson "observation" )] ,
  Json.mkObj [( "id" , toJson "02-empty-expand-zero" ) , ( "op" , toJson "expand" ) , ( "before" ,
    memoryJson m01) , ( "input" , Json.mkObj [( "increment" , toJson (toString (0 : Nat)))]) , (
    "after" , memoryJson m02) , ( "reads" , Json.mkObj []) , ( "savedMemories" , Json.mkObj [(
    "old" , memoryJson m01)]) , ( "savedBytes" , Json.mkObj []) , ( "returnClass" , toJson
    "NoneType" )] ,
  Json.mkObj [( "id" , toJson "03-expand32" ) , ( "op" , toJson "expand" ) , ( "before" ,
    memoryJson m01) , ( "input" , Json.mkObj [( "increment" , toJson (toString (32 : Nat)))]) , (
    "after" , memoryJson m03) , ( "reads" , Json.mkObj []) , ( "savedMemories" , Json.mkObj [(
    "old" , memoryJson m01)]) , ( "savedBytes" , Json.mkObj []) , ( "returnClass" , toJson
    "NoneType" )] ,
  Json.mkObj [( "id" , toJson "04-expand-zero32" ) , ( "op" , toJson "expand" ) , ( "before" ,
    memoryJson m03) , ( "input" , Json.mkObj [( "increment" , toJson (toString (0 : Nat)))]) , (
    "after" , memoryJson m04) , ( "reads" , Json.mkObj []) , ( "savedMemories" , Json.mkObj [(
    "old" , memoryJson m03)]) , ( "savedBytes" , Json.mkObj []) , ( "returnClass" , toJson
    "NoneType" )] ,
  Json.mkObj [( "id" , toJson "05-expand32-again" ) , ( "op" , toJson "expand" ) , ( "before" ,
    memoryJson m03) , ( "input" , Json.mkObj [( "increment" , toJson (toString (32 : Nat)))]) , (
    "after" , memoryJson m05) , ( "reads" , Json.mkObj []) , ( "savedMemories" , Json.mkObj [(
    "old" , memoryJson m03)]) , ( "savedBytes" , Json.mkObj []) , ( "returnClass" , toJson
    "NoneType" )] ,
  Json.mkObj [( "id" , toJson "06-full-write" ) , ( "op" , toJson "write" ) , ( "before" ,
    memoryJson m05) , ( "input" , Json.mkObj [( "start" , toJson (toString (0 : Nat))) , (
    "payload" , bytesJson v06)]) , ( "after" , memoryJson m06) , ( "reads" , Json.mkObj []) , (
    "savedMemories" , Json.mkObj [( "old" , memoryJson m05)]) , ( "savedBytes" , Json.mkObj []) , (
    "returnClass" , toJson "NoneType" )] ,
  Json.mkObj [( "id" , toJson "07-high-interior-zero-full-write" ) , ( "op" , toJson "write" ) , (
    "before" , memoryJson m03) , ( "input" , Json.mkObj [( "start" , toJson (toString (0 : Nat))) ,
    ( "payload" , bytesJson v07)]) , ( "after" , memoryJson m07) , ( "reads" , Json.mkObj []) , (
    "savedMemories" , Json.mkObj [( "old" , memoryJson m03)]) , ( "savedBytes" , Json.mkObj []) , (
    "returnClass" , toJson "NoneType" )] ,
  Json.mkObj [( "id" , toJson "08-read-all" ) , ( "op" , toJson "read" ) , ( "before" , memoryJson
    m06) , ( "input" , Json.mkObj [( "start" , toJson (toString (0 : Nat))) , ( "length" , toJson
    (toString (64 : Nat)))]) , ( "after" , memoryJson m08) , ( "reads" , Json.mkObj [( "result" ,
    bytesJson r08)]) , ( "savedMemories" , Json.mkObj []) , ( "savedBytes" , Json.mkObj []) , (
    "returnClass" , toJson "bytes" )] ,
  Json.mkObj [( "id" , toJson "09-save-cross-window" ) , ( "op" , toJson "read" ) , ( "before" ,
    memoryJson m06) , ( "input" , Json.mkObj [( "start" , toJson (toString (28 : Nat))) , (
    "length" , toJson (toString (8 : Nat)))]) , ( "after" , memoryJson m09) , ( "reads" ,
    Json.mkObj [( "result" , bytesJson r09)]) , ( "savedMemories" , Json.mkObj [( "base" ,
    memoryJson m06)]) , ( "savedBytes" , Json.mkObj [( "window" , bytesJson r09)]) , (
    "returnClass" , toJson "bytes" )] ,
  Json.mkObj [( "id" , toJson "10-cross-word-write" ) , ( "op" , toJson "write" ) , ( "before" ,
    memoryJson m06) , ( "input" , Json.mkObj [( "start" , toJson (toString (28 : Nat))) , (
    "payload" , bytesJson v10)]) , ( "after" , memoryJson m10) , ( "reads" , Json.mkObj []) , (
    "savedMemories" , Json.mkObj [( "base" , memoryJson m06)]) , ( "savedBytes" , Json.mkObj [(
    "window" , bytesJson r09)]) , ( "returnClass" , toJson "NoneType" )] ,
  Json.mkObj [( "id" , toJson "11-cross-word-read" ) , ( "op" , toJson "read" ) , ( "before" ,
    memoryJson m10) , ( "input" , Json.mkObj [( "start" , toJson (toString (28 : Nat))) , (
    "length" , toJson (toString (8 : Nat)))]) , ( "after" , memoryJson m11) , ( "reads" ,
    Json.mkObj [( "result" , bytesJson r11)]) , ( "savedMemories" , Json.mkObj [( "base" ,
    memoryJson m06)]) , ( "savedBytes" , Json.mkObj [( "window" , bytesJson r09)]) , (
    "returnClass" , toJson "bytes" )] ,
  Json.mkObj [( "id" , toJson "12-whole-prefix" ) , ( "op" , toJson "read" ) , ( "before" ,
    memoryJson m10) , ( "input" , Json.mkObj [( "start" , toJson (toString (0 : Nat))) , ( "length"
    , toJson (toString (28 : Nat)))]) , ( "after" , memoryJson m12) , ( "reads" , Json.mkObj [(
    "result" , bytesJson r12)]) , ( "savedMemories" , Json.mkObj [( "base" , memoryJson m06)]) , (
    "savedBytes" , Json.mkObj [( "window" , bytesJson r09)]) , ( "returnClass" , toJson "bytes" )]
    ,
  Json.mkObj [( "id" , toJson "13-whole-suffix" ) , ( "op" , toJson "read" ) , ( "before" ,
    memoryJson m10) , ( "input" , Json.mkObj [( "start" , toJson (toString (36 : Nat))) , (
    "length" , toJson (toString (28 : Nat)))]) , ( "after" , memoryJson m13) , ( "reads" ,
    Json.mkObj [( "result" , bytesJson r13)]) , ( "savedMemories" , Json.mkObj [( "base" ,
    memoryJson m06)]) , ( "savedBytes" , Json.mkObj [( "window" , bytesJson r09)]) , (
    "returnClass" , toJson "bytes" )] ,
  Json.mkObj [( "id" , toJson "14-left-overlap" ) , ( "op" , toJson "write" ) , ( "before" ,
    memoryJson m06) , ( "input" , Json.mkObj [( "start" , toJson (toString (26 : Nat))) , (
    "payload" , bytesJson v14)]) , ( "after" , memoryJson m14) , ( "reads" , Json.mkObj []) , (
    "savedMemories" , Json.mkObj [( "base" , memoryJson m06)]) , ( "savedBytes" , Json.mkObj [(
    "window" , bytesJson r09)]) , ( "returnClass" , toJson "NoneType" )] ,
  Json.mkObj [( "id" , toJson "15-right-overlap" ) , ( "op" , toJson "write" ) , ( "before" ,
    memoryJson m06) , ( "input" , Json.mkObj [( "start" , toJson (toString (30 : Nat))) , (
    "payload" , bytesJson v15)]) , ( "after" , memoryJson m15) , ( "reads" , Json.mkObj []) , (
    "savedMemories" , Json.mkObj [( "base" , memoryJson m06)]) , ( "savedBytes" , Json.mkObj [(
    "window" , bytesJson r09)]) , ( "returnClass" , toJson "NoneType" )] ,
  Json.mkObj [( "id" , toJson "16-self-copy" ) , ( "op" , toJson "write" ) , ( "before" ,
    memoryJson m06) , ( "input" , Json.mkObj [( "start" , toJson (toString (28 : Nat))) , (
    "payload" , bytesJson v16)]) , ( "after" , memoryJson m16) , ( "reads" , Json.mkObj []) , (
    "savedMemories" , Json.mkObj [( "base" , memoryJson m06)]) , ( "savedBytes" , Json.mkObj [(
    "window" , bytesJson r09)]) , ( "returnClass" , toJson "NoneType" )] ,
  Json.mkObj [( "id" , toJson "17-retained-original-and-read" ) , ( "op" , toJson "observe" ) , (
    "before" , memoryJson m10) , ( "input" , Json.mkObj []) , ( "after" , memoryJson m17) , (
    "reads" , Json.mkObj []) , ( "savedMemories" , Json.mkObj [( "base" , memoryJson m06)]) , (
    "savedBytes" , Json.mkObj [( "window" , bytesJson r09)]) , ( "returnClass" , toJson
    "observation" )] ,
  Json.mkObj [( "id" , toJson "18-expand-written32" ) , ( "op" , toJson "expand" ) , ( "before" ,
    memoryJson m10) , ( "input" , Json.mkObj [( "increment" , toJson (toString (32 : Nat)))]) , (
    "after" , memoryJson m18) , ( "reads" , Json.mkObj []) , ( "savedMemories" , Json.mkObj [(
    "old" , memoryJson m10) , ( "base" , memoryJson m06)]) , ( "savedBytes" , Json.mkObj [(
    "window" , bytesJson r09)]) , ( "returnClass" , toJson "NoneType" )] ,
  Json.mkObj [( "id" , toJson "19-exact-end-write" ) , ( "op" , toJson "write" ) , ( "before" ,
    memoryJson m06) , ( "input" , Json.mkObj [( "start" , toJson (toString (60 : Nat))) , (
    "payload" , bytesJson v19)]) , ( "after" , memoryJson m19) , ( "reads" , Json.mkObj []) , (
    "savedMemories" , Json.mkObj [( "base" , memoryJson m06)]) , ( "savedBytes" , Json.mkObj [(
    "window" , bytesJson r09)]) , ( "returnClass" , toJson "NoneType" )] ,
  Json.mkObj [( "id" , toJson "20-exact-end-read" ) , ( "op" , toJson "read" ) , ( "before" ,
    memoryJson m19) , ( "input" , Json.mkObj [( "start" , toJson (toString (60 : Nat))) , (
    "length" , toJson (toString (4 : Nat)))]) , ( "after" , memoryJson m20) , ( "reads" ,
    Json.mkObj [( "result" , bytesJson r20)]) , ( "savedMemories" , Json.mkObj [( "base" ,
    memoryJson m06)]) , ( "savedBytes" , Json.mkObj [( "window" , bytesJson r09)]) , (
    "returnClass" , toJson "bytes" )] ,
  Json.mkObj [( "id" , toJson "21-empty-end-read" ) , ( "op" , toJson "read" ) , ( "before" ,
    memoryJson m06) , ( "input" , Json.mkObj [( "start" , toJson (toString (64 : Nat))) , (
    "length" , toJson (toString (0 : Nat)))]) , ( "after" , memoryJson m21) , ( "reads" ,
    Json.mkObj [( "result" , bytesJson r21)]) , ( "savedMemories" , Json.mkObj []) , ( "savedBytes"
    , Json.mkObj []) , ( "returnClass" , toJson "bytes" )] ,
  Json.mkObj [( "id" , toJson "22-empty-read-inside-write" ) , ( "op" , toJson "read" ) , (
    "before" , memoryJson m10) , ( "input" , Json.mkObj [( "start" , toJson (toString (30 : Nat)))
    , ( "length" , toJson (toString (0 : Nat)))]) , ( "after" , memoryJson m22) , ( "reads" ,
    Json.mkObj [( "result" , bytesJson r22)]) , ( "savedMemories" , Json.mkObj [( "base" ,
    memoryJson m06)]) , ( "savedBytes" , Json.mkObj [( "window" , bytesJson r09)]) , (
    "returnClass" , toJson "bytes" )] ,
  Json.mkObj [( "id" , toJson "23-empty-write-inside-read" ) , ( "op" , toJson "write" ) , (
    "before" , memoryJson m06) , ( "input" , Json.mkObj [( "start" , toJson (toString (30 : Nat)))
    , ( "payload" , bytesJson v23)]) , ( "after" , memoryJson m23) , ( "reads" , Json.mkObj [(
    "preserved-window" , bytesJson r23)]) , ( "savedMemories" , Json.mkObj [( "base" , memoryJson
    m06)]) , ( "savedBytes" , Json.mkObj [( "window" , bytesJson r09)]) , ( "returnClass" , toJson
    "NoneType" )] ,
  Json.mkObj [( "id" , toJson "24-adjacent-prefix" ) , ( "op" , toJson "read" ) , ( "before" ,
    memoryJson m10) , ( "input" , Json.mkObj [( "start" , toJson (toString (28 : Nat))) , (
    "length" , toJson (toString (0 : Nat)))]) , ( "after" , memoryJson m24) , ( "reads" ,
    Json.mkObj [( "result" , bytesJson r24)]) , ( "savedMemories" , Json.mkObj []) , ( "savedBytes"
    , Json.mkObj []) , ( "returnClass" , toJson "bytes" )] ,
  Json.mkObj [( "id" , toJson "25-adjacent-left" ) , ( "op" , toJson "read" ) , ( "before" ,
    memoryJson m10) , ( "input" , Json.mkObj [( "start" , toJson (toString (24 : Nat))) , (
    "length" , toJson (toString (4 : Nat)))]) , ( "after" , memoryJson m25) , ( "reads" ,
    Json.mkObj [( "result" , bytesJson r25)]) , ( "savedMemories" , Json.mkObj []) , ( "savedBytes"
    , Json.mkObj []) , ( "returnClass" , toJson "bytes" )] ,
  Json.mkObj [( "id" , toJson "26-adjacent-right" ) , ( "op" , toJson "read" ) , ( "before" ,
    memoryJson m10) , ( "input" , Json.mkObj [( "start" , toJson (toString (36 : Nat))) , (
    "length" , toJson (toString (4 : Nat)))]) , ( "after" , memoryJson m26) , ( "reads" ,
    Json.mkObj [( "result" , bytesJson r26)]) , ( "savedMemories" , Json.mkObj []) , ( "savedBytes"
    , Json.mkObj []) , ( "returnClass" , toJson "bytes" )] ,
  Json.mkObj [( "id" , toJson "27-empty-read-2p64" ) , ( "op" , toJson "read" ) , ( "before" ,
    memoryJson m06) , ( "input" , Json.mkObj [( "start" , toJson (toString (18446744073709551616 :
    Nat))) , ( "length" , toJson (toString (0 : Nat)))]) , ( "after" , memoryJson m27) , ( "reads"
    , Json.mkObj [( "result" , bytesJson r27)]) , ( "savedMemories" , Json.mkObj [( "base" ,
    memoryJson m06)]) , ( "savedBytes" , Json.mkObj [( "window" , bytesJson r09)]) , (
    "returnClass" , toJson "bytes" )] ,
  Json.mkObj [( "id" , toJson "28-empty-write-2p64" ) , ( "op" , toJson "write" ) , ( "before" ,
    memoryJson m06) , ( "input" , Json.mkObj [( "start" , toJson (toString (18446744073709551616 :
    Nat))) , ( "payload" , bytesJson v28)]) , ( "after" , memoryJson m28) , ( "reads" , Json.mkObj
    []) , ( "savedMemories" , Json.mkObj [( "base" , memoryJson m06)]) , ( "savedBytes" ,
    Json.mkObj [( "window" , bytesJson r09)]) , ( "returnClass" , toJson "NoneType" )] ,
  Json.mkObj [( "id" , toJson "29-empty-read-u256max" ) , ( "op" , toJson "read" ) , ( "before" ,
    memoryJson m06) , ( "input" , Json.mkObj [( "start" , toJson (toString
    (115792089237316195423570985008687907853269984665640564039457584007913129639935 : Nat))) , (
    "length" , toJson (toString (0 : Nat)))]) , ( "after" , memoryJson m29) , ( "reads" ,
    Json.mkObj [( "result" , bytesJson r29)]) , ( "savedMemories" , Json.mkObj [( "base" ,
    memoryJson m06)]) , ( "savedBytes" , Json.mkObj [( "window" , bytesJson r09)]) , (
    "returnClass" , toJson "bytes" )] ,
  Json.mkObj [( "id" , toJson "30-empty-write-u256max" ) , ( "op" , toJson "write" ) , ( "before" ,
    memoryJson m06) , ( "input" , Json.mkObj [( "start" , toJson (toString
    (115792089237316195423570985008687907853269984665640564039457584007913129639935 : Nat))) , (
    "payload" , bytesJson v30)]) , ( "after" , memoryJson m30) , ( "reads" , Json.mkObj []) , (
    "savedMemories" , Json.mkObj [( "base" , memoryJson m06)]) , ( "savedBytes" , Json.mkObj [(
    "window" , bytesJson r09)]) , ( "returnClass" , toJson "NoneType" )] ,
  Json.mkObj [( "id" , toJson "31-lean-only-empty-read-2p4096" ) , ( "op" , toJson "read" ) , (
    "before" , memoryJson m06) , ( "input" , Json.mkObj [( "startExpression" , toJson "2^4096" ) ,
    ( "length" , toJson (toString (0 : Nat)))]) , ( "after" , memoryJson m31) , ( "reads" ,
    Json.mkObj [( "result" , bytesJson r31)]) , ( "savedMemories" , Json.mkObj [( "base" ,
    memoryJson m06)]) , ( "savedBytes" , Json.mkObj [( "window" , bytesJson r09)]) , (
    "returnClass" , toJson "observation" )] ,
  Json.mkObj [( "id" , toJson "32-lean-only-empty-write-2p4096" ) , ( "op" , toJson "write" ) , (
    "before" , memoryJson m06) , ( "input" , Json.mkObj [( "startExpression" , toJson "2^4096" ) ,
    ( "payload" , bytesJson v32)]) , ( "after" , memoryJson m32) , ( "reads" , Json.mkObj []) , (
    "savedMemories" , Json.mkObj [( "base" , memoryJson m06)]) , ( "savedBytes" , Json.mkObj [(
    "window" , bytesJson r09)]) , ( "returnClass" , toJson "observation" )] ,
  Json.mkObj [( "id" , toJson "33-both-empty" ) , ( "op" , toJson "write" ) , ( "before" ,
    memoryJson m01) , ( "input" , Json.mkObj [( "start" , toJson (toString (18446744073709551616 :
    Nat))) , ( "payload" , bytesJson v33)]) , ( "after" , memoryJson m33) , ( "reads" , Json.mkObj
    [( "empty-read-inside" , bytesJson r33)]) , ( "savedMemories" , Json.mkObj [( "old" ,
    memoryJson m01)]) , ( "savedBytes" , Json.mkObj [( "empty" , bytesJson r33)]) , ( "returnClass"
    , toJson "NoneType" )]
]
private def expected : List Json := [
  (Json.parse (String.join [
    "{\"id\":\"01-empty\",\"op\":\"observe\",\"before\":{\"size\":0,\"hex\":\"\"},\"input\":{},",
    "\"after\":{\"size\":0,\"hex\":\"\"},\"reads\":{},\"savedMemories\":{},\"savedBytes\":{},",
    "\"returnClass\":\"observation\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"02-empty-expand-zero\",\"op\":\"expand\",\"before\":{\"size\":0,\"hex\":\"\"},",
    "\"input\":{\"increment\":\"0\"},\"after\":{\"size\":0,\"hex\":\"\"},\"reads\":{},",
    "\"savedMemories\":{\"old\":{\"size\":0,\"hex\":\"\"}},\"savedBytes\":{},\"returnClass\":",
    "\"NoneType\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"03-expand32\",\"op\":\"expand\",\"before\":{\"size\":0,\"hex\":\"\"},\"input\":{",
    "\"increment\":\"32\"},\"after\":{\"size\":32,\"hex\":",
    "\"0000000000000000000000000000000000000000000000000000000000000000\"},\"reads\":{},",
    "\"savedMemories\":{\"old\":{\"size\":0,\"hex\":\"\"}},\"savedBytes\":{},\"returnClass\":",
    "\"NoneType\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"04-expand-zero32\",\"op\":\"expand\",\"before\":{\"size\":32,\"hex\":",
    "\"0000000000000000000000000000000000000000000000000000000000000000\"},\"input\":{",
    "\"increment\":\"0\"},\"after\":{\"size\":32,\"hex\":",
    "\"0000000000000000000000000000000000000000000000000000000000000000\"},\"reads\":{},",
    "\"savedMemories\":{\"old\":{\"size\":32,\"hex\":",
    "\"0000000000000000000000000000000000000000000000000000000000000000\"}},\"savedBytes\":{},",
    "\"returnClass\":\"NoneType\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"05-expand32-again\",\"op\":\"expand\",\"before\":{\"size\":32,\"hex\":",
    "\"0000000000000000000000000000000000000000000000000000000000000000\"},\"input\":{",
    "\"increment\":\"32\"},\"after\":{\"size\":64,\"hex\":",
    "\"000000000000000000000000000000000000000000000000000000000000000",
    "00000000000000000000000000000000000000000000000000000000000000000\"},\"reads\":{},",
    "\"savedMemories\":{\"old\":{\"size\":32,\"hex\":",
    "\"0000000000000000000000000000000000000000000000000000000000000000\"}},\"savedBytes\":{},",
    "\"returnClass\":\"NoneType\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"06-full-write\",\"op\":\"write\",\"before\":{\"size\":64,\"hex\":",
    "\"000000000000000000000000000000000000000000000000000000000000000",
    "00000000000000000000000000000000000000000000000000000000000000000\"},\"input\":{\"start\":",
    "\"0\",\"payload\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"}},\"after\":{\"size\"",
    ":64,\"hex\":\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"reads\":{},",
    "\"savedMemories\":{\"old\":{\"size\":64,\"hex\":",
    "\"000000000000000000000000000000000000000000000000000000000000000",
    "00000000000000000000000000000000000000000000000000000000000000000\"}},\"savedBytes\":{},",
    "\"returnClass\":\"NoneType\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"07-high-interior-zero-full-write\",\"op\":\"write\",\"before\":{\"size\":32,",
    "\"hex\":\"0000000000000000000000000000000000000000000000000000000000000000\"},\"input\":{",
    "\"start\":\"0\",\"payload\":{\"size\":32,\"hex\":",
    "\"0080ff01007f55aa0080ff01007f55aa0080ff01007f55aa0080ff01007f55aa\"}},\"after\":{\"size\"",
    ":32,\"hex\":\"0080ff01007f55aa0080ff01007f55aa0080ff01007f55aa0080ff01007f55aa\"},",
    "\"reads\":{},\"savedMemories\":{\"old\":{\"size\":32,\"hex\":",
    "\"0000000000000000000000000000000000000000000000000000000000000000\"}},\"savedBytes\":{},",
    "\"returnClass\":\"NoneType\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"08-read-all\",\"op\":\"read\",\"before\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"input\":{\"start\":",
    "\"0\",\"length\":\"64\"},\"after\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"reads\":{\"result\"",
    ":{\"size\":64,\"hex\":\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"}},\"savedMemories\"",
    ":{},\"savedBytes\":{},\"returnClass\":\"bytes\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"09-save-cross-window\",\"op\":\"read\",\"before\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"input\":{\"start\":",
    "\"28\",\"length\":\"8\"},\"after\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"reads\":{\"result\"",
    ":{\"size\":8,\"hex\":\"1c1d1e1f20212223\"}},\"savedMemories\":{\"base\":{\"size\":64,",
    "\"hex\":\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"}},\"savedBytes\":{",
    "\"window\":{\"size\":8,\"hex\":\"1c1d1e1f20212223\"}},\"returnClass\":\"bytes\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"10-cross-word-write\",\"op\":\"write\",\"before\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"input\":{\"start\":",
    "\"28\",\"payload\":{\"size\":8,\"hex\":\"fe0080ff01007f55\"}},\"after\":{\"size\":64,",
    "\"hex\":\"000102030405060708090a0b0c0d0e0f101112131415161718191a1bfe0080f",
    "f01007f552425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"reads\":{},",
    "\"savedMemories\":{\"base\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"}},\"savedBytes\":{",
    "\"window\":{\"size\":8,\"hex\":\"1c1d1e1f20212223\"}},\"returnClass\":\"NoneType\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"11-cross-word-read\",\"op\":\"read\",\"before\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1bfe0080f",
    "f01007f552425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"input\":{\"start\":",
    "\"28\",\"length\":\"8\"},\"after\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1bfe0080f",
    "f01007f552425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"reads\":{\"result\"",
    ":{\"size\":8,\"hex\":\"fe0080ff01007f55\"}},\"savedMemories\":{\"base\":{\"size\":64,",
    "\"hex\":\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"}},\"savedBytes\":{",
    "\"window\":{\"size\":8,\"hex\":\"1c1d1e1f20212223\"}},\"returnClass\":\"bytes\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"12-whole-prefix\",\"op\":\"read\",\"before\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1bfe0080f",
    "f01007f552425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"input\":{\"start\":",
    "\"0\",\"length\":\"28\"},\"after\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1bfe0080f",
    "f01007f552425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"reads\":{\"result\"",
    ":{\"size\":28,\"hex\":\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b\"}},",
    "\"savedMemories\":{\"base\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"}},\"savedBytes\":{",
    "\"window\":{\"size\":8,\"hex\":\"1c1d1e1f20212223\"}},\"returnClass\":\"bytes\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"13-whole-suffix\",\"op\":\"read\",\"before\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1bfe0080f",
    "f01007f552425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"input\":{\"start\":",
    "\"36\",\"length\":\"28\"},\"after\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1bfe0080f",
    "f01007f552425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"reads\":{\"result\"",
    ":{\"size\":28,\"hex\":\"2425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"}},",
    "\"savedMemories\":{\"base\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"}},\"savedBytes\":{",
    "\"window\":{\"size\":8,\"hex\":\"1c1d1e1f20212223\"}},\"returnClass\":\"bytes\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"14-left-overlap\",\"op\":\"write\",\"before\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"input\":{\"start\":",
    "\"26\",\"payload\":{\"size\":8,\"hex\":\"1c1d1e1f20212223\"}},\"after\":{\"size\":64,",
    "\"hex\":\"000102030405060708090a0b0c0d0e0f101112131415161718191c1d1e1f202",
    "1222322232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"reads\":{},",
    "\"savedMemories\":{\"base\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"}},\"savedBytes\":{",
    "\"window\":{\"size\":8,\"hex\":\"1c1d1e1f20212223\"}},\"returnClass\":\"NoneType\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"15-right-overlap\",\"op\":\"write\",\"before\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"input\":{\"start\":",
    "\"30\",\"payload\":{\"size\":8,\"hex\":\"1c1d1e1f20212223\"}},\"after\":{\"size\":64,",
    "\"hex\":\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1c1",
    "d1e1f20212223262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"reads\":{},",
    "\"savedMemories\":{\"base\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"}},\"savedBytes\":{",
    "\"window\":{\"size\":8,\"hex\":\"1c1d1e1f20212223\"}},\"returnClass\":\"NoneType\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"16-self-copy\",\"op\":\"write\",\"before\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"input\":{\"start\":",
    "\"28\",\"payload\":{\"size\":8,\"hex\":\"1c1d1e1f20212223\"}},\"after\":{\"size\":64,",
    "\"hex\":\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"reads\":{},",
    "\"savedMemories\":{\"base\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"}},\"savedBytes\":{",
    "\"window\":{\"size\":8,\"hex\":\"1c1d1e1f20212223\"}},\"returnClass\":\"NoneType\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"17-retained-original-and-read\",\"op\":\"observe\",\"before\":{\"size\":64,",
    "\"hex\":\"000102030405060708090a0b0c0d0e0f101112131415161718191a1bfe0080f",
    "f01007f552425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"input\":{},",
    "\"after\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1bfe0080f",
    "f01007f552425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"reads\":{},",
    "\"savedMemories\":{\"base\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"}},\"savedBytes\":{",
    "\"window\":{\"size\":8,\"hex\":\"1c1d1e1f20212223\"}},\"returnClass\":\"observation\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"18-expand-written32\",\"op\":\"expand\",\"before\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1bfe0080f",
    "f01007f552425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"input\":{",
    "\"increment\":\"32\"},\"after\":{\"size\":96,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1bfe0080f",
    "f01007f552425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3",
    "f0000000000000000000000000000000000000000000000000000000000000000\"},\"reads\":{},",
    "\"savedMemories\":{\"old\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1bfe0080f",
    "f01007f552425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"base\":{\"size\"",
    ":64,\"hex\":\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"}},\"savedBytes\":{",
    "\"window\":{\"size\":8,\"hex\":\"1c1d1e1f20212223\"}},\"returnClass\":\"NoneType\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"19-exact-end-write\",\"op\":\"write\",\"before\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"input\":{\"start\":",
    "\"60\",\"payload\":{\"size\":4,\"hex\":\"0080ff00\"}},\"after\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b0080ff00\"},\"reads\":{},",
    "\"savedMemories\":{\"base\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"}},\"savedBytes\":{",
    "\"window\":{\"size\":8,\"hex\":\"1c1d1e1f20212223\"}},\"returnClass\":\"NoneType\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"20-exact-end-read\",\"op\":\"read\",\"before\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b0080ff00\"},\"input\":{\"start\":",
    "\"60\",\"length\":\"4\"},\"after\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b0080ff00\"},\"reads\":{\"result\"",
    ":{\"size\":4,\"hex\":\"0080ff00\"}},\"savedMemories\":{\"base\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"}},\"savedBytes\":{",
    "\"window\":{\"size\":8,\"hex\":\"1c1d1e1f20212223\"}},\"returnClass\":\"bytes\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"21-empty-end-read\",\"op\":\"read\",\"before\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"input\":{\"start\":",
    "\"64\",\"length\":\"0\"},\"after\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"reads\":{\"result\"",
    ":{\"size\":0,\"hex\":\"\"}},\"savedMemories\":{},\"savedBytes\":{},\"returnClass\":",
    "\"bytes\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"22-empty-read-inside-write\",\"op\":\"read\",\"before\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1bfe0080f",
    "f01007f552425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"input\":{\"start\":",
    "\"30\",\"length\":\"0\"},\"after\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1bfe0080f",
    "f01007f552425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"reads\":{\"result\"",
    ":{\"size\":0,\"hex\":\"\"}},\"savedMemories\":{\"base\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"}},\"savedBytes\":{",
    "\"window\":{\"size\":8,\"hex\":\"1c1d1e1f20212223\"}},\"returnClass\":\"bytes\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"23-empty-write-inside-read\",\"op\":\"write\",\"before\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"input\":{\"start\":",
    "\"30\",\"payload\":{\"size\":0,\"hex\":\"\"}},\"after\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"reads\":{",
    "\"preserved-window\":{\"size\":8,\"hex\":\"1c1d1e1f20212223\"}},\"savedMemories\":{",
    "\"base\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"}},\"savedBytes\":{",
    "\"window\":{\"size\":8,\"hex\":\"1c1d1e1f20212223\"}},\"returnClass\":\"NoneType\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"24-adjacent-prefix\",\"op\":\"read\",\"before\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1bfe0080f",
    "f01007f552425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"input\":{\"start\":",
    "\"28\",\"length\":\"0\"},\"after\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1bfe0080f",
    "f01007f552425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"reads\":{\"result\"",
    ":{\"size\":0,\"hex\":\"\"}},\"savedMemories\":{},\"savedBytes\":{},\"returnClass\":",
    "\"bytes\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"25-adjacent-left\",\"op\":\"read\",\"before\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1bfe0080f",
    "f01007f552425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"input\":{\"start\":",
    "\"24\",\"length\":\"4\"},\"after\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1bfe0080f",
    "f01007f552425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"reads\":{\"result\"",
    ":{\"size\":4,\"hex\":\"18191a1b\"}},\"savedMemories\":{},\"savedBytes\":{},\"returnClass\"",
    ":\"bytes\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"26-adjacent-right\",\"op\":\"read\",\"before\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1bfe0080f",
    "f01007f552425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"input\":{\"start\":",
    "\"36\",\"length\":\"4\"},\"after\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1bfe0080f",
    "f01007f552425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"reads\":{\"result\"",
    ":{\"size\":4,\"hex\":\"24252627\"}},\"savedMemories\":{},\"savedBytes\":{},\"returnClass\"",
    ":\"bytes\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"27-empty-read-2p64\",\"op\":\"read\",\"before\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"input\":{\"start\":",
    "\"18446744073709551616\",\"length\":\"0\"},\"after\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"reads\":{\"result\"",
    ":{\"size\":0,\"hex\":\"\"}},\"savedMemories\":{\"base\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"}},\"savedBytes\":{",
    "\"window\":{\"size\":8,\"hex\":\"1c1d1e1f20212223\"}},\"returnClass\":\"bytes\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"28-empty-write-2p64\",\"op\":\"write\",\"before\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"input\":{\"start\":",
    "\"18446744073709551616\",\"payload\":{\"size\":0,\"hex\":\"\"}},\"after\":{\"size\":64,",
    "\"hex\":\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"reads\":{},",
    "\"savedMemories\":{\"base\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"}},\"savedBytes\":{",
    "\"window\":{\"size\":8,\"hex\":\"1c1d1e1f20212223\"}},\"returnClass\":\"NoneType\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"29-empty-read-u256max\",\"op\":\"read\",\"before\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"input\":{\"start\":",
    "\"115792089237316195423570985008687907853269984665640564039457584007913129639935\",",
    "\"length\":\"0\"},\"after\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"reads\":{\"result\"",
    ":{\"size\":0,\"hex\":\"\"}},\"savedMemories\":{\"base\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"}},\"savedBytes\":{",
    "\"window\":{\"size\":8,\"hex\":\"1c1d1e1f20212223\"}},\"returnClass\":\"bytes\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"30-empty-write-u256max\",\"op\":\"write\",\"before\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"input\":{\"start\":",
    "\"115792089237316195423570985008687907853269984665640564039457584007913129639935\",",
    "\"payload\":{\"size\":0,\"hex\":\"\"}},\"after\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"reads\":{},",
    "\"savedMemories\":{\"base\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"}},\"savedBytes\":{",
    "\"window\":{\"size\":8,\"hex\":\"1c1d1e1f20212223\"}},\"returnClass\":\"NoneType\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"31-lean-only-empty-read-2p4096\",\"op\":\"read\",\"before\":{\"size\":64,\"hex\"",
    ":\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"input\":{",
    "\"startExpression\":\"2^4096\",\"length\":\"0\"},\"after\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"reads\":{\"result\"",
    ":{\"size\":0,\"hex\":\"\"}},\"savedMemories\":{\"base\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"}},\"savedBytes\":{",
    "\"window\":{\"size\":8,\"hex\":\"1c1d1e1f20212223\"}},\"returnClass\":\"observation\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"32-lean-only-empty-write-2p4096\",\"op\":\"write\",\"before\":{\"size\":64,",
    "\"hex\":\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"input\":{",
    "\"startExpression\":\"2^4096\",\"payload\":{\"size\":0,\"hex\":\"\"}},\"after\":{\"size\"",
    ":64,\"hex\":\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"},\"reads\":{},",
    "\"savedMemories\":{\"base\":{\"size\":64,\"hex\":",
    "\"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1",
    "f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f\"}},\"savedBytes\":{",
    "\"window\":{\"size\":8,\"hex\":\"1c1d1e1f20212223\"}},\"returnClass\":\"observation\"}"
  ])).toOption.getD Json.null,
  (Json.parse (String.join [
    "{\"id\":\"33-both-empty\",\"op\":\"write\",\"before\":{\"size\":0,\"hex\":\"\"},\"input\"",
    ":{\"start\":\"18446744073709551616\",\"payload\":{\"size\":0,\"hex\":\"\"}},\"after\":{",
    "\"size\":0,\"hex\":\"\"},\"reads\":{\"empty-read-inside\":{\"size\":0,\"hex\":\"\"}},",
    "\"savedMemories\":{\"old\":{\"size\":0,\"hex\":\"\"}},\"savedBytes\":{\"empty\":{\"size\"",
    ":0,\"hex\":\"\"}},\"returnClass\":\"NoneType\"}"
  ])).toOption.getD Json.null
]
#guard observations == expected
