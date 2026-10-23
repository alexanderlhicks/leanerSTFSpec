/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Complete structural SSZ sizing controls

Library `EthConformance`. Exactly 96 complete `Option Nat` controls.
S: static source consequence conditional on an actually admitted intended class;
D: that same conditional claim through the direct dependency mapping;
R: Q67 raw completion, with no admitted source-class claim. No source was executed.
G12 additionally needs an actual source field named `more`; masks alone do not admit it.
Huge parameters are metadata, with at most 257 actual list entries here.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–4.
-/

namespace STFSpec.Conformance.Codec.SszFixedSizeGuards

open STFSpec.Codec

private def largeWord : Nat := 2 ^ 64
private def huge : Nat := 2 ^ 256 + 17

-- U01 (R): complete expected result.
#guard (SszType.fixedSize? (.uint (0))) == (some (0) : Option Nat)

-- U02 (S): complete expected result.
#guard (SszType.fixedSize? (.uint (1))) == (some (1) : Option Nat)

-- U03 (S): complete expected result.
#guard (SszType.fixedSize? (.uint (2))) == (some (2) : Option Nat)

-- U04 (R): complete expected result.
#guard (SszType.fixedSize? (.uint (3))) == (some (3) : Option Nat)

-- U05 (S): complete expected result.
#guard (SszType.fixedSize? (.uint (4))) == (some (4) : Option Nat)

-- U06 (S): complete expected result.
#guard (SszType.fixedSize? (.uint (8))) == (some (8) : Option Nat)

-- U07 (S): complete expected result.
#guard (SszType.fixedSize? (.uint (16))) == (some (16) : Option Nat)

-- U08 (S): complete expected result.
#guard (SszType.fixedSize? (.uint (32))) == (some (32) : Option Nat)

-- U09 (R): complete expected result.
#guard (SszType.fixedSize? (.uint (33))) == (some (33) : Option Nat)

-- U10 (R): complete expected result.
#guard (SszType.fixedSize? (.uint (largeWord))) == (some (largeWord) : Option Nat)

-- U11 (R): complete expected result.
#guard (SszType.fixedSize? (.uint (huge))) == (some (huge) : Option Nat)

-- U12 (R): complete expected result.
#guard (SszType.fixedSize? (.uint (largeWord + 1))) == (some (largeWord + 1) : Option Nat)

-- B01 (S): complete expected result.
#guard (SszType.fixedSize? (.bool)) == (some 1 : Option Nat)

-- V01 (S): complete expected result.
#guard (SszType.fixedSize? (.byteVector (0))) == (some (0) : Option Nat)

-- V02 (S): complete expected result.
#guard (SszType.fixedSize? (.byteVector (1))) == (some (1) : Option Nat)

-- V03 (S): complete expected result.
#guard (SszType.fixedSize? (.byteVector (31))) == (some (31) : Option Nat)

-- V04 (S): complete expected result.
#guard (SszType.fixedSize? (.byteVector (32))) == (some (32) : Option Nat)

-- V05 (S): complete expected result.
#guard (SszType.fixedSize? (.byteVector (33))) == (some (33) : Option Nat)

-- V06 (R): complete expected result.
#guard (SszType.fixedSize? (.byteVector (largeWord))) == (some (largeWord) : Option Nat)

-- V07 (R): complete expected result.
#guard (SszType.fixedSize? (.byteVector (huge))) == (some (huge) : Option Nat)

-- V08 (R): complete expected result.
#guard (SszType.fixedSize? (.byteVector (largeWord + 1))) == (some (largeWord + 1) : Option Nat)

-- Y01 (S): complete expected result.
#guard (SszType.fixedSize? (.byteList (0))) == (none : Option Nat)

-- Y02 (S): complete expected result.
#guard (SszType.fixedSize? (.byteList (1))) == (none : Option Nat)

-- Y03 (S): complete expected result.
#guard (SszType.fixedSize? (.byteList (33))) == (none : Option Nat)

-- Y04 (R): complete expected result.
#guard (SszType.fixedSize? (.byteList (largeWord))) == (none : Option Nat)

-- Y05 (R): complete expected result.
#guard (SszType.fixedSize? (.byteList (huge))) == (none : Option Nat)

-- L01 (S): complete expected result.
#guard (SszType.fixedSize? (.list .bool 0)) == (none : Option Nat)

-- L02 (S): complete expected result.
#guard (SszType.fixedSize? (.list .bool 1)) == (none : Option Nat)

-- L03 (S): complete expected result.
#guard (SszType.fixedSize? (.list (.byteVector 0) 2)) == (none : Option Nat)

-- L04 (S): complete expected result.
#guard (SszType.fixedSize? (.list (.byteList 0) 2)) == (none : Option Nat)

-- L05 (S): complete expected result.
#guard (SszType.fixedSize? (.list (.list .bool 0) 3)) == (none : Option Nat)

-- L06 (R): complete expected result.
#guard (SszType.fixedSize? (.list (.uint 3) 0)) == (none : Option Nat)

-- L07 (R): complete expected result.
#guard (SszType.fixedSize? (.list (.progressiveContainer [] [.bool]) 0)) == (none : Option Nat)

-- L08 (R): complete expected result.
#guard (SszType.fixedSize? (.list (.container []) huge)) == (none : Option Nat)

-- L09 (R): complete expected result.
#guard (SszType.fixedSize? (.list (.uint huge) huge)) == (none : Option Nat)

-- L10 (S): complete expected result.
#guard (SszType.fixedSize? (.list .progressiveByteList 1)) == (none : Option Nat)

-- P01 (S): complete expected result.
#guard (SszType.fixedSize? (.progressiveList .bool)) == (none : Option Nat)

-- P02 (S): complete expected result.
#guard (SszType.fixedSize? (.progressiveList (.byteVector 0))) == (none : Option Nat)

-- P03 (S): complete expected result.
#guard (SszType.fixedSize? (.progressiveList (.byteList 0))) == (none : Option Nat)

-- P04 (S): complete expected result.
#guard (SszType.fixedSize? (.progressiveList (.list .bool 0))) == (none : Option Nat)

-- P05 (R): complete expected result.
#guard (SszType.fixedSize? (.progressiveList (.uint 3))) == (none : Option Nat)

-- P06 (R): complete expected result.
#guard (SszType.fixedSize?
  (.progressiveList (.progressiveContainer [] [.bool]))) ==
  (none : Option Nat)

-- P07 (R): complete expected result.
#guard (SszType.fixedSize? (.progressiveList (.container []))) == (none : Option Nat)

-- P08 (R): complete expected result.
#guard (SszType.fixedSize? (.progressiveList (.uint huge))) == (none : Option Nat)

-- PB01 (S): complete expected result.
#guard (SszType.fixedSize? (.progressiveByteList)) == (none : Option Nat)

-- C01 (R): complete expected result.
#guard (SszType.fixedSize? (.container [])) == (some 0 : Option Nat)

-- C02 (S): complete expected result.
#guard (SszType.fixedSize? (.container [.byteVector 0])) == (some 0 : Option Nat)

-- C03 (R): complete expected result.
#guard (SszType.fixedSize? (.container [.uint 0])) == (some 0 : Option Nat)

-- C04 (S): complete expected result.
#guard (SszType.fixedSize? (.container [.uint 2, .bool, .byteVector 3])) == (some 6 : Option Nat)

-- C05 (S): complete expected result.
#guard (SszType.fixedSize? (.container [.byteList 0])) == (none : Option Nat)

-- C06 (R): complete expected result.
#guard (SszType.fixedSize? (.container [.uint 3, .bool])) == (some 4 : Option Nat)

-- C07 (S): complete expected result.
#guard (SszType.fixedSize? (.container [.bool, .progressiveByteList])) == (none : Option Nat)

-- C08 (S): complete expected result.
#guard (SszType.fixedSize?
  (.container [.container [.bool],
    .byteVector 0])) ==
  (some 1 : Option Nat)

-- C09 (S): complete expected result.
#guard (SszType.fixedSize?
  (.container [.byteList 0,
    .uint 2,
    .byteVector 3])) ==
  (none : Option Nat)

-- C10 (S): complete expected result.
#guard (SszType.fixedSize?
  (.container [.uint 2,
    .byteVector 3,
    .byteList 0])) ==
  (none : Option Nat)

-- C11 (R): complete expected result.
#guard (SszType.fixedSize?
  (.container [.container [],
    .byteVector 0,
    .uint 0])) ==
  (some 0 : Option Nat)

-- C12 (R): complete expected result.
#guard (SszType.fixedSize?
  (.container [.container [.uint 2,
    .byteVector 0],
    .progressiveContainer [false] [.bool,
    .byteVector 3]])) ==
  (some 6 : Option Nat)

-- C13 (S): complete expected result.
#guard (SszType.fixedSize?
  (.container [.container [.bool,
    .byteList 0],
    .uint 2])) ==
  (none : Option Nat)

-- C14 (S): complete expected result.
#guard (SszType.fixedSize?
  (.container [.uint 2,
    .container [.bool,
    .progressiveList .bool]])) ==
  (none : Option Nat)

-- C15 (R): complete expected result.
#guard (SszType.fixedSize? (.container [.uint 3, .uint 3])) == (some 6 : Option Nat)

-- C16 (S): complete expected result.
#guard (SszType.fixedSize?
  (.container [.byteVector 5,
    .byteVector 5,
    .bool])) ==
  (some 11 : Option Nat)

-- C17 (R): complete expected result.
#guard (SszType.fixedSize?
  (.container [.uint huge,
    .byteVector 0,
    .uint 2])) ==
  (some (huge + 2) : Option Nat)

-- C18 (R): complete expected result.
#guard (SszType.fixedSize?
  (.container [.uint 2,
    .uint huge,
    .byteVector 1])) ==
  (some (huge + 3) : Option Nat)

-- C19 (S): complete expected result.
#guard (SszType.fixedSize?
  (.container [.container [.uint 2,
    .bool],
    .container [.uint 2,
    .bool]])) ==
  (some 6 : Option Nat)

-- C20 (D): complete expected result.
#guard (SszType.fixedSize?
  (.container [.progressiveContainer [false,
    true] [.bool],
    .byteVector 0])) ==
  (some 1 : Option Nat)

-- G01 (S): complete expected result.
#guard (SszType.fixedSize? (.progressiveContainer [true] [.bool])) == (some 1 : Option Nat)

-- G02 (D): complete expected result.
#guard (SszType.fixedSize? (.progressiveContainer [false, true] [.bool])) == (some 1 : Option Nat)

-- G03 (R): complete expected result.
#guard (SszType.fixedSize? (.progressiveContainer [] [.bool])) == (some 1 : Option Nat)

-- G04 (R): complete expected result.
#guard (SszType.fixedSize? (.progressiveContainer [true, false] [.bool])) == (some 1 : Option Nat)

-- G05 (R): complete expected result.
#guard (SszType.fixedSize? (.progressiveContainer [true, true] [.bool])) == (some 1 : Option Nat)

-- G06 (R): complete expected result.
#guard (SszType.fixedSize? (.progressiveContainer [false] [.bool])) == (some 1 : Option Nat)

-- G07 (R): complete expected result.
#guard (SszType.fixedSize? (.progressiveContainer [true] [])) == (some 0 : Option Nat)

-- G08 (R): complete expected result.
#guard (SszType.fixedSize? (.progressiveContainer [] [])) == (some 0 : Option Nat)

-- G09 (R): complete expected result.
#guard (SszType.fixedSize? (.progressiveContainer [false] [])) == (some 0 : Option Nat)

-- G10 (R): complete expected result.
#guard (SszType.fixedSize? (.progressiveContainer [true, false] [])) == (some 0 : Option Nat)

-- G11 (R): complete expected result.
#guard (SszType.fixedSize?
  (.progressiveContainer (List.replicate 257 true) (List.replicate 257 .bool))) ==
  (some 257 : Option Nat)

-- G12 (D): complete expected result.
#guard (SszType.fixedSize?
  (.progressiveContainer (List.replicate 256 true) (List.replicate 256 .bool))) ==
  (some 256 : Option Nat)

-- G13 (S): complete expected result.
#guard (SszType.fixedSize?
  (.progressiveContainer (List.replicate 255 true) (List.replicate 255 .bool))) ==
  (some 255 : Option Nat)

-- G14 (R): complete expected result.
#guard (SszType.fixedSize?
  (.progressiveContainer (List.replicate 257 true) [])) ==
  (some 0 : Option Nat)

-- G15 (R): complete expected result.
#guard (SszType.fixedSize?
  (.progressiveContainer (List.replicate 257 false) [.bool])) ==
  (some 1 : Option Nat)

-- G16 (R): complete expected result.
#guard (SszType.fixedSize?
  (.progressiveContainer (List.replicate 256 true) [.bool])) ==
  (some 1 : Option Nat)

-- G17 (S): complete expected result.
#guard (SszType.fixedSize? (.progressiveContainer [true] [.byteList 0])) == (none : Option Nat)

-- G18 (R): complete expected result.
#guard (SszType.fixedSize? (.progressiveContainer [] [.byteList 0])) == (none : Option Nat)

-- G19 (D): complete expected result.
#guard (SszType.fixedSize?
  (.progressiveContainer [false,
    true] [.byteList 0])) ==
  (none : Option Nat)

-- G20 (R): complete expected result.
#guard (SszType.fixedSize?
  (.progressiveContainer (List.replicate 257 false) [.uint 2,
    .byteList 0,
    .byteVector 3])) ==
  (none : Option Nat)

-- G21 (R): complete expected result.
#guard (SszType.fixedSize?
  (.progressiveContainer [false,
    true] [.uint 3,
    .byteVector 0,
    .uint huge])) ==
  (some (huge + 3) : Option Nat)

-- G22 (R): complete expected result.
#guard (SszType.fixedSize?
  (.progressiveContainer [true] [.byteVector 0,
    .uint 0,
    .container []])) ==
  (some 0 : Option Nat)

-- G23 (S): complete expected result.
#guard (SszType.fixedSize?
  (.progressiveContainer [true,
    true] [.container [.uint 2,
    .bool],
    .container [.uint 2,
    .bool]])) ==
  (some 6 : Option Nat)

-- G24 (R): complete expected result.
#guard (SszType.fixedSize?
  (.progressiveContainer [] [.container [.byteList 0],
    .uint huge])) ==
  (none : Option Nat)

-- A01 (R): complete expected result.
#guard (SszType.fixedSize?
  (.container [.progressiveContainer [] [.uint 2,
    .container [.byteVector 0,
    .bool]],
    .container [.uint 3]])) ==
  (some 6 : Option Nat)

-- A02 (R): complete expected result.
#guard (SszType.fixedSize?
  (.progressiveContainer (List.replicate 257 false) [.container [.progressiveContainer [true,
    false] [.uint huge]],
    .byteVector 0,
    .bool])) ==
  (some (huge + 1) : Option Nat)

-- A03 (R): complete expected result.
#guard (SszType.fixedSize?
  (.container [.progressiveList (.progressiveContainer [] [.uint huge]),
    .uint huge])) ==
  (none : Option Nat)

-- A04 (R): complete expected result.
#guard (SszType.fixedSize?
  (.container [.uint huge,
    .progressiveList (.progressiveContainer [] [.uint huge])])) ==
  (none : Option Nat)

-- A05 (R): complete expected result.
#guard (SszType.fixedSize?
  (.progressiveContainer [] [.container [.bool,
    .byteList 0],
    .uint 2])) ==
  (none : Option Nat)

-- A06 (R): complete expected result.
#guard (SszType.fixedSize?
  (.progressiveContainer [] [.uint 2,
    .container [.bool,
    .byteList 0]])) ==
  (none : Option Nat)

-- A07 (S): complete expected result.
#guard (SszType.fixedSize? (.container [.uint 2, .bool, .byteVector 4])) == (some 7 : Option Nat)

end STFSpec.Conformance.Codec.SszFixedSizeGuards
