/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Hash32 RLP complete controls

Library `EthConformance`. Exactly 90 complete handwritten outcomes preserve
nominal values, every byte, complete wires and ordered diagnostics.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/

namespace STFSpec.Conformance.Codec.RlpHash32Guards
open STFSpec.Codec STFSpec.Codec.Rlp STFSpec.Base

private local instance {α : Type} [DecidableEq α] : DecidableEq (Except RlpError α) := by
  intro a b
  cases a <;> cases b <;>
    simp only [Except.ok.injEq, Except.error.injEq, reduceCtorEq] <;> infer_instance

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- S00-model
#guard (match RlpEncode.toRlp (Hash32.ofBytes32 (FixedBytes.ofNat 0 : Bytes32)) with | .bytes b => b == ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ | .list _ => false)

-- S00-typed
#guard RlpDecode.ofRlp (α := Hash32) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) = (.ok (Hash32.ofBytes32 (FixedBytes.ofNat 0 : Bytes32)) : Except RlpError Hash32)

-- S00-wire
#guard encodeOf (Hash32.ofBytes32 (FixedBytes.ofNat 0 : Bytes32)) = ⟨#[160, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

-- S00-roundtrip
#guard decodeTo (α := Hash32) ⟨#[160, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ = (.ok (Hash32.ofBytes32 (FixedBytes.ofNat 0 : Bytes32)) : Except RlpError Hash32)

-- S01-model
#guard (match RlpEncode.toRlp (Hash32.ofBytes32 (FixedBytes.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935 : Bytes32)) with | .bytes b => b == ⟨#[255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]⟩ | .list _ => false)

-- S01-typed
#guard RlpDecode.ofRlp (α := Hash32) (.bytes ⟨#[255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]⟩) = (.ok (Hash32.ofBytes32 (FixedBytes.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935 : Bytes32)) : Except RlpError Hash32)

-- S01-wire
#guard encodeOf (Hash32.ofBytes32 (FixedBytes.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935 : Bytes32)) = ⟨#[160, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]⟩

-- S01-roundtrip
#guard decodeTo (α := Hash32) ⟨#[160, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]⟩ = (.ok (Hash32.ofBytes32 (FixedBytes.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935 : Bytes32)) : Except RlpError Hash32)

-- S02-model
#guard (match RlpEncode.toRlp (Hash32.ofBytes32 (FixedBytes.ofNat 1 : Bytes32)) with | .bytes b => b == ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩ | .list _ => false)

-- S02-typed
#guard RlpDecode.ofRlp (α := Hash32) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩) = (.ok (Hash32.ofBytes32 (FixedBytes.ofNat 1 : Bytes32)) : Except RlpError Hash32)

-- S02-wire
#guard encodeOf (Hash32.ofBytes32 (FixedBytes.ofNat 1 : Bytes32)) = ⟨#[160, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩

-- S02-roundtrip
#guard decodeTo (α := Hash32) ⟨#[160, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩ = (.ok (Hash32.ofBytes32 (FixedBytes.ofNat 1 : Bytes32)) : Except RlpError Hash32)

-- S03-model
#guard (match RlpEncode.toRlp (Hash32.ofBytes32 (FixedBytes.ofNat 452312848583266388373324160190187140051835877600158453279131187530910662911 : Bytes32)) with | .bytes b => b == ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255]⟩ | .list _ => false)

-- S03-typed
#guard RlpDecode.ofRlp (α := Hash32) (.bytes ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255]⟩) = (.ok (Hash32.ofBytes32 (FixedBytes.ofNat 452312848583266388373324160190187140051835877600158453279131187530910662911 : Bytes32)) : Except RlpError Hash32)

-- S03-wire
#guard encodeOf (Hash32.ofBytes32 (FixedBytes.ofNat 452312848583266388373324160190187140051835877600158453279131187530910662911 : Bytes32)) = ⟨#[160, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255]⟩

-- S03-roundtrip
#guard decodeTo (α := Hash32) ⟨#[160, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255]⟩ = (.ok (Hash32.ofBytes32 (FixedBytes.ofNat 452312848583266388373324160190187140051835877600158453279131187530910662911 : Bytes32)) : Except RlpError Hash32)

-- S04-model
#guard (match RlpEncode.toRlp (Hash32.ofBytes32 (FixedBytes.ofNat 1780731860627700044960722568376592200742329637303199754547598369979440671 : Bytes32)) with | .bytes b => b == ⟨#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]⟩ | .list _ => false)

-- S04-typed
#guard RlpDecode.ofRlp (α := Hash32) (.bytes ⟨#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]⟩) = (.ok (Hash32.ofBytes32 (FixedBytes.ofNat 1780731860627700044960722568376592200742329637303199754547598369979440671 : Bytes32)) : Except RlpError Hash32)

-- S04-wire
#guard encodeOf (Hash32.ofBytes32 (FixedBytes.ofNat 1780731860627700044960722568376592200742329637303199754547598369979440671 : Bytes32)) = ⟨#[160, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]⟩

-- S04-roundtrip
#guard decodeTo (α := Hash32) ⟨#[160, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]⟩ = (.ok (Hash32.ofBytes32 (FixedBytes.ofNat 1780731860627700044960722568376592200742329637303199754547598369979440671 : Bytes32)) : Except RlpError Hash32)

-- S05-model
#guard (match RlpEncode.toRlp (Hash32.ofBytes32 (FixedBytes.ofNat 450552876409790643671482431940419874915447411150352389258589821042463539455 : Bytes32)) with | .bytes b => b == ⟨#[0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255]⟩ | .list _ => false)

-- S05-typed
#guard RlpDecode.ofRlp (α := Hash32) (.bytes ⟨#[0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255]⟩) = (.ok (Hash32.ofBytes32 (FixedBytes.ofNat 450552876409790643671482431940419874915447411150352389258589821042463539455 : Bytes32)) : Except RlpError Hash32)

-- S05-wire
#guard encodeOf (Hash32.ofBytes32 (FixedBytes.ofNat 450552876409790643671482431940419874915447411150352389258589821042463539455 : Bytes32)) = ⟨#[160, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255]⟩

-- S05-roundtrip
#guard decodeTo (α := Hash32) ⟨#[160, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255]⟩ = (.ok (Hash32.ofBytes32 (FixedBytes.ofNat 450552876409790643671482431940419874915447411150352389258589821042463539455 : Bytes32)) : Except RlpError Hash32)

-- B00-typed
#guard RlpDecode.ofRlp (α := Hash32) (.bytes ⟨#[31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]⟩) = (.ok (Hash32.ofBytes32 (FixedBytes.ofNat 14074904626401341155369551180448584754667373453244490859944217516317499064576 : Bytes32)) : Except RlpError Hash32)

-- B00-wire
#guard decodeTo (α := Hash32) ⟨#[160, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]⟩ = (.ok (Hash32.ofBytes32 (FixedBytes.ofNat 14074904626401341155369551180448584754667373453244490859944217516317499064576 : Bytes32)) : Except RlpError Hash32)

-- B01-typed
#guard RlpDecode.ofRlp (α := Hash32) (.bytes ⟨#[128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) = (.ok (Hash32.ofBytes32 (FixedBytes.ofNat 57896044618658097711785492504343953926634992332820282019728792003956564819968 : Bytes32)) : Except RlpError Hash32)

-- B01-wire
#guard decodeTo (α := Hash32) ⟨#[160, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ = (.ok (Hash32.ofBytes32 (FixedBytes.ofNat 57896044618658097711785492504343953926634992332820282019728792003956564819968 : Bytes32)) : Except RlpError Hash32)

-- C00-model
#guard RlpDecode.ofRlp (α := Hash32) (.list []) = (.error (.shape "bytes") : Except RlpError Hash32)

-- C00-wire
#guard decodeTo (α := Hash32) ⟨#[192]⟩ = (.error (.shape "bytes") : Except RlpError Hash32)

-- C01-model
#guard RlpDecode.ofRlp (α := Hash32) (.list [.bytes ⟨#[0]⟩]) = (.error (.shape "bytes") : Except RlpError Hash32)

-- C01-wire
#guard decodeTo (α := Hash32) ⟨#[193, 0]⟩ = (.error (.shape "bytes") : Except RlpError Hash32)

-- C02-model
#guard RlpDecode.ofRlp (α := Hash32) (.list [.bytes ⟨#[]⟩]) = (.error (.shape "bytes") : Except RlpError Hash32)

-- C02-wire
#guard decodeTo (α := Hash32) ⟨#[193, 128]⟩ = (.error (.shape "bytes") : Except RlpError Hash32)

-- C03-model
#guard RlpDecode.ofRlp (α := Hash32) (.list [.list []]) = (.error (.shape "bytes") : Except RlpError Hash32)

-- C03-wire
#guard decodeTo (α := Hash32) ⟨#[193, 192]⟩ = (.error (.shape "bytes") : Except RlpError Hash32)

-- D00-model
#guard RlpDecode.ofRlp (α := Hash32) (.bytes ⟨#[]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- D00-wire
#guard decodeTo (α := Hash32) ⟨#[128]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- D01-model
#guard RlpDecode.ofRlp (α := Hash32) (.bytes ⟨#[0]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- D01-wire
#guard decodeTo (α := Hash32) ⟨#[0]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- D02-model
#guard RlpDecode.ofRlp (α := Hash32) (.bytes ⟨#[0, 0]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- D02-wire
#guard decodeTo (α := Hash32) ⟨#[130, 0, 0]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- D03-model
#guard RlpDecode.ofRlp (α := Hash32) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- D03-wire
#guard decodeTo (α := Hash32) ⟨#[147, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- D04-model
#guard RlpDecode.ofRlp (α := Hash32) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- D04-wire
#guard decodeTo (α := Hash32) ⟨#[148, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- D05-model
#guard RlpDecode.ofRlp (α := Hash32) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- D05-wire
#guard decodeTo (α := Hash32) ⟨#[149, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- D06-model
#guard RlpDecode.ofRlp (α := Hash32) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- D06-wire
#guard decodeTo (α := Hash32) ⟨#[159, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- D07-model
#guard RlpDecode.ofRlp (α := Hash32) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- D07-wire
#guard decodeTo (α := Hash32) ⟨#[161, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- D08-model
#guard RlpDecode.ofRlp (α := Hash32) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- D08-wire
#guard decodeTo (α := Hash32) ⟨#[183, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- D09-model
#guard RlpDecode.ofRlp (α := Hash32) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- D09-wire
#guard decodeTo (α := Hash32) ⟨#[184, 56, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- D10-model
#guard RlpDecode.ofRlp (α := Hash32) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- D10-wire
#guard decodeTo (α := Hash32) ⟨#[184, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- D11-model
#guard RlpDecode.ofRlp (α := Hash32) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- D11-wire
#guard decodeTo (α := Hash32) ⟨#[185, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- E00-model
#guard RlpDecode.ofRlp (α := Hash32) (.bytes ⟨#[1]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- E00-wire
#guard decodeTo (α := Hash32) ⟨#[1]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- E01-model
#guard RlpDecode.ofRlp (α := Hash32) (.bytes ⟨#[127]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- E01-wire
#guard decodeTo (α := Hash32) ⟨#[127]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- E02-model
#guard RlpDecode.ofRlp (α := Hash32) (.bytes ⟨#[128]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- E02-wire
#guard decodeTo (α := Hash32) ⟨#[129, 128]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- E03-model
#guard RlpDecode.ofRlp (α := Hash32) (.bytes ⟨#[255]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- E03-wire
#guard decodeTo (α := Hash32) ⟨#[129, 255]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- E04-model
#guard RlpDecode.ofRlp (α := Hash32) (.bytes ⟨#[0, 1]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- E04-wire
#guard decodeTo (α := Hash32) ⟨#[130, 0, 1]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- R00
#guard decodeTo (α := Hash32) ⟨#[]⟩ = (.error (.empty) : Except RlpError Hash32)

-- R01
#guard decodeTo (α := Hash32) ⟨#[5, 6]⟩ = (.error (.nonCanonical "negative length") : Except RlpError Hash32)

-- R02
#guard decodeTo (α := Hash32) ⟨#[129]⟩ = (.error (.truncated) : Except RlpError Hash32)

-- R03
#guard decodeTo (α := Hash32) ⟨#[130, 5]⟩ = (.error (.truncated) : Except RlpError Hash32)

-- R04
#guard decodeTo (α := Hash32) ⟨#[128, 0]⟩ = (.error (.trailing) : Except RlpError Hash32)

-- R05
#guard decodeTo (α := Hash32) ⟨#[129, 5]⟩ = (.error (.nonCanonical "prefixed single byte") : Except RlpError Hash32)

-- R06
#guard decodeTo (α := Hash32) ⟨#[185, 0, 64]⟩ = (.error (.nonCanonical "leading zero length") : Except RlpError Hash32)

-- R07
#guard decodeTo (α := Hash32) ⟨#[184, 5]⟩ = (.error (.nonCanonical "long form for short payload") : Except RlpError Hash32)

-- R08
#guard decodeTo (α := Hash32) ⟨#[184, 56]⟩ = (.error (.truncated) : Except RlpError Hash32)

-- R09
#guard decodeTo (α := Hash32) ⟨#[193]⟩ = (.error (.truncated) : Except RlpError Hash32)

-- R10
#guard decodeTo (α := Hash32) ⟨#[192, 0]⟩ = (.error (.trailing) : Except RlpError Hash32)

-- R11
#guard decodeTo (α := Hash32) ⟨#[193, 129]⟩ = (.error (.truncated) : Except RlpError Hash32)

-- X00
#guard decodeTo (α := Nat) ⟨#[160, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ = (.error (.nonCanonical "integer leading zero") : Except RlpError Nat)

-- X01
#guard decodeTo (α := ByteArray) ⟨#[160, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ = (.ok ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ : Except RlpError ByteArray)

-- X02
#guard decodeTo (α := Hash32) ⟨#[160, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ = (.ok (Hash32.ofBytes32 (FixedBytes.ofNat 0 : Bytes32)) : Except RlpError Hash32)

-- X03
#guard decodeTo (α := Hash32) ⟨#[128]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- X04
#guard RlpDecode.ofRlp (α := Hash32) (.bytes ⟨#[0, 1]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Hash32)

-- X05
#guard RlpDecode.ofRlp (α := Nat) (.bytes ⟨#[0, 1]⟩) = (.error (.nonCanonical "integer leading zero") : Except RlpError Nat)

-- X06
#guard RlpDecode.ofRlp (α := ByteArray) (.bytes ⟨#[0, 1]⟩) = (.ok ⟨#[0, 1]⟩ : Except RlpError ByteArray)

-- X07
#guard RlpDecode.ofRlp (α := Hash32) (.list []) = (.error (.shape "bytes") : Except RlpError Hash32)

end STFSpec.Conformance.Codec.RlpHash32Guards
