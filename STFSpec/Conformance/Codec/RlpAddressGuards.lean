/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Address RLP complete controls

Library `EthConformance`. Exactly 90 complete handwritten outcomes preserve
nominal values, every byte, complete wires and ordered diagnostics. Finite
expected addresses use the public scalar constructor; each positive model
control also checks the complete public checked-byte construction.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/

namespace STFSpec.Conformance.Codec.RlpAddressGuards
open STFSpec.Codec STFSpec.Codec.Rlp STFSpec.Base

private local instance {α : Type} [DecidableEq α] : DecidableEq (Except RlpError α) := by
  intro a b
  cases a <;> cases b <;>
    simp only [Except.ok.injEq, Except.error.injEq, reduceCtorEq] <;> infer_instance

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- S00-model
#guard Address.ofBytes? (Bytes.ofByteArray ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) = some (Address.ofNat 0) ∧
  ((match RlpEncode.toRlp (Address.ofNat 0) with | .bytes b => b == ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ | .list _ => false) = true)

-- S00-typed
#guard RlpDecode.ofRlp (α := Address) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) = (.ok (Address.ofNat 0) : Except RlpError Address)

-- S00-wire
#guard encodeOf (Address.ofNat 0) = ⟨#[148, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

-- S00-roundtrip
#guard decodeTo (α := Address) ⟨#[148, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ = (.ok (Address.ofNat 0) : Except RlpError Address)

-- S01-model
#guard Address.ofBytes? (Bytes.ofByteArray ⟨#[255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]⟩) = some (Address.ofNat 1461501637330902918203684832716283019655932542975) ∧
  ((match RlpEncode.toRlp (Address.ofNat 1461501637330902918203684832716283019655932542975) with | .bytes b => b == ⟨#[255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]⟩ | .list _ => false) = true)

-- S01-typed
#guard RlpDecode.ofRlp (α := Address) (.bytes ⟨#[255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]⟩) = (.ok (Address.ofNat 1461501637330902918203684832716283019655932542975) : Except RlpError Address)

-- S01-wire
#guard encodeOf (Address.ofNat 1461501637330902918203684832716283019655932542975) = ⟨#[148, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]⟩

-- S01-roundtrip
#guard decodeTo (α := Address) ⟨#[148, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]⟩ = (.ok (Address.ofNat 1461501637330902918203684832716283019655932542975) : Except RlpError Address)

-- S02-model
#guard Address.ofBytes? (Bytes.ofByteArray ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩) = some (Address.ofNat 1) ∧
  ((match RlpEncode.toRlp (Address.ofNat 1) with | .bytes b => b == ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩ | .list _ => false) = true)

-- S02-typed
#guard RlpDecode.ofRlp (α := Address) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩) = (.ok (Address.ofNat 1) : Except RlpError Address)

-- S02-wire
#guard encodeOf (Address.ofNat 1) = ⟨#[148, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩

-- S02-roundtrip
#guard decodeTo (α := Address) ⟨#[148, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩ = (.ok (Address.ofNat 1) : Except RlpError Address)

-- S03-model
#guard Address.ofBytes? (Bytes.ofByteArray ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255]⟩) = some (Address.ofNat 5708990770823839524233143877797980545530986751) ∧
  ((match RlpEncode.toRlp (Address.ofNat 5708990770823839524233143877797980545530986751) with | .bytes b => b == ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255]⟩ | .list _ => false) = true)

-- S03-typed
#guard RlpDecode.ofRlp (α := Address) (.bytes ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255]⟩) = (.ok (Address.ofNat 5708990770823839524233143877797980545530986751) : Except RlpError Address)

-- S03-wire
#guard encodeOf (Address.ofNat 5708990770823839524233143877797980545530986751) = ⟨#[148, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255]⟩

-- S03-roundtrip
#guard decodeTo (α := Address) ⟨#[148, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255]⟩ = (.ok (Address.ofNat 5708990770823839524233143877797980545530986751) : Except RlpError Address)

-- S04-model
#guard Address.ofBytes? (Bytes.ofByteArray ⟨#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]⟩) = some (Address.ofNat 22475995960490625424124334220934763854762515) ∧
  ((match RlpEncode.toRlp (Address.ofNat 22475995960490625424124334220934763854762515) with | .bytes b => b == ⟨#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]⟩ | .list _ => false) = true)

-- S04-typed
#guard RlpDecode.ofRlp (α := Address) (.bytes ⟨#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]⟩) = (.ok (Address.ofNat 22475995960490625424124334220934763854762515) : Except RlpError Address)

-- S04-wire
#guard encodeOf (Address.ofNat 22475995960490625424124334220934763854762515) = ⟨#[148, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]⟩

-- S04-roundtrip
#guard decodeTo (α := Address) ⟨#[148, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]⟩ = (.ok (Address.ofNat 22475995960490625424124334220934763854762515) : Except RlpError Address)

-- S05-model
#guard Address.ofBytes? (Bytes.ofByteArray ⟨#[0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255]⟩) = some (Address.ofNat 5686776798952929642815894290724836652357714175) ∧
  ((match RlpEncode.toRlp (Address.ofNat 5686776798952929642815894290724836652357714175) with | .bytes b => b == ⟨#[0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255]⟩ | .list _ => false) = true)

-- S05-typed
#guard RlpDecode.ofRlp (α := Address) (.bytes ⟨#[0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255]⟩) = (.ok (Address.ofNat 5686776798952929642815894290724836652357714175) : Except RlpError Address)

-- S05-wire
#guard encodeOf (Address.ofNat 5686776798952929642815894290724836652357714175) = ⟨#[148, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255]⟩

-- S05-roundtrip
#guard decodeTo (α := Address) ⟨#[148, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255]⟩ = (.ok (Address.ofNat 5686776798952929642815894290724836652357714175) : Except RlpError Address)

-- B00-typed
#guard Address.ofBytes? (Bytes.ofByteArray ⟨#[19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]⟩) = some (Address.ofNat 108873724432616589554458274966207996112469623040) ∧
  RlpDecode.ofRlp (α := Address) (.bytes ⟨#[19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]⟩) = (.ok (Address.ofNat 108873724432616589554458274966207996112469623040) : Except RlpError Address)

-- B00-wire
#guard decodeTo (α := Address) ⟨#[148, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]⟩ = (.ok (Address.ofNat 108873724432616589554458274966207996112469623040) : Except RlpError Address)

-- B01-typed
#guard Address.ofBytes? (Bytes.ofByteArray ⟨#[128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) = some (Address.ofNat 730750818665451459101842416358141509827966271488) ∧
  RlpDecode.ofRlp (α := Address) (.bytes ⟨#[128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) = (.ok (Address.ofNat 730750818665451459101842416358141509827966271488) : Except RlpError Address)

-- B01-wire
#guard decodeTo (α := Address) ⟨#[148, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ = (.ok (Address.ofNat 730750818665451459101842416358141509827966271488) : Except RlpError Address)

-- C00-model
#guard RlpDecode.ofRlp (α := Address) (.list []) = (.error (.shape "bytes") : Except RlpError Address)

-- C00-wire
#guard decodeTo (α := Address) ⟨#[192]⟩ = (.error (.shape "bytes") : Except RlpError Address)

-- C01-model
#guard RlpDecode.ofRlp (α := Address) (.list [.bytes ⟨#[0]⟩]) = (.error (.shape "bytes") : Except RlpError Address)

-- C01-wire
#guard decodeTo (α := Address) ⟨#[193, 0]⟩ = (.error (.shape "bytes") : Except RlpError Address)

-- C02-model
#guard RlpDecode.ofRlp (α := Address) (.list [.bytes ⟨#[]⟩]) = (.error (.shape "bytes") : Except RlpError Address)

-- C02-wire
#guard decodeTo (α := Address) ⟨#[193, 128]⟩ = (.error (.shape "bytes") : Except RlpError Address)

-- C03-model
#guard RlpDecode.ofRlp (α := Address) (.list [.list []]) = (.error (.shape "bytes") : Except RlpError Address)

-- C03-wire
#guard decodeTo (α := Address) ⟨#[193, 192]⟩ = (.error (.shape "bytes") : Except RlpError Address)

-- D00-model
#guard RlpDecode.ofRlp (α := Address) (.bytes ⟨#[]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- D00-wire
#guard decodeTo (α := Address) ⟨#[128]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- D01-model
#guard RlpDecode.ofRlp (α := Address) (.bytes ⟨#[0]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- D01-wire
#guard decodeTo (α := Address) ⟨#[0]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- D02-model
#guard RlpDecode.ofRlp (α := Address) (.bytes ⟨#[0, 0]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- D02-wire
#guard decodeTo (α := Address) ⟨#[130, 0, 0]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- D03-model
#guard RlpDecode.ofRlp (α := Address) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- D03-wire
#guard decodeTo (α := Address) ⟨#[136, 0, 0, 0, 0, 0, 0, 0, 0]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- D04-model
#guard RlpDecode.ofRlp (α := Address) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- D04-wire
#guard decodeTo (α := Address) ⟨#[147, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- D05-model
#guard RlpDecode.ofRlp (α := Address) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- D05-wire
#guard decodeTo (α := Address) ⟨#[149, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- D06-model
#guard RlpDecode.ofRlp (α := Address) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- D06-wire
#guard decodeTo (α := Address) ⟨#[159, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- D07-model
#guard RlpDecode.ofRlp (α := Address) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- D07-wire
#guard decodeTo (α := Address) ⟨#[160, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- D08-model
#guard RlpDecode.ofRlp (α := Address) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- D08-wire
#guard decodeTo (α := Address) ⟨#[183, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- D09-model
#guard RlpDecode.ofRlp (α := Address) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- D09-wire
#guard decodeTo (α := Address) ⟨#[184, 56, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- D10-model
#guard RlpDecode.ofRlp (α := Address) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- D10-wire
#guard decodeTo (α := Address) ⟨#[184, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- D11-model
#guard RlpDecode.ofRlp (α := Address) (.bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- D11-wire
#guard decodeTo (α := Address) ⟨#[185, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- E00-model
#guard RlpDecode.ofRlp (α := Address) (.bytes ⟨#[1]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- E00-wire
#guard decodeTo (α := Address) ⟨#[1]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- E01-model
#guard RlpDecode.ofRlp (α := Address) (.bytes ⟨#[127]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- E01-wire
#guard decodeTo (α := Address) ⟨#[127]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- E02-model
#guard RlpDecode.ofRlp (α := Address) (.bytes ⟨#[128]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- E02-wire
#guard decodeTo (α := Address) ⟨#[129, 128]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- E03-model
#guard RlpDecode.ofRlp (α := Address) (.bytes ⟨#[255]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- E03-wire
#guard decodeTo (α := Address) ⟨#[129, 255]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- E04-model
#guard RlpDecode.ofRlp (α := Address) (.bytes ⟨#[0, 1]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- E04-wire
#guard decodeTo (α := Address) ⟨#[130, 0, 1]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- R00
#guard decodeTo (α := Address) ⟨#[]⟩ = (.error (.empty) : Except RlpError Address)

-- R01
#guard decodeTo (α := Address) ⟨#[5, 6]⟩ = (.error (.nonCanonical "negative length") : Except RlpError Address)

-- R02
#guard decodeTo (α := Address) ⟨#[129]⟩ = (.error (.truncated) : Except RlpError Address)

-- R03
#guard decodeTo (α := Address) ⟨#[130, 5]⟩ = (.error (.truncated) : Except RlpError Address)

-- R04
#guard decodeTo (α := Address) ⟨#[128, 0]⟩ = (.error (.trailing) : Except RlpError Address)

-- R05
#guard decodeTo (α := Address) ⟨#[129, 5]⟩ = (.error (.nonCanonical "prefixed single byte") : Except RlpError Address)

-- R06
#guard decodeTo (α := Address) ⟨#[185, 0, 64]⟩ = (.error (.nonCanonical "leading zero length") : Except RlpError Address)

-- R07
#guard decodeTo (α := Address) ⟨#[184, 5]⟩ = (.error (.nonCanonical "long form for short payload") : Except RlpError Address)

-- R08
#guard decodeTo (α := Address) ⟨#[184, 56]⟩ = (.error (.truncated) : Except RlpError Address)

-- R09
#guard decodeTo (α := Address) ⟨#[193]⟩ = (.error (.truncated) : Except RlpError Address)

-- R10
#guard decodeTo (α := Address) ⟨#[192, 0]⟩ = (.error (.trailing) : Except RlpError Address)

-- R11
#guard decodeTo (α := Address) ⟨#[193, 129]⟩ = (.error (.truncated) : Except RlpError Address)

-- X00
#guard decodeTo (α := Nat) ⟨#[148, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ = (.error (.nonCanonical "integer leading zero") : Except RlpError Nat)

-- X01
#guard decodeTo (α := ByteArray) ⟨#[148, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ = (.ok ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ : Except RlpError ByteArray)

-- X02
#guard decodeTo (α := Address) ⟨#[148, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ = (.ok (Address.ofNat 0) : Except RlpError Address)

-- X03
#guard decodeTo (α := Address) ⟨#[128]⟩ = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- X04
#guard RlpDecode.ofRlp (α := Address) (.bytes ⟨#[0, 1]⟩) = (.error (.shape "fixed bytes length") : Except RlpError Address)

-- X05
#guard RlpDecode.ofRlp (α := Nat) (.bytes ⟨#[0, 1]⟩) = (.error (.nonCanonical "integer leading zero") : Except RlpError Nat)

-- X06
#guard RlpDecode.ofRlp (α := ByteArray) (.bytes ⟨#[0, 1]⟩) = (.ok ⟨#[0, 1]⟩ : Except RlpError ByteArray)

-- X07
#guard RlpDecode.ofRlp (α := Address) (.list []) = (.error (.shape "bytes") : Except RlpError Address)

end STFSpec.Conformance.Codec.RlpAddressGuards
