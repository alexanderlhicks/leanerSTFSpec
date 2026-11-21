/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateWitness

/-!
# Witness code database controls

Library `EthConformance`. Compare complete tables against the pinned EELS
`build_code_db` at `src/ethereum/forks/amsterdam/witness_state.py:33–35`.
A stateful oracle checks query order and replacement on equal answers.
Spec guidance: `STFSpec/informal/modules/EthStateWitness.md` §§3–4.
-/

namespace STFSpec.Conformance.StateWitness.CodeDBGuards

open STFSpec.Base STFSpec.Hash STFSpec.StateWitness

private def hash (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)

private def tableMatches (db : CodeDB) (expected : List (Hash32 × ByteArray)) : Bool :=
  db.map.size == expected.length &&
    expected.all (fun (key, code) ↦ db.map[key]?.map ByteArray.toList == some code.toList)

private def matchesEels (codes : Array ByteArray) :
    List (Hash32 × ByteArray) → Bool :=
  tableMatches (Id.run (CodeDB.build codes))

private def emptyCodeHash : Hash32 :=
  hash 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470

private def code136 : ByteArray := ⟨(Array.range 136).map UInt8.ofNat⟩
private def code137 : ByteArray := ⟨(Array.range 137).map UInt8.ofNat⟩

#guard matchesEels #[] []
#guard matchesEels #[ByteArray.empty] [(emptyCodeHash, ByteArray.empty)]
#guard matchesEels #[⟨#[0x00, 0xff]⟩]
  [(hash 0x0050c0bb1a7f44340fff58dc7250ec88a127ad18267a1cadbb0839d5d67566d8, ⟨#[0x00, 0xff]⟩)]
#guard matchesEels #[⟨#[0xff, 0x00]⟩, ByteArray.empty, ⟨#[0xff, 0x00]⟩]
  [(hash 0x73e691d6019a2f1431d7452655e04e0ffdb11b392d7d8907b8b2af455b002ee5, ⟨#[0xff, 0x00]⟩),
   (emptyCodeHash, ByteArray.empty)]
#guard matchesEels #[code136, code137, code136]
  [(hash 0x7ce759f1ab7f9ce437719970c26b0a66ff11fe3e38e17df89cf5d29c7d7f807e, code136),
   (hash 0xac73d4fae68b8453f764007c1a20ce95994187861f0c3227a3a8e99a73a3b1db, code137)]
#guard matchesEels #[⟨#[0x00]⟩, ⟨#[0xff]⟩, ⟨#[0x00, 0x00]⟩, ⟨#[0xff]⟩]
  [(hash 0xbc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a, ⟨#[0x00]⟩),
   (hash 0x8b1a944cf13a9a1c08facb2c9e98623ef3254d2ddb48113885c3e8e97fec8db9, ⟨#[0xff]⟩),
   (hash 0x54a8c0ab653c15bfb48b47fd011ba2b9617af01cb45cab344acd57c924d56798, ⟨#[0x00, 0x00]⟩)]

private def shortKey : Hash32 := hash 17
private def longKey : Hash32 := hash 29
private abbrev Trace := StateM (List (List UInt8))

private instance : KeccakQuery Trace where
  keccak code := fun observations ↦
    (if code.size ≤ 1 then shortKey else longKey, observations ++ [code.toList])

private def sample : Array ByteArray :=
  #[ByteArray.empty, ⟨#[13, 17]⟩, ⟨#[9]⟩, ⟨#[13, 17]⟩]

private def observed : CodeDB × List (List UInt8) :=
  (CodeDB.build (m := Trace) sample).run []

#guard tableMatches observed.1 [(shortKey, ⟨#[9]⟩), (longKey, ⟨#[13, 17]⟩)]
#guard observed.2 == [[], [13, 17], [9], [13, 17]]

private def observedEmpty : CodeDB × List (List UInt8) :=
  (CodeDB.build (m := Trace) #[]).run [[255]]

#guard tableMatches observedEmpty.1 []
#guard observedEmpty.2 == [[255]]

end STFSpec.Conformance.StateWitness.CodeDBGuards
