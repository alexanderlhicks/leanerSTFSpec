/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Derived address conformance cases

Library `EthConformance`. Complete fixed results and effect traces, arbitrary
answers, preserved errors and transformer forwarding. CREATE facts come from the
actual pinned address functions; CREATE2 facts are EIP-1014 examples 0–3
(https://eips.ethereum.org/EIPS/eip-1014#examples), also observed at the pin.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–4, 7.
-/

namespace STFSpec.Conformance.Codec.AddressGuards

open STFSpec.Base STFSpec.Hash STFSpec.Codec

private def sender : Address := Address.ofNat 0xdeadbeef00000000000000000000000000000000
private def salt : Bytes32 := FixedBytes.ofNat
  0x01020000000000000000000000000000000000000000000000000000000000ff
private def code : ByteArray := ⟨#[0, 128, 255, 0, 1]⟩
private def firstAnswer : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat
  0x8100000000000000000000000000000000000000000000000000000000000001)
private def otherFirst : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat
  0x8100000000000000000000000000000000000000000000000000000000000002)
private def finalAnswer : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat
  0xff0102030405060708090a0b00000102030405060708090a0b0c0d0e0f100000)
private def createPreimage : ByteArray :=
  Rlp.encode (.list [.bytes sender.toBytes.toByteArray, Rlp.ofNat 0])
private def outerPreimage (answer : Hash32) : ByteArray :=
  ⟨#[0xff]⟩ ++ sender.toBytes.toByteArray ++ salt.toBytes.toByteArray ++
    answer.toBytes.toByteArray
private def suffix : Bytes := Bytes.ofList
  [0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 0, 0]

private structure Trace where
  seen : List ByteArray := []
  supplied : List Hash32 := [firstAnswer, finalAnswer]
  failAt : Option Nat := none

private abbrev Recording := StateM Trace

private def record (b : ByteArray) : Recording Hash32 := fun s ↦
  match s.supplied with
  | [] => (finalAnswer, { s with seen := s.seen ++ [b] })
  | hash :: rest => (hash, { s with seen := s.seen ++ [b], supplied := rest })

local instance : KeccakQuery Recording where
  keccak := record

private def createCheck : Bool :=
  let (result, trace) := (computeContractAddressQ (m := Recording) sender 0).run
    { supplied := [finalAnswer] }
  result.toBytes == suffix && trace.seen == [createPreimage] && trace.supplied.isEmpty

private def create2Check (answer : Hash32) : Bool :=
  let (result, trace) := (computeCreate2ContractAddressQ (m := Recording) sender salt code).run
    { supplied := [answer, finalAnswer] }
  result.toBytes == suffix && trace.seen == [code, outerPreimage answer] &&
    trace.supplied.isEmpty

private def extraStateCheck : Bool :=
  let ((result, state), trace) :=
    ((computeCreate2ContractAddressQ (m := StateT Nat Recording) sender salt code).run 91).run {}
  result.toBytes == suffix && state == 91 && trace.seen == [code, outerPreimage firstAnswer]

private def extraExceptCheck : Bool :=
  let (result, trace) :=
    (computeCreate2ContractAddressQ (m := ExceptT String Recording) sender salt code).run.run {}
  (match result with | .ok address => address.toBytes == suffix | .error _ => false) &&
    trace.seen == [code, outerPreimage firstAnswer]

private def extraBothCheck : Bool :=
  let ((result, state), trace) :=
    ((computeCreate2ContractAddressQ (m := ExceptT String (StateT Nat Recording))
      sender salt code).run.run 91).run {}
  (match result with | .ok address => address.toBytes == suffix | .error _ => false) &&
    state == 91 && trace.seen == [code, outerPreimage firstAnswer]

private def failRecording (b : ByteArray) : ExceptT String Recording Hash32 := ExceptT.mk fun s ↦
  let (hash, next) := record b s
  if s.failAt = some s.seen.length then
    (.error (if s.seen.isEmpty then "first: original error" else "second: original error"), next)
  else (.ok hash, next)

section FailingOracle
local instance : KeccakQuery (ExceptT String Recording) where
  keccak := failRecording

private def failureCheck (n : Nat) : Bool :=
  let (result, trace) :=
    (computeCreate2ContractAddressQ (m := ExceptT String Recording) sender salt code).run.run
      { failAt := some n }
  (match result with
    | .error e => e == (if n == 0 then "first: original error" else "second: original error")
    | .ok _ => false) && trace.seen == [code, outerPreimage firstAnswer].take (n + 1)

private def createFailureCheck : Bool :=
  let (result, trace) :=
    (computeContractAddressQ (m := ExceptT String Recording) sender 0).run.run
      { failAt := some 0 }
  (match result with | .error e => e == "first: original error" | .ok _ => false) &&
    trace.seen == [createPreimage]

private def stateFailureCheck : Bool :=
  let (result, trace) :=
    ((computeCreate2ContractAddressQ (m := StateT Nat (ExceptT String Recording))
      sender salt code).run 91).run.run { failAt := some 0 }
  (match result with | .error e => e == "first: original error" | .ok _ => false) &&
    trace.seen == [code]

/-- Complete generic effect/result checks for the committed conformance guards. -/
def genericChecks : Bool := createCheck && create2Check firstAnswer && create2Check otherFirst &&
  (outerPreimage firstAnswer != outerPreimage otherFirst) && extraStateCheck &&
  extraExceptCheck && extraBothCheck && failureCheck 0 && failureCheck 1 &&
  createFailureCheck && stateFailureCheck

#guard genericChecks
end FailingOracle

-- Minimal nonce zero is empty; the exact RLP preimage ends in 80 rather than 00.
#guard createPreimage = ByteArray.mk
  ((([0xd6, 0x94, 0xde, 0xad, 0xbe, 0xef] : List UInt8) ++
    List.replicate 16 0 ++ [0x80]).toArray)
#guard finalAnswer.toBytes.toList.drop 12 = suffix.toList
#guard (Address.ofNat finalAnswer.toNat).toBytes = suffix
#guard (Address.ofNat finalAnswer.toNat).toBytes.size = 20

-- CREATE deterministic values from pinned EELS utils/address.py:42–63.
#guard (computeContractAddress sender 0).toBytes =
  (Address.ofNat 0xf2048c36a5536fea3bc71d49ed59f2c65c546eea).toBytes
#guard (computeContractAddress sender 1).toBytes =
  (Address.ofNat 0x054dd934335ea61232ae4c051f8bf20e540f8291).toBytes
#guard (computeContractAddress sender 2).toBytes =
  (Address.ofNat 0x91bf429534bc6b845f030c5e27a1566a7fe9724c).toBytes
#guard (computeContractAddress sender 3).toBytes =
  (Address.ofNat 0xeb4d964b77de426dd7838df90fa4fff12b475660).toBytes

-- Minimal-nonce width boundaries and unbounded Nat values, from the pinned function.
#guard (computeContractAddress sender 127).toBytes =
  (Address.ofNat 0x7feb088e1893d4a1087288d386c07252abb3c02e).toBytes
#guard (computeContractAddress sender 128).toBytes =
  (Address.ofNat 0x2297787b25b800d655071345a1d3a7951404b50c).toBytes
#guard (computeContractAddress sender 255).toBytes =
  (Address.ofNat 0xc8d17a8bdb6001525f8594e3ca4413d4bd644605).toBytes
#guard (computeContractAddress sender 256).toBytes =
  (Address.ofNat 0xa0ddf5980551b5ec83721bcf168785ac3cedb183).toBytes
#guard (computeContractAddress sender (2 ^ 64 - 1)).toBytes =
  (Address.ofNat 0x66e93872e94cc56d1da3bb63f81dabd9c1d6c125).toBytes
#guard (computeContractAddress sender (2 ^ 64)).toBytes =
  (Address.ofNat 0x253ae080cd8c1d7e12d26c35fb3a9fea9b13d210).toBytes
#guard (computeContractAddress sender (2 ^ 64 + 1)).toBytes =
  (Address.ofNat 0x663bb777d89459a0167a75d13dae548b20c14199).toBytes
#guard (computeContractAddress sender (2 ^ 128 - 1)).toBytes =
  (Address.ofNat 0xd622b083a35b6c92e042458b5b2f59c9201591c2).toBytes
#guard (computeContractAddress sender (2 ^ 128)).toBytes =
  (Address.ofNat 0xa1ced19532c6b9800aec130c5e5545f76a5a44a7).toBytes
#guard (computeContractAddress sender (2 ^ 256 - 1)).toBytes =
  (Address.ofNat 0xccc3628ff8af383753a6446481dc7c82c760dcff).toBytes
#guard (computeContractAddress sender (2 ^ 256)).toBytes =
  (Address.ofNat 0x292ebaf59b878f5ccc865987f10ba1a9989e0b85).toBytes
#guard (computeContractAddress sender (2 ^ 512)).toBytes =
  (Address.ofNat 0xa34e601e13c909f9ae93efbaff0332509700dbac).toBytes

-- Published CREATE2 examples 0–3. Every complete twenty-byte value is compared.
#guard (computeCreate2ContractAddress (Address.ofNat 0) (FixedBytes.ofNat 0) ⟨#[0]⟩).toBytes =
  (Address.ofNat 0x4d1a2e2bb4f88f0250f26ffff098b0b30b26bf38).toBytes
#guard (computeCreate2ContractAddress sender (FixedBytes.ofNat 0) ⟨#[0]⟩).toBytes =
  (Address.ofNat 0xb928f69bb1d91cd65274e3c79d8986362984fda3).toBytes
#guard (computeCreate2ContractAddress sender
  (FixedBytes.ofNat 0x000000000000000000000000feed000000000000000000000000000000000000)
  ⟨#[0]⟩).toBytes = (Address.ofNat 0xd04116cdd17bebe565eb2422f2497e06cc1c9833).toBytes
#guard (computeCreate2ContractAddress (Address.ofNat 0) (FixedBytes.ofNat 0)
  ⟨#[0xde, 0xad, 0xbe, 0xef]⟩).toBytes =
  (Address.ofNat 0x70f2b2914a2a4b783faefb75f459a580616fcb5e).toBytes

end STFSpec.Conformance.Codec.AddressGuards
