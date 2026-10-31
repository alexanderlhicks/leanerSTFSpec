/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block
import Lean

/-!
# Complete ordered logsBloom observations

Library `EthConformance`. Private controls preserve exact public inputs, complete
256-byte outputs and actual oracle traces. The independent literal catalogue retains
20 source cases and synthetic state/failure controls frozen before target observation.
The zero-address/zero-topic anchor is independently derived and source checked;
no historical EIP vector attribution or cryptographic correctness claim is made.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3/4/7.
-/

set_option maxRecDepth 10000

open STFSpec.Block STFSpec.Base STFSpec.Hash STFSpec.Vm.Core Lean

private def digit (n : Nat) : Char := Char.ofNat (if n < 10 then 48 + n else 87 + n)
private def hex (data : ByteArray) : String :=
  String.ofList (data.data.toList.flatMap fun b ↦ [digit (b.toNat / 16), digit (b.toNat % 16)])
private def nibble (c : Char) : Except String Nat :=
  if '0' ≤ c ∧ c ≤ '9' then .ok (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then .ok (c.toNat - 87)
  else .error "noncanonical input hex"
private def unhex : List Char → Except String (List UInt8)
  | [] => .ok []
  | a :: b :: rest => do
    let x ← nibble a
    let y ← nibble b
    return UInt8.ofNat (16 * x + y) :: (← unhex rest)
  | [_] => .error "odd input hex"
private def bytes (s : String) : Except String Bytes := do
  return Bytes.ofList (← unhex s.toList)
private def requireSome {α : Type} (value : Option α) : Except String α :=
  match value with
  | some a => .ok a
  | none => .error "fixture width differs"
private def parseHash (s : String) : Except String Hash32 := do
  requireSome (Hash32.ofBytes? (← bytes s))
private abbrev LogText := String × Array String × String
private def parseLog (l : LogText) : Except String Log := do
  let address ← requireSome (Address.ofBytes? (← bytes l.1))
  let topics ← l.2.1.mapM parseHash
  let data ← bytes l.2.2
  return ⟨address, topics, data⟩
private structure Sample where
  name : String
  stack : String
  action : String
  split : Nat
  logs : Array Log
  calls : Array (Array Log)
  answers : Array Hash32
  failureAt : Option Nat
  errorToken : Option String
private def sample (name stack action : String) (split : Nat) (logs : Array LogText)
    (calls : Array (Array LogText)) (answers : Array String) (failureAt : Option Nat)
    (errorToken : Option String) : Except String Sample := do
  return ⟨name, stack, action, split, ← logs.mapM parseLog,
    ← calls.mapM (fun ls ↦ ls.mapM parseLog), ← answers.mapM parseHash, failureAt, errorToken⟩
private structure Query where
  preimage : ByteArray
  digest : Option Hash32
private structure OracleState where
  config : Sample
  cursor : Nat := 0
  trace : Array Query := #[]
private abbrev KeepM := ExceptT String (StateT OracleState Id)
private def answer (s : OracleState) (preimage : ByteArray) : Except String Hash32 :=
  if s.config.failureAt == some s.cursor then
    .error (s.config.errorToken.getD "missing supplied error")
  else if s.config.stack == "real" then .ok (KeccakQuery.keccak (m := Id) preimage)
  else match s.config.answers[s.cursor]? with
    | some h => .ok h
    | none => .error "synthetic answer schedule exhausted"
private instance : KeccakQuery KeepM where
  keccak preimage := ExceptT.mk fun s ↦
    let result := answer s preimage
    let query : Query := ⟨preimage, result.toOption⟩
    (result, {s with cursor := s.cursor + 1, trace := s.trace.push query})
-- This stack loses its inner state on error; a separate bottom observer retains the
-- actual attempted query prefix, including the failing query with no digest answer.
private abbrev DropM := StateT OracleState (ExceptT String (StateT (Array Query) Id))
private instance : KeccakQuery DropM where
  keccak preimage := fun s ↦ ExceptT.mk fun trace ↦
    let result := answer s preimage
    let query : Query := ⟨preimage, result.toOption⟩
    let state := {s with cursor := s.cursor + 1}
    (result.map (fun h ↦ (h, state)), trace.push query)
private abbrev ForwardM := StateT Nat KeepM
private def runCalls {m : Type → Type} [Monad m] [KeccakQuery m]
    (c : Sample) (restart : m Unit) : m Bloom := do
  let mut result : Bloom := FixedBytes.ofNat 0
  let mut i := 0
  for call in c.calls do
    if i > 0 && c.action == "reset" then restart
    let actual ← logsBloom call
    i := i + 1
    result := FixedBytes.ofNat (result.toNat ||| actual.toNat)
  return result
private def restartKeep : KeepM Unit := do
  modify fun s ↦ {s with cursor := 0}
private def restartDrop : DropM Unit := do
  modify fun s ↦ {s with cursor := 0}
private def restartForward : ForwardM Unit := do
  liftM restartKeep
private structure Observation where
  result : Except String Bloom
  trace : Option (Array Query)
  cursor : Option Nat
  layerState : Option Nat := none
private def observe (c : Sample) : Observation :=
  if c.stack == "id" then
    ⟨.ok (logsBloom (m := Id) c.logs), none, none, none⟩
  else if c.stack == "state-except" then
    let (value, trace) := (((runCalls (m := DropM) c restartDrop).run {config := c}).run).run #[]
    match value with
    | .error e => ⟨.error e, some trace, none, none⟩
    | .ok (b, s) => ⟨.ok b, some trace, some s.cursor, none⟩
  else if c.stack == "forward" then
    let (value, s) := (((runCalls (m := ForwardM) c restartForward).run 73).run).run {config := c}
    match value with
    | .error e => ⟨.error e, some s.trace, some s.cursor, none⟩
    | .ok (b, outer) => ⟨.ok b, some s.trace, some s.cursor, some outer⟩
  else
    let (value, s) := ((runCalls (m := KeepM) c restartKeep).run).run {config := c}
    ⟨value, some s.trace, some s.cursor, none⟩
private def logJson (l : Log) : Json := Json.mkObj [
  ("address", toJson (hex l.address.toBytes.toByteArray)),
  ("topics", toJson (l.topics.map fun h ↦ hex h.toBytes.toByteArray)),
  ("data", toJson (hex l.data.toByteArray))]
private def traceJson (q : Query) : Json := Json.mkObj [
  ("preimage", toJson (hex q.preimage)),
  ("digest", toJson (q.digest.map fun h ↦ hex h.toBytes.toByteArray))]
private def observationJson (c : Sample) (o : Observation) : Json := Json.mkObj [
  ("kind", toJson "case"), ("name", toJson c.name), ("stack", toJson c.stack),
  ("action", toJson c.action), ("split", toJson c.split),
  ("logs", .arr (c.logs.map logJson)),
  ("calls", .arr (c.calls.map fun ls ↦ .arr (ls.map logJson))),
  ("answers", toJson (c.answers.map fun h ↦ hex h.toBytes.toByteArray)),
  ("failure_at", toJson c.failureAt), ("error_token", toJson c.errorToken),
  ("result", toJson (o.result.toOption.map fun b ↦ hex b.toBytes.toByteArray)),
  ("error", toJson (match o.result with | .error e => some e | .ok _ => none)),
  ("trace", match o.trace with | none => .null | some t => .arr (t.map traceJson)),
  ("query_count", toJson (o.trace.map Array.size)),
  ("cursor", toJson o.cursor), ("layer_state", toJson o.layerState)]

private def emit (value : Json) : IO Unit := do (← IO.getStdout).putStrLn value.compress
private def emitCase (input : Except String Sample) : IO Unit := do
  let c ← IO.ofExcept input
  emit (observationJson c (observe c))

/-- Emit complete actual public calls, results, attempted queries and original errors. -/
def main : IO UInt32 := do
  try
    emit (Json.mkObj [("schema", toJson "logs-bloom-v1"), ("catalog", toJson
      "6fe020501102507a348d249da59332a822f691a867279e1153f092249a91160a"), ("count", toJson (112 :
      Nat)), ("source_count", toJson (20 : Nat)), ("source_query_count", toJson (85 : Nat)),
      ("synthetic_count", toJson (72 : Nat))])
    emitCase (sample "source/empty/id" "id" "single" 0
    #[]
    #[#[]]
    #[] none none)
    emitCase (sample "source/empty/logged" "real" "single" 0
    #[]
    #[#[]]
    #[] none none)
    emitCase (sample "source/zero_address/id" "id" "single" 0
    #[("0000000000000000000000000000000000000000", #[], "")]
    #[#[("0000000000000000000000000000000000000000", #[], "")]]
    #["5380c7b7ae81a58eb98d9c78de4a1fd7fd9535fc953ed2be602daaa41767312a"] none none)
    emitCase (sample "source/zero_address/logged" "real" "single" 0
    #[("0000000000000000000000000000000000000000", #[], "")]
    #[#[("0000000000000000000000000000000000000000", #[], "")]]
    #["5380c7b7ae81a58eb98d9c78de4a1fd7fd9535fc953ed2be602daaa41767312a"] none none)
    emitCase (sample "source/ramp_address/id" "id" "single" 0
    #[("000102030405060708090a0b0c0d0e0f10111213", #[], "")]
    #[#[("000102030405060708090a0b0c0d0e0f10111213", #[], "")]]
    #["27de39f50eaf89fe36fa279026a22605711fde9c16c0f23ae2c3e9faf4eed6ae"] none none)
    emitCase (sample "source/ramp_address/logged" "real" "single" 0
    #[("000102030405060708090a0b0c0d0e0f10111213", #[], "")]
    #[#[("000102030405060708090a0b0c0d0e0f10111213", #[], "")]]
    #["27de39f50eaf89fe36fa279026a22605711fde9c16c0f23ae2c3e9faf4eed6ae"] none none)
    emitCase (sample "source/leading_zero_address/id" "id" "single" 0
    #[("0000000000000000000000000000000000000001", #[], "")]
    #[#[("0000000000000000000000000000000000000001", #[], "")]]
    #["1468288056310c82aa4c01a7e12a10f8111a0560e72b700555479031b86c357d"] none none)
    emitCase (sample "source/leading_zero_address/logged" "real" "single" 0
    #[("0000000000000000000000000000000000000001", #[], "")]
    #[#[("0000000000000000000000000000000000000001", #[], "")]]
    #["1468288056310c82aa4c01a7e12a10f8111a0560e72b700555479031b86c357d"] none none)
    emitCase (sample "source/asymmetric_address/id" "id" "single" 0
    #[("fedcba98765432100123456789abcdef10203040", #[], "")]
    #[#[("fedcba98765432100123456789abcdef10203040", #[], "")]]
    #["7097639c3dad0d0e37a840f69d43b5a65ea37e6319b881ad3dd6b5ba54b2d642"] none none)
    emitCase (sample "source/asymmetric_address/logged" "real" "single" 0
    #[("fedcba98765432100123456789abcdef10203040", #[], "")]
    #[#[("fedcba98765432100123456789abcdef10203040", #[], "")]]
    #["7097639c3dad0d0e37a840f69d43b5a65ea37e6319b881ad3dd6b5ba54b2d642"] none none)
    emitCase (sample "source/ff_address/id" "id" "single" 0
    #[("ffffffffffffffffffffffffffffffffffffffff", #[], "")]
    #[#[("ffffffffffffffffffffffffffffffffffffffff", #[], "")]]
    #["d3b5b90cebf74d639049264c331b8cfaadb9a1b2ec320816b39e30081310200a"] none none)
    emitCase (sample "source/ff_address/logged" "real" "single" 0
    #[("ffffffffffffffffffffffffffffffffffffffff", #[], "")]
    #[#[("ffffffffffffffffffffffffffffffffffffffff", #[], "")]]
    #["d3b5b90cebf74d639049264c331b8cfaadb9a1b2ec320816b39e30081310200a"] none none)
    emitCase (sample "source/zero_address_zero_topic/id" "id" "single" 0
    #[("0000000000000000000000000000000000000000",
      #["0000000000000000000000000000000000000000000000000000000000000000"], "")]
    #[#[("0000000000000000000000000000000000000000",
      #["0000000000000000000000000000000000000000000000000000000000000000"], "")]]
    #["5380c7b7ae81a58eb98d9c78de4a1fd7fd9535fc953ed2be602daaa41767312a",
      "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563"] none none)
    emitCase (sample "source/zero_address_zero_topic/logged" "real" "single" 0
    #[("0000000000000000000000000000000000000000",
      #["0000000000000000000000000000000000000000000000000000000000000000"], "")]
    #[#[("0000000000000000000000000000000000000000",
      #["0000000000000000000000000000000000000000000000000000000000000000"], "")]]
    #["5380c7b7ae81a58eb98d9c78de4a1fd7fd9535fc953ed2be602daaa41767312a",
      "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563"] none none)
    emitCase (sample "source/leading_zero_topic/id" "id" "single" 0
    #[("0000000000000000000000000000000000000001",
      #["0000000000000000000000000000000000000000000000000000000000000001"], "")]
    #[#[("0000000000000000000000000000000000000001",
      #["0000000000000000000000000000000000000000000000000000000000000001"], "")]]
    #["1468288056310c82aa4c01a7e12a10f8111a0560e72b700555479031b86c357d",
      "b10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6"] none none)
    emitCase (sample "source/leading_zero_topic/logged" "real" "single" 0
    #[("0000000000000000000000000000000000000001",
      #["0000000000000000000000000000000000000000000000000000000000000001"], "")]
    #[#[("0000000000000000000000000000000000000001",
      #["0000000000000000000000000000000000000000000000000000000000000001"], "")]]
    #["1468288056310c82aa4c01a7e12a10f8111a0560e72b700555479031b86c357d",
      "b10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6"] none none)
    emitCase (sample "source/asymmetric_one_topic/id" "id" "single" 0
    #[("fedcba98765432100123456789abcdef10203040",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"], "deadbeef")]
    #[#[("fedcba98765432100123456789abcdef10203040",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"], "deadbeef")]]
    #["7097639c3dad0d0e37a840f69d43b5a65ea37e6319b881ad3dd6b5ba54b2d642",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d"] none none)
    emitCase (sample "source/asymmetric_one_topic/logged" "real" "single" 0
    #[("fedcba98765432100123456789abcdef10203040",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"], "deadbeef")]
    #[#[("fedcba98765432100123456789abcdef10203040",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"], "deadbeef")]]
    #["7097639c3dad0d0e37a840f69d43b5a65ea37e6319b881ad3dd6b5ba54b2d642",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d"] none none)
    emitCase (sample "source/four_topics/id" "id" "single" 0
    #[("000102030405060708090a0b0c0d0e0f10111213",
      #["0000000000000000000000000000000000000000000000000000000000000000",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "00ff")]
    #[#[("000102030405060708090a0b0c0d0e0f10111213",
      #["0000000000000000000000000000000000000000000000000000000000000000",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "00ff")]]
    #["27de39f50eaf89fe36fa279026a22605711fde9c16c0f23ae2c3e9faf4eed6ae",
      "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563",
      "b10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d",
      "bdd02ebb570629bab919a9b18a336dbb16a314880a4b031dcf6e2a0a8f527516"] none none)
    emitCase (sample "source/four_topics/logged" "real" "single" 0
    #[("000102030405060708090a0b0c0d0e0f10111213",
      #["0000000000000000000000000000000000000000000000000000000000000000",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "00ff")]
    #[#[("000102030405060708090a0b0c0d0e0f10111213",
      #["0000000000000000000000000000000000000000000000000000000000000000",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "00ff")]]
    #["27de39f50eaf89fe36fa279026a22605711fde9c16c0f23ae2c3e9faf4eed6ae",
      "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563",
      "b10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d",
      "bdd02ebb570629bab919a9b18a336dbb16a314880a4b031dcf6e2a0a8f527516"] none none)
    emitCase (sample "source/six_topics/id" "id" "single" 0
    #[("fedcba98765432100123456789abcdef10203040",
      #["0000000000000000000000000000000000000000000000000000000000000000",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100",
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
      "80000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d01"], "012345")]
    #[#[("fedcba98765432100123456789abcdef10203040",
      #["0000000000000000000000000000000000000000000000000000000000000000",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100",
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
      "80000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d01"], "012345")]]
    #["7097639c3dad0d0e37a840f69d43b5a65ea37e6319b881ad3dd6b5ba54b2d642",
      "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563",
      "b10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d",
      "bdd02ebb570629bab919a9b18a336dbb16a314880a4b031dcf6e2a0a8f527516",
      "a9c584056064687e149968cbab758a3376d22aedc6a55823d1b3ecbee81b8fb9",
      "cf5738ffbc98d303de66786ffc2a338e7940a06a7283aabe5e21b0b23f482221"] none none)
    emitCase (sample "source/six_topics/logged" "real" "single" 0
    #[("fedcba98765432100123456789abcdef10203040",
      #["0000000000000000000000000000000000000000000000000000000000000000",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100",
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
      "80000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d01"], "012345")]
    #[#[("fedcba98765432100123456789abcdef10203040",
      #["0000000000000000000000000000000000000000000000000000000000000000",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100",
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
      "80000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d01"], "012345")]]
    #["7097639c3dad0d0e37a840f69d43b5a65ea37e6319b881ad3dd6b5ba54b2d642",
      "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563",
      "b10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d",
      "bdd02ebb570629bab919a9b18a336dbb16a314880a4b031dcf6e2a0a8f527516",
      "a9c584056064687e149968cbab758a3376d22aedc6a55823d1b3ecbee81b8fb9",
      "cf5738ffbc98d303de66786ffc2a338e7940a06a7283aabe5e21b0b23f482221"] none none)
    emitCase (sample "source/duplicate_topics/id" "id" "single" 0
    #[("fedcba98765432100123456789abcdef10203040",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"], "")]
    #[#[("fedcba98765432100123456789abcdef10203040",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"], "")]]
    #["7097639c3dad0d0e37a840f69d43b5a65ea37e6319b881ad3dd6b5ba54b2d642",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d"] none none)
    emitCase (sample "source/duplicate_topics/logged" "real" "single" 0
    #[("fedcba98765432100123456789abcdef10203040",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"], "")]
    #[#[("fedcba98765432100123456789abcdef10203040",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"], "")]]
    #["7097639c3dad0d0e37a840f69d43b5a65ea37e6319b881ad3dd6b5ba54b2d642",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d"] none none)
    emitCase (sample "source/one_topic_base/id" "id" "single" 0
    #[("fedcba98765432100123456789abcdef10203040",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"], "")]
    #[#[("fedcba98765432100123456789abcdef10203040",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"], "")]]
    #["7097639c3dad0d0e37a840f69d43b5a65ea37e6319b881ad3dd6b5ba54b2d642",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d"] none none)
    emitCase (sample "source/one_topic_base/logged" "real" "single" 0
    #[("fedcba98765432100123456789abcdef10203040",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"], "")]
    #[#[("fedcba98765432100123456789abcdef10203040",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"], "")]]
    #["7097639c3dad0d0e37a840f69d43b5a65ea37e6319b881ad3dd6b5ba54b2d642",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d"] none none)
    emitCase (sample "source/data_only_changed/id" "id" "single" 0
    #[("fedcba98765432100123456789abcdef10203040",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"],
      ("ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
      "ffffffffff"))]
    #[#[("fedcba98765432100123456789abcdef10203040",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"],
      ("ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
      "ffffffffff"))]]
    #["7097639c3dad0d0e37a840f69d43b5a65ea37e6319b881ad3dd6b5ba54b2d642",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d"] none none)
    emitCase (sample "source/data_only_changed/logged" "real" "single" 0
    #[("fedcba98765432100123456789abcdef10203040",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"],
      ("ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
      "ffffffffff"))]
    #[#[("fedcba98765432100123456789abcdef10203040",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"],
      ("ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
      "ffffffffff"))]]
    #["7097639c3dad0d0e37a840f69d43b5a65ea37e6319b881ad3dd6b5ba54b2d642",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d"] none none)
    emitCase (sample "source/duplicate_logs/id" "id" "single" 0
    #[("fedcba98765432100123456789abcdef10203040",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"], ""),
      ("fedcba98765432100123456789abcdef10203040",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"], "")]
    #[#[("fedcba98765432100123456789abcdef10203040",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"], ""),
      ("fedcba98765432100123456789abcdef10203040",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"], "")]]
    #["7097639c3dad0d0e37a840f69d43b5a65ea37e6319b881ad3dd6b5ba54b2d642",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d",
      "7097639c3dad0d0e37a840f69d43b5a65ea37e6319b881ad3dd6b5ba54b2d642",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d"] none none)
    emitCase (sample "source/duplicate_logs/logged" "real" "single" 0
    #[("fedcba98765432100123456789abcdef10203040",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"], ""),
      ("fedcba98765432100123456789abcdef10203040",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"], "")]
    #[#[("fedcba98765432100123456789abcdef10203040",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"], ""),
      ("fedcba98765432100123456789abcdef10203040",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"], "")]]
    #["7097639c3dad0d0e37a840f69d43b5a65ea37e6319b881ad3dd6b5ba54b2d642",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d",
      "7097639c3dad0d0e37a840f69d43b5a65ea37e6319b881ad3dd6b5ba54b2d642",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d"] none none)
    emitCase (sample "source/multi_logs/id" "id" "single" 0
    #[("0000000000000000000000000000000000000000",
      #["0000000000000000000000000000000000000000000000000000000000000000"], ""),
      ("000102030405060708090a0b0c0d0e0f10111213",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "00"),
      ("0000000000000000000000000000000000000001", #[], "ff")]
    #[#[("0000000000000000000000000000000000000000",
      #["0000000000000000000000000000000000000000000000000000000000000000"], ""),
      ("000102030405060708090a0b0c0d0e0f10111213",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "00"),
      ("0000000000000000000000000000000000000001", #[], "ff")]]
    #["5380c7b7ae81a58eb98d9c78de4a1fd7fd9535fc953ed2be602daaa41767312a",
      "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563",
      "27de39f50eaf89fe36fa279026a22605711fde9c16c0f23ae2c3e9faf4eed6ae",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d",
      "bdd02ebb570629bab919a9b18a336dbb16a314880a4b031dcf6e2a0a8f527516",
      "1468288056310c82aa4c01a7e12a10f8111a0560e72b700555479031b86c357d"] none none)
    emitCase (sample "source/multi_logs/logged" "real" "single" 0
    #[("0000000000000000000000000000000000000000",
      #["0000000000000000000000000000000000000000000000000000000000000000"], ""),
      ("000102030405060708090a0b0c0d0e0f10111213",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "00"),
      ("0000000000000000000000000000000000000001", #[], "ff")]
    #[#[("0000000000000000000000000000000000000000",
      #["0000000000000000000000000000000000000000000000000000000000000000"], ""),
      ("000102030405060708090a0b0c0d0e0f10111213",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "00"),
      ("0000000000000000000000000000000000000001", #[], "ff")]]
    #["5380c7b7ae81a58eb98d9c78de4a1fd7fd9535fc953ed2be602daaa41767312a",
      "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563",
      "27de39f50eaf89fe36fa279026a22605711fde9c16c0f23ae2c3e9faf4eed6ae",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d",
      "bdd02ebb570629bab919a9b18a336dbb16a314880a4b031dcf6e2a0a8f527516",
      "1468288056310c82aa4c01a7e12a10f8111a0560e72b700555479031b86c357d"] none none)
    emitCase (sample "source/reversed_logs/id" "id" "single" 0
    #[("0000000000000000000000000000000000000001", #[], "ff"),
      ("000102030405060708090a0b0c0d0e0f10111213",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "00"),
      ("0000000000000000000000000000000000000000",
      #["0000000000000000000000000000000000000000000000000000000000000000"], "")]
    #[#[("0000000000000000000000000000000000000001", #[], "ff"),
      ("000102030405060708090a0b0c0d0e0f10111213",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "00"),
      ("0000000000000000000000000000000000000000",
      #["0000000000000000000000000000000000000000000000000000000000000000"], "")]]
    #["1468288056310c82aa4c01a7e12a10f8111a0560e72b700555479031b86c357d",
      "27de39f50eaf89fe36fa279026a22605711fde9c16c0f23ae2c3e9faf4eed6ae",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d",
      "bdd02ebb570629bab919a9b18a336dbb16a314880a4b031dcf6e2a0a8f527516",
      "5380c7b7ae81a58eb98d9c78de4a1fd7fd9535fc953ed2be602daaa41767312a",
      "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563"] none none)
    emitCase (sample "source/reversed_logs/logged" "real" "single" 0
    #[("0000000000000000000000000000000000000001", #[], "ff"),
      ("000102030405060708090a0b0c0d0e0f10111213",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "00"),
      ("0000000000000000000000000000000000000000",
      #["0000000000000000000000000000000000000000000000000000000000000000"], "")]
    #[#[("0000000000000000000000000000000000000001", #[], "ff"),
      ("000102030405060708090a0b0c0d0e0f10111213",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "00"),
      ("0000000000000000000000000000000000000000",
      #["0000000000000000000000000000000000000000000000000000000000000000"], "")]]
    #["1468288056310c82aa4c01a7e12a10f8111a0560e72b700555479031b86c357d",
      "27de39f50eaf89fe36fa279026a22605711fde9c16c0f23ae2c3e9faf4eed6ae",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d",
      "bdd02ebb570629bab919a9b18a336dbb16a314880a4b031dcf6e2a0a8f527516",
      "5380c7b7ae81a58eb98d9c78de4a1fd7fd9535fc953ed2be602daaa41767312a",
      "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563"] none none)
    emitCase (sample "source/topic_order/id" "id" "single" 0
    #[("fedcba98765432100123456789abcdef10203040",
      #["1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100",
      "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "0000000000000000000000000000000000000000000000000000000000000000",
      "0000000000000000000000000000000000000000000000000000000000000001"], "")]
    #[#[("fedcba98765432100123456789abcdef10203040",
      #["1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100",
      "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "0000000000000000000000000000000000000000000000000000000000000000",
      "0000000000000000000000000000000000000000000000000000000000000001"], "")]]
    #["7097639c3dad0d0e37a840f69d43b5a65ea37e6319b881ad3dd6b5ba54b2d642",
      "bdd02ebb570629bab919a9b18a336dbb16a314880a4b031dcf6e2a0a8f527516",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d",
      "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563",
      "b10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6"] none none)
    emitCase (sample "source/topic_order/logged" "real" "single" 0
    #[("fedcba98765432100123456789abcdef10203040",
      #["1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100",
      "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "0000000000000000000000000000000000000000000000000000000000000000",
      "0000000000000000000000000000000000000000000000000000000000000001"], "")]
    #[#[("fedcba98765432100123456789abcdef10203040",
      #["1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100",
      "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "0000000000000000000000000000000000000000000000000000000000000000",
      "0000000000000000000000000000000000000000000000000000000000000001"], "")]]
    #["7097639c3dad0d0e37a840f69d43b5a65ea37e6319b881ad3dd6b5ba54b2d642",
      "bdd02ebb570629bab919a9b18a336dbb16a314880a4b031dcf6e2a0a8f527516",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d",
      "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563",
      "b10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6"] none none)
    emitCase (sample "source/reversed_topics/id" "id" "single" 0
    #[("fedcba98765432100123456789abcdef10203040",
      #["0000000000000000000000000000000000000000000000000000000000000001",
      "0000000000000000000000000000000000000000000000000000000000000000",
      "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "")]
    #[#[("fedcba98765432100123456789abcdef10203040",
      #["0000000000000000000000000000000000000000000000000000000000000001",
      "0000000000000000000000000000000000000000000000000000000000000000",
      "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "")]]
    #["7097639c3dad0d0e37a840f69d43b5a65ea37e6319b881ad3dd6b5ba54b2d642",
      "b10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6",
      "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d",
      "bdd02ebb570629bab919a9b18a336dbb16a314880a4b031dcf6e2a0a8f527516"] none none)
    emitCase (sample "source/reversed_topics/logged" "real" "single" 0
    #[("fedcba98765432100123456789abcdef10203040",
      #["0000000000000000000000000000000000000000000000000000000000000001",
      "0000000000000000000000000000000000000000000000000000000000000000",
      "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "")]
    #[#[("fedcba98765432100123456789abcdef10203040",
      #["0000000000000000000000000000000000000000000000000000000000000001",
      "0000000000000000000000000000000000000000000000000000000000000000",
      "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "")]]
    #["7097639c3dad0d0e37a840f69d43b5a65ea37e6319b881ad3dd6b5ba54b2d642",
      "b10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6",
      "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d",
      "bdd02ebb570629bab919a9b18a336dbb16a314880a4b031dcf6e2a0a8f527516"] none none)
    emitCase (sample "source/many_logs/id" "id" "single" 0
    #[("0000000000000000000000000000000000000000",
      #["0000000000000000000000000000000000000000000000000000000000000000",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "00"),
      ("000102030405060708090a0b0c0d0e0f10111213",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"], "01"),
      ("0000000000000000000000000000000000000001",
      #["0000000000000000000000000000000000000000000000000000000000000000",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "02"),
      ("fedcba98765432100123456789abcdef10203040",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"], "03"),
      ("ffffffffffffffffffffffffffffffffffffffff",
      #["0000000000000000000000000000000000000000000000000000000000000000",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "04"),
      ("0000000000000000000000000000000000000000",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"], "05"),
      ("000102030405060708090a0b0c0d0e0f10111213",
      #["0000000000000000000000000000000000000000000000000000000000000000",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "06"),
      ("0000000000000000000000000000000000000001",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"], "07")]
    #[#[("0000000000000000000000000000000000000000",
      #["0000000000000000000000000000000000000000000000000000000000000000",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "00"),
      ("000102030405060708090a0b0c0d0e0f10111213",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"], "01"),
      ("0000000000000000000000000000000000000001",
      #["0000000000000000000000000000000000000000000000000000000000000000",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "02"),
      ("fedcba98765432100123456789abcdef10203040",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"], "03"),
      ("ffffffffffffffffffffffffffffffffffffffff",
      #["0000000000000000000000000000000000000000000000000000000000000000",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "04"),
      ("0000000000000000000000000000000000000000",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"], "05"),
      ("000102030405060708090a0b0c0d0e0f10111213",
      #["0000000000000000000000000000000000000000000000000000000000000000",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "06"),
      ("0000000000000000000000000000000000000001",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"], "07")]]
    #["5380c7b7ae81a58eb98d9c78de4a1fd7fd9535fc953ed2be602daaa41767312a",
      "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563",
      "bdd02ebb570629bab919a9b18a336dbb16a314880a4b031dcf6e2a0a8f527516",
      "27de39f50eaf89fe36fa279026a22605711fde9c16c0f23ae2c3e9faf4eed6ae",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d",
      "b10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6",
      "a9c584056064687e149968cbab758a3376d22aedc6a55823d1b3ecbee81b8fb9",
      "1468288056310c82aa4c01a7e12a10f8111a0560e72b700555479031b86c357d",
      "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563",
      "bdd02ebb570629bab919a9b18a336dbb16a314880a4b031dcf6e2a0a8f527516",
      "7097639c3dad0d0e37a840f69d43b5a65ea37e6319b881ad3dd6b5ba54b2d642",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d",
      "b10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6",
      "a9c584056064687e149968cbab758a3376d22aedc6a55823d1b3ecbee81b8fb9",
      "d3b5b90cebf74d639049264c331b8cfaadb9a1b2ec320816b39e30081310200a",
      "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563",
      "bdd02ebb570629bab919a9b18a336dbb16a314880a4b031dcf6e2a0a8f527516",
      "5380c7b7ae81a58eb98d9c78de4a1fd7fd9535fc953ed2be602daaa41767312a",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d",
      "b10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6",
      "a9c584056064687e149968cbab758a3376d22aedc6a55823d1b3ecbee81b8fb9",
      "27de39f50eaf89fe36fa279026a22605711fde9c16c0f23ae2c3e9faf4eed6ae",
      "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563",
      "bdd02ebb570629bab919a9b18a336dbb16a314880a4b031dcf6e2a0a8f527516",
      "1468288056310c82aa4c01a7e12a10f8111a0560e72b700555479031b86c357d",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d",
      "b10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6",
      "a9c584056064687e149968cbab758a3376d22aedc6a55823d1b3ecbee81b8fb9"] none none)
    emitCase (sample "source/many_logs/logged" "real" "single" 0
    #[("0000000000000000000000000000000000000000",
      #["0000000000000000000000000000000000000000000000000000000000000000",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "00"),
      ("000102030405060708090a0b0c0d0e0f10111213",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"], "01"),
      ("0000000000000000000000000000000000000001",
      #["0000000000000000000000000000000000000000000000000000000000000000",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "02"),
      ("fedcba98765432100123456789abcdef10203040",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"], "03"),
      ("ffffffffffffffffffffffffffffffffffffffff",
      #["0000000000000000000000000000000000000000000000000000000000000000",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "04"),
      ("0000000000000000000000000000000000000000",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"], "05"),
      ("000102030405060708090a0b0c0d0e0f10111213",
      #["0000000000000000000000000000000000000000000000000000000000000000",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "06"),
      ("0000000000000000000000000000000000000001",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"], "07")]
    #[#[("0000000000000000000000000000000000000000",
      #["0000000000000000000000000000000000000000000000000000000000000000",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "00"),
      ("000102030405060708090a0b0c0d0e0f10111213",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"], "01"),
      ("0000000000000000000000000000000000000001",
      #["0000000000000000000000000000000000000000000000000000000000000000",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "02"),
      ("fedcba98765432100123456789abcdef10203040",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"], "03"),
      ("ffffffffffffffffffffffffffffffffffffffff",
      #["0000000000000000000000000000000000000000000000000000000000000000",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "04"),
      ("0000000000000000000000000000000000000000",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"], "05"),
      ("000102030405060708090a0b0c0d0e0f10111213",
      #["0000000000000000000000000000000000000000000000000000000000000000",
      "1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100"], "06"),
      ("0000000000000000000000000000000000000001",
      #["000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"], "07")]]
    #["5380c7b7ae81a58eb98d9c78de4a1fd7fd9535fc953ed2be602daaa41767312a",
      "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563",
      "bdd02ebb570629bab919a9b18a336dbb16a314880a4b031dcf6e2a0a8f527516",
      "27de39f50eaf89fe36fa279026a22605711fde9c16c0f23ae2c3e9faf4eed6ae",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d",
      "b10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6",
      "a9c584056064687e149968cbab758a3376d22aedc6a55823d1b3ecbee81b8fb9",
      "1468288056310c82aa4c01a7e12a10f8111a0560e72b700555479031b86c357d",
      "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563",
      "bdd02ebb570629bab919a9b18a336dbb16a314880a4b031dcf6e2a0a8f527516",
      "7097639c3dad0d0e37a840f69d43b5a65ea37e6319b881ad3dd6b5ba54b2d642",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d",
      "b10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6",
      "a9c584056064687e149968cbab758a3376d22aedc6a55823d1b3ecbee81b8fb9",
      "d3b5b90cebf74d639049264c331b8cfaadb9a1b2ec320816b39e30081310200a",
      "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563",
      "bdd02ebb570629bab919a9b18a336dbb16a314880a4b031dcf6e2a0a8f527516",
      "5380c7b7ae81a58eb98d9c78de4a1fd7fd9535fc953ed2be602daaa41767312a",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d",
      "b10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6",
      "a9c584056064687e149968cbab758a3376d22aedc6a55823d1b3ecbee81b8fb9",
      "27de39f50eaf89fe36fa279026a22605711fde9c16c0f23ae2c3e9faf4eed6ae",
      "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563",
      "bdd02ebb570629bab919a9b18a336dbb16a314880a4b031dcf6e2a0a8f527516",
      "1468288056310c82aa4c01a7e12a10f8111a0560e72b700555479031b86c357d",
      "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d",
      "b10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6",
      "a9c584056064687e149968cbab758a3376d22aedc6a55823d1b3ecbee81b8fb9"] none none)
    emitCase (sample "synthetic/bit0/except-state" "except-state" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["0000000000000000000000000000000000000000000000000000000000000000"] none none)
    emitCase (sample "synthetic/bit0/state-except" "state-except" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["0000000000000000000000000000000000000000000000000000000000000000"] none none)
    emitCase (sample "synthetic/bit0/forward" "forward" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["0000000000000000000000000000000000000000000000000000000000000000"] none none)
    emitCase (sample "synthetic/bit1/except-state" "except-state" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["0001000100010000000000000000000000000000000000000000000000000000"] none none)
    emitCase (sample "synthetic/bit1/state-except" "state-except" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["0001000100010000000000000000000000000000000000000000000000000000"] none none)
    emitCase (sample "synthetic/bit1/forward" "forward" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["0001000100010000000000000000000000000000000000000000000000000000"] none none)
    emitCase (sample "synthetic/bit7/except-state" "except-state" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["0007000700070000000000000000000000000000000000000000000000000000"] none none)
    emitCase (sample "synthetic/bit7/state-except" "state-except" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["0007000700070000000000000000000000000000000000000000000000000000"] none none)
    emitCase (sample "synthetic/bit7/forward" "forward" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["0007000700070000000000000000000000000000000000000000000000000000"] none none)
    emitCase (sample "synthetic/bit8/except-state" "except-state" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["0008000800080000000000000000000000000000000000000000000000000000"] none none)
    emitCase (sample "synthetic/bit8/state-except" "state-except" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["0008000800080000000000000000000000000000000000000000000000000000"] none none)
    emitCase (sample "synthetic/bit8/forward" "forward" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["0008000800080000000000000000000000000000000000000000000000000000"] none none)
    emitCase (sample "synthetic/bit2047/except-state" "except-state" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["07ff07ff07ff0000000000000000000000000000000000000000000000000000"] none none)
    emitCase (sample "synthetic/bit2047/state-except" "state-except" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["07ff07ff07ff0000000000000000000000000000000000000000000000000000"] none none)
    emitCase (sample "synthetic/bit2047/forward" "forward" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["07ff07ff07ff0000000000000000000000000000000000000000000000000000"] none none)
    emitCase (sample "synthetic/three_pairs/except-state" "except-state" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["0001000807ff0000000000000000000000000000000000000000000000000000"] none none)
    emitCase (sample "synthetic/three_pairs/state-except" "state-except" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["0001000807ff0000000000000000000000000000000000000000000000000000"] none none)
    emitCase (sample "synthetic/three_pairs/forward" "forward" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["0001000807ff0000000000000000000000000000000000000000000000000000"] none none)
    emitCase (sample "synthetic/high_mask/except-state" "except-state" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["f800f801ffff0000000000000000000000000000000000000000000000000000"] none none)
    emitCase (sample "synthetic/high_mask/state-except" "state-except" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["f800f801ffff0000000000000000000000000000000000000000000000000000"] none none)
    emitCase (sample "synthetic/high_mask/forward" "forward" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["f800f801ffff0000000000000000000000000000000000000000000000000000"] none none)
    emitCase (sample "synthetic/collisions/except-state" "except-state" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["0007000700080000000000000000000000000000000000000000000000000000"] none none)
    emitCase (sample "synthetic/collisions/state-except" "state-except" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["0007000700080000000000000000000000000000000000000000000000000000"] none none)
    emitCase (sample "synthetic/collisions/forward" "forward" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["0007000700080000000000000000000000000000000000000000000000000000"] none none)
    emitCase (sample "synthetic/tail_zero/except-state" "except-state" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["0001000807ff0000000000000000000000000000000000000000000000000000"] none none)
    emitCase (sample "synthetic/tail_zero/state-except" "state-except" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["0001000807ff0000000000000000000000000000000000000000000000000000"] none none)
    emitCase (sample "synthetic/tail_zero/forward" "forward" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["0001000807ff0000000000000000000000000000000000000000000000000000"] none none)
    emitCase (sample "synthetic/tail_ff/except-state" "except-state" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["0001000807ffffffffffffffffffffffffffffffffffffffffffffffffffffff"] none none)
    emitCase (sample "synthetic/tail_ff/state-except" "state-except" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["0001000807ffffffffffffffffffffffffffffffffffffffffffffffffffffff"] none none)
    emitCase (sample "synthetic/tail_ff/forward" "forward" "single" 0
    #[("0000000000000000000000000000000000000013", #[], "ff001122")]
    #[#[("0000000000000000000000000000000000000013", #[], "ff001122")]]
    #["0001000807ffffffffffffffffffffffffffffffffffffffffffffffffffffff"] none none)
    emitCase (sample "stateful/single/except-state" "except-state" "single" 1
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] none none)
    emitCase (sample "stateful/single/state-except" "state-except" "single" 1
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] none none)
    emitCase (sample "stateful/single/forward" "forward" "single" 1
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] none none)
    emitCase (sample "stateful/append/except-state" "except-state" "append" 1
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203")],
      #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] none none)
    emitCase (sample "stateful/append/state-except" "state-except" "append" 1
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203")],
      #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] none none)
    emitCase (sample "stateful/append/forward" "forward" "append" 1
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203")],
      #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] none none)
    emitCase (sample "stateful/reset/except-state" "except-state" "reset" 1
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203")],
      #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] none none)
    emitCase (sample "stateful/reset/state-except" "state-except" "reset" 1
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203")],
      #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] none none)
    emitCase (sample "stateful/reset/forward" "forward" "reset" 1
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203")],
      #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] none none)
    emitCase (sample "stateful/dedup/except-state" "except-state" "dedup" 1
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "010203")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] none none)
    emitCase (sample "stateful/dedup/state-except" "state-except" "dedup" 1
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "010203")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] none none)
    emitCase (sample "stateful/dedup/forward" "forward" "dedup" 1
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "010203")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] none none)
    emitCase (sample "stateful/reorder/except-state" "except-state" "reorder" 1
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000009",
      "0000000000000000000000000000000000000000000000000000000000000004"], "00ff"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] none none)
    emitCase (sample "stateful/reorder/state-except" "state-except" "reorder" 1
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000009",
      "0000000000000000000000000000000000000000000000000000000000000004"], "00ff"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] none none)
    emitCase (sample "stateful/reorder/forward" "forward" "reorder" 1
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000009",
      "0000000000000000000000000000000000000000000000000000000000000004"], "00ff"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] none none)
    emitCase (sample "failure/0/except-state" "except-state" "single" 0
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] (some 0) (some
      "oracle failure #0: 00ff / original"))
    emitCase (sample "failure/0/state-except" "state-except" "single" 0
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] (some 0) (some
      "oracle failure #0: 00ff / original"))
    emitCase (sample "failure/0/forward" "forward" "single" 0
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] (some 0) (some
      "oracle failure #0: 00ff / original"))
    emitCase (sample "failure/1/except-state" "except-state" "single" 0
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] (some 1) (some
      "oracle failure #1: 00ff / original"))
    emitCase (sample "failure/1/state-except" "state-except" "single" 0
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] (some 1) (some
      "oracle failure #1: 00ff / original"))
    emitCase (sample "failure/1/forward" "forward" "single" 0
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] (some 1) (some
      "oracle failure #1: 00ff / original"))
    emitCase (sample "failure/2/except-state" "except-state" "single" 0
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] (some 2) (some
      "oracle failure #2: 00ff / original"))
    emitCase (sample "failure/2/state-except" "state-except" "single" 0
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] (some 2) (some
      "oracle failure #2: 00ff / original"))
    emitCase (sample "failure/2/forward" "forward" "single" 0
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] (some 2) (some
      "oracle failure #2: 00ff / original"))
    emitCase (sample "failure/3/except-state" "except-state" "single" 0
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] (some 3) (some
      "oracle failure #3: 00ff / original"))
    emitCase (sample "failure/3/state-except" "state-except" "single" 0
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] (some 3) (some
      "oracle failure #3: 00ff / original"))
    emitCase (sample "failure/3/forward" "forward" "single" 0
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] (some 3) (some
      "oracle failure #3: 00ff / original"))
    emitCase (sample "failure/4/except-state" "except-state" "single" 0
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] (some 4) (some
      "oracle failure #4: 00ff / original"))
    emitCase (sample "failure/4/state-except" "state-except" "single" 0
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] (some 4) (some
      "oracle failure #4: 00ff / original"))
    emitCase (sample "failure/4/forward" "forward" "single" 0
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] (some 4) (some
      "oracle failure #4: 00ff / original"))
    emitCase (sample "failure/5/except-state" "except-state" "single" 0
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] (some 5) (some
      "oracle failure #5: 00ff / original"))
    emitCase (sample "failure/5/state-except" "state-except" "single" 0
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] (some 5) (some
      "oracle failure #5: 00ff / original"))
    emitCase (sample "failure/5/forward" "forward" "single" 0
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] (some 5) (some
      "oracle failure #5: 00ff / original"))
    emitCase (sample "failure_append/3/except-state" "except-state" "append" 1
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203")],
      #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] (some 3) (some
      "oracle failure #3: 00ff / original"))
    emitCase (sample "failure_append/3/state-except" "state-except" "append" 1
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203")],
      #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] (some 3) (some
      "oracle failure #3: 00ff / original"))
    emitCase (sample "failure_append/3/forward" "forward" "append" 1
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203")],
      #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] (some 3) (some
      "oracle failure #3: 00ff / original"))
    emitCase (sample "failure_append/4/except-state" "except-state" "append" 1
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203")],
      #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] (some 4) (some
      "oracle failure #4: 00ff / original"))
    emitCase (sample "failure_append/4/state-except" "state-except" "append" 1
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203")],
      #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] (some 4) (some
      "oracle failure #4: 00ff / original"))
    emitCase (sample "failure_append/4/forward" "forward" "append" 1
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203")],
      #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] (some 4) (some
      "oracle failure #4: 00ff / original"))
    emitCase (sample "failure_append/5/except-state" "except-state" "append" 1
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203")],
      #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] (some 5) (some
      "oracle failure #5: 00ff / original"))
    emitCase (sample "failure_append/5/state-except" "state-except" "append" 1
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203")],
      #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] (some 5) (some
      "oracle failure #5: 00ff / original"))
    emitCase (sample "failure_append/5/forward" "forward" "append" 1
    #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203"),
      ("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]
    #[#[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000004"], "010203")],
      #[("0000000000000000000000000000000000000011",
      #["0000000000000000000000000000000000000000000000000000000000000004",
      "0000000000000000000000000000000000000000000000000000000000000009"], "00ff")]]
    #["0001000200031f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f",
      "000e0013001a2020202020202020202020202020202020202020202020202020",
      "001b002400312121212121212121212121212121212121212121212121212121",
      "0028003500482222222222222222222222222222222222222222222222222222",
      "00350046005f2323232323232323232323232323232323232323232323232323",
      "0042005700762424242424242424242424242424242424242424242424242424"] (some 5) (some
      "oracle failure #5: 00ff / original"))
    emit (Json.mkObj [("end", toJson true), ("count", toJson (112 : Nat)), ("catalog", toJson
      "6fe020501102507a348d249da59332a822f691a867279e1153f092249a91160a")])
    return 0
  catch error =>
    (← IO.getStderr).putStrLn s!"FAIL {error}"
    return 1
