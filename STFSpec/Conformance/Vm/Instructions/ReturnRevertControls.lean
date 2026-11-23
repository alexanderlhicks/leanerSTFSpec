/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions
import STFSpec.Fork.Amsterdam
import STFSpec.State.BlockInitialization
import STFSpec.State.TransactionInitialization

/-!
# RETURN and REVERT controls

Library `EthConformance`. The cases exercise both handlers through the
Instructions facade. See `STFSpec/informal/modules/EthVmInstructions.md` §4.
-/

namespace STFSpec.Conformance.Vm.Instructions.ReturnRevertControls

open STFSpec.Base STFSpec.State STFSpec.Vm.Core STFSpec.Vm.Instructions

private structure Case where
  stack : List Nat
  gas : Nat
  zero : Nat
  wordPrice : Nat
  isStatic : Bool := false

private def address := Address.ofNat 61
private def slot (n : Nat) : Bytes32 := FixedBytes.ofNat n
private def hash (n : Nat) : Hash32 := Hash32.ofBytes32 (slot n)

private def context (c : Case) : FrameCtx :=
  let cfg := STFSpec.Fork.Amsterdam.vmConfig
  let costs := { cfg.costs with zero := c.zero, memoryPerWord := c.wordPrice }
  let block : BlockEnvironment :=
    ⟨U64.ofNat 11, 13, #[hash 17, hash 19], Address.ofNat 23, 29, 31,
      U256.ofNat 37, slot 41, U64.ofNat 43, hash 47, U64.ofNat 53⟩
  let tx : TransactionEnvironment :=
    ⟨address, Address.ofNat 67, true, Bytes.ofList [0, 128, 0], U256.ofNat 69, 71, 73,
      79, 83, 89, ∅, ∅, #[], #[], some 0, some (hash 97)⟩
  ⟨{ cfg with costs }, block, tx, address, Address.ofNat 107, U256.max, Bytes.ofList [255, 0, 128],
    some address, Bytes.ofList [243, 253], validJumpDestinations (Bytes.ofList [91, 0, 91]),
    7, by decide, true, c.isStatic, false, Address.ofNat 109⟩

private def entryBytes : List UInt8 := (List.range 32).map UInt8.ofNat

private def entryMemory : Memory :=
  let expanded := Memory.empty.expand 32 (by decide)
  let bytes := Bytes.ofList entryBytes
  expanded.write 0 bytes (by
    right
    rw [← Memory.length_toBytes, Memory.toBytes_expand, Memory.toBytes_empty]
    decide)

private def frame (c : Case) : Frame :=
  let stack := c.stack.reverse.foldl (fun s value ↦ (s.push (U256.ofNat value)).toOption.getD s) Stack.empty
  let log : Log := ⟨address, #[hash 113, hash 127], Bytes.ofList [255, 0, 128]⟩
  ⟨2 ^ 260 + 29, stack, entryMemory, ⟨c.gas, 13, 17, -19, 23, 29⟩,
    .concat (.leaf [log]) (.leaf [log]), (∅ : AddrSet).insert address, Bytes.ofList [255, 0, 128],
    (∅ : AddrSet).insert address, (∅ : SlotSet).insert (address, slot 131)⟩

private def world : VmWorld Id :=
  let err : WitnessError := .missing (.node (hash 137))
  let provider : PreState Id :=
    ⟨fun _ ↦ .error err, fun _ _ ↦ .error err, fun _ ↦ .error err, fun _ ↦ .error err⟩
  let block := { BlockState.new provider ⟨hash 139, hash 149, hash 151, hash 157⟩ with
    oldestAncestorOffset := some (2 ^ 190) }
  let base := TxState.new block
  ⟨{ base with obs.createdAccounts := base.obs.createdAccounts.insert address }⟩

private def modelFrame (f : Frame) :=
  let g := f.gasMeter
  (f.pc, f.stack.toList.map U256.toNat, f.memory.toBytes,
    (g.gasLeft, g.stateGasLeft, g.stateGasBaseline, g.refundCounter,
      g.stateGasSpilled, g.stateGasCommittedSpill),
    f.logs.toList.map (fun log ↦ (log.address.toNat, log.topics.map Hash32.toNat, log.data.toList)),
    f.accountsToDelete.toList.map Address.toNat, f.returnData.toList,
    f.accessedAddresses.toList.map Address.toNat,
    f.accessedStorageKeys.toList.map (fun (a, k) ↦ (a.toNat, k.toNat)))

private def memoryCost (coefficient words : Nat) := coefficient * words + words * words / 512

private def expected (c : Case) (reverting : Bool) : String × List Nat × Nat × List UInt8 × List UInt8 :=
  match c.stack with
  | [] | [_] => ("underflow", [], c.gas, entryBytes, [])
  | off :: len :: rest =>
    let words := if len = 0 then 1 else max 1 ((off + len + 31) / 32)
    let growth := memoryCost c.wordPrice words - memoryCost c.wordPrice 1
    let price := growth + (if reverting then c.zero else 2 * c.zero)
    if price > c.gas then ("denied", rest, c.gas, entryBytes, [])
    else
      let memory := entryBytes ++ List.replicate (32 * words - 32) 0
      let output := if len = 0 then [] else (memory.drop off).take len
      (if reverting then "revert" else "stop", rest, c.gas - price, memory, output)

private def evaluate (c : Case) (reverting : Bool) :=
  let op := if reverting then (revert : Handler Id) else return_
  ((op (context c) (frame c)).run world).run

private def check (c : Case) (reverting : Bool) : Bool :=
  let (tag, words, execution, memory, output) := expected c reverting
  let (pc, _, _, (_, state, baseline, refund, spill, committed), logs, deleted, ret, addresses, slots) :=
    modelFrame (frame c)
  let wanted := (pc, words, memory, (execution, state, baseline, refund, spill, committed),
    logs, deleted, ret, addresses, slots)
  match evaluate c reverting with
  | .error _ => false
  | .ok (result, nextWorld) =>
    nextWorld.tx.block.oldestAncestorOffset == some (2 ^ 190) &&
      nextWorld.tx.obs.createdAccounts.contains address &&
      (match result with
      | .halt next .stackUnderflow => tag == "underflow" && modelFrame next == wanted
      | .halt next .outOfGas => tag == "denied" && modelFrame next == wanted
      | .stop next returned => tag == "stop" && modelFrame next == wanted && returned.toList == output
      | .revert next returned => tag == "revert" && modelFrame next == wanted && returned.toList == output
      | _ => false)

private def memorySnapshot (reverting : Bool) : Bool :=
  let c : Case := ⟨[30, 4, 91], 17, 7, 3, true⟩
  let check (next : Frame) (returned : Bytes) : Bool :=
    let different := Bytes.ofList [41, 43, 47, 53]
    if fits : 30 + different.size ≤ next.memory.size then
      let changed := next.memory.write 30 different (Or.inr fits)
      returned.toList == [30, 31, 0, 0] &&
        entryMemory.toBytes == entryBytes &&
        changed.toBytes == (List.range 30).map UInt8.ofNat ++ [41, 43, 47, 53] ++ List.replicate 30 0
    else false
  match evaluate c reverting with
  | .ok (.stop next returned, _) => !reverting && check next returned
  | .ok (.revert next returned, _) => reverting && check next returned
  | _ => false

private def paired (c : Case) : Bool := check c false && check c true

#guard paired ⟨[], 0, 7, 3, true⟩
#guard paired ⟨[29], 0, 7, 3, false⟩
#guard paired ⟨[2 ^ 256 - 1, 0, 91], 0, 0, 3, true⟩
#guard paired ⟨[2 ^ 256 - 1, 0, 91], 6, 7, 3, false⟩
#guard paired ⟨[2 ^ 256 - 1, 0, 91], 7, 7, 3, true⟩
#guard paired ⟨[2 ^ 256 - 1, 0, 91], 13, 7, 3, false⟩
#guard paired ⟨[2 ^ 256 - 1, 0, 91], 14, 7, 3, true⟩
#guard paired ⟨[2 ^ 256 - 1, 2 ^ 256 - 1, 91], 0, 0, 3, false⟩
#guard paired ⟨[5, 3, 91], 19, 0, 3, true⟩
#guard paired ⟨[30, 4, 91], 2, 0, 3, false⟩
#guard paired ⟨[30, 4, 91], 3, 0, 3, true⟩
#guard paired ⟨[30, 4, 91], 9, 7, 3, false⟩
#guard paired ⟨[30, 4, 91], 10, 7, 3, true⟩
#guard paired ⟨[30, 4, 91], 16, 7, 3, false⟩
#guard paired ⟨[30, 4, 91], 17, 7, 3, true⟩
#guard paired ⟨[30, 4, 91], 20, 7, 13, false⟩
#guard paired ⟨[30, 4, 91], 27, 7, 13, true⟩
#guard paired ⟨[30, 4, 91], 0, 0, 0, false⟩
#guard memorySnapshot false
#guard memorySnapshot true

end STFSpec.Conformance.Vm.Instructions.ReturnRevertControls
