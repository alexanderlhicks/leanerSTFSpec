/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions
import STFSpec.Fork.Amsterdam

/-!
# KECCAK controls

Library `EthConformance`. The guards exercise the public facade in `Id` and
with a recording oracle that returns its own digest. They compare all mutable
frame fields and sample the retained world. See
`STFSpec/informal/modules/EthVmInstructions.md` §4.
-/

namespace STFSpec.Conformance.Vm.Instructions.KeccakControls

open STFSpec.Base STFSpec.Hash STFSpec.State STFSpec.Vm.Core STFSpec.Vm.Instructions

private def addr (n : Nat) := Address.ofNat n
private def hash (n : Nat) := Hash32.ofBytes32 (FixedBytes.ofNat n)

private def blockEnv : BlockEnvironment :=
  ⟨U64.ofNat 11, 13, #[hash 17, hash 19], addr 23, 29, 31,
    U256.ofNat 37, FixedBytes.ofNat 41, U64.ofNat 43, hash 47, U64.ofNat 53⟩

private def txEnv : TransactionEnvironment :=
  ⟨addr 59, addr 61, true, Bytes.ofList [0, 128, 0], U256.ofNat 67, 71, 73,
    79, 83, 89, ∅, ∅, #[], #[], some 0, some (hash 97)⟩

private def context (base word seed memoryPerWord : Nat) (static : Bool) : FrameCtx :=
  let costs := { STFSpec.Fork.Amsterdam.gasCosts with
    opcodeKeccak256Base := base
    opcodeKeccak256PerWord := word
    zero := seed
    memoryPerWord }
  ⟨⟨costs, ⟨0, 7, 2 ^ 300 + 11, 13⟩, ⟨7, 0, 2 ^ 301 + 17⟩⟩,
    blockEnv, txEnv, addr 101, addr 103, U256.max, Bytes.ofList [255, 0, 128],
    some (addr 0), Bytes.ofList [0x20], validJumpDestinations (Bytes.ofList [0x20]),
    1024, by decide, true, static, false, addr 107⟩

private def world (m : Type → Type) [Monad m] : VmWorld m :=
  let pre : PreState m := ⟨fun _ ↦ pure (.ok none), fun _ _ ↦ pure (.ok (U256.ofNat 109)),
    fun _ ↦ pure (.ok (ByteArray.mk #[0, 255, 128])), fun _ ↦ pure (.ok (hash 113))⟩
  let block : BlockState m :=
    ⟨pre, ⟨hash 127, hash 131, hash 137, hash 139⟩,
      (∅ : Std.ExtTreeMap Address (Option Account)).insert (addr 149) none,
      ⟨157, ∅, ∅⟩, ∅, ⟨163, ∅, ∅⟩, ∅, ∅, ∅, ∅, ∅, ∅,
      some (2 ^ 290 + 167)⟩
  let rev : TxRevertible :=
    ⟨∅, ⟨173, ∅, ∅⟩, ∅, ⟨179, ∅, ∅⟩, ∅, ∅, ∅,
      (∅ : Std.ExtTreeMap (Address × Bytes32) U256).insert
        (addr 181, FixedBytes.ofNat 191) (U256.ofNat 193)⟩
  let obs : TxObs :=
    ⟨(∅ : Std.HashSet Address).insert (addr 197), ∅, ∅,
      (∅ : Std.HashSet Address).insert (addr 199)⟩
  ⟨⟨block, rev, obs⟩⟩

private def initial : List UInt8 := (List.range 32).map UInt8.ofNat
private def expanded : Memory := Memory.empty.expand 32 (by decide)

private theorem expanded_size : expanded.size = 32 := by
  rw [← Memory.length_toBytes, expanded, Memory.toBytes_expand, Memory.toBytes_empty]
  rfl

private def memory : Memory := expanded.write 0 (Bytes.ofList initial) (by
  right
  rw [expanded_size]
  decide)

private def frame (pc gas : Nat) (stack : Stack) : Frame :=
  let entry : Log := ⟨addr 256, #[hash 256, hash 1, hash 256], Bytes.ofList [255, 0, 128]⟩
  ⟨pc, stack, memory, ⟨gas, 101, 2, -17, 5, 11⟩,
    .concat (.leaf [entry]) (.concat .empty (.leaf [entry])),
    (∅ : AddrSet).insert (addr 256), Bytes.ofList [0, 255, 128, 0],
    (∅ : AddrSet).insert (addr 1),
    ((∅ : SlotSet).insert (addr 1, FixedBytes.ofNat 256)).insert (addr 256, FixedBytes.ofNat 1)⟩

private def frameModel (f : Frame) :=
  (f.pc, f.stack.toList.map U256.toNat, f.memory.toBytes,
    (f.gasMeter.gasLeft, f.gasMeter.stateGasLeft, f.gasMeter.stateGasBaseline,
      f.gasMeter.refundCounter, f.gasMeter.stateGasSpilled, f.gasMeter.stateGasCommittedSpill),
    f.logs.toList.map (fun l ↦
      (l.address.toNat, l.topics.toList.map Hash32.toNat, l.data.toList)),
    f.accountsToDelete.toList.map Address.toNat, f.returnData.toList,
    f.accessedAddresses.toList.map Address.toNat,
    f.accessedStorageKeys.toList.map (fun (a, k) ↦ (a.toNat, k.toNat)))

private def worldModel {m : Type → Type} (w : VmWorld m) :=
  let tx := w.tx
  (tx.block.accountOrder.next, tx.block.storageAddressOrder.next,
    tx.rev.accountOrder.next, tx.rev.storageAddressOrder.next,
    tx.block.oldestAncestorOffset, tx.block.consts.emptyCodeHash.toNat,
    tx.obs.createdAccounts.contains (addr 199), tx.obs.accountReads.contains (addr 197))

private def stackOf (words : List Nat) : Option Stack :=
  words.reverse.foldlM (fun stack word ↦ (stack.push (U256.ofNat word)).toOption) Stack.empty

private structure Expected where
  pc : Nat
  gas : Nat
  stack : List Nat
  memory : List UInt8
  fault : Option ExceptionalHalt

private def agrees {m : Type → Type} [Monad m] (ctx : FrameCtx) (expected : Expected)
    (result : Except VmFault (StepResult ctx × VmWorld m)) : Bool := Id.run do
  let some stack := stackOf expected.stack | return false
  let desired := frameModel (frame expected.pc expected.gas stack)
  match result, expected.fault with
  | .ok (.halt after .outOfGas, retained), some .outOfGas
  | .ok (.halt after .stackUnderflow, retained), some .stackUnderflow
  | .ok (.continue after, retained), none =>
    return frameModel { after with memory } == desired &&
      after.memory.toBytes == expected.memory && worldModel retained == worldModel (world m)
  | _, _ => return false

private def concrete (ctx : FrameCtx) (pc gas : Nat) (words : List Nat) (expected : Expected) : Bool :=
  match stackOf words with
  | none => false
  | some stack => agrees ctx expected (((keccak ctx (frame pc gas stack)).run (world Id)).run)

private abbrev Recording := StateT (List (List UInt8)) Id
private def answer := hash 0x008000ff
private def answerBytes : List UInt8 := List.replicate 29 0 ++ [128, 0, 255]

private def recorded (ctx : FrameCtx) (pc gas : Nat) (words : List Nat) (expected : Expected)
    (preimages : List (List UInt8)) : Bool := Id.run do
  let some stack := stackOf words | return false
  letI : KeccakQuery Recording := ⟨fun data observed ↦
    (answer, observed ++ [data.data.toList])⟩
  let action := ((keccak ctx (frame pc gas stack)).run (world Recording)).run
  let (outcome, trace) := action.run []
  let exactAnswer := match outcome, expected.fault with
    | .ok (.continue after, _), none =>
      (after.stack.toList.head?.map (fun word ↦ word.toBeBytes32.toBytes.toList)) == some answerBytes
    | _, some _ => true
    | _, none => false
  return agrees ctx expected outcome && trace == preimages && exactAnswer

private def priced (static : Bool) := context 11 13 7 5 static
private def extended : List UInt8 := initial ++ List.replicate 32 0
private def maxWord : Nat := 2 ^ 256 - 1
private def emptyHash : Nat := 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470

#guard recorded (priced false) 7 0 [] ⟨7, 0, [], initial, some .stackUnderflow⟩ []
#guard recorded (priced true) 7 100 [30] ⟨7, 100, [], initial, some .stackUnderflow⟩ []
#guard recorded (priced true) 7 35 [30, 5, 53] ⟨7, 35, [53], initial, some .outOfGas⟩ []
#guard recorded (priced false) maxWord 36 [30, 5, 53]
  ⟨2 ^ 256, 0, [answer.toNat, 53], extended, none⟩ [[30, 31, 0, 0, 0]]
#guard recorded (priced true) 7 36 [30, 5, 53]
  ⟨8, 0, [answer.toNat, 53], extended, none⟩ [[30, 31, 0, 0, 0]]
#guard recorded (priced false) 7 18 [maxWord, 0] ⟨8, 0, [answer.toNat], initial, none⟩ [[]]
#guard recorded (context 0 0 0 0 true) 7 0 [31, 2] ⟨8, 0, [answer.toNat], extended, none⟩ [[31, 0]]
#guard recorded (priced false) 7 100 [maxWord, maxWord]
  ⟨7, 100, [], initial, some .outOfGas⟩ []

#guard concrete (priced false) 7 18 [maxWord, 0] ⟨8, 0, [emptyHash], initial, none⟩
#guard concrete (priced true) 7 18 ([0, 0] ++ List.range 1022)
  ⟨8, 0, emptyHash :: List.range 1022, initial, none⟩
#guard concrete (context (2 ^ 300 + 3) 17 5 29 false) 9 (2 ^ 300 + 8) [0, 0]
  ⟨10, 0, [emptyHash], initial, none⟩

end STFSpec.Conformance.Vm.Instructions.KeccakControls
