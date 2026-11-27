/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions
import STFSpec.Fork.Amsterdam

/-!
# CREATE and CREATE2 resume controls

Library `EthConformance`. Check the complete parent and child frame models at
the settled return boundary of both pinned wrappers, then check the resumed
parent. Raw controls vary the configured refund and the supplied output.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md` §4.
-/

namespace STFSpec.Conformance.Vm.Instructions.CreateResumeControls
open STFSpec.Base STFSpec.Vm.Core STFSpec.Vm.Instructions

private structure FrameView where
  pc : Nat
  stack : List Nat
  memory : List UInt8
  meter : Nat × Nat × Nat × Int × Nat × Nat
  logs : List (Nat × List Nat × List UInt8)
  deleted : List Nat
  returnData : List UInt8
  addresses : List Nat
  slots : List (Nat × Nat)
deriving DecidableEq

private def view (frame : Frame) : FrameView :=
  let meter := frame.gasMeter
  ⟨frame.pc, frame.stack.toList.map U256.toNat, frame.memory.toBytes,
   (meter.gasLeft, meter.stateGasLeft, meter.stateGasBaseline, meter.refundCounter,
     meter.stateGasSpilled, meter.stateGasCommittedSpill),
   frame.logs.toList.map (fun log ↦
     (log.address.toNat, log.topics.toList.map Hash32.toNat, log.data.toList)),
   frame.accountsToDelete.toList.map Address.toNat, frame.returnData.toList,
   frame.accessedAddresses.toList.map Address.toNat,
   frame.accessedStorageKeys.toList.map (fun (a, k) ↦ (a.toNat, k.toNat))⟩

private def fromView (v : FrameView) (memoryBound : v.memory.length ≤ 32) : Option Frame := do
  let stack ← v.stack.reverse.foldlM
    (fun stack value ↦ (stack.push (U256.ofNat value)).toOption) Stack.empty
  let memory := if v.memory.isEmpty then Memory.empty else
    let expanded := Memory.empty.expand 32 (by decide)
    expanded.write 0 (Bytes.ofList v.memory) (by
      right
      have size_eq : expanded.size = 32 := by
        change (Memory.empty.expand 32 _).size = 32
        rw [← Memory.length_toBytes, Memory.toBytes_expand, Memory.toBytes_empty]
        rfl
      rw [size_eq, Nat.zero_add, Bytes.size_ofList]
      exact memoryBound)
  let (gas, reservoir, baseline, refund, spill, committed) := v.meter
  let logs := v.logs.map (fun (address, topics, data) ↦
    ⟨Address.ofNat address, (topics.map (fun t ↦ Hash32.ofBytes32 (FixedBytes.ofNat t))).toArray,
      Bytes.ofList data⟩)
  return ⟨v.pc, stack, memory, ⟨gas, reservoir, baseline, refund, spill, committed⟩, .leaf logs,
    v.deleted.foldl (fun acc a ↦ acc.insert (Address.ofNat a)) (∅ : AddrSet),
    Bytes.ofList v.returnData,
    v.addresses.foldl (fun acc a ↦ acc.insert (Address.ofNat a)) (∅ : AddrSet),
    v.slots.foldl (fun acc (a, k) ↦ acc.insert (Address.ofNat a, FixedBytes.ofNat k)) (∅ : SlotSet)⟩

private def checkResume (cfg : VmConfig) (parentView childView expected : FrameView)
    (parentBound : parentView.memory.length ≤ 32) (childBound : childView.memory.length ≤ 32)
    (output : List UInt8) (error : Option FrameError) (target : Nat) (charged : Bool) : Bool :=
  match fromView parentView parentBound, fromView childView childBound with
  | some parent, some child =>
    if settled : ChildSettled child error.isSome then
      if room : parent.stack.size < STACK_DEPTH_LIMIT then
        let req : CreateRequest :=
          ⟨2 ^ 269, 17, U256.ofNat 19, Address.ofNat 23, Address.ofNat target,
            Bytes.ofList [29, 0, 31], charged⟩
        let outcome : ChildOutcome := ⟨child, Bytes.ofList output, error, settled⟩
        let resumed := resumeAfterCreate cfg parent req outcome room
        decide (view parent = parentView ∧ view child = childView ∧ view resumed = expected)
      else false
    else false
  | _, _ => false

private def checkPinned := checkResume STFSpec.Fork.Amsterdam.vmConfig

private def parentMemory : List UInt8 :=
  [31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16,
   15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]

private def createAddress : Nat := 1306238769791179542834482573973407241488195540151
private def create2Address : Nat := 467325607498788087893704697010616059068666523395

-- CREATE success, charged true, initial reservoir 250000.
#guard checkPinned
  ⟨(2 ^ 263 + 700), [3], parentMemory, (15437, 0, 250071, (-37), 17, 13), [(87, [26, (2 ^ 256 -
   1)], [0, 153])], [88], [], [90, createAddress], [(92, 49)]⟩
  ⟨0, [], [], (31, 13, 66400, 37, 11, 0), [(913, [919], [129, 0])], [947], [], [90, 929,
   createAddress], [(92, 49), (937, 941)]⟩
  ⟨(2 ^ 263 + 701), [createAddress, 3], parentMemory, (15481, 0, 250071, 0, 15, 13), [(87, [26, (2
   ^ 256 - 1)], [0, 153]), (913, [919], [129, 0])], [88, 947], [], [90, 929, createAddress], [(92,
   49), (937, 941)]⟩
  (by decide) (by decide) [173, 0, 239] none createAddress true

-- CREATE success, charged false, initial reservoir 250000.
#guard checkPinned
  ⟨(2 ^ 263 + 701), [3], parentMemory, (15437, 0, 250071, (-37), 17, 13), [(87, [26, (2 ^ 256 -
   1)], [0, 153])], [88], [], [90, createAddress], [(92, 49)]⟩
  ⟨0, [], [], (31, 13, 250000, 37, 11, 0), [(913, [919], [129, 0])], [947], [], [90, 929,
   createAddress], [(92, 49), (937, 941)]⟩
  ⟨(2 ^ 263 + 702), [createAddress, 3], parentMemory, (15481, 0, 250071, 0, 15, 13), [(87, [26, (2
   ^ 256 - 1)], [0, 153]), (913, [919], [129, 0])], [88, 947], [], [90, 929, createAddress], [(92,
   49), (937, 941)]⟩
  (by decide) (by decide) [173, 0, 239] none createAddress false

-- CREATE revert, charged true, initial reservoir 250000.
#guard checkPinned
  ⟨(2 ^ 263 + 702), [3], parentMemory, (15437, 0, 250071, (-37), 17, 13), [(87, [26, (2 ^ 256 -
   1)], [0, 153])], [88], [], [90, createAddress], [(92, 49)]⟩
  ⟨0, [], [], (42, 66400, 66400, 0, 0, 0), [(913, [919], [129, 0])], [947], [], [90, 929,
   createAddress], [(92, 49), (937, 941)]⟩
  ⟨(2 ^ 263 + 703), [0, 3], parentMemory, (15496, 249983, 250071, (-37), 0, 13), [(87, [26, (2 ^
   256 - 1)], [0, 153])], [88], [173, 0, 239], [90, createAddress], [(92, 49)]⟩
  (by decide) (by decide) [173, 0, 239] (some .revert) createAddress true

-- CREATE revert, charged true, initial reservoir 0.
#guard checkPinned
  ⟨(2 ^ 263 + 703), [3], parentMemory, (12568, 0, 71, (-37), 183617, 13), [(87, [26, (2 ^ 256 -
   1)], [0, 153])], [88], [], [90, createAddress], [(92, 49)]⟩
  ⟨0, [], [], (42, 0, 0, 0, 0, 0), [(913, [919], [129, 0])], [947], [], [90, 929, createAddress],
   [(92, 49), (937, 941)]⟩
  ⟨(2 ^ 263 + 704), [0, 3], parentMemory, (196210, 0, 71, (-37), 17, 13), [(87, [26, (2 ^ 256 -
   1)], [0, 153])], [88], [173, 0, 239], [90, createAddress], [(92, 49)]⟩
  (by decide) (by decide) [173, 0, 239] (some .revert) createAddress true

-- CREATE revert, charged false, initial reservoir 250000.
#guard checkPinned
  ⟨(2 ^ 263 + 704), [3], parentMemory, (15437, 0, 250071, (-37), 17, 13), [(87, [26, (2 ^ 256 -
   1)], [0, 153])], [88], [], [90, createAddress], [(92, 49)]⟩
  ⟨0, [], [], (42, 250000, 250000, 0, 0, 0), [(913, [919], [129, 0])], [947], [], [90, 929,
   createAddress], [(92, 49), (937, 941)]⟩
  ⟨(2 ^ 263 + 705), [0, 3], parentMemory, (15479, 250000, 250071, (-37), 17, 13), [(87, [26, (2 ^
   256 - 1)], [0, 153])], [88], [173, 0, 239], [90, createAddress], [(92, 49)]⟩
  (by decide) (by decide) [173, 0, 239] (some .revert) createAddress false

-- CREATE halt, charged true, initial reservoir 0.
#guard checkPinned
  ⟨(2 ^ 263 + 705), [3], parentMemory, (12568, 0, 71, (-37), 183617, 13), [(87, [26, (2 ^ 256 -
   1)], [0, 153])], [88], [], [90, createAddress], [(92, 49)]⟩
  ⟨0, [], [], (0, 0, 0, 0, 0, 0), [(913, [919], [129, 0])], [947], [], [90, 929, createAddress],
   [(92, 49), (937, 941)]⟩
  ⟨(2 ^ 263 + 706), [0, 3], parentMemory, (196168, 0, 71, (-37), 17, 13), [(87, [26, (2 ^ 256 -
   1)], [0, 153])], [88], [], [90, createAddress], [(92, 49)]⟩
  (by decide) (by decide) [] (some (.halt .outOfGas)) createAddress true

-- CREATE2 success, charged true, initial reservoir 250000.
#guard checkPinned
  ⟨(2 ^ 263 + 700), [3], parentMemory, (15437, 0, 250071, (-37), 17, 13), [(87, [26, (2 ^ 256 -
   1)], [0, 153])], [88], [], [90, create2Address], [(92, 49)]⟩
  ⟨0, [], [], (31, 13, 66400, 37, 11, 0), [(913, [919], [129, 0])], [947], [], [90, 929,
   create2Address], [(92, 49), (937, 941)]⟩
  ⟨(2 ^ 263 + 701), [create2Address, 3], parentMemory, (15481, 0, 250071, 0, 15, 13), [(87, [26,
   (2 ^ 256 - 1)], [0, 153]), (913, [919], [129, 0])], [88, 947], [], [90, 929, create2Address],
   [(92, 49), (937, 941)]⟩
  (by decide) (by decide) [173, 0, 239] none create2Address true

-- CREATE2 success, charged false, initial reservoir 250000.
#guard checkPinned
  ⟨(2 ^ 263 + 701), [3], parentMemory, (15437, 0, 250071, (-37), 17, 13), [(87, [26, (2 ^ 256 -
   1)], [0, 153])], [88], [], [90, create2Address], [(92, 49)]⟩
  ⟨0, [], [], (31, 13, 250000, 37, 11, 0), [(913, [919], [129, 0])], [947], [], [90, 929,
   create2Address], [(92, 49), (937, 941)]⟩
  ⟨(2 ^ 263 + 702), [create2Address, 3], parentMemory, (15481, 0, 250071, 0, 15, 13), [(87, [26,
   (2 ^ 256 - 1)], [0, 153]), (913, [919], [129, 0])], [88, 947], [], [90, 929, create2Address],
   [(92, 49), (937, 941)]⟩
  (by decide) (by decide) [173, 0, 239] none create2Address false

-- CREATE2 revert, charged true, initial reservoir 250000.
#guard checkPinned
  ⟨(2 ^ 263 + 702), [3], parentMemory, (15437, 0, 250071, (-37), 17, 13), [(87, [26, (2 ^ 256 -
   1)], [0, 153])], [88], [], [90, create2Address], [(92, 49)]⟩
  ⟨0, [], [], (42, 66400, 66400, 0, 0, 0), [(913, [919], [129, 0])], [947], [], [90, 929,
   create2Address], [(92, 49), (937, 941)]⟩
  ⟨(2 ^ 263 + 703), [0, 3], parentMemory, (15496, 249983, 250071, (-37), 0, 13), [(87, [26, (2 ^
   256 - 1)], [0, 153])], [88], [173, 0, 239], [90, create2Address], [(92, 49)]⟩
  (by decide) (by decide) [173, 0, 239] (some .revert) create2Address true

-- CREATE2 revert, charged true, initial reservoir 0.
#guard checkPinned
  ⟨(2 ^ 263 + 703), [3], parentMemory, (12568, 0, 71, (-37), 183617, 13), [(87, [26, (2 ^ 256 -
   1)], [0, 153])], [88], [], [90, create2Address], [(92, 49)]⟩
  ⟨0, [], [], (42, 0, 0, 0, 0, 0), [(913, [919], [129, 0])], [947], [], [90, 929, create2Address],
   [(92, 49), (937, 941)]⟩
  ⟨(2 ^ 263 + 704), [0, 3], parentMemory, (196210, 0, 71, (-37), 17, 13), [(87, [26, (2 ^ 256 -
   1)], [0, 153])], [88], [173, 0, 239], [90, create2Address], [(92, 49)]⟩
  (by decide) (by decide) [173, 0, 239] (some .revert) create2Address true

-- CREATE2 revert, charged false, initial reservoir 250000.
#guard checkPinned
  ⟨(2 ^ 263 + 704), [3], parentMemory, (15437, 0, 250071, (-37), 17, 13), [(87, [26, (2 ^ 256 -
   1)], [0, 153])], [88], [], [90, create2Address], [(92, 49)]⟩
  ⟨0, [], [], (42, 250000, 250000, 0, 0, 0), [(913, [919], [129, 0])], [947], [], [90, 929,
   create2Address], [(92, 49), (937, 941)]⟩
  ⟨(2 ^ 263 + 705), [0, 3], parentMemory, (15479, 250000, 250071, (-37), 17, 13), [(87, [26, (2 ^
   256 - 1)], [0, 153])], [88], [173, 0, 239], [90, create2Address], [(92, 49)]⟩
  (by decide) (by decide) [173, 0, 239] (some .revert) create2Address false

-- CREATE2 halt, charged true, initial reservoir 0.
#guard checkPinned
  ⟨(2 ^ 263 + 705), [3], parentMemory, (12568, 0, 71, (-37), 183617, 13), [(87, [26, (2 ^ 256 -
   1)], [0, 153])], [88], [], [90, create2Address], [(92, 49)]⟩
  ⟨0, [], [], (0, 0, 0, 0, 0, 0), [(913, [919], [129, 0])], [947], [], [90, 929, create2Address],
   [(92, 49), (937, 941)]⟩
  ⟨(2 ^ 263 + 706), [0, 3], parentMemory, (196168, 0, 71, (-37), 17, 13), [(87, [26, (2 ^ 256 -
   1)], [0, 153])], [88], [], [90, create2Address], [(92, 49)]⟩
  (by decide) (by decide) [] (some (.halt .outOfGas)) create2Address true

private def rawConfig (accountBytes costPerByte : Nat) : VmConfig :=
  let pinned := STFSpec.Fork.Amsterdam.vmConfig
  ⟨{ pinned.costs with warmAccess := accountBytes },
    ⟨costPerByte, accountBytes, 27, 39⟩,
    { pinned.limits with stackDepthLimit := 0 }⟩

private def rawParent : FrameView :=
  ⟨2 ^ 276 + 11, (2 ^ 256 - 1) :: List.replicate 1022 17, parentMemory,
    (9, 5, 43, -7, 17, 3), [(7, [8, 9], [0, 255])], [11], [127], [13], [(17, 19)]⟩

private def rawChild : FrameView :=
  ⟨47, [53, 59], [], (11, 13, 13, 0, 0, 0), [(61, [67], [71])], [73], [79], [83], [(89, 97)]⟩

private def rawOutput : List UInt8 := [0, 255, 231]

private def rawFailure (meter : Nat × Nat × Nat × Int × Nat × Nat) : FrameView :=
  { rawParent with
    pc := 2 ^ 276 + 12
    stack := 0 :: rawParent.stack
    meter := meter
    returnData := rawOutput }

-- The raw settled predicate admits this halt with nonempty output and returned gas.
#guard checkResume (rawConfig 3 5) rawParent rawChild (rawFailure (35, 18, 43, -7, 2, 3))
  (by decide) (by decide) rawOutput (some (.halt .outOfGas)) (2 ^ 160 - 1) true
#guard checkResume (rawConfig 5 3) rawParent rawChild (rawFailure (35, 18, 43, -7, 2, 3))
  (by decide) (by decide) rawOutput (some (.halt .outOfGas)) (2 ^ 160 - 1) true
#guard checkResume (rawConfig 0 5) rawParent rawChild (rawFailure (20, 18, 43, -7, 17, 3))
  (by decide) (by decide) rawOutput (some .revert) (2 ^ 160 - 1) true
#guard checkResume (rawConfig (2 ^ 270) 3) rawParent rawChild
  (rawFailure (37, 3 * 2 ^ 270 + 1, 43, -7, 0, 3))
  (by decide) (by decide) rawOutput (some .revert) (2 ^ 160 - 1) true

end STFSpec.Conformance.Vm.Instructions.CreateResumeControls
