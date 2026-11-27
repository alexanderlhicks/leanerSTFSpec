/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Fork.Amsterdam
import STFSpec.Hash
import STFSpec.Vm.Instructions

/-!
# CREATE and CREATE2 handler controls

Library `EthConformance`. Compare the two public handlers with the pinned EELS
wrappers at the first local exit or the entry to `process_create`. The controls
observe the complete parent frame, the request and prepared child, and the
ordered State and Keccak effects.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md` §§2.5/4.
-/

namespace STFSpec.Conformance.Vm.Instructions.CreateControls

open STFSpec.Base STFSpec.Hash STFSpec.State STFSpec.Vm.Core STFSpec.Vm.Instructions

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

private def parentMemory : List UInt8 :=
  [31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16,
    15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]

private def parentView (index : Nat) (stack : List Nat) (gas reservoir baseline : Nat) :
    FrameView :=
  ⟨2 ^ 263 + 700 + index, stack, parentMemory, (gas, reservoir, baseline, -37, 17, 13),
    [(87, [26, 2 ^ 256 - 1], [0, 153])], [88], [33, 128, 0, 255], [90], [(92, 49)]⟩

private def fromParentView (v : FrameView) : Option Frame := do
  let stack ← v.stack.reverse.foldlM
    (fun stack value ↦ (stack.push (U256.ofNat value)).toOption) Stack.empty
  let expanded := Memory.empty.expand 32 (by decide)
  let memory := expanded.write 0 (Bytes.ofList parentMemory) (by
    right
    rw [Nat.zero_add, Bytes.size_ofList, ← Memory.length_toBytes, Memory.toBytes_expand,
      Memory.toBytes_empty]
    decide)
  let (gas, reservoir, baseline, refund, spill, committed) := v.meter
  let logs := v.logs.map fun (a, topics, data) ↦
    Log.mk (Address.ofNat a) ((topics.map fun value ↦
      Hash32.ofBytes32 (FixedBytes.ofNat value)).toArray) (Bytes.ofList data)
  return ⟨v.pc, stack, memory, ⟨gas, reservoir, baseline, refund, spill, committed⟩,
    .leaf logs, v.deleted.foldl (fun acc a ↦ acc.insert (Address.ofNat a)) (∅ : AddrSet),
    Bytes.ofList v.returnData,
    v.addresses.foldl (fun acc a ↦ acc.insert (Address.ofNat a)) (∅ : AddrSet),
    v.slots.foldl (fun acc (a, k) ↦ (acc : SlotSet).insert (Address.ofNat a,
      FixedBytes.ofNat k)) (∅ : SlotSet)⟩

private def sender := Address.ofNat 13
private def key (n : Nat) := Hash32.ofBytes32 (FixedBytes.ofNat n)
private def consts : HashConsts := Id.run (HashConsts.query (m := Id))

private def context (depth : Nat) (within : depth ≤ STACK_DEPTH_LIMIT) : FrameCtx :=
  ⟨STFSpec.Fork.Amsterdam.vmConfig,
    ⟨U64.ofNat 11, 13, #[key 17], Address.ofNat 23, 29, 31, U256.ofNat 37,
      FixedBytes.ofNat 41, U64.ofNat 43, key 47, U64.ofNat 53⟩,
    ⟨Address.ofNat 59, Address.ofNat 61, true, Bytes.ofList [0, 128, 0], U256.ofNat 67, 71, 73,
      79, 83, 89, ∅, ∅, #[], #[], some 0, some (key 97)⟩,
    Address.ofNat 101, sender, U256.zero, Bytes.empty, none, Bytes.empty,
    validJumpDestinations Bytes.empty, depth, within, true, false, false, Address.ofNat 107⟩

private def handler {m : Type → Type} [Monad m] [KeccakQuery m] (salted : Bool) : Handler m :=
  if salted then create2 else create

private abbrev Trace := List (Nat × List UInt8)
private abbrev TraceM := StateT Trace Id

local instance : KeccakQuery TraceM where
  keccak data := do
    modify fun events ↦ (1, data.toList) :: events
    pure (Id.run (KeccakQuery.keccak (m := Id) data))

private def initialWorld (failure : Option Address) (balance : Nat) : VmWorld TraceM :=
  let pre : PreState TraceM := ⟨fun address ↦ do
    modify fun events ↦ (0, address.toBytes.toList) :: events
    if failure = some address then pure (.error (.missing (.node (key address.toNat))))
    else if address = sender then
      pure (.ok (some (Account.mk 4 (U256.ofNat balance) consts.emptyCodeHash)))
    else pure (.ok none),
    fun _ _ ↦ pure (.ok U256.zero),
    fun _ ↦ pure (.ok ByteArray.empty),
    fun _ ↦ pure (.ok (key 5))⟩
  let block : BlockState TraceM := ⟨pre, consts, ∅, ⟨0, ∅, ∅⟩, ∅, ⟨0, ∅, ∅⟩, ∅, ∅, ∅,
    ∅, ∅, ∅, none⟩
  let stale := Address.ofNat 14
  let writes := (∅ : Std.ExtTreeMap Address (Option Account)).insert stale none
  let order : WriteOrder Address := ⟨0, ∅, ∅⟩
  let rev : TxRevertible := ⟨writes, order.record stale, ∅, ⟨0, ∅, ∅⟩, ∅, ∅, ∅, ∅⟩
  ⟨⟨block, rev, ⟨(∅ : Std.HashSet Address).insert (Address.ofNat 7), ∅, ∅, ∅⟩⟩⟩

private def childView (gas reservoir target : Nat) : FrameView :=
  ⟨0, [], [], (gas, reservoir, reservoir, 0, 0, 0), [], [], [], [90, target], [(92, 49)]⟩

private def checkChild (ctx : FrameCtx) (frame : Frame) (req : CreateRequest)
    (deeper : ctx.depth < STACK_DEPTH_LIMIT)
    (target : Nat) (init : List UInt8) (charged : Bool) (child : FrameView) : Bool :=
  let built := childFrame frame req.gas req.stateGasReservoir
  let childCtx := childCtxOfCreate ctx req deeper
  decide (view built = child ∧ childCtx.depth = ctx.depth + 1 ∧
    req.contractAddress.toNat = target ∧ req.endowment.toNat = 5 ∧
    req.caller = sender ∧ req.initCode.toList = init ∧ req.newAccountCharged = charged)

private def sameEarlyHalt : ExceptionalHalt → ExceptionalHalt → Bool
  | .writeInStaticContext, .writeInStaticContext
  | .stackUnderflow, .stackUnderflow
  | .outOfGas, .outOfGas => true
  | _, _ => false

private def checkEarly (salted static : Bool) (error : ExceptionalHalt)
    (before after : FrameView) : Bool := Id.run do
  let some parent := fromParentView before | return false
  let ctx := { context 0 (by decide) with isStatic := static }
  let run := ((handler salted ctx parent).run (initialWorld (some sender) 0)).run
  let (result, events) := Id.run (run.run [])
  match result with
  | .ok (.halt frame actual, world) =>
    return decide (view parent = before ∧ view frame = after ∧
      sameEarlyHalt actual error = true ∧ events = [] ∧
      (world.tx.obs.accountReads.toList.map Address.toNat) = [7] ∧
      (world.tx.rev.accountOrder.toList.map Address.toNat) = [14])
  | _ => return false

private structure OverlayCase where
  nonce : Nat
  balance : Nat
  destination : Nat
  targetAccount : Option (Nat × Nat)
  targetStorage : Bool
  expectedNonce : Nat

private def withOverlay (row : OverlayCase) : VmWorld TraceM :=
  let world := initialWorld (some sender) row.balance
  let tx := world.tx
  let destination := Address.ofNat row.destination
  let account := row.targetAccount.map fun (nonce, balance) ↦
    Account.mk nonce (U256.ofNat balance) consts.emptyCodeHash
  let writes := (tx.rev.accountWrites.insert sender
    (some (Account.mk row.nonce (U256.ofNat row.balance) consts.emptyCodeHash))).insert
      destination account
  let storage := if row.targetStorage then
    tx.rev.storageWrites.insert destination
      ((∅ : Std.ExtTreeMap Bytes32 U256).insert (FixedBytes.ofNat 37) (U256.ofNat 63))
  else tx.rev.storageWrites
  let rev := { tx.rev with accountWrites := writes, storageWrites := storage }
  { world with tx := { tx with rev } }

private def checkOverlay (salted : Bool) (kind : Nat) (ctx : FrameCtx)
    (before after : FrameView) (row : OverlayCase) (child : Option FrameView) : Bool := Id.run do
  let some parent := fromParentView before | return false
  let run := ((handler salted ctx parent).run (withOverlay row)).run
  let (result, events) := Id.run (run.run [])
  let .ok (outcome, world) := result | return false
  let tx := world.tx
  let destination := Address.ofNat row.destination
  let writes := tx.rev.accountWrites
  let expectedTarget := row.targetAccount.map fun (nonce, balance) ↦
    Account.mk nonce (U256.ofNat balance) consts.emptyCodeHash
  let readAddresses := (tx.obs.accountReads.toList.map Address.toNat).mergeSort
  let reads := if kind = 0 && row.expectedNonce = row.nonce then [7, 13]
    else [7, 13, row.destination]
  let order := if row.expectedNonce = row.nonce then [14] else [14, 13]
  let storage := tx.rev.storageWrites[destination]?.bind fun slots ↦
    slots[(FixedBytes.ofNat 37 : Bytes32)]?
  let expectedStorage := if row.targetStorage then some (U256.ofNat 63) else none
  if ¬ (view parent = before ∧
      writes[sender]?.join = some (Account.mk row.expectedNonce (U256.ofNat row.balance)
        consts.emptyCodeHash) ∧ writes[destination]? = some expectedTarget ∧
      writes[Address.ofNat 14]? = some none ∧ writes.size = 3 ∧ readAddresses = reads ∧
      (tx.rev.accountOrder.toList.map Address.toNat) = order ∧ storage = expectedStorage ∧
      tx.obs.storageReads.isEmpty ∧ tx.obs.codeReads.isEmpty ∧ tx.obs.createdAccounts.isEmpty ∧
      events.length = (if salted then 2 else 1) ∧ events.all (·.1 == 1)) then
    return false
  match outcome with
  | .continue frame => return decide (kind = 0 ∧ view frame = after)
  | .halt frame .outOfGas => return decide (kind = 1 ∧ view frame = after)
  | .create frame req deeper _ =>
    let some built := child | return false
    return (kind == 2 && decide (view frame = after) &&
      checkChild ctx frame req deeper row.destination [29, 28, 27] row.targetAccount.isNone built)
  | _ => return false

private inductive TraceResult where
  | staticHalt
  | missing (address : Nat)
  | insufficientBalance
  | dispatch (address : Nat) (child : FrameView)

private def checkTrace (salted : Bool) (balance : Nat) (before after : FrameView)
    (expected : TraceResult) (events : Trace) (reads order : List Nat) : Bool := Id.run do
  let some parent := fromParentView before | return false
  let static := match expected with | .staticHalt => true | _ => false
  let failure := match expected with | .missing a => some (Address.ofNat a) | _ => none
  let ctx := { context 0 (by decide) with isStatic := static }
  let run := ((handler salted ctx parent).run (initialWorld failure balance)).run
  let (result, actualEvents) := Id.run (run.run [])
  if view parent ≠ before ∨ actualEvents.reverse ≠ events then return false
  match expected, result with
  | .missing address, .error (.state (.witness (.missing (.node actual)))) =>
    return decide (actual = key address)
  | _, .ok (outcome, world) =>
    let tx := world.tx
    let readList := (tx.obs.accountReads.toList.map Address.toNat).mergeSort
    let orderList := tx.rev.accountOrder.toList.map Address.toNat
    if readList ≠ reads ∨ orderList ≠ order then return false
    match expected, outcome with
    | .staticHalt, .halt frame .writeInStaticContext => return decide (view frame = after)
    | .insufficientBalance, .continue frame => return decide (view frame = after)
    | .dispatch target child, .create frame req deeper _ =>
      return (decide (view frame = after ∧
        tx.rev.accountWrites[sender]?.join = some (Account.mk 5 (U256.ofNat balance)
          consts.emptyCodeHash)) &&
        checkChild ctx frame req deeper target [0, 0, 0] true child)
    | _, _ => return false
  | _, _ => return false

private def createAddress : Nat := 1399957342458449829415449262875661016032825821046
private def create2Address : Nat := 467325607498788087893704697010616059068666523395
private def create2ExpandedAddress : Nat := 1035193371977834085574074371184957699501160593194
private def createWideNonceAddress : Nat := 52847940081690334075868579615170458299306081310

-- CREATE static.
#guard checkEarly false true .writeInStaticContext
  (parentView 0 [] 7 31 71)
  (parentView 0 [] 7 31 71)

-- CREATE underflow-0.
#guard checkEarly false false .stackUnderflow
  (parentView 1 [] 100000 31 71)
  (parentView 1 [] 100000 31 71)

-- CREATE underflow-1.
#guard checkEarly false false .stackUnderflow
  (parentView 2 [1] 100000 31 71)
  (parentView 2 [] 100000 31 71)

-- CREATE underflow-2.
#guard checkEarly false false .stackUnderflow
  (parentView 3 [2, 1] 100000 31 71)
  (parentView 3 [] 100000 31 71)

-- CREATE unpaid-oversize.
#guard checkEarly false false .outOfGas
  (parentView 4 [0, 19, 131073] 12000 31 71)
  (parentView 4 [] 12000 31 71)

-- CREATE paid-oversize.
#guard checkEarly false false .outOfGas
  (parentView 5 [0, 19, 131073] 1000000 31 71)
  (parentView 5 [] 934734 31 71)

-- CREATE2 static.
#guard checkEarly true true .writeInStaticContext
  (parentView 6 [] 7 31 71)
  (parentView 6 [] 7 31 71)

-- CREATE2 underflow-0.
#guard checkEarly true false .stackUnderflow
  (parentView 7 [] 100000 31 71)
  (parentView 7 [] 100000 31 71)

-- CREATE2 underflow-1.
#guard checkEarly true false .stackUnderflow
  (parentView 8 [1] 100000 31 71)
  (parentView 8 [] 100000 31 71)

-- CREATE2 underflow-2.
#guard checkEarly true false .stackUnderflow
  (parentView 9 [2, 1] 100000 31 71)
  (parentView 9 [] 100000 31 71)

-- CREATE2 underflow-3.
#guard checkEarly true false .stackUnderflow
  (parentView 10 [3, 2, 1] 100000 31 71)
  (parentView 10 [] 100000 31 71)

-- CREATE2 unpaid-oversize.
#guard checkEarly true false .outOfGas
  (parentView 11 [0, 19, 131073, 19] 12000 31 71)
  (parentView 11 [] 12000 31 71)

-- CREATE2 paid-oversize.
#guard checkEarly true false .outOfGas
  (parentView 12 [0, 19, 131073, 19] 1000000 31 71)
  (parentView 12 [] 910152 31 71)

-- CREATE balance.
#guard checkOverlay false 0 (context 0 (by decide))
  (parentView 0 [5, 2, 3, 3] 1000000 240000 240071)
  { parentView 1 [0, 3] 987998 240000 240071 with
    returnData := [] }
  ⟨4, 2, createAddress, none, false,
    4⟩ none

-- CREATE max-nonce.
#guard checkOverlay false 0 (context 0 (by decide))
  (parentView 1 [5, 2, 3, 3] 1000000 240000 240071)
  { parentView 2 [0, 3] 987998 240000 240071 with
    returnData := [] }
  ⟨18446744073709551615, 11, 1122277603772745162125417827708389019474603683337, none, false,
    18446744073709551615⟩ none

-- CREATE max-depth.
#guard checkOverlay false 0 (context 1024 (by decide))
  (parentView 2 [5, 2, 3, 3] 1000000 240000 240071)
  { parentView 3 [0, 3] 987998 240000 240071 with
    returnData := [] }
  ⟨4, 11, createAddress, none, false,
    4⟩ none

-- CREATE warm-before-shortage.
#guard checkOverlay false 1 (context 0 (by decide))
  (parentView 3 [5, 2, 3, 3] 20000 3 74)
  { parentView 3 [3] 7998 3 74 with
    returnData := []
    addresses := [90, createAddress] }
  ⟨4, 11, createAddress, none, false,
    4⟩ none

-- CREATE collision.
#guard checkOverlay false 0 (context 0 (by decide))
  (parentView 4 [5, 2, 3, 3] 1000000 240000 240071)
  { parentView 5 [0, 3] 15437 240000 240071 with
    returnData := []
    addresses := [90, createAddress] }
  ⟨4, 11, createAddress, (some (1, 2)), false,
    5⟩ none

-- CREATE new-from-reservoir.
#guard checkOverlay false 2 (context 0 (by decide))
  (parentView 5 [5, 2, 3, 3] 1000000 240000 240071)
  { parentView 5 [3] 15437 0 240071 with
    returnData := []
    addresses := [90, createAddress] }
  ⟨4, 11, createAddress, none, false,
    5⟩ (some (childView 972561 56400 createAddress))

-- CREATE alive-deployable-with-storage.
#guard checkOverlay false 2 (context 0 (by decide))
  (parentView 6 [5, 2, 3, 3] 1000000 240000 240071)
  { parentView 6 [3] 15437 0 240071 with
    returnData := []
    addresses := [90, createAddress] }
  ⟨4, 11, createAddress, (some (0, 2)), true,
    5⟩ (some (childView 972561 240000 createAddress))

-- CREATE new-from-execution.
#guard checkOverlay false 2 (context 0 (by decide))
  (parentView 7 [5, 2, 3, 3] 1000000 3 74)
  { parentView 7 [3] 12568 0 74 with
    meter := (12568, 0, 74, -37, 183614, 13)
    returnData := []
    addresses := [90, createAddress] }
  ⟨4, 11, createAddress, none, false,
    5⟩ (some (childView 791833 0 createAddress))

-- CREATE nonce-above-word.
#guard checkOverlay false 2 (context 0 (by decide))
  (parentView 8 [5, 2, 3, 3] 1000000 240000 240071)
  { parentView 8 [3] 15437 0 240071 with
    returnData := []
    addresses := [90, createWideNonceAddress] }
  ⟨18446744073709551617, 11, createWideNonceAddress, none, false,
    18446744073709551618⟩ (some (childView 972561 56400 createWideNonceAddress))

-- CREATE2 balance.
#guard checkOverlay true 0 (context 0 (by decide))
  (parentView 9 [5, 2, 3, 19, 3] 1000000 240000 240071)
  { parentView 10 [0, 3] 987992 240000 240071 with
    returnData := [] }
  ⟨4, 2, create2Address, none, false,
    4⟩ none

-- CREATE2 max-nonce.
#guard checkOverlay true 0 (context 0 (by decide))
  (parentView 10 [5, 2, 3, 19, 3] 1000000 240000 240071)
  { parentView 11 [0, 3] 987992 240000 240071 with
    returnData := [] }
  ⟨18446744073709551615, 11, create2Address, none, false,
    18446744073709551615⟩ none

-- CREATE2 max-depth.
#guard checkOverlay true 0 (context 1024 (by decide))
  (parentView 11 [5, 2, 3, 19, 3] 1000000 240000 240071)
  { parentView 12 [0, 3] 987992 240000 240071 with
    returnData := [] }
  ⟨4, 11, create2Address, none, false,
    4⟩ none

-- CREATE2 warm-before-shortage.
#guard checkOverlay true 1 (context 0 (by decide))
  (parentView 12 [5, 2, 3, 19, 3] 20000 3 74)
  { parentView 12 [3] 7992 3 74 with
    returnData := []
    addresses := [90, create2Address] }
  ⟨4, 11, create2Address, none, false,
    4⟩ none

-- CREATE2 collision.
#guard checkOverlay true 0 (context 0 (by decide))
  (parentView 13 [5, 2, 3, 19, 3] 1000000 240000 240071)
  { parentView 14 [0, 3] 15437 240000 240071 with
    returnData := []
    addresses := [90, create2Address] }
  ⟨4, 11, create2Address, (some (1, 2)), false,
    5⟩ none

-- CREATE2 new-from-reservoir.
#guard checkOverlay true 2 (context 0 (by decide))
  (parentView 14 [5, 2, 3, 19, 3] 1000000 240000 240071)
  { parentView 14 [3] 15437 0 240071 with
    returnData := []
    addresses := [90, create2Address] }
  ⟨4, 11, create2Address, none, false,
    5⟩ (some (childView 972555 56400 create2Address))

-- CREATE2 alive-deployable-with-storage.
#guard checkOverlay true 2 (context 0 (by decide))
  (parentView 15 [5, 2, 3, 19, 3] 1000000 240000 240071)
  { parentView 15 [3] 15437 0 240071 with
    returnData := []
    addresses := [90, create2Address] }
  ⟨4, 11, create2Address, (some (0, 2)), true,
    5⟩ (some (childView 972555 240000 create2Address))

-- CREATE2 new-from-execution.
#guard checkOverlay true 2 (context 0 (by decide))
  (parentView 16 [5, 2, 3, 19, 3] 1000000 3 74)
  { parentView 16 [3] 12568 0 74 with
    meter := (12568, 0, 74, -37, 183614, 13)
    returnData := []
    addresses := [90, create2Address] }
  ⟨4, 11, create2Address, none, false,
    5⟩ (some (childView 791827 0 create2Address))

-- CREATE2 nonce-above-word.
#guard checkOverlay true 2 (context 0 (by decide))
  (parentView 17 [5, 2, 3, 19, 3] 1000000 240000 240071)
  { parentView 17 [3] 15437 0 240071 with
    returnData := []
    addresses := [90, create2Address] }
  ⟨18446744073709551617, 11, create2Address, none, false,
    18446744073709551618⟩ (some (childView 972555 56400 create2Address))

-- CREATE static.
#guard checkTrace false 11
  (parentView 0 [5, 34, 3, 3] 1000000 240000 240071)
  (parentView 0 [5, 34, 3, 3] 1000000 240000 240071)
  .staticHalt
  []
  [7] [14]

-- CREATE missing sender.
#guard checkTrace false 11
  (parentView 0 [5, 34, 3, 3] 1000000 240000 240071)
  { parentView 0 [3] 987995 240000 240071 with
    memory := parentMemory ++ List.replicate 32 0 }
  (.missing 13)
  [(0, [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x0d])]
  [7, 13] [14]

-- CREATE balance.
#guard checkTrace false 2
  (parentView 0 [5, 34, 3, 3] 1000000 240000 240071)
  { parentView 1 [0, 3] 987995 240000 240071 with
    returnData := []
    memory := parentMemory ++ List.replicate 32 0 }
  .insufficientBalance
  [(0, [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x0d]),
    (1, [0xd6, 0x94, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0d, 0x04]),
    (0, [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x0d])]
  [7, 13] [14]

-- CREATE missing destination.
#guard checkTrace false 11
  (parentView 0 [5, 34, 3, 3] 1000000 240000 240071)
  { parentView 0 [3] 987995 240000 240071 with
    returnData := []
    memory := parentMemory ++ List.replicate 32 0
    addresses := [90, createAddress] }
  (.missing createAddress)
  [(0, [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x0d]),
    (1, [0xd6, 0x94, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0d, 0x04]),
    (0, [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x0d]),
    (0, [0xf5, 0x38, 0x42, 0x24, 0xa1, 0x56, 0x7a, 0x51, 0x5f, 0xe7, 0xde, 0xfe, 0xa7, 0x8e,
      0xf8, 0x62, 0x16, 0xf7, 0xc7, 0x76])]
  [7, 13, createAddress] [14]

-- CREATE dispatch.
#guard checkTrace false 11
  (parentView 0 [5, 34, 3, 3] 1000000 240000 240071)
  { parentView 0 [3] 15437 0 240071 with
    returnData := []
    memory := parentMemory ++ List.replicate 32 0
    addresses := [90, createAddress] }
  (.dispatch createAddress (childView 972558 56400 createAddress))
  [(0, [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x0d]),
    (1, [0xd6, 0x94, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0d, 0x04]),
    (0, [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x0d]),
    (0, [0xf5, 0x38, 0x42, 0x24, 0xa1, 0x56, 0x7a, 0x51, 0x5f, 0xe7, 0xde, 0xfe, 0xa7, 0x8e,
      0xf8, 0x62, 0x16, 0xf7, 0xc7, 0x76]),
    (0, [0xf5, 0x38, 0x42, 0x24, 0xa1, 0x56, 0x7a, 0x51, 0x5f, 0xe7, 0xde, 0xfe, 0xa7, 0x8e,
      0xf8, 0x62, 0x16, 0xf7, 0xc7, 0x76]),
    (0, [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x0d])]
  [7, 13, createAddress] [14, 13]

-- CREATE2 static.
#guard checkTrace true 11
  (parentView 0 [5, 34, 3, 19, 3] 1000000 240000 240071)
  (parentView 0 [5, 34, 3, 19, 3] 1000000 240000 240071)
  .staticHalt
  []
  [7] [14]

-- CREATE2 missing sender.
#guard checkTrace true 11
  (parentView 0 [5, 34, 3, 19, 3] 1000000 240000 240071)
  { parentView 0 [3] 987989 240000 240071 with
    returnData := []
    memory := parentMemory ++ List.replicate 32 0 }
  (.missing 13)
  [(1, [0x00, 0x00, 0x00]),
    (1, [0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0d, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x13, 0x99, 0xff, 0x0d,
      0x91, 0x25, 0xe1, 0xfc, 0x95, 0x31, 0xa1, 0x12, 0x62, 0xe1, 0x5a, 0xeb, 0x2c, 0x60,
      0x50, 0x9a, 0x07, 0x8c, 0x4c, 0xc4, 0xc6, 0x4c, 0xef, 0xdf, 0xb0, 0x6f, 0xf6, 0x86,
      0x47]),
    (0, [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x0d])]
  [7, 13] [14]

-- CREATE2 balance.
#guard checkTrace true 2
  (parentView 0 [5, 34, 3, 19, 3] 1000000 240000 240071)
  { parentView 1 [0, 3] 987989 240000 240071 with
    returnData := []
    memory := parentMemory ++ List.replicate 32 0 }
  .insufficientBalance
  [(1, [0x00, 0x00, 0x00]),
    (1, [0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0d, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x13, 0x99, 0xff, 0x0d,
      0x91, 0x25, 0xe1, 0xfc, 0x95, 0x31, 0xa1, 0x12, 0x62, 0xe1, 0x5a, 0xeb, 0x2c, 0x60,
      0x50, 0x9a, 0x07, 0x8c, 0x4c, 0xc4, 0xc6, 0x4c, 0xef, 0xdf, 0xb0, 0x6f, 0xf6, 0x86,
      0x47]),
    (0, [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x0d])]
  [7, 13] [14]

-- CREATE2 missing destination.
#guard checkTrace true 11
  (parentView 0 [5, 34, 3, 19, 3] 1000000 240000 240071)
  { parentView 0 [3] 987989 240000 240071 with
    returnData := []
    memory := parentMemory ++ List.replicate 32 0
    addresses := [90, create2ExpandedAddress] }
  (.missing create2ExpandedAddress)
  [(1, [0x00, 0x00, 0x00]),
    (1, [0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0d, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x13, 0x99, 0xff, 0x0d,
      0x91, 0x25, 0xe1, 0xfc, 0x95, 0x31, 0xa1, 0x12, 0x62, 0xe1, 0x5a, 0xeb, 0x2c, 0x60,
      0x50, 0x9a, 0x07, 0x8c, 0x4c, 0xc4, 0xc6, 0x4c, 0xef, 0xdf, 0xb0, 0x6f, 0xf6, 0x86,
      0x47]),
    (0, [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x0d]),
    (0, [0xb5, 0x53, 0xad, 0x1d, 0xeb, 0xea, 0x84, 0x0c, 0x6e, 0x22, 0x13, 0x6e, 0xb3, 0xd1,
      0x1b, 0xad, 0x33, 0xfe, 0xf7, 0x2a])]
  [7, 13, create2ExpandedAddress] [14]

-- CREATE2 dispatch.
#guard checkTrace true 11
  (parentView 0 [5, 34, 3, 19, 3] 1000000 240000 240071)
  { parentView 0 [3] 15437 0 240071 with
    returnData := []
    memory := parentMemory ++ List.replicate 32 0
    addresses := [90, create2ExpandedAddress] }
  (.dispatch create2ExpandedAddress (childView 972552 56400 create2ExpandedAddress))
  [(1, [0x00, 0x00, 0x00]),
    (1, [0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0d, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x13, 0x99, 0xff, 0x0d,
      0x91, 0x25, 0xe1, 0xfc, 0x95, 0x31, 0xa1, 0x12, 0x62, 0xe1, 0x5a, 0xeb, 0x2c, 0x60,
      0x50, 0x9a, 0x07, 0x8c, 0x4c, 0xc4, 0xc6, 0x4c, 0xef, 0xdf, 0xb0, 0x6f, 0xf6, 0x86,
      0x47]),
    (0, [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x0d]),
    (0, [0xb5, 0x53, 0xad, 0x1d, 0xeb, 0xea, 0x84, 0x0c, 0x6e, 0x22, 0x13, 0x6e, 0xb3, 0xd1,
      0x1b, 0xad, 0x33, 0xfe, 0xf7, 0x2a]),
    (0, [0xb5, 0x53, 0xad, 0x1d, 0xeb, 0xea, 0x84, 0x0c, 0x6e, 0x22, 0x13, 0x6e, 0xb3, 0xd1,
      0x1b, 0xad, 0x33, 0xfe, 0xf7, 0x2a]),
    (0, [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x0d])]
  [7, 13, create2ExpandedAddress] [14, 13]

end STFSpec.Conformance.Vm.Instructions.CreateControls
