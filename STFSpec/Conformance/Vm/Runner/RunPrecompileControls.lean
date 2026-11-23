/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Runner

/-!
# Precompile frame adapter controls

Library `EthConformance`. The clients use the Runner facade and compare complete
frames. See `STFSpec/informal/modules/EthVmRunner.md` §4.
-/

namespace STFSpec.Conformance.Vm.Runner.RunPrecompileControls

open STFSpec.Base STFSpec.Vm.Core STFSpec.Vm.Runner

private theorem literal_run {m : Type → Type} [Monad m]
    (p : PrecompileFn m) (f : Frame) (input : Bytes) :
    runPrecompile p f input = (do
      match ← p input f.gasMeter with
      | .ok paid output => pure ⟨{ f with gasMeter := paid }, output, none⟩
      | .halt error =>
        let restored := restoreStateGas f.gasMeter
        let meter := forfeitRemainingGas restored (restoreStateGas_post f.gasMeter).1
        pure ⟨{ f with gasMeter := meter }, Bytes.empty, some (.halt error)⟩) := rfl

private theorem id_success (p : PrecompileFn Id) (f : Frame) (input output : Bytes)
    (paid : GasMeter) (success : p input f.gasMeter = .ok paid output) :
    runPrecompile p f input = ⟨{ f with gasMeter := paid }, output, none⟩ := by
  simp only [runPrecompile, success]
  rfl

private theorem id_halt (p : PrecompileFn Id) (f : Frame) (input : Bytes)
    (error : ExceptionalHalt) (failure : p input f.gasMeter = .halt error) :
    runPrecompile p f input = ⟨{ f with
      gasMeter := { f.gasMeter with
        gasLeft := 0
        stateGasLeft := f.gasMeter.stateGasBaseline
        stateGasSpilled := 0
        refundCounter := 0 } }, Bytes.empty, some (.halt error)⟩ := by
  simp only [runPrecompile, failure, forfeitRemainingGas_eq, restoreStateGas_eq]
  rfl

private theorem halt_after_debit (f : Frame) (input : Bytes) (error : ExceptionalHalt)
    (paid : GasMeter) (related : { paid with gasLeft := f.gasMeter.gasLeft } = f.gasMeter) :
    runPrecompile (m := Id) (fun _ _ ↦ .halt error) { f with gasMeter := paid } input =
      runPrecompile (m := Id) (fun _ _ ↦ .halt error) f input := by
  have baseline := congrArg GasMeter.stateGasBaseline related
  have committed := congrArg GasMeter.stateGasCommittedSpill related
  change paid.stateGasBaseline = f.gasMeter.stateGasBaseline at baseline
  change paid.stateGasCommittedSpill = f.gasMeter.stateGasCommittedSpill at committed
  simp [runPrecompile, forfeitRemainingGas_eq, restoreStateGas_eq, baseline, committed]

private theorem certified_id_success (table : PrecompileTable Id) (address : Address)
    (p : PrecompileFn Id) (f : Frame) (input output : Bytes) (paid : GasMeter)
    (installed : table.lookup address = some p) (success : p input f.gasMeter = .ok paid output) :
    let result : FrameResult := runPrecompile p f input
    result.frame.gasMeter.phi ≤ f.gasMeter.phi ∧
      { result.frame.gasMeter with gasLeft := f.gasMeter.gasLeft } = f.gasMeter := by
  dsimp only
  rw [id_success p f input output paid success]
  have rule := (satisfiesM_id_iff (MeterOk f.gasMeter) (p input f.gasMeter)).mp
    (table.meter_law address p input f.gasMeter installed)
  rw [success] at rule
  change paid.gasLeft ≤ f.gasMeter.gasLeft ∧
    { paid with gasLeft := f.gasMeter.gasLeft } = f.gasMeter at rule
  have pending := congrArg GasMeter.stateGasSpilled rule.2
  have committed := congrArg GasMeter.stateGasCommittedSpill rule.2
  change paid.stateGasSpilled = f.gasMeter.stateGasSpilled at pending
  change paid.stateGasCommittedSpill = f.gasMeter.stateGasCommittedSpill at committed
  exact ⟨by simp only [GasMeter.phi, pending, committed]; omega, rule.2⟩

private theorem option_failure (f : Frame) (input : Bytes) :
    runPrecompile (m := Option) (fun _ _ ↦ none) f input = none := rfl

private def addr := Address.ofNat 257
private def key : Bytes32 := FixedBytes.ofNat 263
private def topic := Hash32.ofBytes32 (FixedBytes.ofNat 269)
private def input := Bytes.ofList [0, 128, 255]
private def answer := Bytes.ofList [239, 0, 128, 17]
private def entryMeter : GasMeter := ⟨29, 31, 37, -41, 43, 47⟩
private def paidMeter : GasMeter := ⟨11, 53, 59, 61, 67, 71⟩
private def haltedMeter : GasMeter := ⟨0, 37, 37, 0, 0, 47⟩

private def frame (meter : GasMeter) : Frame :=
  let log : Log := ⟨addr, #[topic], Bytes.ofList [73, 0, 255]⟩
  ⟨2 ^ 256 + 79, (Stack.empty.push U256.max).toOption.getD Stack.empty,
    Memory.empty.expand 32 (by decide), meter, .concat .empty (.leaf [log]),
    (∅ : AddrSet).insert addr, Bytes.ofList [83, 0, 128],
    (∅ : AddrSet).insert (Address.ofNat 89), (∅ : SlotSet).insert (addr, key)⟩

private def meterModel (g : GasMeter) :=
  (g.gasLeft, g.stateGasLeft, g.stateGasBaseline, g.refundCounter,
    g.stateGasSpilled, g.stateGasCommittedSpill)

private def frameModel (f : Frame) :=
  (f.pc, f.stack.toList.map U256.toNat, f.memory.toBytes, meterModel f.gasMeter,
    f.logs.toList.map (fun log ↦
      (log.address.toNat, log.topics.toList.map Hash32.toNat, log.data.toList)),
    f.accountsToDelete.toList.map Address.toNat, f.returnData.toList,
    f.accessedAddresses.toList.map Address.toNat,
    f.accessedStorageKeys.toList.map (fun (a, slot) ↦ (a.toNat, slot.toNat)))

private def observedCall : PrecompileFn (StateM (Nat × Bool)) := fun bytes meter ↦ do
  let (count, _) ← get
  set (count + 1, bytes.toList == input.toList && meterModel meter == meterModel entryMeter)
  pure (.ok paidMeter answer)

private def successControl : Bool :=
  let (result, observation) := (runPrecompile observedCall (frame entryMeter) input).run (0, false)
  observation == (1, true) && result.error.isNone &&
    frameModel result.frame == frameModel (frame paidMeter) && result.output.toList == answer.toList

private def haltControl (error : ExceptionalHalt)
    (matchesError : Option FrameError → Bool) : Bool :=
  let result : FrameResult := runPrecompile (m := Id) (fun _ _ ↦ .halt error) (frame entryMeter) input
  matchesError result.error && frameModel result.frame == frameModel (frame haltedMeter) &&
    result.output.toList.isEmpty

#guard successControl
#guard haltControl .outOfGas (fun | some (.halt .outOfGas) => true | _ => false)
#guard haltControl .invalidParameter (fun | some (.halt .invalidParameter) => true | _ => false)
#guard haltControl (.precompileHalt "bounded probe")
  (fun | some (.halt (.precompileHalt reason)) => reason == "bounded probe" | _ => false)

end STFSpec.Conformance.Vm.Runner.RunPrecompileControls
