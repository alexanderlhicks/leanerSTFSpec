/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Runner

/-!
# Complete raw runner output controls

Library `EthConformance`. Complete supplied records retain independent gas fields,
negative state usage, nonempty effects and every error alternative. These controls
claim raw storage only, without executing an EELS producer or a Lean runner.
Spec guidance: `STFSpec/informal/modules/EthVmRunner.md` §§3/4/5/7.
-/

namespace STFSpec.Conformance.Vm.Runner.OutputControls
open STFSpec.Base STFSpec.Vm.Core STFSpec.Vm.Runner

private def deleted : AddrSet := (∅ : AddrSet).insert (Address.ofNat 257)
private def entry : Log :=
  { address := Address.ofNat 513
    topics := #[Hash32.ofBytes32 (FixedBytes.ofNat 7),
      Hash32.ofBytes32 (FixedBytes.ofNat 256), Hash32.ofBytes32 (FixedBytes.ofNat 7)]
    data := Bytes.ofList [255, 0, 128] }
private def rope : LogRope := .concat (.leaf [entry]) (.concat .empty (.leaf [entry]))
private def meter : GasMeter :=
  { gasLeft := 1, stateGasLeft := 7, stateGasBaseline := 3, refundCounter := -11,
    stateGasSpilled := 13, stateGasCommittedSpill := 17 }
private def frame : Frame :=
  Frame.mk (2 ^ 300 + 19) Stack.empty Memory.empty meter rope deleted
    (Bytes.ofList [0, 128, 255]) (∅ : AddrSet) (∅ : SlotSet)
private def returned : Bytes := Bytes.ofList [255, 128, 0, 255]
private def frameResult (error : Option FrameError) : FrameResult :=
  FrameResult.mk frame returned error
private def transactionOutput (error : Option FrameError) : TransactionOutput :=
  TransactionOutput.mk (2 ^ 300 + 23) (2 ^ 301 + 29) rope deleted error returned
    (2 ^ 302 + 31) (-37)

-- Whole provider values, including raw rope shape, remain intact for every error.
private theorem complete_frame_result (error : Option FrameError) :
    ((frameResult error).frame, (frameResult error).output, (frameResult error).error) =
      (frame, returned, error) := by
  rfl

private theorem complete_transaction_output (error : Option FrameError) :
    let r := transactionOutput error
    (r.gasLeft, r.refundCounter, r.logs, r.accountsToDelete,
      r.error, r.returnData, r.stateGasLeft, r.stateGasUsed) =
      (2 ^ 300 + 23, 2 ^ 301 + 29, rope, deleted,
        error, returned, 2 ^ 302 + 31, (-37 : Int)) := by
  rfl

private def errors : List (Option FrameError) :=
  [none, some .revert, some (.halt .stackUnderflow), some (.halt .stackOverflow),
    some (.halt .outOfGas), some (.halt (.invalidOpcode 239)), some (.halt .invalidJumpDest),
    some (.halt .stackDepthLimit), some (.halt .writeInStaticContext),
    some (.halt .outOfBoundsRead), some (.halt .invalidParameter),
    some (.halt .invalidContractPrefix), some (.halt .addressCollision),
    some (.halt .kzgProofError), some (.halt (.precompileHalt "complete\nreason\u0000λ"))]

private theorem all_error_payloads :
    errors.map (fun error ↦ (frameResult error).error) = errors ∧
      errors.map (fun error ↦ (transactionOutput error).error) = errors := by
  exact ⟨rfl, rfl⟩

private theorem arbitrary_error_payloads (opcode : UInt8) (reason : String) :
    (frameResult (some (.halt (.invalidOpcode opcode)))).error =
        some (.halt (.invalidOpcode opcode)) ∧
      (transactionOutput (some (.halt (.precompileHalt reason)))).error =
        some (.halt (.precompileHalt reason)) := by
  exact ⟨rfl, rfl⟩

-- Complete public observations show nonempty effects even on failure.
#guard (frameResult (some .revert)).frame.returnData.toList == [0, 128, 255]
#guard (frameResult (some .revert)).output.toList == [255, 128, 0, 255]
#guard (transactionOutput (some (.halt .outOfGas))).returnData.toList == [255, 128, 0, 255]
#guard (transactionOutput (some .revert)).accountsToDelete.toList.map Address.toNat == [257]
#guard ((transactionOutput (some .revert)).logs.toList.map fun log ↦
  (log.address.toNat, log.topics.toList.map Hash32.toNat, log.data.toList)) ==
    [(513, [7, 256, 7], [255, 0, 128]), (513, [7, 256, 7], [255, 0, 128])]
#guard (transactionOutput none).stateGasUsed == (-37 : Int)
#guard ((transactionOutput none).gasLeft, (transactionOutput none).refundCounter,
  (transactionOutput none).stateGasLeft) == (2 ^ 300 + 23, 2 ^ 301 + 29, 2 ^ 302 + 31)

end STFSpec.Conformance.Vm.Runner.OutputControls
