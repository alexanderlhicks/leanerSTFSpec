/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Runner

/-!
# Complete raw runner output clients

Library `EthConformance`. Private public-facade clients check exact field types,
construction, reconstruction and isolated updates. No provider storage is unfolded.
Spec guidance: `STFSpec/informal/modules/EthVmRunner.md` §§3/4/5/7.
-/

namespace STFSpec.Conformance.Vm.Runner.OutputCallerProofs
open STFSpec.Base STFSpec.Vm.Core STFSpec.Vm.Runner

private def frameResultType : Type := FrameResult
private def transactionOutputType : Type := TransactionOutput

private def frame_result_constructor_type :
    Frame → Bytes → (Option FrameError) → FrameResult :=
  FrameResult.mk

private def frame_result_frame_type : FrameResult → Frame := FrameResult.frame

private def frame_result_output_type : FrameResult → Bytes := FrameResult.output

private def frame_result_error_type : FrameResult → Option FrameError := FrameResult.error

private theorem frame_result_construct
    (frame : Frame)
    (output : Bytes)
    (error : Option FrameError) :
    let r := FrameResult.mk frame output error
    (r.frame, r.output, r.error) =
      (frame, output, error) := by
  rfl

private theorem frame_result_reconstruct (r : FrameResult) :
    FrameResult.mk r.frame r.output r.error = r := by
  rfl

private theorem frame_result_replace_frame (r : FrameResult) (replacement : Frame) :
    ({ r with frame := replacement } : FrameResult) =
      FrameResult.mk replacement r.output r.error := by
  rfl

private theorem frame_result_replace_output (r : FrameResult) (replacement : Bytes) :
    ({ r with output := replacement } : FrameResult) =
      FrameResult.mk r.frame replacement r.error := by
  rfl

private theorem frame_result_replace_error (r : FrameResult) (replacement : Option FrameError) :
    ({ r with error := replacement } : FrameResult) =
      FrameResult.mk r.frame r.output replacement := by
  rfl

private def transaction_output_constructor_type :
    Nat → Nat → LogRope → AddrSet → Option FrameError → Bytes → Nat → Int →
      TransactionOutput :=
  TransactionOutput.mk

private def transaction_output_gas_left_type : TransactionOutput → Nat :=
  TransactionOutput.gasLeft

private def transaction_output_refund_counter_type : TransactionOutput → Nat :=
  TransactionOutput.refundCounter

private def transaction_output_logs_type : TransactionOutput → LogRope := TransactionOutput.logs

private def transaction_output_accounts_to_delete_type : TransactionOutput → AddrSet :=
  TransactionOutput.accountsToDelete

private def transaction_output_error_type : TransactionOutput → Option FrameError :=
  TransactionOutput.error

private def transaction_output_return_data_type : TransactionOutput → Bytes :=
  TransactionOutput.returnData

private def transaction_output_state_gas_left_type : TransactionOutput → Nat :=
  TransactionOutput.stateGasLeft

private def transaction_output_state_gas_used_type : TransactionOutput → Int :=
  TransactionOutput.stateGasUsed

private theorem transaction_output_construct
    (gasLeft : Nat)
    (refundCounter : Nat)
    (logs : LogRope)
    (accountsToDelete : AddrSet)
    (error : Option FrameError)
    (returnData : Bytes)
    (stateGasLeft : Nat)
    (stateGasUsed : Int) :
    let r := TransactionOutput.mk gasLeft refundCounter logs accountsToDelete error returnData
        stateGasLeft stateGasUsed
    (r.gasLeft, r.refundCounter, r.logs, r.accountsToDelete, r.error, r.returnData,
        r.stateGasLeft, r.stateGasUsed) =
      (gasLeft, refundCounter, logs, accountsToDelete, error, returnData, stateGasLeft,
        stateGasUsed) := by
  rfl

private theorem transaction_output_reconstruct (r : TransactionOutput) :
    TransactionOutput.mk r.gasLeft r.refundCounter r.logs r.accountsToDelete r.error r.returnData
        r.stateGasLeft r.stateGasUsed = r := by
  rfl

private theorem transaction_output_replace_gas_left (r : TransactionOutput) (replacement : Nat) :
    ({ r with gasLeft := replacement } : TransactionOutput) =
      TransactionOutput.mk replacement r.refundCounter r.logs r.accountsToDelete r.error
        r.returnData r.stateGasLeft r.stateGasUsed := by
  rfl

private theorem transaction_output_replace_refund_counter (r : TransactionOutput)
    (replacement : Nat) :
    ({ r with refundCounter := replacement } : TransactionOutput) =
      TransactionOutput.mk r.gasLeft replacement r.logs r.accountsToDelete r.error r.returnData
        r.stateGasLeft r.stateGasUsed := by
  rfl

private theorem transaction_output_replace_logs (r : TransactionOutput) (replacement : LogRope) :
    ({ r with logs := replacement } : TransactionOutput) =
      TransactionOutput.mk r.gasLeft r.refundCounter replacement r.accountsToDelete r.error
        r.returnData r.stateGasLeft r.stateGasUsed := by
  rfl

private theorem transaction_output_replace_accounts_to_delete (r : TransactionOutput)
    (replacement : AddrSet) :
    ({ r with accountsToDelete := replacement } : TransactionOutput) =
      TransactionOutput.mk r.gasLeft r.refundCounter r.logs replacement r.error r.returnData
        r.stateGasLeft r.stateGasUsed := by
  rfl

private theorem transaction_output_replace_error (r : TransactionOutput)
    (replacement : Option FrameError) :
    ({ r with error := replacement } : TransactionOutput) =
      TransactionOutput.mk r.gasLeft r.refundCounter r.logs r.accountsToDelete replacement
        r.returnData r.stateGasLeft r.stateGasUsed := by
  rfl

private theorem transaction_output_replace_return_data (r : TransactionOutput)
    (replacement : Bytes) :
    ({ r with returnData := replacement } : TransactionOutput) =
      TransactionOutput.mk r.gasLeft r.refundCounter r.logs r.accountsToDelete r.error
        replacement r.stateGasLeft r.stateGasUsed := by
  rfl

private theorem transaction_output_replace_state_gas_left (r : TransactionOutput)
    (replacement : Nat) :
    ({ r with stateGasLeft := replacement } : TransactionOutput) =
      TransactionOutput.mk r.gasLeft r.refundCounter r.logs r.accountsToDelete r.error
        r.returnData replacement r.stateGasUsed := by
  rfl

private theorem transaction_output_replace_state_gas_used (r : TransactionOutput)
    (replacement : Int) :
    ({ r with stateGasUsed := replacement } : TransactionOutput) =
      TransactionOutput.mk r.gasLeft r.refundCounter r.logs r.accountsToDelete r.error
        r.returnData r.stateGasLeft replacement := by
  rfl

end STFSpec.Conformance.Vm.Runner.OutputCallerProofs
