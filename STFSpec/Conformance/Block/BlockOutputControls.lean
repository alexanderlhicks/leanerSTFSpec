/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block

/-!
# Raw block output clients

Library `EthConformance`. Private clients check construction, readback, reconstruction
and independent updates through the Block facade. Interpreted guards compare whole values.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3–5.
-/

namespace STFSpec.Conformance.Block.BlockOutputControls

open STFSpec.Base STFSpec.Block STFSpec.Vm.Core

private def constructor :
    Nat → Nat → Nat → Array ByteArray → Array ByteArray → Array ByteArray →
      LogRope → U64 → Array ByteArray → BlockAccessList → BlockOutput :=
  BlockOutput.mk

private def fields (output : BlockOutput) :
    Nat × Nat × Nat × Array ByteArray × Array ByteArray × Array ByteArray ×
      LogRope × U64 × Array ByteArray × BlockAccessList :=
  (output.blockGasUsed, output.blockStateGasUsed, output.cumulativeGasUsed,
    output.transactionValues, output.receiptValues, output.withdrawalValues,
    output.blockLogs, output.blobGasUsed, output.requests, output.blockAccessList)

private theorem read_fields (executionGas stateGas paidGas : Nat)
    (transactions receipts withdrawals : Array ByteArray) (logs : LogRope)
    (blobGas : U64) (requests : Array ByteArray) (accounts : BlockAccessList) :
    fields (constructor executionGas stateGas paidGas transactions receipts withdrawals
      logs blobGas requests accounts) =
      (executionGas, stateGas, paidGas, transactions, receipts, withdrawals,
        logs, blobGas, requests, accounts) := rfl

private theorem reconstruct (output : BlockOutput) :
    constructor output.blockGasUsed output.blockStateGasUsed output.cumulativeGasUsed
      output.transactionValues output.receiptValues output.withdrawalValues
      output.blockLogs output.blobGasUsed output.requests output.blockAccessList = output := rfl

private theorem update_execution_gas (output : BlockOutput) (gas : Nat) :
    fields { output with blockGasUsed := gas } =
      (gas, output.blockStateGasUsed, output.cumulativeGasUsed,
        output.transactionValues, output.receiptValues, output.withdrawalValues,
        output.blockLogs, output.blobGasUsed, output.requests, output.blockAccessList) := rfl

private theorem update_state_gas (output : BlockOutput) (gas : Nat) :
    fields { output with blockStateGasUsed := gas } =
      (output.blockGasUsed, gas, output.cumulativeGasUsed,
        output.transactionValues, output.receiptValues, output.withdrawalValues,
        output.blockLogs, output.blobGasUsed, output.requests, output.blockAccessList) := rfl

private theorem update_paid_gas (output : BlockOutput) (gas : Nat) :
    fields { output with cumulativeGasUsed := gas } =
      (output.blockGasUsed, output.blockStateGasUsed, gas,
        output.transactionValues, output.receiptValues, output.withdrawalValues,
        output.blockLogs, output.blobGasUsed, output.requests, output.blockAccessList) := rfl

private theorem update_transactions (output : BlockOutput) (transactions : Array ByteArray) :
    fields { output with transactionValues := transactions } =
      (output.blockGasUsed, output.blockStateGasUsed, output.cumulativeGasUsed,
        transactions, output.receiptValues, output.withdrawalValues,
        output.blockLogs, output.blobGasUsed, output.requests, output.blockAccessList) := rfl

private theorem update_receipts (output : BlockOutput) (receipts : Array ByteArray) :
    fields { output with receiptValues := receipts } =
      (output.blockGasUsed, output.blockStateGasUsed, output.cumulativeGasUsed,
        output.transactionValues, receipts, output.withdrawalValues,
        output.blockLogs, output.blobGasUsed, output.requests, output.blockAccessList) := rfl

private theorem update_withdrawals (output : BlockOutput) (withdrawals : Array ByteArray) :
    fields { output with withdrawalValues := withdrawals } =
      (output.blockGasUsed, output.blockStateGasUsed, output.cumulativeGasUsed,
        output.transactionValues, output.receiptValues, withdrawals,
        output.blockLogs, output.blobGasUsed, output.requests, output.blockAccessList) := rfl

private theorem update_logs (output : BlockOutput) (logs : LogRope) :
    fields { output with blockLogs := logs } =
      (output.blockGasUsed, output.blockStateGasUsed, output.cumulativeGasUsed,
        output.transactionValues, output.receiptValues, output.withdrawalValues,
        logs, output.blobGasUsed, output.requests, output.blockAccessList) := rfl

private theorem update_blob_gas (output : BlockOutput) (gas : U64) :
    fields { output with blobGasUsed := gas } =
      (output.blockGasUsed, output.blockStateGasUsed, output.cumulativeGasUsed,
        output.transactionValues, output.receiptValues, output.withdrawalValues,
        output.blockLogs, gas, output.requests, output.blockAccessList) := rfl

private theorem update_requests (output : BlockOutput) (requests : Array ByteArray) :
    fields { output with requests := requests } =
      (output.blockGasUsed, output.blockStateGasUsed, output.cumulativeGasUsed,
        output.transactionValues, output.receiptValues, output.withdrawalValues,
        output.blockLogs, output.blobGasUsed, requests, output.blockAccessList) := rfl

private theorem update_accounts (output : BlockOutput) (accounts : BlockAccessList) :
    fields { output with blockAccessList := accounts } =
      (output.blockGasUsed, output.blockStateGasUsed, output.cumulativeGasUsed,
        output.transactionValues, output.receiptValues, output.withdrawalValues,
        output.blockLogs, output.blobGasUsed, output.requests, accounts) := rfl

private def byteValues (values : Array ByteArray) : List (List UInt8) :=
  values.toList.map (fun bytes ↦ (Bytes.ofByteArray bytes).toList)

private abbrev LogView := List UInt8 × List (List UInt8) × List UInt8

private def observeLog (entry : Log) : LogView :=
  (entry.address.toBytes.toList, entry.topics.toList.map (·.toBytes.toList),
    entry.data.toList)

private abbrev AccountView :=
  List UInt8 × List (Nat × List (Nat × Nat)) × List Nat × List (Nat × Nat) ×
    List (Nat × Nat) × List (Nat × List UInt8)

private def observeAccount (account : AccountChanges) : AccountView :=
  (account.address.toBytes.toList,
    account.storageChanges.map (fun slot ↦
      (slot.slot.toNat, slot.changes.map (fun c ↦ (c.blockAccessIndex.toNat, c.newValue.toNat)))),
    account.storageReads.map U256.toNat,
    account.balanceChanges.map (fun c ↦ (c.blockAccessIndex.toNat, c.postBalance.toNat)),
    account.nonceChanges.map (fun c ↦ (c.blockAccessIndex.toNat, c.newNonce.toNat)),
    account.codeChanges.map (fun c ↦
      (c.blockAccessIndex.toNat, (Bytes.ofByteArray c.newCode).toList)))

private def observe (output : BlockOutput) :
    Nat × Nat × Nat × List (List UInt8) × List (List UInt8) × List (List UInt8) ×
      List LogView × Nat × List (List UInt8) × List AccountView :=
  (output.blockGasUsed, output.blockStateGasUsed, output.cumulativeGasUsed,
    byteValues output.transactionValues, byteValues output.receiptValues,
    byteValues output.withdrawalValues, output.blockLogs.toList.map observeLog,
    output.blobGasUsed.toNat, byteValues output.requests,
    output.blockAccessList.toList.map observeAccount)

private def firstLog : Log :=
  ⟨Address.ofNat 0x0102030405060708090a0b0c0d0e0f1011121314,
    #[Hash32.ofBytes32 (FixedBytes.ofNat 127), Hash32.ofBytes32 (FixedBytes.ofNat 128),
      Hash32.ofBytes32 (FixedBytes.ofNat 127)],
    Bytes.ofByteArray ⟨#[0, 11, 255]⟩⟩

private def secondLog : Log :=
  ⟨Address.ofNat 0xff, #[], Bytes.ofByteArray ⟨#[19]⟩⟩

private def account : AccountChanges :=
  ⟨Address.ofNat 0x1234,
    [⟨U256.ofNat 200, [⟨U32.ofNat 5, U256.max⟩, ⟨U32.zero, U256.zero⟩]⟩],
    [U256.ofNat 200, U256.zero, U256.ofNat 200],
    [⟨U32.max, U256.ofNat 201⟩], [⟨U32.ofNat 7, U64.max⟩],
    [⟨U32.ofNat 9, ⟨#[0, 67, 255]⟩⟩, ⟨U32.ofNat 2, ByteArray.empty⟩]⟩

private def populated : BlockOutput :=
  constructor (2 ^ 70 + 3) 37 (2 ^ 80 + 5)
    #[⟨#[0, 17, 255]⟩, ByteArray.empty, ⟨#[0, 17, 255]⟩]
    #[⟨#[192]⟩]
    #[⟨#[2, 128]⟩, ⟨#[1, 129]⟩]
    (.concat (.leaf [firstLog]) (.concat .empty (.leaf [secondLog, firstLog])))
    U64.max
    #[⟨#[2, 22]⟩, ByteArray.empty, ⟨#[0, 33]⟩, ⟨#[2, 22]⟩]
    #[account, ⟨Address.ofNat 0, [], [], [], [], []⟩, account]

private def expectedFirstLog : LogView :=
  let topic (value : UInt8) := List.replicate 31 0 ++ [value]
  ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20],
    [topic 127, topic 128, topic 127], [0, 11, 255])

private def expectedSecondLog : LogView :=
  (List.replicate 19 0 ++ [255], [], [19])

private def expectedAccount : AccountView :=
  (List.replicate 18 0 ++ [18, 52], [(200, [(5, 2 ^ 256 - 1), (0, 0)])],
    [200, 0, 200], [(4294967295, 201)], [(7, 18446744073709551615)],
    [(9, [0, 67, 255]), (2, [])])

#guard observe (constructor 0 0 0 #[] #[] #[] .empty U64.zero #[] #[]) ==
  (0, 0, 0, [], [], [], [], 0, [], [])

#guard observe populated ==
  (2 ^ 70 + 3, 37, 2 ^ 80 + 5, [[0, 17, 255], [], [0, 17, 255]], [[192]],
    [[2, 128], [1, 129]], [expectedFirstLog, expectedSecondLog, expectedFirstLog],
    18446744073709551615, [[2, 22], [], [0, 33], [2, 22]],
    [expectedAccount, (List.replicate 20 0, [], [], [], [], []), expectedAccount])

#guard match populated.blockLogs with
  | .concat (.leaf [first]) (.concat .empty (.leaf [second, repeated])) =>
    (observeLog first, observeLog second, observeLog repeated) ==
      (expectedFirstLog, expectedSecondLog, expectedFirstLog)
  | _ => false

end STFSpec.Conformance.Block.BlockOutputControls
