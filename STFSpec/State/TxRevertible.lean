/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.Account
import STFSpec.State.WriteOrder
import Std.Data.ExtTreeSet

/-!
# Raw revertible transaction data

Library `EthState`: exactly the persistent write, order, clear and transient fields.
Construction retains arbitrary raw values, including disagreeing order indexes.
D23 splits the revertible fields of EELS TransactionState from observations, and D22
keeps them in persistent trees; B1 adds explicit write-order indexes. Snapshot and
tracker operations remain separate.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/4/5/7.
-/

namespace STFSpec.State

open Base

/-- Raw revertible fields of EELS `src/ethereum/forks/amsterdam/state_tracker.py:91–117`,
with D22 persistent trees, D23 observation separation and B1 order metadata.
This carrier imposes no reachability, well-formedness or order/value agreement premise. -/
structure TxRevertible where
  /-- Whole optional account writes, retaining deletion tombstones. -/
  accountWrites : Std.ExtTreeMap Address (Option Account)
  /-- Raw account write-order index. -/
  accountOrder : WriteOrder Address
  /-- Whole per-address slot maps, retaining empty maps and zero writes. -/
  storageWrites : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)
  /-- Raw storage-address write-order index. -/
  storageAddressOrder : WriteOrder Address
  /-- Whole optional per-address raw slot-order indexes. -/
  storageSlotOrder : Std.ExtTreeMap Address (WriteOrder Bytes32)
  /-- Arbitrary complete bytecode by supplied code hash. -/
  codeWrites : Std.ExtTreeMap Hash32 ByteArray
  /-- Independent storage-clear membership, without a replay order. -/
  storageClears : Std.ExtTreeSet Address
  /-- Raw transient writes by the existing lexical address/slot key. -/
  transient : Std.ExtTreeMap (Address × Bytes32) U256

end STFSpec.State
