/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.FixedBytes
import Std.Data.HashSet

/-!
# Raw transaction observations

Library `EthState`: the D23 observation partition of the reference TransactionState.
Construction retains arbitrary supplied sets; tracker operations and lifetimes are separate.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/5/7.
-/

namespace STFSpec.State

/-- Raw D23 partition of EELS `src/ethereum/forks/amsterdam/state_tracker.py:91–117`.
The four fields at :103, :107, :111 and :113 use canonical Base key dictionaries.
This carrier alone establishes no linear ownership or persistence across rollback. -/
structure TxObs where
  /-- Account read observations; EELS `state_tracker.py:103`. -/
  accountReads : Std.HashSet STFSpec.Base.Address
  /-- Storage read observations; EELS `state_tracker.py:107`. -/
  storageReads : Std.HashSet (STFSpec.Base.Address × STFSpec.Base.Bytes32)
  /-- Code read observations; EELS `state_tracker.py:51,111`. -/
  codeReads : Std.HashSet (STFSpec.Base.Address × STFSpec.Base.Hash32)
  /-- Created accounts; EELS `state_tracker.py:113`. -/
  createdAccounts : Std.HashSet STFSpec.Base.Address

end STFSpec.State
