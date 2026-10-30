/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.FixedBytes

/-!
# Raw system addresses and budgets

Library `EthBlock`. Independent supplied addresses and unrestricted natural-number
budgets. Concrete fork values and their consumers are separate.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3–7.
-/

namespace STFSpec.Block

open STFSpec.Base

/-- Raw system addresses and call budgets, with no relationships beyond field types. -/
structure SystemAddrs where
  /-- System caller address. -/
  systemAddress : Address
  /-- Beacon roots contract address. -/
  beaconRoots : Address
  /-- Historical block hashes contract address. -/
  historyStorage : Address
  /-- Withdrawal requests contract address. -/
  withdrawalRequests : Address
  /-- Consolidation requests contract address. -/
  consolidationRequests : Address
  /-- Builder deposits contract address. -/
  builderDeposits : Address
  /-- Builder exits contract address. -/
  builderExits : Address
  /-- Deposit contract address. -/
  depositContract : Address
  /-- System transaction execution gas grant. -/
  txGas : Nat
  /-- Expected upper bound on new storage slots written by one system call (pinned EELS
  `src/ethereum/forks/amsterdam/fork.py:122–126`); it sizes the state-gas reservoir and
  is not enforced as a cap. -/
  maxSstoresPerCall : Nat

end STFSpec.Block
