/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.Account
import STFSpec.State.WriteOrder
import STFSpec.State.TxRevertible
import STFSpec.State.MathState
import STFSpec.State.BlockDiff
import STFSpec.State.Apply
import STFSpec.State.PreState
import STFSpec.State.StateError
import STFSpec.State.Structural
import STFSpec.State.TxObs
import STFSpec.State.BlockState
import STFSpec.State.TxState
import STFSpec.State.MarkAccountCreated
import STFSpec.State.TransactionSnapshot
import STFSpec.State.AncestorAccess
import STFSpec.State.PreStateAccount
import STFSpec.State.AccountOptional
import STFSpec.State.AccountEmptiness
import STFSpec.State.DestroyStorage
import STFSpec.State.SetAccount
import STFSpec.State.DestroyAccount
import STFSpec.State.ModifyState
import STFSpec.State.EtherUpdates
import STFSpec.State.AccountExists
import STFSpec.State.CurrentStorage
import STFSpec.State.StorageOriginal
import STFSpec.State.TransientStorage
import STFSpec.State.TransientStorageWrite
import STFSpec.State.AccountDefault
import STFSpec.State.AccountDeployable
import STFSpec.State.BlockInitialization
import STFSpec.State.TransactionInitialization
import STFSpec.State.ReadSets
import STFSpec.State.BlockExtraction
import STFSpec.State.BlockView
import STFSpec.State.TransactionView
import STFSpec.State.ModelsLookups

/-!
# STFSpec.State

State semantics: accounts, the pre-state lookup contract, transaction and block
overlays, observations, mathematical views and block diffs. This library is
independent of trie commitments.

The supplied operations include initialization, snapshot and restore, account
and storage reads, hash-only code lookup, ancestor access recording, ordered
account writes, storage clear, account destruction and modification, Ether
transfers and credits, transient storage operations and marking a created account. The source map records the scope and laws of each operation.
Spec guidance: `STFSpec/informal/modules/EthState.md`.
-/
