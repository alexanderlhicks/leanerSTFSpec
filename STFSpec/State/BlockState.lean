/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.PreState
import STFSpec.State.WriteOrder
import Std.Data.HashSet

/-!
# Raw block state

Library `EthState`: the nine source fields plus caller-supplied F20 constants and
three B1 order indexes. Construction retains arbitrary complete fields, without
validation, normalization, hashing, tracker operations or lifetime claims.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/5/7.
-/

namespace STFSpec.State

/-- Raw block carrier from EELS `src/ethereum/forks/amsterdam/state_tracker.py:57–86`.
The source has nine fields; F20 adds `consts`, and B1 adds the three order indexes.
The arbitrary type constructor and complete supplied provider require no class premise.
Constants acquisition/coherence and reachable tracker/lifetime laws remain caller obligations. -/
structure BlockState (m : Type → Type) where
  /-- Complete supplied provider record; EELS `state_tracker.py:74`. -/
  preState : PreState m
  /-- Caller-supplied F20 constants; storing them performs no protocol hash. -/
  consts : STFSpec.Base.HashConsts
  /-- Raw account writes, including deletion tombstones; EELS `state_tracker.py:76–78`. -/
  accountWrites : Std.ExtTreeMap STFSpec.Base.Address (Option Account)
  /-- Supplied B1 account-order metadata, without a WF or history premise. -/
  accountOrder : WriteOrder STFSpec.Base.Address
  /-- Raw storage writes, retaining zero values and empty inner maps;
  EELS `state_tracker.py:80–82`. -/
  storageWrites : Std.ExtTreeMap STFSpec.Base.Address
    (Std.ExtTreeMap STFSpec.Base.Bytes32 STFSpec.Base.U256)
  /-- Supplied B1 storage-address-order metadata. -/
  storageAddressOrder : WriteOrder STFSpec.Base.Address
  /-- Supplied B1 per-address slot-order metadata. -/
  storageSlotOrder : Std.ExtTreeMap STFSpec.Base.Address (WriteOrder STFSpec.Base.Bytes32)
  /-- Complete supplied code writes; EELS `state_tracker.py:84`. -/
  codeWrites : Std.ExtTreeMap STFSpec.Base.Hash32 ByteArray
  /-- Storage clear membership without a clear order; EELS `state_tracker.py:86`. -/
  storageClears : Std.ExtTreeSet STFSpec.Base.Address
  /-- Independent raw account read set; EELS `state_tracker.py:75`. -/
  accountReads : Std.HashSet STFSpec.Base.Address
  /-- Independent raw storage read set; EELS `state_tracker.py:79`. -/
  storageReads : Std.HashSet (STFSpec.Base.Address × STFSpec.Base.Bytes32)
  /-- Independent raw code read set; EELS `state_tracker.py:51,83`. -/
  codeReads : Std.HashSet (STFSpec.Base.Address × STFSpec.Base.Hash32)
  /-- Raw optional unbounded ancestor offset; EELS `state_tracker.py:85`. -/
  oldestAncestorOffset : Option Nat

end STFSpec.State
