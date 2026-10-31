/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core.Limits
import STFSpec.Vm.Core.Config
import STFSpec.Vm.Core.Environments
import STFSpec.Vm.Core.Jumpdest
import STFSpec.Vm.Core.Frame

/-!
# Immutable call context and assembled frame view

Library `EthVmCore`. The context and Frame partition pinned EELS
`src/ethereum/forks/amsterdam/vm/__init__.py:153–191` (R-ENV-3).
Configuration and systemAddress carry supplied policy, rather than extra source fields.
Depth uses the existing literal bound from `interpreter.py:84` (F8).
Future handler signatures enforce read-only context use; raw record construction
alone adds no code/map, environment, configuration or frame coherence invariant.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7.
-/

namespace STFSpec.Vm.Core
open STFSpec.Base

/-- The thirteen fixed source fields, two supplied policy fields and local depth proof.
Intended frame creation and child inheritance supply source and policy coherence. -/
structure FrameCtx where
  /-- Complete supplied VM policy; intended construction establishes coherence. -/
  config : VmConfig
  /-- Complete VM-visible block environment. -/
  blockEnv : BlockEnvironment
  /-- Complete VM-visible transaction environment. -/
  txEnv : TransactionEnvironment
  /-- Caller address, independent of currentTarget. -/
  caller : Address
  /-- Current execution target. -/
  currentTarget : Address
  /-- Supplied call value. -/
  value : U256
  /-- Complete call input, independent of the transaction input. -/
  callData : Bytes
  /-- Optional code address; absence differs from a present zero address. -/
  codeAddress : Option Address
  /-- Complete code bytes. -/
  code : Bytes
  /-- Supplied immutable map; intended construction establishes agreement with code. -/
  jumpdests : JumpdestMap
  /-- Logical call depth, including depth zero. -/
  depth : Nat
  /-- The sole local domain proof; independent of config.limits.stackDepthLimit. -/
  depth_le : depth ≤ STACK_DEPTH_LIMIT
  /-- Whether entry should transfer the supplied value. -/
  shouldTransferValue : Bool
  /-- Whether the call is static. -/
  isStatic : Bool
  /-- Whether precompile dispatch is disabled. -/
  disablePrecompiles : Bool
  /-- Supplied immutable F8 policy address, independent of the raw configuration. -/
  systemAddress : Address

/-- The complete context/mutable-frame view of source Evm data.
Control outcomes and parent execution remain with Instructions and Runner. -/
structure Evm where
  /-- Complete fixed call context. -/
  ctx : FrameCtx
  /-- Complete independent mutable frame. -/
  frame : Frame

end STFSpec.Vm.Core
