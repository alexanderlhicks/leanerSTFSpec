/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Complete raw context and assembled-frame controls

Library `EthConformance`. Three complete boundary controls retain arbitrary whole
GasCosts, environments, system address and Frame values. Private configurations
use the public raw constructor, including limits different from the local depth bound.
Finite metadata covers empty/mixed/all bytes, None/Some-zero/nonzero code addresses,
independent code/maps, distinct nominal addresses, flags and depths 0/1/1024.
These controls add no intended-construction or execution claim.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/5/7.
-/

namespace STFSpec.Conformance.Vm.Core.ContextGuards
open STFSpec.Vm.Core STFSpec.Base

private def smallConfig (costs : GasCosts) : VmConfig :=
  VmConfig.mk costs (StateGasCosts.mk 0 7 (2 ^ 300 + 11) 13)
    (VmLimits.mk 7 0 (2 ^ 301 + 17))

private def largeConfig (costs : GasCosts) : VmConfig :=
  VmConfig.mk costs (StateGasCosts.mk 19 0 23 29) (VmLimits.mk 2048 31 0)

private def high : Address := Address.ofNat (2 ^ 159 + 257)
private def maximal : Address := Address.ofNat (2 ^ 160 - 1)
private def zeroAddress : Address := Address.ofNat 0
private def allBytes : List UInt8 := (List.range 256).map UInt8.ofNat
private def mixed : Bytes := Bytes.ofList [0, 255, 128, 1, 0]
private def destinations : JumpdestMap := validJumpDestinations (Bytes.ofList [91, 0, 91])

private def atZero (costs : GasCosts) (be : BlockEnvironment) (te : TransactionEnvironment)
    (systemAddress : Address) : FrameCtx :=
  FrameCtx.mk (smallConfig costs) be te zeroAddress high U256.zero Bytes.empty
    none Bytes.empty destinations 0 (by decide) false false false systemAddress

private def atLimit (costs : GasCosts) (be : BlockEnvironment) (te : TransactionEnvironment)
    (systemAddress : Address) : FrameCtx :=
  FrameCtx.mk (smallConfig costs) be te high maximal U256.max (Bytes.ofList allBytes)
    (some zeroAddress) (Bytes.ofList [96, 91, 91]) destinations 1024 (by decide)
    true false true systemAddress

private def fullCode (costs : GasCosts) (be : BlockEnvironment) (te : TransactionEnvironment)
    (systemAddress : Address) : FrameCtx :=
  FrameCtx.mk (largeConfig costs) be te maximal zeroAddress (U256.ofNat 256) mixed
    (some high) (Bytes.ofList allBytes) (validJumpDestinations Bytes.empty) 1 (by decide)
    false true false systemAddress

-- Observe complete supplied provider values rather than selecting a subset of their fields.
-- Code and callData use Base's complete public byte model; map identity stays abstract.
private def view (evm : Evm) :=
  let ctx := evm.ctx
  (ctx.config, ctx.blockEnv, ctx.txEnv, ctx.caller, ctx.currentTarget, ctx.value,
    ctx.callData.toList, ctx.codeAddress, ctx.code.toList, ctx.jumpdests, ctx.depth,
    ctx.shouldTransferValue, ctx.isStatic, ctx.disablePrecompiles, ctx.systemAddress, evm.frame)

private theorem empty_control (costs : GasCosts) (be : BlockEnvironment)
    (te : TransactionEnvironment) (systemAddress : Address) (f : Frame) :
    view (Evm.mk (atZero costs be te systemAddress) f) =
      (smallConfig costs, be, te, zeroAddress, high, U256.zero,
        [], none, [], destinations, 0, false, false, false, systemAddress, f) := by
  simp only [view, atZero, Bytes.toList_empty]

private theorem upper_control (costs : GasCosts) (be : BlockEnvironment)
    (te : TransactionEnvironment) (systemAddress : Address) (f : Frame) :
    view (Evm.mk (atLimit costs be te systemAddress) f) =
      (smallConfig costs, be, te, high, maximal, U256.max,
        allBytes, some zeroAddress, [96, 91, 91], destinations, 1024,
        true, false, true, systemAddress, f) := by
  simp only [view, atLimit, Bytes.toList_ofList]

private theorem full_byte_control (costs : GasCosts) (be : BlockEnvironment)
    (te : TransactionEnvironment) (systemAddress : Address) (f : Frame) :
    view (Evm.mk (fullCode costs be te systemAddress) f) =
      (largeConfig costs, be, te, maximal, zeroAddress, U256.ofNat 256,
        [0, 255, 128, 1, 0], some high, allBytes, validJumpDestinations Bytes.empty,
        1, false, true, false, systemAddress, f) := by
  simp only [view, fullCode, mixed, Bytes.toList_ofList]

-- The raw config's limit is not a hidden premise of the admitted local depth.
private theorem independent_depth_limit (costs : GasCosts) (be : BlockEnvironment)
    (te : TransactionEnvironment) (systemAddress : Address) :
    let ctx := atLimit costs be te systemAddress
    ctx.config.limits.stackDepthLimit = 7 ∧ ctx.depth = 1024 ∧
      ctx.depth ≤ STACK_DEPTH_LIMIT := by
  exact ⟨rfl, rfl, (atLimit costs be te systemAddress).depth_le⟩

-- Whole-record clients above retain the exact supplied map despite unrelated code.
-- Its finite membership consequences use only the provider's public lookup equations.
private theorem independent_map_control (costs : GasCosts) (be : BlockEnvironment)
    (te : TransactionEnvironment) (systemAddress : Address) :
    let ctx := atZero costs be te systemAddress
    ctx.code = Bytes.empty ∧ ctx.jumpdests.contains 0 = true ∧
      ctx.jumpdests.contains 1 = false ∧ ctx.jumpdests.contains 2 = true ∧
      ctx.jumpdests.contains (2 ^ 128) = false := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · change (validJumpDestinations (Bytes.ofList [91, 0, 91])).contains 0 = true
    rw [validJumpDestinations_contains_cons]
    decide
  · change (validJumpDestinations (Bytes.ofList [91, 0, 91])).contains 1 = false
    rw [validJumpDestinations_contains_cons]
    change (validJumpDestinations (Bytes.ofList [0, 91])).contains 0 = false
    rw [validJumpDestinations_contains_cons]
    decide
  · change (validJumpDestinations (Bytes.ofList [91, 0, 91])).contains 2 = true
    rw [validJumpDestinations_contains_cons]
    change (validJumpDestinations (Bytes.ofList [0, 91])).contains 1 = true
    rw [validJumpDestinations_contains_cons]
    change (validJumpDestinations (Bytes.ofList [91])).contains 0 = true
    rw [validJumpDestinations_contains_cons]
    decide
  · change (validJumpDestinations (Bytes.ofList [91, 0, 91])).contains (2 ^ 128) = false
    apply validJumpDestinations_contains_of_size_le
    rw [Bytes.size_ofList]
    decide

private theorem empty_map_control (costs : GasCosts) (be : BlockEnvironment)
    (te : TransactionEnvironment) (systemAddress : Address) (i : Nat) :
    (fullCode costs be te systemAddress).jumpdests.contains i = false := by
  exact validJumpDestinations_contains_empty i

-- The sole proof field rejects a context at the first out-of-domain depth.
#check_failure fun (costs : GasCosts) (be : BlockEnvironment) (te : TransactionEnvironment)
    (systemAddress : Address) ↦
  FrameCtx.mk (smallConfig costs) be te zeroAddress high U256.zero Bytes.empty
    none Bytes.empty destinations 1025 (by decide) false false false systemAddress
#guard allBytes.map UInt8.toNat == List.range 256
#guard high.toBytes.toList == [128] ++ List.replicate 17 0 ++ [1, 1]
#guard maximal.toBytes.toList == List.replicate 20 255
#guard zeroAddress.toBytes.toList == List.replicate 20 0

end STFSpec.Conformance.Vm.Core.ContextGuards
