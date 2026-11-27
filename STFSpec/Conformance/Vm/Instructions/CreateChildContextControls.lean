/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions
import STFSpec.Fork.Amsterdam

/-!
# CREATE child context controls

Library `EthConformance`. Exercise the public constructor at the admitted depth
endpoints and check a fresh jump map against the child's own init code.
Spec guidance in `STFSpec/informal/modules/EthVmInstructions.md` §4.
-/

namespace STFSpec.Conformance.Vm.Instructions.CreateChildContextControls
open STFSpec.Base STFSpec.Vm.Core STFSpec.Vm.Instructions

private def addr (n : Nat) := Address.ofNat n
private def hash (n : Nat) := Hash32.ofBytes32 (FixedBytes.ofNat n)

private def parent (depth : Nat) (h : depth ≤ STACK_DEPTH_LIMIT) : FrameCtx :=
  let cfg : VmConfig :=
    ⟨{ STFSpec.Fork.Amsterdam.gasCosts with zero := 73, warmAccess := 7 },
      ⟨11, 13, 2 ^ 261 + 17, 19⟩, ⟨7, 23, 29⟩⟩
  let block : BlockEnvironment :=
    ⟨U64.ofNat 31, 37, #[hash 41, hash 43], addr 47, 53, 59,
      U256.ofNat (2 ^ 201 + 61), FixedBytes.ofNat (2 ^ 251 + 67), U64.ofNat 71, hash 79, U64.ofNat 83⟩
  let tx : TransactionEnvironment :=
    ⟨addr 89, addr 97, true, Bytes.ofList [0, 128, 255], U256.ofNat 101,
      103, 107, 109, 113, 127, (∅ : AddrSet).insert (addr 131), ∅, #[], #[], some 0, some (hash 137)⟩
  ⟨cfg, block, tx, addr 139, addr 149, U256.max, Bytes.ofList [255, 0, 128],
    some (addr 151), Bytes.ofList [91], validJumpDestinations (Bytes.ofList [0, 91]),
    depth, h, false, true, true, addr (2 ^ 159 + 157)⟩

private def request (init : Bytes) : CreateRequest :=
  ⟨2 ^ 260 + 163, 167, U256.ofNat (2 ^ 255 + 173), addr (2 ^ 152 + 179),
    addr (2 ^ 144 + 181), init, false⟩

private def positions (ctx : FrameCtx) : List Nat :=
  (List.range ctx.code.size).filter ctx.jumpdests.contains

private def childFields (ctx : FrameCtx) (req : CreateRequest)
    (h : ctx.depth < STACK_DEPTH_LIMIT) (jumps : List Nat) : Bool :=
  let child := childCtxOfCreate ctx req h
  child.config.costs.zero == 73 && child.config.costs.warmAccess == 7 &&
    child.config.limits.stackDepthLimit == 7 && child.systemAddress == ctx.systemAddress &&
    child.blockEnv.blockHashes == ctx.blockEnv.blockHashes && child.txEnv.data == ctx.txEnv.data &&
    child.caller == req.caller && child.currentTarget == req.contractAddress &&
    child.value == req.endowment && child.callData.toList == [] && child.codeAddress.isNone &&
    child.code.toList == req.initCode.toList && child.depth == ctx.depth + 1 &&
    child.shouldTransferValue && !child.isStatic && !child.disablePrecompiles &&
    positions child == jumps && !child.jumpdests.contains (2 ^ 262 + 191)

#guard childFields (parent 0 (by decide)) (request Bytes.empty) (by decide) []
#guard childFields (parent 1 (by decide)) (request (Bytes.ofList [91])) (by decide) [0]
#guard childFields (parent 1023 (by decide)) (request (Bytes.ofList [91, 96, 91, 91, 127, 91]))
  (by decide) [0, 3]
#guard childFields (parent 111 (by decide)) (request (Bytes.ofList [95, 91, 97, 91, 91, 91]))
  (by decide) [1, 5]

private theorem inherited (ctx : FrameCtx) (req : CreateRequest) (h : ctx.depth < STACK_DEPTH_LIMIT) :
    let child := childCtxOfCreate ctx req h
    child.config = ctx.config ∧ child.systemAddress = ctx.systemAddress ∧
      child.blockEnv = ctx.blockEnv ∧ child.txEnv = ctx.txEnv := by
  refine ⟨childCtxOfCreate_config ctx req h, childCtxOfCreate_systemAddress ctx req h, ?_⟩
  rw [childCtxOfCreate_eq]
  exact ⟨rfl, rfl⟩

private theorem ignoresGrants (ctx : FrameCtx) (req : CreateRequest) (h : ctx.depth < STACK_DEPTH_LIMIT)
    (gas reservoir : Nat) (newAccountCharged : Bool) :
    childCtxOfCreate ctx { req with gas, stateGasReservoir := reservoir, newAccountCharged } h =
      childCtxOfCreate ctx req h := by
  rw [childCtxOfCreate_eq, childCtxOfCreate_eq]

end STFSpec.Conformance.Vm.Instructions.CreateChildContextControls
