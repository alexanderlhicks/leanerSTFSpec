/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions

/-!
# Typed result and handler clients

Library `EthConformance`. Private facade clients retain complete arbitrary payloads,
distinguish all six cases and exercise dependent context and local strict bounds.
Stack clients use only public constructors, model equations and operation laws.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Vm.Instructions.StepResultCallerProofs
open STFSpec.Base STFSpec.Vm.Core STFSpec.Vm.Instructions

private def continue_signature :
    (ctx : FrameCtx) → Frame → StepResult ctx := @StepResult.continue
private def stop_signature :
    (ctx : FrameCtx) → Frame → Bytes → StepResult ctx := @StepResult.stop
private def revert_signature :
    (ctx : FrameCtx) → Frame → Bytes → StepResult ctx := @StepResult.revert
private def halt_signature :
    (ctx : FrameCtx) → Frame → ExceptionalHalt → StepResult ctx := @StepResult.halt
private def call_signature :
    (ctx : FrameCtx) → (parent : Frame) → CallRequest →
      ctx.depth < STACK_DEPTH_LIMIT → parent.stack.size < STACK_DEPTH_LIMIT →
      StepResult ctx := @StepResult.call
private def create_signature :
    (ctx : FrameCtx) → (parent : Frame) → CreateRequest →
      ctx.depth < STACK_DEPTH_LIMIT → parent.stack.size < STACK_DEPTH_LIMIT →
      StepResult ctx := @StepResult.create

private def payload {ctx : FrameCtx} : StepResult ctx →
    Frame × Option Bytes × Option ExceptionalHalt × Option CallRequest × Option CreateRequest
  | .continue f => (f, none, none, none, none)
  | .stop f output => (f, some output, none, none, none)
  | .revert f output => (f, some output, none, none, none)
  | .halt f e => (f, none, some e, none, none)
  | .call parent req _ _ => (parent, none, none, some req, none)
  | .create parent req _ _ => (parent, none, none, none, some req)

private theorem complete_payloads (ctx : FrameCtx) (f : Frame) (output : Bytes)
    (e : ExceptionalHalt) (callReq : CallRequest) (createReq : CreateRequest)
    (h : ctx.depth < STACK_DEPTH_LIMIT) (hs : f.stack.size < STACK_DEPTH_LIMIT) :
    payload (.continue f : StepResult ctx) = (f, none, none, none, none) ∧
    payload (.stop f output : StepResult ctx) = (f, some output, none, none, none) ∧
    payload (.revert f output : StepResult ctx) = (f, some output, none, none, none) ∧
    payload (.halt f e : StepResult ctx) = (f, none, some e, none, none) ∧
    payload (.call f callReq h hs) = (f, none, none, some callReq, none) ∧
    payload (.create f createReq h hs) = (f, none, none, none, some createReq) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem complete_injectivity (ctx : FrameCtx) (f g : Frame) (out out' : Bytes)
    (e e' : ExceptionalHalt) (callReq callReq' : CallRequest)
    (createReq createReq' : CreateRequest) (h : ctx.depth < STACK_DEPTH_LIMIT)
    (hf : f.stack.size < STACK_DEPTH_LIMIT) (hg : g.stack.size < STACK_DEPTH_LIMIT) :
    ((.continue f : StepResult ctx) = .continue g ↔ f = g) ∧
    ((.stop f out : StepResult ctx) = .stop g out' ↔ f = g ∧ out = out') ∧
    ((.revert f out : StepResult ctx) = .revert g out' ↔ f = g ∧ out = out') ∧
    ((.halt f e : StepResult ctx) = .halt g e' ↔ f = g ∧ e = e') ∧
    (StepResult.call f callReq h hf = .call g callReq' h hg ↔ f = g ∧ callReq = callReq') ∧
    (StepResult.create f createReq h hf = .create g createReq' h hg ↔
      f = g ∧ createReq = createReq') := by
  simp only [StepResult.continue.injEq, StepResult.stop.injEq, StepResult.revert.injEq,
    StepResult.halt.injEq, StepResult.call.injEq, StepResult.create.injEq,
    iff_self, and_self]

private theorem all_cases_distinct (ctx : FrameCtx)
    (next stopped reverted halted called created : Frame) (stopOut revertOut : Bytes)
    (e : ExceptionalHalt) (callReq : CallRequest) (createReq : CreateRequest)
    (h : ctx.depth < STACK_DEPTH_LIMIT)
    (hc : called.stack.size < STACK_DEPTH_LIMIT) (hn : created.stack.size < STACK_DEPTH_LIMIT) :
    List.Pairwise (fun a b : StepResult ctx ↦ a ≠ b)
      [.continue next, .stop stopped stopOut, .revert reverted revertOut, .halt halted e,
        .call called callReq h hc, .create created createReq h hn] := by
  simp

private theorem dependent_elimination
    (P : (ctx : FrameCtx) → StepResult ctx → Prop)
    (onContinue : ∀ ctx f, P ctx (.continue f))
    (onStop : ∀ ctx f output, P ctx (.stop f output))
    (onRevert : ∀ ctx f output, P ctx (.revert f output))
    (onHalt : ∀ ctx f e, P ctx (.halt f e))
    (onCall : ∀ ctx parent req h hs, P ctx (.call parent req h hs))
    (onCreate : ∀ ctx parent req h hs, P ctx (.create parent req h hs))
    (ctx : FrameCtx) (r : StepResult ctx) : P ctx r := by
  cases r with
  | «continue» f => exact onContinue ctx f
  | stop f output => exact onStop ctx f output
  | revert f output => exact onRevert ctx f output
  | halt f e => exact onHalt ctx f e
  | call parent req h hs => exact onCall ctx parent req h hs
  | create parent req h hs => exact onCreate ctx parent req h hs

private def reconstruct {ctx : FrameCtx} : StepResult ctx → StepResult ctx
  | .continue f => .continue f
  | .stop f output => .stop f output
  | .revert f output => .revert f output
  | .halt f e => .halt f e
  | .call parent req h hs => .call parent req h hs
  | .create parent req h hs => .create parent req h hs

private theorem reconstruct_eq (ctx : FrameCtx) (r : StepResult ctx) :
    reconstruct r = r := by
  cases r <;> rfl

private theorem local_bounds (ctx : FrameCtx) (r : StepResult ctx) :
    match r with
    | .call parent _ _ _ | .create parent _ _ _ =>
      ctx.depth < STACK_DEPTH_LIMIT ∧ parent.stack.size < STACK_DEPTH_LIMIT
    | _ => True := by
  cases r with
  | call _ _ h hs | create _ _ h hs => exact ⟨h, hs⟩
  | _ => trivial

private def handler_signature (m : Type → Type) :
    Handler m → (ctx : FrameCtx) → Frame → VmM m (StepResult ctx) := fun h ↦ h

private def handler_formation (m : Type → Type) : Type := Handler m

private theorem handler_alias (m : Type → Type) :
    Handler m = ((ctx : FrameCtx) → Frame → VmM m (StepResult ctx)) := rfl

private def handler_run (m : Type → Type) (h : Handler m) (ctx : FrameCtx)
    (f : Frame) (w : VmWorld m) : m (Except VmFault (StepResult ctx × VmWorld m)) :=
  h ctx f w

private theorem stack_empty_size : Stack.empty.size = 0 := by
  rw [Stack.size_eq_length_toList, Stack.toList_empty]
  rfl

private theorem stack_of_size (n : Nat) (hn : n ≤ STACK_DEPTH_LIMIT) :
    ∃ s : Stack, s.size = n := by
  change n ≤ 1024 at hn
  induction n with
  | zero => exact ⟨Stack.empty, stack_empty_size⟩
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih (by omega)
    cases hp : s.push (U256.ofNat 0) with
    | error e =>
      have := (Stack.push_eq_error_iff s (U256.ofNat 0) e).mp hp
      omega
    | ok t =>
      have ht := ((Stack.push_eq_ok_iff s t (U256.ofNat 0)).mp hp).2
      have hl := congrArg List.length ht
      rw [List.length_cons, ← Stack.size_eq_length_toList t,
        ← Stack.size_eq_length_toList s] at hl
      exact ⟨t, by omega⟩

private theorem depth_at_limit_excludes_children (ctx : FrameCtx)
    (hd : ctx.depth = STACK_DEPTH_LIMIT) (r : StepResult ctx) :
    match r with
    | .call _ _ _ _ | .create _ _ _ _ => False
    | _ => True := by
  cases r with
  | call _ _ h _ | create _ _ h _ => omega
  | _ => trivial

private theorem stack_at_limit_excludes_children (ctx : FrameCtx)
    (parent : Frame) (hs : parent.stack.size = STACK_DEPTH_LIMIT) (r : StepResult ctx) :
    match r with
    | .call suspended _ _ _ | .create suspended _ _ _ => suspended ≠ parent
    | _ => True := by
  cases r with
  | call suspended _ _ hd | create suspended _ _ hd =>
    intro he
    subst suspended
    omega
  | _ => trivial

private theorem full_and_room_stacks :
    (∃ s : Stack, s.size = STACK_DEPTH_LIMIT) ∧
    (∃ s : Stack, s.size = STACK_DEPTH_LIMIT - 1 ∧ s.size < STACK_DEPTH_LIMIT) := by
  constructor
  · exact stack_of_size STACK_DEPTH_LIMIT (by omega)
  · obtain ⟨s, hs⟩ := stack_of_size (STACK_DEPTH_LIMIT - 1) (by omega)
    exact ⟨s, hs, by rw [hs]; decide⟩

private theorem strict_bound_construction (ctx : FrameCtx) (parent : Frame)
    (callReq : CallRequest) (createReq : CreateRequest)
    (depth : Nat) (hd : depth < STACK_DEPTH_LIMIT) (stack : Stack)
    (hs : stack.size < STACK_DEPTH_LIMIT) (configuredLimit : Nat) :
    let fixed := { ctx with
      config := { ctx.config with
        limits := { ctx.config.limits with stackDepthLimit := configuredLimit } }
      depth := depth
      depth_le := Nat.le_of_lt hd }
    let suspended := { parent with stack := stack }
    payload (StepResult.call (ctx := fixed) suspended callReq hd hs) =
      (suspended, none, none, some callReq, none) ∧
    payload (StepResult.create (ctx := fixed) suspended createReq hd hs) =
      (suspended, none, none, none, some createReq) := by
  exact ⟨rfl, rfl⟩

private theorem terminal_at_limits (ctx : FrameCtx) (parent : Frame) (output : Bytes)
    (e : ExceptionalHalt) (configuredLimit : Nat) :
    let fixed := { ctx with
      config := { ctx.config with
        limits := { ctx.config.limits with stackDepthLimit := configuredLimit } }
      depth := STACK_DEPTH_LIMIT
      depth_le := Nat.le_refl _ }
    ∃ s : Stack, s.size = STACK_DEPTH_LIMIT ∧
      payload (.continue { parent with stack := s } : StepResult fixed) =
        ({ parent with stack := s }, none, none, none, none) ∧
      payload (.stop { parent with stack := s } output : StepResult fixed) =
        ({ parent with stack := s }, some output, none, none, none) ∧
      payload (.revert { parent with stack := s } output : StepResult fixed) =
        ({ parent with stack := s }, some output, none, none, none) ∧
      payload (.halt { parent with stack := s } e : StepResult fixed) =
        ({ parent with stack := s }, none, some e, none, none) := by
  obtain ⟨s, hs⟩ := full_and_room_stacks.1
  exact ⟨s, hs, rfl, rfl, rfl, rfl⟩

end STFSpec.Conformance.Vm.Instructions.StepResultCallerProofs
