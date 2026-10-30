/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Runner

/-!
# Execution entry-kind facade clients

Library `EthConformance`. Private constructor, exhaustive elimination, branch and
disjointness clients for the nominal carrier. No execution semantics is asserted.
Spec guidance: `STFSpec/informal/modules/EthVmRunner.md` §§3/4/5/7.
-/

namespace STFSpec.Conformance.Vm.Runner.ExecKindCallerProofs

open STFSpec.Vm.Runner

universe u

private def frame_loop_constructor : ExecKind := ExecKind.frameLoop

private def call_constructor : ExecKind := ExecKind.call

private def create_constructor : ExecKind := ExecKind.create

private theorem exhaustive (kind : ExecKind) :
    kind = .frameLoop ∨ kind = .call ∨ kind = .create := by
  cases kind with
  | frameLoop => exact Or.inl rfl
  | call => exact Or.inr (Or.inl rfl)
  | create => exact Or.inr (Or.inr rfl)

private def eliminate {P : ExecKind → Sort u}
    (frameLoop : P .frameLoop) (call : P .call) (create : P .create)
    (kind : ExecKind) : P kind :=
  match kind with
  | .frameLoop => frameLoop
  | .call => call
  | .create => create

private theorem frame_loop_branch {P : ExecKind → Sort u}
    (frameLoop : P .frameLoop) (call : P .call) (create : P .create) :
    eliminate frameLoop call create .frameLoop = frameLoop := rfl

private theorem call_branch {P : ExecKind → Sort u}
    (frameLoop : P .frameLoop) (call : P .call) (create : P .create) :
    eliminate frameLoop call create .call = call := rfl

private theorem create_branch {P : ExecKind → Sort u}
    (frameLoop : P .frameLoop) (call : P .call) (create : P .create) :
    eliminate frameLoop call create .create = create := rfl

private theorem frame_loop_ne_call : ExecKind.frameLoop ≠ .call := by
  intro h
  cases h

private theorem frame_loop_ne_create : ExecKind.frameLoop ≠ .create := by
  intro h
  cases h

private theorem call_ne_frame_loop : ExecKind.call ≠ .frameLoop := by
  intro h
  cases h

private theorem call_ne_create : ExecKind.call ≠ .create := by
  intro h
  cases h

private theorem create_ne_frame_loop : ExecKind.create ≠ .frameLoop := by
  intro h
  cases h

private theorem create_ne_call : ExecKind.create ≠ .call := by
  intro h
  cases h

end STFSpec.Conformance.Vm.Runner.ExecKindCallerProofs
