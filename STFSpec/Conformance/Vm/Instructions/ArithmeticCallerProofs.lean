/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions

/-!
# Arithmetic public-law clients

Library `EthConformance`. Generic consumers retain complete action equations;
actual Id consumers use exact accounting and locally conditional progress.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Vm.Instructions.ArithmeticCallerProofs
open STFSpec.Base STFSpec.Vm.Core STFSpec.Vm.Instructions

private def signatures {m : Type → Type} [Monad m] : Handler m × Handler m × Handler m × Handler m :=
  (add, sub, mul, div)

private theorem empty_precedence {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((add ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) ∧
    ((sub ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) ∧
    ((mul ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) ∧
    ((div ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) :=
  ⟨add_run_empty ctx f w h, sub_run_empty ctx f w h,
    mul_run_empty ctx f w h, div_run_empty ctx f w h⟩

private theorem add_singleton_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ rest : Stack, rest.toList = [] ∧
      ((add ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .stackUnderflow, w)) := by
  obtain ⟨rest, _, hm, hr⟩ := add_run_singleton ctx f w x h
  exact ⟨rest, hm, hr⟩

private theorem add_shortage_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeAdd) :
    ∃ rest : Stack, rest.size = xs.length ∧
      ((add ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .outOfGas, w)) := by
  obtain ⟨_, rest, _, _, hm, hr⟩ := add_run_oog ctx f w x y xs h hc
  exact ⟨rest, by rw [Stack.size_eq_length_toList, hm], hr⟩

private theorem add_success_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : ctx.config.costs.opcodeAdd ≤ f.gasMeter.gasLeft) :
    ∃ out : Stack, out.toList = U256.add x y :: xs ∧
      ((add ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeAdd } }, w)) := by
  obtain ⟨_, _, out, _, _, _, _, hm, hr⟩ := add_run_success ctx f w x y xs h hc
  exact ⟨out, hm, hr⟩

private theorem add_accounting (ctx : FrameCtx) (f f' : Frame)
    (w w' : VmWorld Id)
    (h : ((add ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeAdd) :
    f'.gasMeter.phi + ctx.config.costs.opcodeAdd = f.gasMeter.phi ∧
      f'.gasMeter.phi + 1 ≤ f.gasMeter.phi :=
  ⟨add_continue_phi ctx f f' w w' h, add_continue_progress ctx f f' w w' h hc⟩

private theorem sub_singleton_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ rest : Stack, rest.toList = [] ∧
      ((sub ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .stackUnderflow, w)) := by
  obtain ⟨rest, _, hm, hr⟩ := sub_run_singleton ctx f w x h
  exact ⟨rest, hm, hr⟩

private theorem sub_shortage_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeSub) :
    ∃ rest : Stack, rest.size = xs.length ∧
      ((sub ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .outOfGas, w)) := by
  obtain ⟨_, rest, _, _, hm, hr⟩ := sub_run_oog ctx f w x y xs h hc
  exact ⟨rest, by rw [Stack.size_eq_length_toList, hm], hr⟩

private theorem sub_success_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : ctx.config.costs.opcodeSub ≤ f.gasMeter.gasLeft) :
    ∃ out : Stack, out.toList = U256.sub x y :: xs ∧
      ((sub ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSub } }, w)) := by
  obtain ⟨_, _, out, _, _, _, _, hm, hr⟩ := sub_run_success ctx f w x y xs h hc
  exact ⟨out, hm, hr⟩

private theorem sub_accounting (ctx : FrameCtx) (f f' : Frame)
    (w w' : VmWorld Id)
    (h : ((sub ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeSub) :
    f'.gasMeter.phi + ctx.config.costs.opcodeSub = f.gasMeter.phi ∧
      f'.gasMeter.phi + 1 ≤ f.gasMeter.phi :=
  ⟨sub_continue_phi ctx f f' w w' h, sub_continue_progress ctx f f' w w' h hc⟩

private theorem mul_singleton_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ rest : Stack, rest.toList = [] ∧
      ((mul ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .stackUnderflow, w)) := by
  obtain ⟨rest, _, hm, hr⟩ := mul_run_singleton ctx f w x h
  exact ⟨rest, hm, hr⟩

private theorem mul_shortage_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeMul) :
    ∃ rest : Stack, rest.size = xs.length ∧
      ((mul ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .outOfGas, w)) := by
  obtain ⟨_, rest, _, _, hm, hr⟩ := mul_run_oog ctx f w x y xs h hc
  exact ⟨rest, by rw [Stack.size_eq_length_toList, hm], hr⟩

private theorem mul_success_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : ctx.config.costs.opcodeMul ≤ f.gasMeter.gasLeft) :
    ∃ out : Stack, out.toList = U256.mul x y :: xs ∧
      out.toList.map U256.toNat = (x.toNat * y.toNat) % 2 ^ 256 :: xs.map U256.toNat ∧
      ((mul ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeMul } }, w)) := by
  obtain ⟨_, _, out, _, _, _, _, hm, hr⟩ := mul_run_success ctx f w x y xs h hc
  refine ⟨out, hm, ?_, hr⟩
  rw [hm, List.map_cons, U256.toNat_mul]

private theorem mul_accounting (ctx : FrameCtx) (f f' : Frame)
    (w w' : VmWorld Id)
    (h : ((mul ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeMul) :
    f'.gasMeter.phi + ctx.config.costs.opcodeMul = f.gasMeter.phi ∧
      f'.gasMeter.phi + 1 ≤ f.gasMeter.phi :=
  ⟨mul_continue_phi ctx f f' w w' h, mul_continue_progress ctx f f' w w' h hc⟩

private theorem div_singleton_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ rest : Stack, rest.toList = [] ∧
      ((div ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .stackUnderflow, w)) := by
  obtain ⟨rest, _, hm, hr⟩ := div_run_singleton ctx f w x h
  exact ⟨rest, hm, hr⟩

private theorem div_shortage_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeDiv) :
    ∃ rest : Stack, rest.size = xs.length ∧
      ((div ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .outOfGas, w)) := by
  obtain ⟨_, rest, _, _, hm, hr⟩ := div_run_oog ctx f w x y xs h hc
  exact ⟨rest, by rw [Stack.size_eq_length_toList, hm], hr⟩

private theorem div_success_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : ctx.config.costs.opcodeDiv ≤ f.gasMeter.gasLeft) :
    ∃ out : Stack, out.toList = U256.div x y :: xs ∧
      out.toList.map U256.toNat = (if y.toNat = 0 then 0 else x.toNat / y.toNat) :: xs.map U256.toNat ∧
      ((div ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeDiv } }, w)) := by
  obtain ⟨_, _, out, _, _, _, _, hm, hr⟩ := div_run_success ctx f w x y xs h hc
  refine ⟨out, hm, ?_, hr⟩
  rw [hm, List.map_cons, U256.toNat_div]

private theorem div_accounting (ctx : FrameCtx) (f f' : Frame)
    (w w' : VmWorld Id)
    (h : ((div ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeDiv) :
    f'.gasMeter.phi + ctx.config.costs.opcodeDiv = f.gasMeter.phi ∧
      f'.gasMeter.phi + 1 ≤ f.gasMeter.phi :=
  ⟨div_continue_phi ctx f f' w w' h, div_continue_progress ctx f f' w w' h hc⟩

private def signedModSignatures {m : Type → Type} [Monad m] :
    Handler m × Handler m × Handler m := (sdiv, mod, smod)

private theorem sdiv_empty_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((sdiv ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) :=
  sdiv_run_empty ctx f w h

private theorem sdiv_singleton_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ rest : Stack, rest.toList = [] ∧
      ((sdiv ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .stackUnderflow, w)) := by
  obtain ⟨rest, _, hm, hr⟩ := sdiv_run_singleton ctx f w x h
  exact ⟨rest, hm, hr⟩

private theorem sdiv_shortage_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeSdiv) :
    ∃ rest : Stack, rest.size = xs.length ∧
      ((sdiv ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .outOfGas, w)) := by
  obtain ⟨_, rest, _, _, hm, hr⟩ := sdiv_run_oog ctx f w x y xs h hc
  exact ⟨rest, by rw [Stack.size_eq_length_toList, hm], hr⟩

private theorem sdiv_success_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : ctx.config.costs.opcodeSdiv ≤ f.gasMeter.gasLeft) :
    ∃ out : Stack, out.toList = U256.sdiv x y :: xs ∧
      out.toList.map U256.toInt = (if y.toInt = 0 then 0 else
        if x.toInt = -(2 : Int) ^ 255 ∧ y.toInt = -1 then -(2 : Int) ^ 255
        else x.toInt.tdiv y.toInt) :: xs.map U256.toInt ∧
      ((sdiv ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSdiv } }, w)) := by
  obtain ⟨_, _, out, _, _, _, _, hm, hr⟩ := sdiv_run_success ctx f w x y xs h hc
  refine ⟨out, hm, ?_, hr⟩
  rw [hm, List.map_cons, U256.toInt_sdiv]

private theorem sdiv_accounting (ctx : FrameCtx) (f f' : Frame)
    (w w' : VmWorld Id)
    (h : ((sdiv ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeSdiv) :
    f'.gasMeter.phi + ctx.config.costs.opcodeSdiv = f.gasMeter.phi ∧
      f'.gasMeter.phi + 1 ≤ f.gasMeter.phi :=
  ⟨sdiv_continue_phi ctx f f' w w' h, sdiv_continue_progress ctx f f' w w' h hc⟩

private theorem mod_empty_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((mod ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) :=
  mod_run_empty ctx f w h

private theorem mod_singleton_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ rest : Stack, rest.toList = [] ∧
      ((mod ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .stackUnderflow, w)) := by
  obtain ⟨rest, _, hm, hr⟩ := mod_run_singleton ctx f w x h
  exact ⟨rest, hm, hr⟩

private theorem mod_shortage_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeMod) :
    ∃ rest : Stack, rest.size = xs.length ∧
      ((mod ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .outOfGas, w)) := by
  obtain ⟨_, rest, _, _, hm, hr⟩ := mod_run_oog ctx f w x y xs h hc
  exact ⟨rest, by rw [Stack.size_eq_length_toList, hm], hr⟩

private theorem mod_success_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : ctx.config.costs.opcodeMod ≤ f.gasMeter.gasLeft) :
    ∃ out : Stack, out.toList = U256.mod x y :: xs ∧
      out.toList.map U256.toNat = (if y.toNat = 0 then 0 else x.toNat % y.toNat) :: xs.map U256.toNat ∧
      ((mod ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeMod } }, w)) := by
  obtain ⟨_, _, out, _, _, _, _, hm, hr⟩ := mod_run_success ctx f w x y xs h hc
  refine ⟨out, hm, ?_, hr⟩
  rw [hm, List.map_cons, U256.toNat_mod]

private theorem mod_accounting (ctx : FrameCtx) (f f' : Frame)
    (w w' : VmWorld Id)
    (h : ((mod ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeMod) :
    f'.gasMeter.phi + ctx.config.costs.opcodeMod = f.gasMeter.phi ∧
      f'.gasMeter.phi + 1 ≤ f.gasMeter.phi :=
  ⟨mod_continue_phi ctx f f' w w' h, mod_continue_progress ctx f f' w w' h hc⟩

private theorem smod_empty_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((smod ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) :=
  smod_run_empty ctx f w h

private theorem smod_singleton_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ rest : Stack, rest.toList = [] ∧
      ((smod ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .stackUnderflow, w)) := by
  obtain ⟨rest, _, hm, hr⟩ := smod_run_singleton ctx f w x h
  exact ⟨rest, hm, hr⟩

private theorem smod_shortage_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeSmod) :
    ∃ rest : Stack, rest.size = xs.length ∧
      ((smod ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .outOfGas, w)) := by
  obtain ⟨_, rest, _, _, hm, hr⟩ := smod_run_oog ctx f w x y xs h hc
  exact ⟨rest, by rw [Stack.size_eq_length_toList, hm], hr⟩

private theorem smod_success_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : ctx.config.costs.opcodeSmod ≤ f.gasMeter.gasLeft) :
    ∃ out : Stack, out.toList = U256.smod x y :: xs ∧
      out.toList.map U256.toInt = (if y.toInt = 0 then 0 else x.toInt.tmod y.toInt) :: xs.map U256.toInt ∧
      ((smod ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSmod } }, w)) := by
  obtain ⟨_, _, out, _, _, _, _, hm, hr⟩ := smod_run_success ctx f w x y xs h hc
  refine ⟨out, hm, ?_, hr⟩
  rw [hm, List.map_cons, U256.toInt_smod]

private theorem smod_accounting (ctx : FrameCtx) (f f' : Frame)
    (w w' : VmWorld Id)
    (h : ((smod ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeSmod) :
    f'.gasMeter.phi + ctx.config.costs.opcodeSmod = f.gasMeter.phi ∧
      f'.gasMeter.phi + 1 ≤ f.gasMeter.phi :=
  ⟨smod_continue_phi ctx f f' w w' h, smod_continue_progress ctx f f' w w' h hc⟩

private def signextendSignature {m : Type → Type} [Monad m] : Handler m := signextend

private theorem signextend_empty_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((signextend ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) :=
  signextend_run_empty ctx f w h

private theorem signextend_singleton_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ rest : Stack, rest.toList = [] ∧
      ((signextend ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .stackUnderflow, w)) := by
  obtain ⟨rest, _, hm, hr⟩ := signextend_run_singleton ctx f w x h
  exact ⟨rest, hm, hr⟩

private theorem signextend_shortage_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeSignextend) :
    ∃ rest : Stack, rest.size = xs.length ∧
      ((signextend ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .outOfGas, w)) := by
  obtain ⟨_, rest, _, _, hm, hr⟩ := signextend_run_oog ctx f w x y xs h hc
  exact ⟨rest, by rw [Stack.size_eq_length_toList, hm], hr⟩

private theorem signextend_success_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : ctx.config.costs.opcodeSignextend ≤ f.gasMeter.gasLeft) :
    ∃ out : Stack, out.toList = U256.signextend x y :: xs ∧
      out.toList.map U256.toNat = (if 31 < x.toNat then y.toNat else
        y.toNat % 2 ^ (8 * (x.toNat + 1)) +
          if y.toBitVec.getLsbD (8 * (x.toNat + 1) - 1) then
            2 ^ 256 - 2 ^ (8 * (x.toNat + 1)) else 0) :: xs.map U256.toNat ∧
      ((signextend ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSignextend } }, w)) := by
  obtain ⟨_, _, out, _, _, _, _, hm, hr⟩ := signextend_run_success ctx f w x y xs h hc
  refine ⟨out, hm, ?_, hr⟩
  rw [hm, List.map_cons, U256.toNat_signextend]

private theorem signextend_accounting (ctx : FrameCtx) (f f' : Frame)
    (w w' : VmWorld Id)
    (h : ((signextend ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeSignextend) :
    f'.gasMeter.phi + ctx.config.costs.opcodeSignextend = f.gasMeter.phi ∧
      f'.gasMeter.phi + 1 ≤ f.gasMeter.phi :=
  ⟨signextend_continue_phi ctx f f' w w' h, signextend_continue_progress ctx f f' w w' h hc⟩

private theorem signextend_identity_large {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (k x : U256) (xs : List U256)
    (h : f.stack.toList = k :: x :: xs) (hc : ctx.config.costs.opcodeSignextend ≤ f.gasMeter.gasLeft)
    (hk : 31 < k.toNat) :
    ∃ out : Stack, out.toList = x :: xs ∧
      ((signextend ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSignextend } }, w)) := by
  obtain ⟨_, _, out, _, _, _, _, hm, hr⟩ := signextend_run_success ctx f w k x xs h hc
  rw [U256.signextend_eq_self_of_lt k x hk] at hm
  exact ⟨out, hm, hr⟩

private theorem signextend_identity_last {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (k x : U256) (xs : List U256)
    (h : f.stack.toList = k :: x :: xs) (hc : ctx.config.costs.opcodeSignextend ≤ f.gasMeter.gasLeft)
    (hk : k.toNat = 31) :
    ∃ out : Stack, out.toList = x :: xs ∧
      ((signextend ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSignextend } }, w)) := by
  obtain ⟨_, _, out, _, _, _, _, hm, hr⟩ := signextend_run_success ctx f w k x xs h hc
  rw [U256.signextend_eq_self_of_eq k x hk] at hm
  exact ⟨out, hm, hr⟩

end STFSpec.Conformance.Vm.Instructions.ArithmeticCallerProofs
