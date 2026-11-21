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

private def addmodSignature {m : Type → Type} [Monad m] : Handler m := addmod

private theorem addmod_run_empty_client {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((addmod ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) :=
  addmod_run_empty ctx f w h

private theorem addmod_run_singleton_client {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      ((addmod ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w)) :=
  addmod_run_singleton ctx f w x h

private theorem addmod_run_pair_client {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256)
    (h : f.stack.toList = [x, y]) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = [] ∧ ((addmod ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .stackUnderflow, w)) :=
  addmod_run_pair ctx f w x y h

private theorem addmod_run_oog_client {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y z : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: z :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeAddmod) :
    ∃ s₁ s₂ s₃ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.pop = .ok (z, s₃) ∧ s₃.toList = xs ∧ ((addmod ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₃ } .outOfGas, w)) :=
  addmod_run_oog ctx f w x y z xs h hc

private theorem addmod_run_success_client {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y z : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: z :: xs)
    (hc : ctx.config.costs.opcodeAddmod ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ s₃ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.pop = .ok (z, s₃) ∧ s₃.toList = xs ∧ s₃.push (U256.addmod x y z) = .ok out ∧
      out.toList = U256.addmod x y z :: xs ∧
      ((addmod ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeAddmod } }, w)) :=
  addmod_run_success ctx f w x y z xs h hc

private theorem addmod_continue_phi_client (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((addmod ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeAddmod = f.gasMeter.phi :=
  addmod_continue_phi ctx f f' w w' h

private theorem addmod_continue_progress_client (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((addmod ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeAddmod) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi :=
  addmod_continue_progress ctx f f' w w' h hc

private theorem addmod_numeric_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y z : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: z :: xs)
    (hc : ctx.config.costs.opcodeAddmod ≤ f.gasMeter.gasLeft) :
    ∃ out : Stack,
      out.toList.map U256.toNat =
        (if z.toNat = 0 then 0 else (x.toNat + y.toNat) % z.toNat) ::
          xs.map U256.toNat ∧
      ((addmod ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeAddmod } }, w)) := by
  obtain ⟨_, _, _, out, _, _, _, _, _, hm, hr⟩ := addmod_run_success ctx f w x y z xs h hc
  refine ⟨out, ?_, hr⟩
  rw [hm, List.map_cons, U256.toNat_addmod]

private def mulmodSignature {m : Type → Type} [Monad m] : Handler m := mulmod

private theorem mulmod_run_empty_client {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((mulmod ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) :=
  mulmod_run_empty ctx f w h

private theorem mulmod_run_singleton_client {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      ((mulmod ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w)) :=
  mulmod_run_singleton ctx f w x h

private theorem mulmod_run_pair_client {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256)
    (h : f.stack.toList = [x, y]) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = [] ∧ ((mulmod ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .stackUnderflow, w)) :=
  mulmod_run_pair ctx f w x y h

private theorem mulmod_run_oog_client {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y z : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: z :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeMulmod) :
    ∃ s₁ s₂ s₃ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.pop = .ok (z, s₃) ∧ s₃.toList = xs ∧ ((mulmod ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₃ } .outOfGas, w)) :=
  mulmod_run_oog ctx f w x y z xs h hc

private theorem mulmod_run_success_client {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y z : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: z :: xs)
    (hc : ctx.config.costs.opcodeMulmod ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ s₃ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.pop = .ok (z, s₃) ∧ s₃.toList = xs ∧ s₃.push (U256.mulmod x y z) = .ok out ∧
      out.toList = U256.mulmod x y z :: xs ∧
      ((mulmod ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeMulmod } }, w)) :=
  mulmod_run_success ctx f w x y z xs h hc

private theorem mulmod_continue_phi_client (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((mulmod ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeMulmod = f.gasMeter.phi :=
  mulmod_continue_phi ctx f f' w w' h

private theorem mulmod_continue_progress_client (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((mulmod ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeMulmod) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi :=
  mulmod_continue_progress ctx f f' w w' h hc

private theorem mulmod_numeric_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y z : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: z :: xs)
    (hc : ctx.config.costs.opcodeMulmod ≤ f.gasMeter.gasLeft) :
    ∃ out : Stack,
      out.toList.map U256.toNat =
        (if z.toNat = 0 then 0 else (x.toNat * y.toNat) % z.toNat) ::
          xs.map U256.toNat ∧
      ((mulmod ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeMulmod } }, w)) := by
  obtain ⟨_, _, _, out, _, _, _, _, _, hm, hr⟩ := mulmod_run_success ctx f w x y z xs h hc
  refine ⟨out, ?_, hr⟩
  rw [hm, List.map_cons, U256.toNat_mulmod]

section
local notation "expCost(" ctx ", " exponent ")" =>
  (GasCosts.opcodeExpBase (VmConfig.costs (FrameCtx.config ctx)) +
    GasCosts.opcodeExpPerByte (VmConfig.costs (FrameCtx.config ctx)) *
    ((U256.bitLength exponent + 7) / 8))

private def expSignature {m : Type → Type} [Monad m] : Handler m := exp

private theorem exp_run_empty_client {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((exp ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) :=
  exp_run_empty ctx f w h

private theorem exp_run_singleton_client {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (base : U256)
    (h : f.stack.toList = [base]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (base, s₁) ∧ s₁.toList = [] ∧
      ((exp ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w)) :=
  exp_run_singleton ctx f w base h

private theorem exp_run_oog_client {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (base exponent : U256) (xs : List U256)
    (h : f.stack.toList = base :: exponent :: xs) (hc : f.gasMeter.gasLeft < expCost(ctx, exponent)) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (base, s₁) ∧ s₁.pop = .ok (exponent, s₂) ∧
      s₂.toList = xs ∧ ((exp ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w)) :=
  exp_run_oog ctx f w base exponent xs h hc

private theorem exp_run_success_client {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (base exponent : U256) (xs : List U256)
    (h : f.stack.toList = base :: exponent :: xs) (hc : expCost(ctx, exponent) ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (base, s₁) ∧ s₁.pop = .ok (exponent, s₂) ∧
      s₂.toList = xs ∧ s₂.push (U256.exp base exponent) = .ok out ∧
      out.toList = U256.exp base exponent :: xs ∧
      ((exp ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - expCost(ctx, exponent) } }, w)) :=
  exp_run_success ctx f w base exponent xs h hc

private theorem exp_continue_phi_client (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (base exponent : U256) (xs : List U256)
    (hstack : f.stack.toList = base :: exponent :: xs)
    (hrun : ((exp ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + expCost(ctx, exponent) = f.gasMeter.phi :=
  exp_continue_phi ctx f f' w w' base exponent xs hstack hrun

private theorem exp_continue_progress_client (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (base exponent : U256) (xs : List U256)
    (hstack : f.stack.toList = base :: exponent :: xs)
    (hrun : ((exp ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ expCost(ctx, exponent)) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi :=
  exp_continue_progress ctx f f' w w' base exponent xs hstack hrun hc

private theorem exp_numeric_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (base exponent : U256) (xs : List U256)
    (h : f.stack.toList = base :: exponent :: xs) (hc : expCost(ctx, exponent) ≤ f.gasMeter.gasLeft) :
    ∃ out : Stack, out.toList.map U256.toNat =
      (base.toNat ^ exponent.toNat % 2^256) :: xs.map U256.toNat ∧
      ((exp ctx f).run w).run = pure (Except.ok (.continue {f with
        pc := f.pc + 1, stack := out, gasMeter := {f.gasMeter with
          gasLeft := f.gasMeter.gasLeft - expCost(ctx, exponent)}}, w)) := by
  obtain ⟨_, _, out, _, _, _, _, hm, hr⟩ := exp_run_success ctx f w base exponent xs h hc
  refine ⟨out, ?_, hr⟩
  rw [hm, List.map_cons, U256.toNat_exp]

private theorem exp_actual_pop_accounting (ctx : FrameCtx) (f f' : Frame)
    (w w' : VmWorld Id) (base exponent : U256) (s₁ s₂ : Stack)
    (h₁ : f.stack.pop = .ok (base, s₁)) (h₂ : s₁.pop = .ok (exponent, s₂))
    (hrun : ((exp ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + expCost(ctx, exponent) = f.gasMeter.phi := by
  have hm₁ := (Stack.pop_eq_ok_iff f.stack s₁ base).mp h₁
  have hm₂ := (Stack.pop_eq_ok_iff s₁ s₂ exponent).mp h₂
  have hs : f.stack.toList = base :: exponent :: s₂.toList := by rw [hm₁, hm₂]
  exact exp_continue_phi ctx f f' w w' base exponent s₂.toList hs hrun

private theorem exp_zero_cost (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (base exponent : U256) (xs : List U256)
    (hs : f.stack.toList = base :: exponent :: xs)
    (hr : ((exp ctx f).run w).run = .ok (.continue f', w'))
    (hb : ctx.config.costs.opcodeExpBase = 0)
    (hp : ctx.config.costs.opcodeExpPerByte = 0) : f'.gasMeter.phi = f.gasMeter.phi := by
  have h := exp_continue_phi ctx f f' w w' base exponent xs hs hr
  simpa only [hb, hp, Nat.zero_mul, Nat.add_zero] using h

private theorem exp_per_byte_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (base : U256) (xs : List U256)
    (hs : f.stack.toList = base :: U256.one :: xs)
    (hr : ((exp ctx f).run w).run = .ok (.continue f', w'))
    (hb : ctx.config.costs.opcodeExpBase = 0)
    (hp : ctx.config.costs.opcodeExpPerByte = 1) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  apply exp_continue_progress ctx f f' w w' base U256.one xs hs hr
  simp only [hb, hp, U256.bitLength_def, U256.toNat_one]
  decide

private theorem exp_zero_exponent_value {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (base : U256) (xs : List U256)
    (hs : f.stack.toList = base :: U256.zero :: xs)
    (hc : ctx.config.costs.opcodeExpBase ≤ f.gasMeter.gasLeft) :
    ∃ out : Stack, out.toList = U256.one :: xs ∧
      ((exp ctx f).run w).run = pure (Except.ok (.continue {f with
        pc := f.pc + 1, stack := out, gasMeter := {f.gasMeter with
          gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeExpBase}}, w)) := by
  have hb : U256.bitLength U256.zero = 0 := by
    simp only [U256.bitLength_def, U256.toNat_zero, ↓reduceIte]
  obtain ⟨_, _, out, _, _, _, _, hm, hr⟩ := exp_run_success ctx f w base U256.zero xs hs
    (by simpa only [hb, Nat.zero_add, Nat.reduceDiv, Nat.mul_zero, Nat.add_zero] using hc)
  refine ⟨out, ?_, ?_⟩
  · simpa only [U256.exp_zero] using hm
  · simpa only [hb, Nat.zero_add, Nat.reduceDiv, Nat.mul_zero, Nat.add_zero] using hr

private theorem exp_one_exponent_result {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (base : U256) (xs : List U256)
    (hs : f.stack.toList = base :: U256.one :: xs)
    (hc : ctx.config.costs.opcodeExpBase + ctx.config.costs.opcodeExpPerByte ≤
      f.gasMeter.gasLeft) :
    ∃ out : Stack, out.toList = base :: xs ∧
      ((exp ctx f).run w).run = pure (Except.ok (.continue {f with
        pc := f.pc + 1, stack := out, gasMeter := {f.gasMeter with
          gasLeft := f.gasMeter.gasLeft -
            (ctx.config.costs.opcodeExpBase + ctx.config.costs.opcodeExpPerByte)}}, w)) := by
  have hb : U256.bitLength U256.one = 1 := by
    rw [U256.bitLength_def, U256.toNat_one]
    rfl
  obtain ⟨_, _, out, _, _, _, _, hm, hr⟩ := exp_run_success ctx f w base U256.one xs hs
    (by simpa only [hb, Nat.reduceAdd, Nat.reduceDiv, Nat.mul_one] using hc)
  refine ⟨out, ?_, ?_⟩
  · simpa only [U256.exp_one] using hm
  · simpa only [hb, Nat.reduceAdd, Nat.reduceDiv, Nat.mul_one] using hr

private theorem exp_zero_exponent_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (base : U256) (xs : List U256)
    (hs : f.stack.toList = base :: U256.zero :: xs)
    (hr : ((exp ctx f).run w).run = .ok (.continue f', w'))
    (hb : ctx.config.costs.opcodeExpBase = 0) : f'.gasMeter.phi = f.gasMeter.phi := by
  have hp := exp_continue_phi ctx f f' w w' base U256.zero xs hs hr
  simpa only [hb, U256.bitLength_def, U256.toNat_zero, ↓reduceIte,
    Nat.zero_add, Nat.reduceDiv, Nat.mul_zero, Nat.add_zero] using hp

private theorem exp_byte_count_bound (exponent : U256) :
    (U256.bitLength exponent + 7) / 8 ≤ 32 := by
  have h := U256.bitLength_le exponent
  omega

private theorem exp_one_value (base : U256) : U256.exp base U256.one = base :=
  U256.exp_one base

private theorem exp_one_base (exponent : U256) : U256.exp U256.one exponent = U256.one :=
  U256.one_exp exponent

private theorem exp_zero_base (exponent : U256) (h : exponent.toNat ≠ 0) :
    U256.exp U256.zero exponent = U256.zero := U256.zero_exp exponent h

private theorem exp_short_stack_no_continue (ctx : FrameCtx) (f f' : Frame)
    (w w' : VmWorld Id) (h : f.stack.toList = [] ∨ ∃ base, f.stack.toList = [base]) :
    ((exp ctx f).run w).run ≠ .ok (.continue f', w') := by
  rcases h with h | ⟨base, h⟩
  · rw [exp_run_empty ctx f w h]
    intro he
    cases he
  · obtain ⟨_, _, _, hr⟩ := exp_run_singleton ctx f w base h
    rw [hr]
    intro he
    cases he

end

end STFSpec.Conformance.Vm.Instructions.ArithmeticCallerProofs
