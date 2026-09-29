/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import Lean

/-!
# Declaration check

Checks the *compiled* declarations of the declaration checked modules, so that no source-level
formatting can hide a violation (`CONTRIBUTING.md` §4):

* **axioms**: every declaration may depend only on `propext`, `Quot.sound` and
  `Classical.choice`. This rejects `sorryAx` (unless `--allow-sorry`), and the auxiliary
  `…._native.*` axioms introduced by `native_decide`, `bv_decide` and `decide +native`;
* **no `axiom` declarations** in checked modules;
* **no `unsafe`, `partial` or `opaque` constants** (totality and transparency);
* **no `@[extern]` or `@[implemented_by]`** (D21). There is no exception mechanism;
* **`@[csimp]` is banned** (D21, a design rule for executable correspondence: compiled
  code must run the definition we reason about). Every registered `@[csimp]` theorem,
  current or superseded, that lives in or replaces a function defined in a checked module
  is a finding. An axiom-dirty one is *additionally* reported, even under `--allow-sorry`,
  because it may already have been applied when earlier code was compiled.

Only `--allow-sorry` is accepted as an option (for the Mathlib and security packages during development);
any other `--flag` is rejected.
-/

open Lean

namespace CheckDecls

/-- Axioms every declaration may depend on. -/
def allowedAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- One violation found by the declaration check. -/
structure Finding where
  decl : Name
  kind : String
  detail : String

/-- A minimal environment monad, enough to run Lean's `collectAxioms`. -/
abbrev EnvM := StateM Environment

instance : MonadEnv EnvM where
  getEnv := get
  modifyEnv := modify

/-- The axioms `n` depends on, transitively. -/
def axiomsOf (env : Environment) (n : Name) : Array Name :=
  ((collectAxioms n : EnvM (Array Name)).run env).1

/-- The module that defines `n`, if it was imported. -/
def moduleOf? (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx.toNat]?

/-- Whether `n` is defined in a module under one of the declaration checked roots. -/
def inScope (env : Environment) (roots : Array Name) (n : Name) : Bool :=
  match moduleOf? env n with
  | some m => roots.any (·.isPrefixOf m)
  | none => false

/-- The current `@[csimp]` replacement for each function. Requires an environment imported
with `loadExts := true`; otherwise extension states are empty and this would silently
return nothing. Only the *latest* replacement per function is kept here, so this is not
enough for checking (see `csimpTheorems`). -/
def csimpEntries (env : Environment) : List Compiler.CSimp.Entry :=
  (Compiler.CSimp.ext.getState env).map.toList.map (·.2)

/-- Every `@[csimp]` theorem ever registered, including ones superseded by a later
replacement for the same function. A superseded replacement may already have been applied
when compiling earlier definitions, so each one must be checked. -/
def csimpTheorems (env : Environment) : List Name :=
  (Compiler.CSimp.ext.getState env).thmNames.toList

/-- Check all declarations under `roots`. -/
def check (env : Environment) (roots : Array Name) (allowSorry : Bool) :
    Array Finding := Id.run do
  let mut out : Array Finding := #[]
  for (n, ci) in env.constants.toList do
    unless inScope env roots n do continue
    if let .axiomInfo _ := ci then
      out := out.push ⟨n, "axiom", "axiom declaration"⟩
    if ci.isUnsafe then
      out := out.push ⟨n, "unsafe", "unsafe declaration"⟩
    -- A `partial def` compiles to an *opaque* constant (implemented by an auxiliary
    -- `_unsafe_rec`); structural and well-founded recursion yield safe definitions, which
    -- also get `_unsafe_rec` compiler auxiliaries, so the suffix alone is not evidence.
    -- Opaque constants are banned outright: they cannot be unfolded in proofs.
    if let .opaqueInfo _ := ci then
      unless isExtern env n do
        let kind := if env.contains (n ++ `_unsafe_rec) then "partial" else "opaque"
        out := out.push ⟨n, kind, s!"{kind} constant (cannot be unfolded in proofs)"⟩
    if isExtern env n then
      out := out.push ⟨n, "extern", "@[extern] declaration"⟩
    if (Compiler.getImplementedBy? env n).isSome then
      out := out.push ⟨n, "implemented_by", "@[implemented_by] declaration"⟩
    let bad := (axiomsOf env n).filter fun a =>
      !(allowedAxioms.contains a) && !(allowSorry && a == ``sorryAx)
    unless bad.isEmpty do
      out := out.push ⟨n, "axioms", s!"depends on {bad.toList}"⟩
  -- Compiler replacements: always strict, and over *every* registered theorem (current or
  -- superseded) that lives in scope or replaces a function defined in scope.
  let replaces : NameMap Name := (csimpEntries env).foldl
    (fun m e => m.insert e.thmName e.fromDeclName) {}
  for thm in csimpTheorems env do
    let target := (replaces.find? thm).getD thm
    if inScope env roots thm || inScope env roots target then
      out := out.push ⟨thm, "csimp-banned", s!"@[csimp] {target} is banned in the spec (D21)"⟩
      let bad := (axiomsOf env thm).filter (!allowedAxioms.contains ·)
      unless bad.isEmpty do
        let superseded := if replaces.contains thm then "" else " (superseded, but may already have been applied)"
        out := out.push ⟨thm, "csimp", s!"@[csimp] theorem depends on {bad.toList}{superseded}"⟩
  return out

/-- Entry point: `check-decls [--allow-sorry] Module ...`.
`unsafe` because loading extension states runs initializers; the tool itself is not part
of the declaration checked spec. -/
unsafe def run (args : List String) : IO UInt32 := do
  let usage := "usage: check-decls [--allow-sorry] Module ..."
  let (flags, mods) := args.partition (·.startsWith "--")
  if let some f := flags.find? (· != "--allow-sorry") then
    IO.eprintln s!"check-decls: unknown option {f}\n{usage}"
    return 2
  let allowSorry := flags.contains "--allow-sorry"
  if mods.isEmpty then
    IO.eprintln usage
    return 2
  initSearchPath (← findSysroot)
  let roots := mods.toArray.map String.toName
  -- `loadExts := true` is essential: without it every environment extension (including
  -- the `@[csimp]` table) keeps its initial, empty state.
  enableInitializersExecution
  let env ← importModules (roots.map fun m => { module := m }) {} (trustLevel := 1024)
    (loadExts := true)
  let nCsimp := (csimpTheorems env).length
  if nCsimp == 0 then
    IO.eprintln "check-decls: no @[csimp] entries visible; extension state not loaded"
    return 3
  let found := check env roots allowSorry
  let nDecls := env.constants.toList.countP fun (n, _) => inScope env roots n
  for f in found do
    IO.println s!"{f.kind}: {f.decl}: {f.detail}"
  IO.println s!"check-decls: {nDecls} declarations under {roots.toList}, {nCsimp} csimp theorems checked; {found.size} findings"
  return if found.isEmpty then 0 else 1

end CheckDecls
