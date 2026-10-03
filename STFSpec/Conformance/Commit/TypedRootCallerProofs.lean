/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit

/-!
# Imported typed-root clients

Library `EthConformance`. Named clients compose public storage, preparation and
C8 laws without unfolding their representations. Monad-law requirements remain
explicit. No concrete key/value encoding bridge or NoDefault premise is adopted.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/7.0.3; Q53.
-/

namespace STFSpec.Conformance.Commit.TypedRootCallerProofs

open STFSpec.Base STFSpec.Hash STFSpec.Commit

variable {K V : Type} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]
variable [TrieValue V] [KeyBytes K]

omit [Std.LawfulEqOrd K] in
/-- Direct complete composition uses Monad alone, without preparation sequencing. -/
theorem complete_action {m : Type → Type} [Monad m] [KeccakQuery m]
    (emptyRoot : Hash32) (t : Trie K V) (unsecured : t.secured = false)
    (safe : t.PrepareSafe) :
    root (m := m) emptyRoot t unsecured safe = mathRoot emptyRoot (prepareTrieModel t) :=
  root_eq_mathRoot emptyRoot t unsecured safe

omit [Std.LawfulEqOrd K] in
/-- Any caller-supplied empty root is retained, including a nonliteral constant. -/
theorem supplied_empty {m : Type → Type} [Monad m] [KeccakQuery m]
    (emptyRoot : Hash32) (t : Trie K V) (unsecured : t.secured = false)
    (safe : t.PrepareSafe) (empty : t.data = ∅) :
    root (m := m) emptyRoot t unsecured safe = pure emptyRoot :=
  root_empty emptyRoot t unsecured safe empty

/-- Only the explicitly lawful domain identifies separately sequenced preparation. -/
theorem sequenced_reference {m : Type → Type} [Monad m] [KeccakQuery m] [LawfulMonad m]
    (emptyRoot : Hash32) (t : Trie K V) (unsecured : t.secured = false)
    (safe : t.PrepareSafe) :
    root (m := m) emptyRoot t unsecured safe = (do
      let prepared ← prepareTrie (m := m) t unsecured safe
      mathRoot emptyRoot prepared) := root_eq_reference emptyRoot t unsecured safe

/-- Complete optional storage observations determine complete typed-root actions. -/
theorem equal_storage {m : Type → Type} [Monad m] [KeccakQuery m]
    (emptyRoot : Hash32) (t u : Trie K V) (ut : t.secured = false) (uu : u.secured = false)
    (st : t.PrepareSafe) (su : u.PrepareSafe) (same : ∀ k : K, t.data[k]? = u.data[k]?) :
    root (m := m) emptyRoot t ut st = root emptyRoot u uu su := by
  rw [root_eq_mathRoot, root_eq_mathRoot,
    prepareTrieModel_congr t u (Std.ExtTreeMap.ext_getElem? same)]

omit [Std.LawfulEqOrd K] in
/-- The actual state transformer action is forwarded directly to C8. -/
theorem state_forwarding {σ : Type} {m : Type → Type} [Monad m] [KeccakQuery (StateT σ m)]
    (emptyRoot : Hash32) (t : Trie K V) (unsecured : t.secured = false)
    (safe : t.PrepareSafe) (state : σ) :
    (root (m := StateT σ m) emptyRoot t unsecured safe).run state =
      (mathRoot (m := StateT σ m) emptyRoot (prepareTrieModel t)).run state := by
  rw [root_eq_mathRoot]

omit [Std.LawfulEqOrd K] in
/-- Original C8 errors and underlying effects are forwarded without a local handler. -/
theorem error_forwarding {ε : Type} {m : Type → Type} [Monad m] [KeccakQuery (ExceptT ε m)]
    (emptyRoot : Hash32) (t : Trie K V) (unsecured : t.secured = false)
    (safe : t.PrepareSafe) :
    (root (m := ExceptT ε m) emptyRoot t unsecured safe).run =
      (mathRoot (m := ExceptT ε m) emptyRoot (prepareTrieModel t)).run := by
  rw [root_eq_mathRoot]

end STFSpec.Conformance.Commit.TypedRootCallerProofs
