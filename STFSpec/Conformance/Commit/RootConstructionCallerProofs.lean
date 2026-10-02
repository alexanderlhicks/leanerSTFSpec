/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit.Root

/-!
# Universal public-contract clients of recursive construction

Library `EthConformance`. Clients use the public C7 equations, finite-map and
node/codec contracts. They do not name private selection, measures or storage.
The explicit domain/maximality premises are supplied by callers; lawful monad
premises occur only for reassociation and original transformer-error equations.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/7.1/7.3.
-/

namespace STFSpec.Conformance.Commit.RootConstructionCallerProofs

open STFSpec.Commit STFSpec.Codec STFSpec.Hash

/-- Every finite full map is a zero-depth caller, including empty keys and values. -/
def atZero {m : Type → Type} [Monad m] [KeccakQuery m]
    (obj : Std.ExtTreeMap Nibbles ByteArray) : m (Option InternalNode) :=
  patricialize obj 0 (PatricializeDomain.zero obj)

/-- Whole-map optional observations, rather than insertion histories, determine C7. -/
theorem same_final_map {m : Type → Type} [Monad m] [KeccakQuery m]
    (obj other : Std.ExtTreeMap Nibbles ByteArray)
    (same : ∀ key : Nibbles, obj[key]? = other[key]?) :
    atZero (m := m) obj = atZero other :=
  patricialize_ext obj other 0 (PatricializeDomain.zero obj) (PatricializeDomain.zero other) same

/-- Arbitrary-depth proof witnesses are irrelevant to the complete monadic action. -/
theorem proof_arguments {m : Type → Type} [Monad m] [KeccakQuery m]
    (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (left right : PatricializeDomain obj level) :
    patricialize (m := m) obj level left = patricialize obj level right :=
  patricialize_domain_irrel obj level left right

/-- A single original value is kept, with no C6 encoding at the C7 return. -/
theorem singleton_original {m : Type → Type} [Monad m] [KeccakQuery m]
    (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (domain : PatricializeDomain obj level) (single : obj.size = 1)
    (key : Nibbles) (member : key ∈ obj) :
    patricialize (m := m) obj level domain =
      pure (some (.leaf (key.drop level) (.bytes (obj[key]'member)))) :=
  patricialize_singleton obj level domain single key member

/-- Two different members supply equal extension equations with the same recursive action.
The common amount is specified entirely by reachable-domain/maximality premises. -/
theorem extension_members {m : Type → Type} [Monad m] [KeccakQuery m]
    (obj : Std.ExtTreeMap Nibbles ByteArray) (level amount : Nat)
    (domain : PatricializeDomain obj level) (multikey : 1 < obj.size)
    (a b : Nibbles) (ha : a ∈ obj) (hb : b ∈ obj) (positive : 0 < amount)
    (advanced : PatricializeDomain obj (level + amount))
    (maximal : ∀ extra, PatricializeDomain obj (level + extra) → extra ≤ amount) :
    (do
      let child ← patricialize (m := m) obj (level + amount) advanced
      let reference ← encodeInternalNode child
      pure (some (InternalNode.extension (a.extract level (level + amount)) reference))) =
    (do
      let child ← patricialize (m := m) obj (level + amount) advanced
      let reference ← encodeInternalNode child
      pure (some (InternalNode.extension (b.extract level (level + amount)) reference))) := by
  rw [← patricialize_extension obj level amount domain multikey a ha positive advanced maximal,
    ← patricialize_extension obj level amount domain multikey b hb positive advanced maximal]

/-- An original recursive error suppresses the extension's child encoding entirely. -/
theorem extension_original_error {m : Type → Type} [Monad m] [LawfulMonad m]
    {ε : Type} [KeccakQuery (ExceptT ε m)]
    (obj : Std.ExtTreeMap Nibbles ByteArray) (level amount : Nat)
    (domain : PatricializeDomain obj level) (multikey : 1 < obj.size)
    (key : Nibbles) (member : key ∈ obj) (positive : 0 < amount)
    (advanced : PatricializeDomain obj (level + amount))
    (maximal : ∀ extra, PatricializeDomain obj (level + extra) → extra ≤ amount)
    (error : ε)
    (failed : (patricialize (m := ExceptT ε m) obj (level + amount) advanced).run =
      pure (.error error)) :
    (patricialize (m := ExceptT ε m) obj level domain).run = pure (.error error) := by
  rw [patricialize_extension obj level amount domain multikey key member positive advanced maximal,
    ExceptT.run_bind, failed]
  simp

/-- The public branch equation's first actual child failure suppresses all later
construction and encoding, preserving the original error without wrapping it. -/
theorem branch_original_error {m : Type → Type} [Monad m] [LawfulMonad m]
    {ε : Type} [KeccakQuery (ExceptT ε m)]
    (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (domain : PatricializeDomain obj level) (multikey : 1 < obj.size)
    (key : Nibbles) (member : key ∈ obj)
    (noPrefix : ¬ PatricializeDomain obj (level + 1)) (error : ε)
    (failed : (patricialize (m := ExceptT ε m)
      (obj.filter (fun path _ ↦
        if h : level < path.size then decide (path.get ⟨level, h⟩ = 0) else false))
      (level + 1) (domain.child 0)).run = pure (.error error)) :
    (patricialize (m := ExceptT ε m) obj level domain).run = pure (.error error) := by
  rw [patricialize_branch_lawful obj level domain multikey key member noPrefix,
    Vector.ofFnM_succ', ExceptT.run_bind, ExceptT.run_bind, ExceptT.run_bind, failed]
  simp

/-- Ordered full child fields and the final ending field are observed through C6 laws. -/
theorem branch_positions (children : Vector RlpItem 16) (value : RlpItem) (digit : Fin 16) :
    (children.toList ++ [value])[digit.val]'(by simp; omega) = children[digit] ∧
      (children.toList ++ [value])[16]'(by simp) = value :=
  ⟨branch_items_get children value digit, branch_items_value children value⟩

end STFSpec.Conformance.Commit.RootConstructionCallerProofs
