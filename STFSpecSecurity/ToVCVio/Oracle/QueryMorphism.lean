/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import Init.Control.Lawful.Basic

/-!
# Explicit query-preserving monad interpretation

The record states the pure, bind and chosen-query laws required by a consumer.
It does not infer transport of an arbitrary direct-style kernel from its type.
Library `ToVCVio` in `STFSpecSecurity`.
Spec guidance: `STFSpec/informal/modules/ToVCVio.md` §§5/7.
-/

namespace ToVCVio.Oracle

/-- A chosen interpretation map preserving pure, bind and the same query action.
Its fields are proof obligations; polymorphic capability types alone supply none. -/
structure QueryMorphism (Input Answer : Type) (m n : Type → Type) [Monad m] [Monad n]
    (qm : Input → m Answer) (qn : Input → n Answer) where
  map : {α : Type} → m α → n α
  map_pure : ∀ {α : Type} (a : α), map (pure a) = pure a
  map_bind : ∀ {α β : Type} (a : m α) (k : α → m β),
    map (a >>= k) = map a >>= fun x => map (k x)
  map_query : ∀ input, map (qm input) = qn input

end ToVCVio.Oracle
