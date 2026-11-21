/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateWitness

/-!
# Witness code database clients

Library `EthConformance`. Private facade clients check the map carrier, the separate
authenticity predicate and the bare monadic builder type.
Spec guidance: `STFSpec/informal/modules/EthStateWitness.md` §§3–5.
-/

namespace STFSpec.Conformance.StateWitness.CodeDBCallerProofs

open STFSpec.Base STFSpec.Hash STFSpec.StateWitness

private theorem constructor_map (entries : Std.HashMap Hash32 ByteArray) :
    (CodeDB.mk entries).map = entries := rfl

private theorem reconstruct (db : CodeDB) : CodeDB.mk db.map = db := rfl

private theorem replace_map (db : CodeDB) (entries : Std.HashMap Hash32 ByteArray) :
    { db with map := entries } = CodeDB.mk entries := rfl

private theorem authentic_iff (H : ByteArray → Hash32) (db : CodeDB) :
    CodeDB.Authentic H db ↔ ∀ key code, db.map[key]? = some code → H code = key :=
  Iff.rfl

private def build {m : Type → Type} [Monad m] [KeccakQuery m] :
    Array ByteArray → m CodeDB :=
  CodeDB.build

end STFSpec.Conformance.StateWitness.CodeDBCallerProofs
