/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Public block-initialization callers

Library `EthConformance`: exact class-free signature and clients of the explicit
F20 law. Defaults and whole-provider retention are verified inside the State owner.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/4/7/8.
-/

namespace STFSpec.Conformance.State.BlockInitializationCallerProofs

open STFSpec.State STFSpec.Base

private def signature : {m : Type → Type} → PreState m → HashConsts → BlockState m :=
  @BlockState.new

private def Contravariant (α : Type) : Type := α → Nat

#check_failure (inferInstance : Monad Contravariant)

private def noMonadSignature : PreState Contravariant → HashConsts → BlockState Contravariant :=
  signature

private theorem constants {m : Type → Type} (ps : PreState m) (consts : HashConsts) :
    (BlockState.new ps consts).consts = consts := BlockState.new_consts ps consts

private theorem noMonadConstants (ps : PreState Contravariant) (consts : HashConsts) :
    (noMonadSignature ps consts).consts = consts := BlockState.new_consts ps consts

private theorem completeHashBytes {m : Type → Type} (ps : PreState m) (consts : HashConsts) :
    ((BlockState.new ps consts).consts.emptyCodeHash.toBytes,
      (BlockState.new ps consts).consts.emptyTrieRoot.toBytes,
      (BlockState.new ps consts).consts.emptyOmmerHash.toBytes,
      (BlockState.new ps consts).consts.transferTopic.toBytes) =
    (consts.emptyCodeHash.toBytes, consts.emptyTrieRoot.toBytes,
      consts.emptyOmmerHash.toBytes, consts.transferTopic.toBytes) := by
  rw [BlockState.new_consts]

end STFSpec.Conformance.State.BlockInitializationCallerProofs
