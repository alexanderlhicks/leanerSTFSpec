/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Runner

/-!
# Public checked-carrier clients

Library `EthConformance`. Private clients retain complete payloads and base
actions through the public Runner facade. Local Id compositions exercise the
two separate short-circuit channels; they implement no guest or runner adapter.
Spec guidance: `STFSpec/informal/modules/EthVmRunner.md` §§3/4/5/7.
-/

namespace STFSpec.Conformance.Vm.Runner.CheckedCallerProofs
open STFSpec.Vm.Runner

private def errorSignature : Nat → InternalError := InternalError.fuelExhausted
private def resultSignature : Type → Type → Type := CheckedResult
private def transformerSignature : Type → (Type → Type) → Type → Type := CheckedT

private theorem result_unfolding (ε α : Type) :
    CheckedResult ε α = Except InternalError (Except ε α) := rfl

private theorem transformer_unfolding (ε : Type) (m : Type → Type) :
    CheckedT ε m = ExceptT ε (ExceptT InternalError m) := rfl

private theorem depth_payload (depth : Nat) :
    (match InternalError.fuelExhausted depth with
      | .fuelExhausted d => d) = depth := rfl

private theorem complete_result {ε α : Type} (result : CheckedResult ε α) :
    (match result with
      | .error e => Except.error e
      | .ok (.error e) => Except.ok (Except.error e)
      | .ok (.ok a) => Except.ok (Except.ok a)) = result := by
  cases result with
  | error e => rfl
  | ok value => cases value <;> rfl

-- No Monad, hash-query or lawful-monad premise is needed for either direction.
private def runSignature {ε α : Type} {m : Type → Type} :
    CheckedT ε m α → m (Except InternalError (Except ε α)) := fun action => action.run.run

private theorem complete_action {ε α : Type} {m : Type → Type}
    (action : m (CheckedResult ε α)) :
    (ExceptT.mk (ExceptT.mk action) : CheckedT ε m α).run.run = action := rfl

private theorem complete_internal {ε α : Type} (depth : Nat) :
    (ExceptT.mk (ExceptT.mk (Except.error (.fuelExhausted depth))) :
      CheckedT ε Id α).run.run = Except.error (.fuelExhausted depth) := rfl

private theorem complete_rejection {ε α : Type} (error : ε) :
    (ExceptT.mk (ExceptT.mk (Except.ok (Except.error error))) :
      CheckedT ε Id α).run.run = Except.ok (Except.error error) := rfl

private theorem complete_success {ε α : Type} (value : α) :
    (ExceptT.mk (ExceptT.mk (Except.ok (Except.ok value))) :
      CheckedT ε Id α).run.run = Except.ok (Except.ok value) := rfl

-- Observe all alternatives with complete structured error/success payloads.
private def observe (result : CheckedResult (String × List Nat) (Int × List Nat)) :
    Nat × Nat × String × Int × List Nat :=
  match result with
  | .error (.fuelExhausted depth) => (0, depth, "", 0, [])
  | .ok (.error (text, data)) => (1, 0, text, 0, data)
  | .ok (.ok (number, data)) => (2, 0, "", number, data)

#guard observe (.error (.fuelExhausted 0)) == (0, 0, "", 0, [])
#guard observe (.error (.fuelExhausted (2^300 + 71))) == (0, 2^300 + 71, "", 0, [])
#guard observe (.ok (.error ("rejected", [0, 2^260, 7, 7]))) ==
  (1, 0, "rejected", 0, [0, 2^260, 7, 7])
#guard observe (.ok (.ok (-19, [2^280, 0, 13, 13]))) ==
  (2, 0, "", -19, [2^280, 0, 13, 13])

-- Actual Id-monad binds: a first failure prevents the later, different failure.
private def internalFirst : CheckedT (String × List Nat) Id (Int × List Nat) := do
  let _ : Nat ← ExceptT.mk (ExceptT.mk (.error (.fuelExhausted (2^300 + 71))))
  throw ("later rejection", [11, 12])

private def rejectionFirst : CheckedT (String × List Nat) Id (Int × List Nat) := do
  let _ : Nat ← throw ("first rejection", [0, 2^260, 7, 7])
  ExceptT.mk (ExceptT.mk (.error (.fuelExhausted 999)))

private def successThenInternal : CheckedT (String × List Nat) Id (Int × List Nat) := do
  let depth : Nat ← pure 0
  ExceptT.mk (ExceptT.mk (.error (.fuelExhausted depth)))

private def successThenRejection : CheckedT (String × List Nat) Id (Int × List Nat) := do
  let data : List Nat ← pure [0, 2^260, 7, 7]
  throw ("rejected", data)

private def successThenSuccess : CheckedT (String × List Nat) Id (Int × List Nat) := do
  let number : Int ← pure (-19)
  let data : List Nat ← pure [2^280, 0, 13, 13]
  pure (number, data)

#guard observe internalFirst.run.run == (0, 2^300 + 71, "", 0, [])
#guard observe rejectionFirst.run.run == (1, 0, "first rejection", 0, [0, 2^260, 7, 7])
#guard observe successThenInternal.run.run == (0, 0, "", 0, [])
#guard observe successThenRejection.run.run == (1, 0, "rejected", 0, [0, 2^260, 7, 7])
#guard observe successThenSuccess.run.run == (2, 0, "", -19, [2^280, 0, 13, 13])

end STFSpec.Conformance.Vm.Runner.CheckedCallerProofs
