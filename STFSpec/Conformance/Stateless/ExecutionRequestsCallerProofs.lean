/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless

/-!
# Raw execution-request aggregate clients

Library `EthConformance`. Private facade clients check complete arbitrary arrays,
reconstruction, determination, independent updates and public Array conversions.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Stateless.ExecutionRequestsCallerProofs

open STFSpec.Stateless

private def constructor : Array DepositRequest → Array WithdrawalRequest →
    Array ConsolidationRequest → Array BuilderDepositRequest → Array BuilderExitRequest →
    ExecutionRequests := ExecutionRequests.mk

private def deposits : ExecutionRequests → Array DepositRequest := ExecutionRequests.deposits
private def withdrawals : ExecutionRequests → Array WithdrawalRequest :=
  ExecutionRequests.withdrawals
private def consolidations : ExecutionRequests → Array ConsolidationRequest :=
  ExecutionRequests.consolidations
private def builderDeposits : ExecutionRequests → Array BuilderDepositRequest :=
  ExecutionRequests.builderDeposits
private def builderExits : ExecutionRequests → Array BuilderExitRequest :=
  ExecutionRequests.builderExits

private def fields (r : ExecutionRequests) :
    Array DepositRequest × Array WithdrawalRequest × Array ConsolidationRequest ×
      Array BuilderDepositRequest × Array BuilderExitRequest :=
  (r.deposits, r.withdrawals, r.consolidations, r.builderDeposits, r.builderExits)

private def observe (r : ExecutionRequests) :
    List DepositRequest × List WithdrawalRequest × List ConsolidationRequest ×
      List BuilderDepositRequest × List BuilderExitRequest :=
  (r.deposits.toList, r.withdrawals.toList, r.consolidations.toList, r.builderDeposits.toList,
    r.builderExits.toList)

private theorem construction (deposits : Array DepositRequest)
    (withdrawals : Array WithdrawalRequest) (consolidations : Array ConsolidationRequest)
    (builderDeposits : Array BuilderDepositRequest) (builderExits : Array BuilderExitRequest) :
    fields (constructor deposits withdrawals consolidations builderDeposits builderExits) =
      (deposits, withdrawals, consolidations, builderDeposits, builderExits) := rfl

private theorem construction_observations (d : Array DepositRequest)
    (w : Array WithdrawalRequest) (c : Array ConsolidationRequest)
    (b : Array BuilderDepositRequest) (e : Array BuilderExitRequest) :
    observe (ExecutionRequests.mk d w c b e) =
      (d.toList, w.toList, c.toList, b.toList, e.toList) := rfl

private theorem whole_conversion_recovery (r : ExecutionRequests) :
    ExecutionRequests.mk r.deposits.toList.toArray r.withdrawals.toList.toArray
      r.consolidations.toList.toArray r.builderDeposits.toList.toArray
      r.builderExits.toList.toArray = r := by
  simp only [Array.toArray_toList]

private theorem reconstruction (r : ExecutionRequests) :
    ExecutionRequests.mk r.deposits r.withdrawals r.consolidations r.builderDeposits r.builderExits
      = r := rfl

private theorem fields_determine (r s : ExecutionRequests) (h : fields r = fields s) :
    r = s := by
  cases r
  cases s
  cases h
  rfl

private theorem observations_determine (r s : ExecutionRequests) (h : observe r = observe s) :
    r = s := by
  simp only [observe, Prod.mk.injEq] at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  apply fields_determine
  simp only [fields, Prod.mk.injEq]
  exact ⟨Array.toList_inj.mp h0, Array.toList_inj.mp h1, Array.toList_inj.mp h2,
    Array.toList_inj.mp h3, Array.toList_inj.mp h4⟩

private theorem update_deposits (r : ExecutionRequests) (value : Array DepositRequest) :
    { r with deposits := value } =
      ExecutionRequests.mk value r.withdrawals r.consolidations r.builderDeposits r.builderExits :=
        rfl

private theorem observe_update_deposits (r : ExecutionRequests) (value : Array DepositRequest) :
    observe { r with deposits := value } =
      (value.toList, r.withdrawals.toList, r.consolidations.toList, r.builderDeposits.toList,
        r.builderExits.toList) := rfl

private theorem recover_deposits (r : ExecutionRequests) :
    r.deposits.toList.toArray = r.deposits := Array.toArray_toList

private theorem update_withdrawals (r : ExecutionRequests) (value : Array WithdrawalRequest) :
    { r with withdrawals := value } =
      ExecutionRequests.mk r.deposits value r.consolidations r.builderDeposits r.builderExits :=
        rfl

private theorem observe_update_withdrawals (r : ExecutionRequests)
    (value : Array WithdrawalRequest) :
    observe { r with withdrawals := value } =
      (r.deposits.toList, value.toList, r.consolidations.toList, r.builderDeposits.toList,
        r.builderExits.toList) := rfl

private theorem recover_withdrawals (r : ExecutionRequests) :
    r.withdrawals.toList.toArray = r.withdrawals := Array.toArray_toList

private theorem update_consolidations (r : ExecutionRequests)
    (value : Array ConsolidationRequest) :
    { r with consolidations := value } =
      ExecutionRequests.mk r.deposits r.withdrawals value r.builderDeposits r.builderExits := rfl

private theorem observe_update_consolidations (r : ExecutionRequests)
    (value : Array ConsolidationRequest) :
    observe { r with consolidations := value } =
      (r.deposits.toList, r.withdrawals.toList, value.toList, r.builderDeposits.toList,
        r.builderExits.toList) := rfl

private theorem recover_consolidations (r : ExecutionRequests) :
    r.consolidations.toList.toArray = r.consolidations := Array.toArray_toList

private theorem update_builderDeposits (r : ExecutionRequests)
    (value : Array BuilderDepositRequest) :
    { r with builderDeposits := value } =
      ExecutionRequests.mk r.deposits r.withdrawals r.consolidations value r.builderExits := rfl

private theorem observe_update_builderDeposits (r : ExecutionRequests)
    (value : Array BuilderDepositRequest) :
    observe { r with builderDeposits := value } =
      (r.deposits.toList, r.withdrawals.toList, r.consolidations.toList, value.toList,
        r.builderExits.toList) := rfl

private theorem recover_builderDeposits (r : ExecutionRequests) :
    r.builderDeposits.toList.toArray = r.builderDeposits := Array.toArray_toList

private theorem update_builderExits (r : ExecutionRequests) (value : Array BuilderExitRequest) :
    { r with builderExits := value } =
      ExecutionRequests.mk r.deposits r.withdrawals r.consolidations r.builderDeposits value := rfl

private theorem observe_update_builderExits (r : ExecutionRequests)
    (value : Array BuilderExitRequest) :
    observe { r with builderExits := value } =
      (r.deposits.toList, r.withdrawals.toList, r.consolidations.toList, r.builderDeposits.toList,
        value.toList) := rfl

private theorem recover_builderExits (r : ExecutionRequests) :
    r.builderExits.toList.toArray = r.builderExits := Array.toArray_toList

end STFSpec.Conformance.Stateless.ExecutionRequestsCallerProofs
