/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless

/-!
# Raw stateless input facade clients

Library `EthConformance`. Private clients retain all three independent whole fields.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Stateless.InputCallerProofs

open STFSpec.Stateless

private def construct : NewPayloadRequest → ExecutionWitness → STFSpec.Base.U64 →
    StatelessInput := StatelessInput.mk

private def requestProjection : StatelessInput → NewPayloadRequest :=
  StatelessInput.newPayloadRequest

private def witnessProjection : StatelessInput → ExecutionWitness := StatelessInput.witness

private def chainProjection : StatelessInput → STFSpec.Base.U64 := StatelessInput.chainId

private def fields (x : StatelessInput) :
    NewPayloadRequest × ExecutionWitness × STFSpec.Base.U64 :=
  (requestProjection x, witnessProjection x, chainProjection x)

private theorem constructor_fields (request : NewPayloadRequest) (witness : ExecutionWitness)
    (chainId : STFSpec.Base.U64) :
    fields (construct request witness chainId) = (request, witness, chainId) := rfl

private theorem reconstruction (x : StatelessInput) :
    StatelessInput.mk x.newPayloadRequest x.witness x.chainId = x := rfl

private theorem all_fields_determine (x y : StatelessInput) (h : fields x = fields y) :
    x = y := by
  cases x
  cases y
  cases h
  rfl

private theorem update_request (x : StatelessInput) (request : NewPayloadRequest) :
    { x with newPayloadRequest := request } =
      StatelessInput.mk request x.witness x.chainId := rfl

private theorem update_witness (x : StatelessInput) (witness : ExecutionWitness) :
    { x with witness := witness } =
      StatelessInput.mk x.newPayloadRequest witness x.chainId := rfl

private theorem update_chain (x : StatelessInput) (chainId : STFSpec.Base.U64) :
    { x with chainId := chainId } =
      StatelessInput.mk x.newPayloadRequest x.witness chainId := rfl

private theorem chain_observation (x : StatelessInput) :
    STFSpec.Base.U64.ofNat x.chainId.toNat = x.chainId :=
  STFSpec.Base.U64.ofNat_toNat x.chainId

private theorem witness_array_recovery (x : StatelessInput) :
    ExecutionWitness.mk x.witness.state.toList.toArray x.witness.codes.toList.toArray
      x.witness.headers.toList.toArray = x.witness := by simp

end STFSpec.Conformance.Stateless.InputCallerProofs
