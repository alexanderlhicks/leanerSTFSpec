/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless

/-!
# Raw execution witness clients

Library `EthConformance`. Private public-facade clients retain all three independent
arrays through construction, projection, reconstruction and record updates.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Stateless.ExecutionWitnessCallerProofs

open STFSpec.Stateless

private def construct (state codes headers : Array ByteArray) : ExecutionWitness :=
  ExecutionWitness.mk state codes headers

private def fields (w : ExecutionWitness) :
    Array ByteArray × Array ByteArray × Array ByteArray :=
  (w.state, w.codes, w.headers)

private theorem constructor_fields (state codes headers : Array ByteArray) :
    fields (construct state codes headers) = (state, codes, headers) := rfl

private theorem reconstruction (w : ExecutionWitness) :
    ExecutionWitness.mk w.state w.codes w.headers = w := rfl

private theorem all_fields_determine (w v : ExecutionWitness) (h : fields w = fields v) :
    w = v := by
  cases w
  cases v
  cases h
  rfl

private theorem update_state (w : ExecutionWitness) (state : Array ByteArray) :
    { w with state := state } = ExecutionWitness.mk state w.codes w.headers := rfl

private theorem update_codes (w : ExecutionWitness) (codes : Array ByteArray) :
    { w with codes := codes } = ExecutionWitness.mk w.state codes w.headers := rfl

private theorem update_headers (w : ExecutionWitness) (headers : Array ByteArray) :
    { w with headers := headers } = ExecutionWitness.mk w.state w.codes headers := rfl

end STFSpec.Conformance.Stateless.ExecutionWitnessCallerProofs
