/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless

/-!
# Stateless output public-law clients

Library `EthConformance`. Symbolic private clients consume the public output laws
through the facade, preserving the complete field domain and all 43 bytes.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§4/7.
-/

namespace STFSpec.Conformance.Stateless

open STFSpec.Base STFSpec.Stateless

private theorem output_fields (root : Hash32) (valid : Bool) (chain : U64) (schema : UInt16) :
    (serializeStatelessOutput ⟨root, valid, chain, schema⟩).data.toList =
      root.toBytes.toList ++ [if valid then 1 else 0] ++
      (List.range 8).map (fun i ↦ UInt8.ofNat ((chain.toNat / 256^i) % 256)) ++
      (List.range 2).map (fun i ↦ UInt8.ofNat ((schema.toNat / 256^i) % 256)) :=
  serializeStatelessOutput_eq _

private theorem all_fields_preserved (a b : StatelessValidationResult) :
    serializeStatelessOutput a = serializeStatelessOutput b ↔
      a.newPayloadRequestRoot = b.newPayloadRequestRoot ∧
      a.successfulValidation = b.successfulValidation ∧ a.chainId = b.chainId ∧
      a.schemaId = b.schemaId := by
  rw [serializeStatelessOutput_inj]
  constructor
  · intro h
    subst b
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨hr, hv, hc, hs⟩
    cases a
    cases b
    simp_all

private theorem exact_size (root : Hash32) (valid : Bool) (chain : U64) (schema : UInt16) :
    (serializeStatelessOutput ⟨root, valid, chain, schema⟩).size = 43 :=
  serializeStatelessOutput_size _

private theorem sentinel_fields :
    zeroSentinel.newPayloadRequestRoot = Hash32.ofBytes32 (FixedBytes.ofNat 0) ∧
    zeroSentinel.successfulValidation = false ∧ zeroSentinel.chainId = U64.zero ∧
    zeroSentinel.schemaId = 0 := zeroSentinel_fields

private theorem sentinel_bytes :
    serializeStatelessOutput zeroSentinel = (List.replicate 43 0).toByteArray := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simpa only [List.toList_data_toByteArray] using serializeStatelessOutput_zeroSentinel

end STFSpec.Conformance.Stateless
