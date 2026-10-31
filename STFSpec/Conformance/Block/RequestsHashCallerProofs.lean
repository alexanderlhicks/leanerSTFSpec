/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block

/-!
# Private facade clients of the complete execution-request commitment law

Library `EthConformance`. Only the public whole-result equation and public Base
byte contracts are used; no SHA provider implementation is unfolded.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3/4/5/7.
-/

namespace STFSpec.Conformance.Block.RequestsHashCallerProofs
open STFSpec.Block STFSpec.Base

private theorem complete_equation (requests : List ByteArray) :
    computeRequestsHash requests = Hash32.ofBytes32 (Hash.sha256
      (Bytes.ofList ((requests.map (fun request ↦
        (Hash.sha256 request).toBytes.toList)).flatten)).toByteArray) :=
  computeRequestsHash_eq requests

private theorem complete_output_bytes (requests : List ByteArray) :
    (computeRequestsHash requests).toBytes = (Hash.sha256
      (Bytes.ofList ((requests.map (fun request ↦
        (Hash.sha256 request).toBytes.toList)).flatten)).toByteArray).toBytes := by
  rw [computeRequestsHash_eq, Hash32.toBytes_ofBytes32]

private theorem empty :
    computeRequestsHash [] = Hash32.ofBytes32 (Hash.sha256 ByteArray.empty) := by
  rw [computeRequestsHash_eq]
  rfl

private theorem singleton (request : ByteArray) :
    computeRequestsHash [request] =
      Hash32.ofBytes32 (Hash.sha256 (Hash.sha256 request).toBytes.toByteArray) := by
  rw [computeRequestsHash_eq]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil, Bytes.ofList_toList]

private theorem pair (first second : ByteArray) :
    computeRequestsHash [first, second] = Hash32.ofBytes32 (Hash.sha256
      ((Hash.sha256 first).toBytes ++ (Hash.sha256 second).toBytes).toByteArray) := by
  rw [computeRequestsHash_eq]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil]
  rw [← Bytes.toList_append, Bytes.ofList_toList]

private theorem preimage_size (requests : List ByteArray) :
    (Bytes.ofList ((requests.map (fun request ↦
      (Hash.sha256 request).toBytes.toList)).flatten)).size = 32 * requests.length := by
  rw [Bytes.size_ofList]
  induction requests with
  | nil => rfl
  | cons request requests ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, Bytes.length_toList,
      FixedBytes.size_toBytes, List.length_cons] at *
    omega

end STFSpec.Conformance.Block.RequestsHashCallerProofs
