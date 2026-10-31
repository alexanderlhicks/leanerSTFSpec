/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Hash.Sha256Digest

/-!
# Ordered execution-request SHA commitment

Library `EthBlock`. Pinned EELS `src/ethereum/forks/amsterdam/requests.py:307–328`.
Every complete inner digest is emitted in input order into one reserved packed
preimage. Request production and validation belong to their callers.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§2.10/3/4/5/7.
-/

namespace STFSpec.Block
open STFSpec.Base

private def requestsHashPreimageModel (requests : List ByteArray) : List UInt8 :=
  (requests.map (fun request ↦ (Hash.sha256 request).toBytes.toList)).flatten

private def requestsHashPreimage (requests : List ByteArray) : ByteArray :=
  requests.foldl (fun acc request ↦ (Hash.sha256 request).toBytes.foldl ByteArray.push acc)
    (ByteArray.emptyWithCapacity (32 * requests.length))

private theorem foldl_push_model (bytes : List UInt8) (acc : ByteArray) :
    (bytes.foldl ByteArray.push acc).data.toList = acc.data.toList ++ bytes := by
  induction bytes generalizing acc with
  | nil => simp
  | cons byte bytes ih =>
    simp only [List.foldl_cons, ih, ByteArray.data_push, Array.toList_push]
    simp only [List.append_assoc, List.singleton_append]

private theorem foldl_requests_model (requests : List ByteArray) (acc : ByteArray) :
    (requests.foldl (fun acc request ↦
      (Hash.sha256 request).toBytes.foldl ByteArray.push acc) acc).data.toList =
      acc.data.toList ++ requestsHashPreimageModel requests := by
  induction requests generalizing acc with
  | nil => simp [requestsHashPreimageModel]
  | cons request requests ih =>
    rw [List.foldl_cons, ih, Bytes.foldl_eq, foldl_push_model]
    simp [requestsHashPreimageModel, List.append_assoc]

private theorem requestsHashPreimage_eq (requests : List ByteArray) :
    requestsHashPreimage requests =
      (Bytes.ofList (requestsHashPreimageModel requests)).toByteArray := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [requestsHashPreimage, foldl_requests_model, Bytes.toList_toByteArray,
    Bytes.toList_ofList]
  rfl

/-- SHA-256 of the ordered concatenation of all complete request SHA-256 digests;
pinned EELS `src/ethereum/forks/amsterdam/requests.py:307–328`. No request is
filtered or validated. The materialized outer preimage has 32 bytes per request;
this is not a source streaming-memory or total allocation-volume claim. Q46's
total SHA extension applies on all finite inputs. Source/FIPS agreement separately
requires `8 * request.size < 2^64` for every request and
`8 * (32 * requests.length) < 2^64`, together with host/API premises. -/
def computeRequestsHash (requests : List ByteArray) : Hash32 :=
  Hash32.ofBytes32 (Hash.sha256 (requestsHashPreimage requests))

/-- Complete ordered result equation: every byte of each inner digest enters the
outer SHA preimage, including empty requests and duplicates. `Hash32.ofBytes32`
preserves the entire outer digest under its public byte bridge. No FIPS/source
claim beyond Q46's domain or host-resource correspondence is implied. -/
theorem computeRequestsHash_eq (requests : List ByteArray) :
    computeRequestsHash requests = Hash32.ofBytes32 (Hash.sha256
      (Bytes.ofList ((requests.map (fun request ↦
        (Hash.sha256 request).toBytes.toList)).flatten)).toByteArray) := by
  rw [computeRequestsHash, requestsHashPreimage_eq]
  rfl

end STFSpec.Block
