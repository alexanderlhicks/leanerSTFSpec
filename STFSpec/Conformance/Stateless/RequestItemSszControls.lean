/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless

/-!
# Request-item adapter completion controls

Library `EthConformance`. Private interpreted controls exercise exact shape, checked
byte widths and unsigned ranges. These facts specify no public decoder diagnostic.
Arbitrary correct-width cryptographic contents remain accepted.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Stateless.RequestItemSszControls

open STFSpec.Stateless STFSpec.Codec

private def zeros (n : Nat) : ByteArray := (List.replicate n (0 : UInt8)).toByteArray

private def indexed (n : Nat) : ByteArray :=
  ((List.range n).map (fun i ↦ UInt8.ofNat (i + 1))).toByteArray

namespace DepositRequest

private abbrev schema := STFSpec.Stateless.DepositRequest.instSszSchema

private def ordinary : List SszValue := [.bytes (zeros 48), .bytes (zeros 32), .uint 0,
  .bytes (zeros 96), .uint 0]

#guard (schema.ofValue? (.uint 0)).isNone
#guard (schema.ofValue? (.bool false)).isNone
#guard (schema.ofValue? (.bytes (zeros 0))).isNone
#guard (schema.ofValue? (.list [])).isNone
#guard (schema.ofValue? (.container [])).isNone
#guard (schema.ofValue? (.container ordinary.tail)).isNone
#guard (schema.ofValue? (.container (ordinary ++ [.uint 0]))).isNone
#guard (schema.ofValue? (.container (ordinary ++ [.bytes (zeros 96)]))).isNone

-- pubkey
#guard (schema.ofValue? (.container [.bool false, .bytes (zeros 32), .uint 0, .bytes (zeros 96),
  .uint 0])).isNone
#guard (schema.ofValue? (.container [.list [], .bytes (zeros 32), .uint 0, .bytes (zeros 96),
  .uint 0])).isNone
#guard (schema.ofValue? (.container [.container [], .bytes (zeros 32), .uint 0,
  .bytes (zeros 96), .uint 0])).isNone
#guard (schema.ofValue? (.container [.uint 0, .bytes (zeros 32), .uint 0, .bytes (zeros 96),
  .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 47), .bytes (zeros 32), .uint 0,
  .bytes (zeros 96), .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (indexed 47), .bytes (zeros 32), .uint 0,
  .bytes (zeros 96), .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 49), .bytes (zeros 32), .uint 0,
  .bytes (zeros 96), .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (indexed 49), .bytes (zeros 32), .uint 0,
  .bytes (zeros 96), .uint 0])).isNone

-- withdrawalCredentials
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bool false, .uint 0, .bytes (zeros 96),
  .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .list [], .uint 0, .bytes (zeros 96),
  .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .container [], .uint 0,
  .bytes (zeros 96), .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .uint 0, .uint 0, .bytes (zeros 96),
  .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 31), .uint 0,
  .bytes (zeros 96), .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (indexed 31), .uint 0,
  .bytes (zeros 96), .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 33), .uint 0,
  .bytes (zeros 96), .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (indexed 33), .uint 0,
  .bytes (zeros 96), .uint 0])).isNone

-- amount
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .bool false,
  .bytes (zeros 96), .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .list [],
  .bytes (zeros 96), .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .container [],
  .bytes (zeros 96), .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .bytes (zeros 8),
  .bytes (zeros 96), .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32),
  .uint 18446744073709551616, .bytes (zeros 96), .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32),
  .uint 18446744073709551617, .bytes (zeros 96), .uint 0])).isNone

-- signature
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .uint 0, .bool false,
  .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .uint 0, .list [],
  .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .uint 0,
  .container [], .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .uint 0, .uint 0,
  .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .uint 0,
  .bytes (zeros 95), .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .uint 0,
  .bytes (indexed 95), .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .uint 0,
  .bytes (zeros 97), .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .uint 0,
  .bytes (indexed 97), .uint 0])).isNone

-- index
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .uint 0,
  .bytes (zeros 96), .bool false])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .uint 0,
  .bytes (zeros 96), .list []])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .uint 0,
  .bytes (zeros 96), .container []])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .uint 0,
  .bytes (zeros 96), .bytes (zeros 8)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .uint 0,
  .bytes (zeros 96), .uint 18446744073709551616])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .uint 0,
  .bytes (zeros 96), .uint 18446744073709551617])).isNone

-- Exact widths retain arbitrary cryptographic bytes and maximum unsigned values.
#guard (schema.ofValue? (.container [.bytes ((List.replicate 48 (255 : UInt8)).toByteArray),
  .bytes ((List.replicate 32 (255 : UInt8)).toByteArray), .uint 18446744073709551615,
  .bytes ((List.replicate 96 (255 : UInt8)).toByteArray), .uint 18446744073709551615])).isSome
#guard (schema.ofValue? (.container [.bool false, .bytes (zeros 32), .uint 0, .bytes (zeros 96),
  .list []])).isNone

end DepositRequest

namespace WithdrawalRequest

private abbrev schema := STFSpec.Stateless.WithdrawalRequest.instSszSchema

private def ordinary : List SszValue := [.bytes (zeros 20), .bytes (zeros 48), .uint 0]

#guard (schema.ofValue? (.uint 0)).isNone
#guard (schema.ofValue? (.bool false)).isNone
#guard (schema.ofValue? (.bytes (zeros 0))).isNone
#guard (schema.ofValue? (.list [])).isNone
#guard (schema.ofValue? (.container [])).isNone
#guard (schema.ofValue? (.container ordinary.tail)).isNone
#guard (schema.ofValue? (.container (ordinary ++ [.uint 0]))).isNone
#guard (schema.ofValue? (.container (ordinary ++ [.bytes (zeros 96)]))).isNone

-- sourceAddress
#guard (schema.ofValue? (.container [.bool false, .bytes (zeros 48), .uint 0])).isNone
#guard (schema.ofValue? (.container [.list [], .bytes (zeros 48), .uint 0])).isNone
#guard (schema.ofValue? (.container [.container [], .bytes (zeros 48), .uint 0])).isNone
#guard (schema.ofValue? (.container [.uint 0, .bytes (zeros 48), .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 19), .bytes (zeros 48), .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (indexed 19), .bytes (zeros 48), .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 21), .bytes (zeros 48), .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (indexed 21), .bytes (zeros 48), .uint 0])).isNone

-- validatorPubkey
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bool false, .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .list [], .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .container [], .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .uint 0, .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bytes (zeros 47), .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bytes (indexed 47), .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bytes (zeros 49), .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bytes (indexed 49), .uint 0])).isNone

-- amount
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bytes (zeros 48), .bool false])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bytes (zeros 48), .list []])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bytes (zeros 48), .container []])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bytes (zeros 48),
  .bytes (zeros 8)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bytes (zeros 48),
  .uint 18446744073709551616])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bytes (zeros 48),
  .uint 18446744073709551617])).isNone

-- Exact widths retain arbitrary cryptographic bytes and maximum unsigned values.
#guard (schema.ofValue? (.container [.bytes ((List.replicate 20 (255 : UInt8)).toByteArray),
  .bytes ((List.replicate 48 (255 : UInt8)).toByteArray), .uint 18446744073709551615])).isSome
#guard (schema.ofValue? (.container [.bool false, .bytes (zeros 48), .list []])).isNone

end WithdrawalRequest

namespace ConsolidationRequest

private abbrev schema := STFSpec.Stateless.ConsolidationRequest.instSszSchema

private def ordinary : List SszValue := [.bytes (zeros 20), .bytes (zeros 48), .bytes (zeros 48)]

#guard (schema.ofValue? (.uint 0)).isNone
#guard (schema.ofValue? (.bool false)).isNone
#guard (schema.ofValue? (.bytes (zeros 0))).isNone
#guard (schema.ofValue? (.list [])).isNone
#guard (schema.ofValue? (.container [])).isNone
#guard (schema.ofValue? (.container ordinary.tail)).isNone
#guard (schema.ofValue? (.container (ordinary ++ [.uint 0]))).isNone
#guard (schema.ofValue? (.container (ordinary ++ [.bytes (zeros 96)]))).isNone

-- sourceAddress
#guard (schema.ofValue? (.container [.bool false, .bytes (zeros 48), .bytes (zeros 48)])).isNone
#guard (schema.ofValue? (.container [.list [], .bytes (zeros 48), .bytes (zeros 48)])).isNone
#guard (schema.ofValue? (.container [.container [], .bytes (zeros 48), .bytes (zeros 48)])).isNone
#guard (schema.ofValue? (.container [.uint 0, .bytes (zeros 48), .bytes (zeros 48)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 19), .bytes (zeros 48),
  .bytes (zeros 48)])).isNone
#guard (schema.ofValue? (.container [.bytes (indexed 19), .bytes (zeros 48),
  .bytes (zeros 48)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 21), .bytes (zeros 48),
  .bytes (zeros 48)])).isNone
#guard (schema.ofValue? (.container [.bytes (indexed 21), .bytes (zeros 48),
  .bytes (zeros 48)])).isNone

-- sourcePubkey
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bool false, .bytes (zeros 48)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .list [], .bytes (zeros 48)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .container [], .bytes (zeros 48)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .uint 0, .bytes (zeros 48)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bytes (zeros 47),
  .bytes (zeros 48)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bytes (indexed 47),
  .bytes (zeros 48)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bytes (zeros 49),
  .bytes (zeros 48)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bytes (indexed 49),
  .bytes (zeros 48)])).isNone

-- targetPubkey
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bytes (zeros 48), .bool false])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bytes (zeros 48), .list []])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bytes (zeros 48), .container []])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bytes (zeros 48), .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bytes (zeros 48),
  .bytes (zeros 47)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bytes (zeros 48),
  .bytes (indexed 47)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bytes (zeros 48),
  .bytes (zeros 49)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bytes (zeros 48),
  .bytes (indexed 49)])).isNone

-- Exact widths retain arbitrary cryptographic bytes and maximum unsigned values.
#guard (schema.ofValue? (.container [.bytes ((List.replicate 20 (255 : UInt8)).toByteArray),
  .bytes ((List.replicate 48 (255 : UInt8)).toByteArray),
  .bytes ((List.replicate 48 (255 : UInt8)).toByteArray)])).isSome
#guard (schema.ofValue? (.container [.bool false, .bytes (zeros 48), .list []])).isNone

end ConsolidationRequest

namespace BuilderDepositRequest

private abbrev schema := STFSpec.Stateless.BuilderDepositRequest.instSszSchema

private def ordinary : List SszValue := [.bytes (zeros 48), .bytes (zeros 32), .uint 0,
  .bytes (zeros 96)]

#guard (schema.ofValue? (.uint 0)).isNone
#guard (schema.ofValue? (.bool false)).isNone
#guard (schema.ofValue? (.bytes (zeros 0))).isNone
#guard (schema.ofValue? (.list [])).isNone
#guard (schema.ofValue? (.container [])).isNone
#guard (schema.ofValue? (.container ordinary.tail)).isNone
#guard (schema.ofValue? (.container (ordinary ++ [.uint 0]))).isNone
#guard (schema.ofValue? (.container (ordinary ++ [.bytes (zeros 96)]))).isNone

-- pubkey
#guard (schema.ofValue? (.container [.bool false, .bytes (zeros 32), .uint 0,
  .bytes (zeros 96)])).isNone
#guard (schema.ofValue? (.container [.list [], .bytes (zeros 32), .uint 0,
  .bytes (zeros 96)])).isNone
#guard (schema.ofValue? (.container [.container [], .bytes (zeros 32), .uint 0,
  .bytes (zeros 96)])).isNone
#guard (schema.ofValue? (.container [.uint 0, .bytes (zeros 32), .uint 0,
  .bytes (zeros 96)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 47), .bytes (zeros 32), .uint 0,
  .bytes (zeros 96)])).isNone
#guard (schema.ofValue? (.container [.bytes (indexed 47), .bytes (zeros 32), .uint 0,
  .bytes (zeros 96)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 49), .bytes (zeros 32), .uint 0,
  .bytes (zeros 96)])).isNone
#guard (schema.ofValue? (.container [.bytes (indexed 49), .bytes (zeros 32), .uint 0,
  .bytes (zeros 96)])).isNone

-- withdrawalCredentials
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bool false, .uint 0,
  .bytes (zeros 96)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .list [], .uint 0,
  .bytes (zeros 96)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .container [], .uint 0,
  .bytes (zeros 96)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .uint 0, .uint 0,
  .bytes (zeros 96)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 31), .uint 0,
  .bytes (zeros 96)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (indexed 31), .uint 0,
  .bytes (zeros 96)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 33), .uint 0,
  .bytes (zeros 96)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (indexed 33), .uint 0,
  .bytes (zeros 96)])).isNone

-- amount
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .bool false,
  .bytes (zeros 96)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .list [],
  .bytes (zeros 96)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .container [],
  .bytes (zeros 96)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .bytes (zeros 8),
  .bytes (zeros 96)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32),
  .uint 18446744073709551616, .bytes (zeros 96)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32),
  .uint 18446744073709551617, .bytes (zeros 96)])).isNone

-- signature
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .uint 0,
  .bool false])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .uint 0,
  .list []])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .uint 0,
  .container []])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .uint 0,
  .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .uint 0,
  .bytes (zeros 95)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .uint 0,
  .bytes (indexed 95)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .uint 0,
  .bytes (zeros 97)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 48), .bytes (zeros 32), .uint 0,
  .bytes (indexed 97)])).isNone

-- Exact widths retain arbitrary cryptographic bytes and maximum unsigned values.
#guard (schema.ofValue? (.container [.bytes ((List.replicate 48 (255 : UInt8)).toByteArray),
  .bytes ((List.replicate 32 (255 : UInt8)).toByteArray), .uint 18446744073709551615,
  .bytes ((List.replicate 96 (255 : UInt8)).toByteArray)])).isSome
#guard (schema.ofValue? (.container [.bool false, .bytes (zeros 32), .uint 0, .list []])).isNone

end BuilderDepositRequest

namespace BuilderExitRequest

private abbrev schema := STFSpec.Stateless.BuilderExitRequest.instSszSchema

private def ordinary : List SszValue := [.bytes (zeros 20), .bytes (zeros 48)]

#guard (schema.ofValue? (.uint 0)).isNone
#guard (schema.ofValue? (.bool false)).isNone
#guard (schema.ofValue? (.bytes (zeros 0))).isNone
#guard (schema.ofValue? (.list [])).isNone
#guard (schema.ofValue? (.container [])).isNone
#guard (schema.ofValue? (.container ordinary.tail)).isNone
#guard (schema.ofValue? (.container (ordinary ++ [.uint 0]))).isNone
#guard (schema.ofValue? (.container (ordinary ++ [.bytes (zeros 96)]))).isNone

-- sourceAddress
#guard (schema.ofValue? (.container [.bool false, .bytes (zeros 48)])).isNone
#guard (schema.ofValue? (.container [.list [], .bytes (zeros 48)])).isNone
#guard (schema.ofValue? (.container [.container [], .bytes (zeros 48)])).isNone
#guard (schema.ofValue? (.container [.uint 0, .bytes (zeros 48)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 19), .bytes (zeros 48)])).isNone
#guard (schema.ofValue? (.container [.bytes (indexed 19), .bytes (zeros 48)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 21), .bytes (zeros 48)])).isNone
#guard (schema.ofValue? (.container [.bytes (indexed 21), .bytes (zeros 48)])).isNone

-- pubkey
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bool false])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .list []])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .container []])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .uint 0])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bytes (zeros 47)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bytes (indexed 47)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bytes (zeros 49)])).isNone
#guard (schema.ofValue? (.container [.bytes (zeros 20), .bytes (indexed 49)])).isNone

-- Exact widths retain arbitrary cryptographic bytes and maximum unsigned values.
#guard (schema.ofValue? (.container [.bytes ((List.replicate 20 (255 : UInt8)).toByteArray),
  .bytes ((List.replicate 48 (255 : UInt8)).toByteArray)])).isSome
#guard (schema.ofValue? (.container [.bool false, .list []])).isNone

end BuilderExitRequest

end STFSpec.Conformance.Stateless.RequestItemSszControls
