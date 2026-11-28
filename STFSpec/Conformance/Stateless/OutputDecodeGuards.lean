/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Conformance.Stateless.OutputDecode

/-!
# Host output decoder checks

Library `EthConformance`. See `STFSpec/informal/modules/EthConformance.md` §4.
-/

namespace STFSpec.Conformance.Stateless.OutputDecodeGuards

open STFSpec.Base STFSpec.Stateless

private def root : List UInt8 := (List.replicate 8 [0, 128, 255, 13]).flatten

private def decodesAs (wire rootBytes : List UInt8) (success : Bool) (chain schema : Nat) : Bool :=
  match deserializeStatelessOutput wire.toByteArray with
  | .error _ => false
  | .ok result =>
    result.newPayloadRequestRoot.toBytes.toList == rootBytes &&
    result.successfulValidation == success &&
    result.chainId.toNat == chain &&
    result.schemaId.toNat == schema &&
    (serializeStatelessOutput result).data.toList == wire

private def fails (wire : List UInt8) : Bool :=
  match deserializeStatelessOutput wire.toByteArray with
  | .ok _ => false
  | .error _ => true

#guard decodesAs (List.replicate 43 0) (List.replicate 32 0) false 0 0
#guard decodesAs (root ++ [1, 128, 112, 96, 80, 64, 48, 32, 16, 1, 21])
  root true 0x1020304050607080 0x1501
#guard decodesAs (root.reverse ++ [0] ++ List.replicate 8 255 ++ [52, 18])
  root.reverse false 0xffffffffffffffff 0x1234
#guard decodesAs (root ++ [1, 13] ++ List.replicate 9 0) root true 13 0

#guard fails []
#guard fails (root ++ List.replicate 10 0)
#guard fails (root ++ List.replicate 12 0)
#guard fails (List.replicate 4096 0)
#guard fails (root ++ [2] ++ List.replicate 10 0)
#guard fails (root ++ [255] ++ List.replicate 10 0)
#guard match deserializeStatelessOutput (root ++ [2] ++ List.replicate 11 0).toByteArray with
  | .error .length => true
  | _ => false

end STFSpec.Conformance.Stateless.OutputDecodeGuards
