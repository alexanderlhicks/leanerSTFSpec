/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block

/-!
# Small interpreted deposit extraction controls

Library `EthConformance`. Exact nullary constructor identities and whole successful
bytes are checked without adding instances to the public carrier.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §4.
-/

namespace STFSpec.Conformance.Block.DepositDataGuards
open STFSpec.Block STFSpec.Base

private def framed (bad : Nat) : ByteArray :=
  (Bytes.generate 576 fun i ↦ if i = bad then 255 else match i with
    | 31 => 160 | 62 => 1 | 94 => 1 | 95 => 64 | 126 => 1 | 127 => 128 | 158 => 2
    | 191 => 48 | 287 => 32 | 351 => 8 | 415 => 96 | 543 => 8 | _ => 0).toByteArray

private def code : Except DepositError ByteArray → Nat
  | .error .length => 0
  | .error .pubkeyOffset => 1
  | .error .wcOffset => 2
  | .error .amountOffset => 3
  | .error .signatureOffset => 4
  | .error .indexOffset => 5
  | .error .pubkeySize => 6
  | .error .wcSize => 7
  | .error .amountSize => 8
  | .error .signatureSize => 9
  | .error .indexSize => 10
  | .ok _ => 11

#guard code (extractDepositData ByteArray.empty) == 0
#guard code (extractDepositData (framed 31)) == 1
#guard code (extractDepositData (framed 63)) == 2
#guard code (extractDepositData (framed 95)) == 3
#guard code (extractDepositData (framed 127)) == 4
#guard code (extractDepositData (framed 159)) == 5
#guard code (extractDepositData (framed 191)) == 6
#guard code (extractDepositData (framed 287)) == 7
#guard code (extractDepositData (framed 351)) == 8
#guard code (extractDepositData (framed 415)) == 9
#guard code (extractDepositData (framed 543)) == 10
#guard match extractDepositData (framed 576) with
  | .ok bytes => bytes == (Bytes.generate 192 (fun _ ↦ 0)).toByteArray
  | .error _ => false

end STFSpec.Conformance.Block.DepositDataGuards
