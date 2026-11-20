/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless

/-!
# Aggregate inverse implementation controls

Library `EthConformance`. Private interpreted controls cover complete ordered
collections and malformed outer, field and child shapes. These checks add no public
off-typing promise or byte-decoder policy.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Stateless.ExecutionRequestsSszControls

open STFSpec.Stateless STFSpec.Codec

private abbrev schema := ExecutionRequests.instSszSchema

private def bytes (n : Nat) : SszValue :=
  .bytes ((List.range n).map (fun i => UInt8.ofNat ((37 * i + 129) % 256))).toByteArray

private def replace {α : Type} (xs : List α) (i : Nat) (x : α) : List α :=
  xs.take i ++ [x] ++ xs.drop (i + 1)

private def deposit : List SszValue :=
  [bytes 48, bytes 32, .uint (2 ^ 64 - 1), bytes 96, .uint (2 ^ 64 - 1)]

private def withdrawal : List SszValue :=
  [bytes 20, bytes 48, .uint (2 ^ 64 - 1)]

private def consolidation : List SszValue :=
  [bytes 20, bytes 48, bytes 48]

private def builderDeposit : List SszValue :=
  [bytes 48, bytes 32, .uint (2 ^ 64 - 1), bytes 96]

private def builderExit : List SszValue :=
  [bytes 20, bytes 48]

private def baseline : List (List SszValue) :=
  [[.container deposit, .container deposit, .container deposit],
   [.container withdrawal, .container withdrawal, .container withdrawal],
   [.container consolidation, .container consolidation, .container consolidation],
   [.container builderDeposit, .container builderDeposit, .container builderDeposit],
   [.container builderExit, .container builderExit, .container builderExit]]

private def aggregate (fields : List (List SszValue)) : SszValue :=
  .container (fields.map SszValue.list)

private def reject (v : SszValue) : Bool := (schema.ofValue? v).isNone

private def badChild (field : Nat) (v : SszValue) : Bool :=
  [0, 1, 2].all (fun pos => reject (aggregate
    (replace baseline field (replace (baseline.getD field []) pos v))))

#guard (schema.ofValue? (aggregate baseline)).isSome
#guard (schema.ofValue? (.container [.list [], .list [], .list [], .list [], .list []])).isSome

#guard ([.uint 0, .bool false, .bytes ByteArray.empty, .list []] : List SszValue).all reject
#guard [0, 1, 2, 3, 4, 6].all (fun n => reject (.container (List.replicate n (.list []))))
#guard [0, 1, 2, 3, 4].all (fun i =>
  ([.uint 0, .bool false, .bytes ByteArray.empty, .container []] : List SszValue).all
    (fun v => reject (.container (replace (baseline.map SszValue.list) i v))))

#guard ([.uint 0, .bool false, .bytes ByteArray.empty, .list []] : List SszValue).all
  (badChild 0)
#guard (List.range 5).all (fun n => badChild 0 (.container (deposit.take n)))
#guard badChild 0 (.container (deposit ++ [.uint 0]))
#guard badChild 0 (.container (replace deposit 0 (bytes 47)))
#guard badChild 0 (.container (replace deposit 0 (bytes 49)))
#guard badChild 0 (.container (replace deposit 0 (.uint 0)))
#guard badChild 0 (.container (replace deposit 1 (bytes 31)))
#guard badChild 0 (.container (replace deposit 1 (bytes 33)))
#guard badChild 0 (.container (replace deposit 1 (.uint 0)))
#guard badChild 0 (.container (replace deposit 2 (.uint (2 ^ 64))))
#guard badChild 0 (.container (replace deposit 2 (.uint (2 ^ 64 + 1))))
#guard badChild 0 (.container (replace deposit 2 (bytes 8)))
#guard badChild 0 (.container (replace deposit 3 (bytes 95)))
#guard badChild 0 (.container (replace deposit 3 (bytes 97)))
#guard badChild 0 (.container (replace deposit 3 (.uint 0)))
#guard badChild 0 (.container (replace deposit 4 (.uint (2 ^ 64))))
#guard badChild 0 (.container (replace deposit 4 (.uint (2 ^ 64 + 1))))
#guard badChild 0 (.container (replace deposit 4 (bytes 8)))

#guard ([.uint 0, .bool false, .bytes ByteArray.empty, .list []] : List SszValue).all
  (badChild 1)
#guard (List.range 3).all (fun n => badChild 1 (.container (withdrawal.take n)))
#guard badChild 1 (.container (withdrawal ++ [.uint 0]))
#guard badChild 1 (.container (replace withdrawal 0 (bytes 19)))
#guard badChild 1 (.container (replace withdrawal 0 (bytes 21)))
#guard badChild 1 (.container (replace withdrawal 0 (.uint 0)))
#guard badChild 1 (.container (replace withdrawal 1 (bytes 47)))
#guard badChild 1 (.container (replace withdrawal 1 (bytes 49)))
#guard badChild 1 (.container (replace withdrawal 1 (.uint 0)))
#guard badChild 1 (.container (replace withdrawal 2 (.uint (2 ^ 64))))
#guard badChild 1 (.container (replace withdrawal 2 (.uint (2 ^ 64 + 1))))
#guard badChild 1 (.container (replace withdrawal 2 (bytes 8)))

#guard ([.uint 0, .bool false, .bytes ByteArray.empty, .list []] : List SszValue).all
  (badChild 2)
#guard (List.range 3).all (fun n => badChild 2 (.container (consolidation.take n)))
#guard badChild 2 (.container (consolidation ++ [.uint 0]))
#guard badChild 2 (.container (replace consolidation 0 (bytes 19)))
#guard badChild 2 (.container (replace consolidation 0 (bytes 21)))
#guard badChild 2 (.container (replace consolidation 0 (.uint 0)))
#guard badChild 2 (.container (replace consolidation 1 (bytes 47)))
#guard badChild 2 (.container (replace consolidation 1 (bytes 49)))
#guard badChild 2 (.container (replace consolidation 1 (.uint 0)))
#guard badChild 2 (.container (replace consolidation 2 (bytes 47)))
#guard badChild 2 (.container (replace consolidation 2 (bytes 49)))
#guard badChild 2 (.container (replace consolidation 2 (.uint 0)))

#guard ([.uint 0, .bool false, .bytes ByteArray.empty, .list []] : List SszValue).all
  (badChild 3)
#guard (List.range 4).all (fun n => badChild 3 (.container (builderDeposit.take n)))
#guard badChild 3 (.container (builderDeposit ++ [.uint 0]))
#guard badChild 3 (.container (replace builderDeposit 0 (bytes 47)))
#guard badChild 3 (.container (replace builderDeposit 0 (bytes 49)))
#guard badChild 3 (.container (replace builderDeposit 0 (.uint 0)))
#guard badChild 3 (.container (replace builderDeposit 1 (bytes 31)))
#guard badChild 3 (.container (replace builderDeposit 1 (bytes 33)))
#guard badChild 3 (.container (replace builderDeposit 1 (.uint 0)))
#guard badChild 3 (.container (replace builderDeposit 2 (.uint (2 ^ 64))))
#guard badChild 3 (.container (replace builderDeposit 2 (.uint (2 ^ 64 + 1))))
#guard badChild 3 (.container (replace builderDeposit 2 (bytes 8)))
#guard badChild 3 (.container (replace builderDeposit 3 (bytes 95)))
#guard badChild 3 (.container (replace builderDeposit 3 (bytes 97)))
#guard badChild 3 (.container (replace builderDeposit 3 (.uint 0)))

#guard ([.uint 0, .bool false, .bytes ByteArray.empty, .list []] : List SszValue).all
  (badChild 4)
#guard (List.range 2).all (fun n => badChild 4 (.container (builderExit.take n)))
#guard badChild 4 (.container (builderExit ++ [.uint 0]))
#guard badChild 4 (.container (replace builderExit 0 (bytes 19)))
#guard badChild 4 (.container (replace builderExit 0 (bytes 21)))
#guard badChild 4 (.container (replace builderExit 0 (.uint 0)))
#guard badChild 4 (.container (replace builderExit 1 (bytes 47)))
#guard badChild 4 (.container (replace builderExit 1 (bytes 49)))
#guard badChild 4 (.container (replace builderExit 1 (.uint 0)))

#guard reject (.container [
  .list [.container deposit, .uint 0, .container deposit],
  .list [.container withdrawal, .container []],
  .list [.bool false, .container consolidation],
  .list [.container builderDeposit, .bytes ByteArray.empty],
  .list [.container builderExit, .list []]])

end STFSpec.Conformance.Stateless.ExecutionRequestsSszControls
