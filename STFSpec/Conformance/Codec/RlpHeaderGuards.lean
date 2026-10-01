/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# RLP header deterministic guards

Library `EthConformance`. Header extents, bounds, cursor positions and diagnostic order;
full raw decoding and its canonicality checks remain separate.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–4.
-/

namespace STFSpec.Conformance.Codec.RlpHeaderGuards

open STFSpec.Base STFSpec.Codec STFSpec.Codec.Rlp

private def bytes (xs : List UInt8) : ByteArray := xs.toByteArray

private def sameResult : Except RlpError Nat → Except RlpError Nat → Bool
  | .ok n, .ok m => n == m
  | .error e, .error f => decide (e = f)
  | _, _ => false

#guard sameResult (decodeItemLength (bytes []) 0) (.error .empty)
#guard sameResult (decodeItemLength (bytes [0, 128, 255]) 3) (.error .empty)
#guard sameResult (decodeItemLength (bytes [184, 1]) (2 ^ 256 + 1)) (.error .empty)
#guard sameResult (decodeItemLength (bytes [0]) 0) (.ok 1)
#guard sameResult (decodeItemLength (bytes [127, 255]) 0) (.ok 1)
#guard sameResult (decodeItemLength (bytes [128]) 0) (.ok 1)
#guard sameResult (decodeItemLength (bytes [129, 5]) 0) (.ok 2)
#guard sameResult (decodeItemLength (bytes [183]) 0) (.ok 56)
#guard sameResult (decodeItemLength (bytes [184]) 0) (.error .truncated)
#guard sameResult (decodeItemLength (bytes [184, 1]) 0) (.ok 3)
#guard sameResult (decodeItemLength (bytes [184, 55]) 0) (.ok 57)
#guard sameResult (decodeItemLength (bytes [184, 56]) 0) (.ok 58)
#guard sameResult (decodeItemLength (bytes [184, 0]) 0)
  (.error (.nonCanonical "leading zero length"))
#guard sameResult (decodeItemLength (bytes [185, 0]) 0) (.error .truncated)
#guard sameResult (decodeItemLength (bytes [185, 0, 255]) 0)
  (.error (.nonCanonical "leading zero length"))
#guard sameResult (decodeItemLength (bytes [185, 1, 2]) 0) (.ok 261)
#guard sameResult (decodeItemLength (bytes [186, 2, 1, 3]) 0) (.ok 131335)
#guard sameResult (decodeItemLength (bytes [191, 255, 255, 255, 255, 255, 255, 255, 255]) 0)
  (.ok (2 ^ 64 + 8))
#guard sameResult (decodeItemLength (bytes [192, 255]) 0) (.ok 1)
#guard sameResult (decodeItemLength (bytes [193]) 0) (.ok 2)
#guard sameResult (decodeItemLength (bytes [247]) 0) (.ok 56)
#guard sameResult (decodeItemLength (bytes [248]) 0) (.error .truncated)
#guard sameResult (decodeItemLength (bytes [248, 5, 0]) 0) (.ok 7)
#guard sameResult (decodeItemLength (bytes [249, 0]) 0) (.error .truncated)
#guard sameResult (decodeItemLength (bytes [249, 0, 1]) 0)
  (.error (.nonCanonical "leading zero length"))
#guard sameResult (decodeItemLength (bytes [255, 255, 255, 255, 255, 255, 255, 255, 255]) 0)
  (.ok (2 ^ 64 + 8))
#guard sameResult (decodeItemLength (bytes [0, 249, 1, 2, 99, 98]) 1) (.ok 261)
#guard sameResult (decodeItemLength (bytes [185, 1, 2]) 0)
  (decodeItemLength (bytes [185, 1, 2, 99]) 0)

-- Finite all-tag sweep has independent numeric expected values for short tags.
#guard (List.range 256).all (fun n ↦
  let tag := UInt8.ofNat n
  let expected := if n < 128 then some 1 else if n ≤ 183 then some (1 + (n - 128)) else
    if n ≤ 191 then none else if n ≤ 247 then some (1 + (n - 192)) else none
  (decodeItemLength (bytes [tag]) 0).toOption == expected)

end STFSpec.Conformance.Codec.RlpHeaderGuards
