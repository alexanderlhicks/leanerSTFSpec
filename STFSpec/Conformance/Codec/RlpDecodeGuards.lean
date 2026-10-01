/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Raw RLP decoder regressions

Library `EthConformance`. Exact byte/list trees and ordered diagnostic failures
for locked ethereum-rlp 0.1.6 `rlp.py:143–162,385–543`.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–4.
-/

namespace STFSpec.Conformance.Codec.RlpDecodeGuards

open STFSpec.Codec STFSpec.Codec.Rlp

-- No nested instances are derived. Compare the complete constructor tree.
mutual
  private def sameItem : RlpItem → RlpItem → Bool
    | .bytes a, .bytes b => decide (a = b)
    | .list xs, .list ys => sameItems xs ys
    | _, _ => false
  private def sameItems : List RlpItem → List RlpItem → Bool
    | [], [] => true
    | x :: xs, y :: ys => sameItem x y && sameItems xs ys
    | _, _ => false
end

private def sameResult : Except RlpError RlpItem → Except RlpError RlpItem → Bool
  | .ok x, .ok y => sameItem x y
  | .error e, .error f => decide (e = f)
  | _, _ => false

private def bytes (xs : List UInt8) : ByteArray := xs.toByteArray

#guard sameResult (decode (bytes [])) (.error .empty)
#guard sameResult (decode (bytes [0])) (.ok (.bytes (bytes [0])))
#guard sameResult (decode (bytes [127])) (.ok (.bytes (bytes [127])))
#guard sameResult (decode (bytes [128])) (.ok (.bytes (bytes [])))
#guard sameResult (decode (bytes [129])) (.error .truncated)
#guard sameResult (decode (bytes [255])) (.error .truncated)
#guard sameResult (decode (bytes [129, 128])) (.ok (.bytes (bytes [128])))
#guard sameResult (decode (bytes [129, 5])) (.error (.nonCanonical "prefixed single byte"))
#guard sameResult (decode (bytes [5, 6])) (.error (.nonCanonical "negative length"))
#guard sameResult (decode (bytes [129, 5, 0])) (.error .trailing)
#guard sameResult (decode (bytes [130, 5])) (.error .truncated)
#guard sameResult (decode (bytes [128, 0])) (.error .trailing)
#guard sameResult (decode (bytes [192])) (.ok (.list []))
#guard sameResult (decode (bytes [193])) (.error .truncated)
#guard sameResult (decode (bytes [192, 0])) (.error .trailing)
#guard sameResult (decode (bytes [194, 130, 0])) (.error .truncated)
#guard sameResult (decode (bytes [193, 129])) (.error .truncated)
#guard sameResult (decode (bytes [194, 129, 0])) (.error (.nonCanonical "prefixed single byte"))
#guard sameResult (decode (bytes [195, 129, 0])) (.error .truncated)
#guard sameResult (decode (bytes [194, 129, 0, 0])) (.error .trailing)
#guard sameResult (decode (bytes [196, 129, 0, 129, 0]))
  (.error (.nonCanonical "prefixed single byte"))
#guard sameResult (decode (bytes [196, 0, 129, 0, 129]))
  (.error (.nonCanonical "prefixed single byte"))
#guard sameResult (decode (bytes [185, 0])) (.error .truncated)
#guard sameResult (decode (bytes [185, 0, 64])) (.error (.nonCanonical "leading zero length"))
#guard sameResult (decode (bytes [184, 5]))
  (.error (.nonCanonical "long form for short payload"))
#guard sameResult (decode (bytes [248, 5]))
  (.error (.nonCanonical "long form for short payload"))
#guard sameResult (decode (bytes [249, 0])) (.error .truncated)
#guard sameResult (decode (bytes [249, 0, 64])) (.error (.nonCanonical "leading zero length"))
#guard sameResult (decode (bytes [195, 185, 0, 56]))
  (.error (.nonCanonical "leading zero length"))
-- Header permissiveness determines child-extent-before-child-canonicality priority.
#guard sameResult (decode (bytes [194, 184, 5])) (.error .truncated)
#guard sameResult (decode (bytes [199, 184, 5, 0, 0, 0, 0, 0]))
  (.error (.nonCanonical "long form for short payload"))
#guard sameResult (decode (bytes ([191] ++ List.replicate 8 255))) (.error .truncated)
#guard sameResult (decode (bytes ([255] ++ List.replicate 8 255))) (.error .truncated)
#guard sameResult (decode (bytes [196, 128, 192, 129, 128]))
  (.ok (.list [.bytes (bytes []), .list [], .bytes (bytes [128])]))
#guard sameResult (decode (bytes [196, 193, 192, 0, 128]))
  (.ok (.list [.list [.list []], .bytes (bytes [0]), .bytes (bytes [])]))
#guard sameResult (decode (bytes [131, 0, 1, 0])) (.ok (.bytes (bytes [0, 1, 0])))
#guard sameResult (decode (bytes ([183] ++ List.replicate 55 128)))
  (.ok (.bytes (bytes (List.replicate 55 128))))
#guard sameResult (decode (bytes ([184, 56] ++ List.replicate 56 128)))
  (.ok (.bytes (bytes (List.replicate 56 128))))
#guard sameResult (decode (bytes ([184, 255] ++ List.replicate 255 0)))
  (.ok (.bytes (bytes (List.replicate 255 0))))
#guard sameResult (decode (bytes ([185, 1, 0] ++ List.replicate 256 1)))
  (.ok (.bytes (bytes (List.replicate 256 1))))
#guard sameResult (decode (bytes ([247] ++ List.replicate 55 128)))
  (.ok (.list (List.replicate 55 (.bytes (bytes [])))))
#guard sameResult (decode (bytes ([248, 56] ++ List.replicate 56 128)))
  (.ok (.list (List.replicate 56 (.bytes (bytes [])))))
#guard sameResult (decode (bytes ([184, 56] ++ List.replicate 56 128 ++ [0]))) (.error .trailing)
#guard sameResult (decode (bytes ([248, 56] ++ List.replicate 56 128 ++ [0]))) (.error .trailing)

end STFSpec.Conformance.Codec.RlpDecodeGuards
