/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Raw SSZ aggregate controls

Library `EthConformance`. Four bounded controls observe whole raw envelopes,
including unsupported widths, zero limits, independent masks, all bytes, duplicate
children and nested order. The private fixed-context consumers are neither codecs
nor schema validators and impose no public construction restriction.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §4/§7.
-/

namespace STFSpec.Conformance.Codec.SszModelGuards

open STFSpec.Codec

private def rawFields : List SszType :=
  [.uint 3, .bool, .byteVector 0, .byteList 0, .list (.uint (2 ^ 256 + 1)) 0,
    .progressiveList (.byteList 13), .progressiveByteList, .container [],
    .progressiveContainer [true, false] [.uint 0, .byteVector 7]]

private def observesFields : SszType → Bool
  | .container [.uint w, .bool, .byteVector n, .byteList limit,
      .list (.uint innerWidth) innerLimit, .progressiveList (.byteList innerBytes),
      .progressiveByteList, .container [],
      .progressiveContainer mask [.uint zeroWidth, .byteVector finalWidth]] =>
    w == 3 && n == 0 && limit == 0 && innerWidth == 2 ^ 256 + 1 && innerLimit == 0 &&
      innerBytes == 13 && mask == [true, false] && zeroWidth == 0 && finalWidth == 7
  | _ => false

#guard observesFields (.container rawFields)

private def observesLongMask : SszType → Bool
  | .progressiveContainer mask [] => mask == List.replicate 257 false
  | _ => false

#guard observesLongMask (.progressiveContainer (List.replicate 257 false) [])

private def observesValue : SszValue → Bool
  | .container [.uint n, .bool flag, .bytes bytes,
      .list [.container [], .list [], .bytes empty, .uint first, .uint second],
      .container [.bool last]] =>
    n == 2 ^ 256 + 17 && flag == false && bytes.data.toList == [0, 255, 0, 128] &&
      empty.data.toList == [] && first == 7 && second == 7 && last == true
  | _ => false

#guard observesValue (.container [
  .uint (2 ^ 256 + 17), .bool false, .bytes ⟨#[0, 255, 0, 128]⟩,
  .list [.container [], .list [], .bytes ByteArray.empty, .uint 7, .uint 7],
  .container [.bool true]])

#guard !observesValue (.container [
  .uint (2 ^ 256 + 17), .bool false, .bytes ⟨#[0, 255, 0, 128]⟩,
  .list [.list [], .container [], .bytes ByteArray.empty, .uint 7, .uint 7],
  .container [.bool true]])

end STFSpec.Conformance.Codec.SszModelGuards
