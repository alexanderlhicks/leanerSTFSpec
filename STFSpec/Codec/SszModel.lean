/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

/-!
# Raw SSZ model vocabulary

Library `EthCodec`. These inductives are their own raw models: construction imposes
no schema, width, length, typing or mask invariant. Descriptor families correspond
to `src/ethereum/utils/ssz.py:32–87,179–225,231–258`; value payloads abstract the
shapes in `src/ethereum/utils/ssz.py:263–325` at the pin. No Python class admission,
schema adapter, codec, root operation or diagnostic producer is supplied here.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §3/§5/§7.
-/

namespace STFSpec.Codec

/-- Raw SSZ type syntax, with unrestricted natural parameters and ordered children. -/
inductive SszType where
  /-- Unsigned integer descriptor; the raw byte width is unrestricted. -/
  | uint (bytes : Nat)
  /-- Boolean descriptor. -/
  | bool
  /-- Fixed byte-vector descriptor with a raw length. -/
  | byteVector (n : Nat)
  /-- Byte-list descriptor with a raw limit. -/
  | byteList (limit : Nat)
  /-- List descriptor with an element type and a raw limit. -/
  | list (elem : SszType) (limit : Nat)
  /-- Progressive list descriptor. -/
  | progressiveList (elem : SszType)
  /-- Progressive byte-list descriptor. -/
  | progressiveByteList
  /-- Ordinary container descriptor retaining field order. -/
  | container (fields : List SszType)
  /-- Progressive container descriptor retaining independent raw mask and fields. -/
  | progressiveContainer (activeFields : List Bool) (fields : List SszType)

/-- Raw SSZ values, without a typing judgment or source-object conversion. -/
inductive SszValue where
  /-- Natural payload, without an integer-width restriction. -/
  | uint (n : Nat)
  /-- Boolean payload. -/
  | bool (b : Bool)
  /-- Complete byte payload, including empty arrays and zero bytes. -/
  | bytes (b : ByteArray)
  /-- Ordered raw list children. -/
  | list (xs : List SszValue)
  /-- Ordered raw container fields. -/
  | container (xs : List SszValue)

/-- Nominal SSZ diagnostics from the interface guidance; no producer or priority is defined. -/
inductive SszError where
  /-- Length diagnostic tag. -/
  | length
  /-- Offset diagnostic tag. -/
  | offset
  /-- Limit diagnostic tag. -/
  | limit
  /-- Boolean-byte diagnostic tag. -/
  | boolByte
  /-- Trailing-data diagnostic tag. -/
  | trailing
  /-- Shape diagnostic tag. -/
  | shape

end STFSpec.Codec
