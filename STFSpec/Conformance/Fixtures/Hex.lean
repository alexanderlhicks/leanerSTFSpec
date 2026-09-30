/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Conformance.Fixtures.Types

/-!
# Fixture hex decoding

Total linear byte decoding for `EthConformance`, with exact `0x` prefix and no whitespace.
Spec guidance: `STFSpec/informal/modules/EthConformance.md`.
-/

namespace STFSpec.Conformance.Internal

private def nibble (byte : UInt8) : Option UInt8 :=
  if 48 ≤ byte && byte ≤ 57 then some (byte - 48)
  else if 65 ≤ byte && byte ≤ 70 then some (byte - 55)
  else if 97 ≤ byte && byte ≤ 102 then some (byte - 87)
  else none

/-- Internal strict hex decoder. Offsets in errors count UTF-8 bytes after `0x`. -/
def decodeHex (location text : String) : Except FixtureError ByteArray := do
  let bytes := text.toUTF8
  if bytes[0]? != some 48 || bytes[1]? != some 120 then
    throw (.hexPrefix location)
  if (bytes.size - 2) % 2 != 0 then
    throw (.oddHexLength location)
  let mut result := ByteArray.emptyWithCapacity ((bytes.size - 2) / 2)
  for i in [: (bytes.size - 2) / 2] do
    let offset := 2 + 2 * i
    let a ← match bytes[offset]? >>= nibble with
      | some n => pure n
      | none => throw (.nonHex location (2 * i))
    let b ← match bytes[offset + 1]? >>= nibble with
      | some n => pure n
      | none => throw (.nonHex location (2 * i + 1))
    result := result.push (16 * a + b)
  return result

end STFSpec.Conformance.Internal
