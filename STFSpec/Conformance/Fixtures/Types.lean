/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

/-!
# Guest fixture records

Identity and byte-record types for `EthConformance`. These records do not
classify or execute a guest. `FixtureError` describes fixture extraction failures only.
Spec guidance: `STFSpec/informal/modules/EthConformance.md`.
-/

namespace STFSpec.Conformance

/-- Archive-relative file, test identifier, zero-based block position and fixture hash. -/
structure FixtureId where
  file : String
  testId : String
  blockIndex : Nat
  infoHash : String
  deriving BEq, Repr, DecidableEq

/-- Guest input and expected output read directly from a block's paired byte fields. -/
structure GuestRecord where
  id : FixtureId
  input : ByteArray
  expected : ByteArray
  deriving BEq

/-- Named fixture failures; these never stand for a guest failure or `InternalError`. -/
inductive FixtureError where
  | jsonSyntax (message : String)
  | expectedObject (location : String)
  | missingField (location field : String)
  | expectedArray (location : String)
  | expectedString (location : String)
  | hexPrefix (location : String)
  | oddHexLength (location : String)
  | nonHex (location : String) (offset : Nat)
  | unpairedGuestFields (location : String)
  | outputLength (location : String) (actual : Nat)
  | infoHashLength (location : String) (actual : Nat)
  | unsupportedFile (file : String)
  | fixtureFormat (location expected actual : String)
  | conflictingShape (location : String)
  | duplicateIdentity (id : FixtureId)
  deriving BEq, Repr, DecidableEq

end STFSpec.Conformance
