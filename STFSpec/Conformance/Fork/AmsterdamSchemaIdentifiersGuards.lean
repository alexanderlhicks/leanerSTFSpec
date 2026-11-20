/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Fork

/-!
# Amsterdam input schema identifier controls

Library `EthConformance`. Private public-facade clients for all five exact types
and complete values, with interpreted whole-integer and whole-byte controls.
Spec guidance: `STFSpec/informal/modules/EthFork.md` §§3–4.
-/

open STFSpec.Fork.Amsterdam

private def forkType : UInt8 := STATELESS_INPUT_SCHEMA_FORK_INDEX
private def revisionType : UInt8 := STATELESS_INPUT_SCHEMA_REVISION
private def idType : UInt16 := STATELESS_INPUT_SCHEMA_ID
private def sizeType : Nat := STATELESS_INPUT_SCHEMA_ID_SIZE
private def bytesType : ByteArray := STATELESS_INPUT_SCHEMA_ID_BYTES

private theorem fork_value : STATELESS_INPUT_SCHEMA_FORK_INDEX = (0x15 : UInt8) := rfl
private theorem revision_value : STATELESS_INPUT_SCHEMA_REVISION = (1 : UInt8) := rfl
private theorem id_value : STATELESS_INPUT_SCHEMA_ID = (0x1501 : UInt16) := by decide
private theorem size_value : STATELESS_INPUT_SCHEMA_ID_SIZE = 2 := rfl
private theorem bytes_value : STATELESS_INPUT_SCHEMA_ID_BYTES = ⟨#[0x15, 0x01]⟩ := by decide
private theorem id_formula : STATELESS_INPUT_SCHEMA_ID =
    (STATELESS_INPUT_SCHEMA_FORK_INDEX.toUInt16 <<< 8) |||
      STATELESS_INPUT_SCHEMA_REVISION.toUInt16 := rfl
private theorem bytes_formula : STATELESS_INPUT_SCHEMA_ID_BYTES =
    ⟨#[(STATELESS_INPUT_SCHEMA_ID >>> 8).toUInt8, STATELESS_INPUT_SCHEMA_ID.toUInt8]⟩ := rfl
private theorem bytes_size :
    STATELESS_INPUT_SCHEMA_ID_BYTES.size = STATELESS_INPUT_SCHEMA_ID_SIZE := rfl

#guard STATELESS_INPUT_SCHEMA_FORK_INDEX.toNat == 21
#guard STATELESS_INPUT_SCHEMA_REVISION.toNat == 1
#guard STATELESS_INPUT_SCHEMA_ID.toNat == 5377
#guard STATELESS_INPUT_SCHEMA_ID_SIZE == 2
#guard STATELESS_INPUT_SCHEMA_ID_BYTES == ⟨#[0x15, 0x01]⟩
#guard STATELESS_INPUT_SCHEMA_ID_BYTES.size == 2

#check_failure STFSpec.Fork.Amsterdam.schema_bytes_eq
#check_failure STFSpec.Fork.Amsterdam.schema_bytes_size
