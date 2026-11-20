/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Fork
import STFSpec.Stateless

/-!
# Stateless input schema identifier controls

Library `EthConformance`. Private public-facade clients for the nominal selector,
transparent aliases, complete values and selected coherence, without private helper access.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3–4.
-/

open STFSpec STFSpec.Stateless

private def forkType : ProtocolFork := schemaForkIndex
private def revisionType : UInt8 := schemaRevision
private def idType : UInt16 := schemaId
private def sizeType : Nat := schemaIdSize
private def bytesType : ByteArray := schemaIdBytes

private theorem fork_value : schemaForkIndex = ProtocolFork.amsterdam := rfl
private theorem revision_value : schemaRevision = (1 : UInt8) := rfl
private theorem id_value : schemaId = (0x1501 : UInt16) := by decide
private theorem size_value : schemaIdSize = 2 := rfl
private theorem bytes_value : schemaIdBytes = ⟨#[0x15, 0x01]⟩ := by decide
private theorem revision_alias :
    schemaRevision = Fork.Amsterdam.STATELESS_INPUT_SCHEMA_REVISION := rfl
private theorem id_alias : schemaId = Fork.Amsterdam.STATELESS_INPUT_SCHEMA_ID := rfl
private theorem size_alias : schemaIdSize = Fork.Amsterdam.STATELESS_INPUT_SCHEMA_ID_SIZE := rfl
private theorem bytes_alias : schemaIdBytes = Fork.Amsterdam.STATELESS_INPUT_SCHEMA_ID_BYTES := rfl
private theorem fork_coherence :
    schemaForkIndex.toIndex = Fork.Amsterdam.STATELESS_INPUT_SCHEMA_FORK_INDEX := rfl
private theorem id_coherence : schemaId =
    (schemaForkIndex.toIndex.toUInt16 <<< 8) ||| schemaRevision.toUInt16 := rfl
private theorem bytes_coherence :
    schemaIdBytes = ⟨#[schemaForkIndex.toIndex, schemaRevision]⟩ := by decide
private theorem bytes_size : schemaIdBytes.size = schemaIdSize := rfl

#guard match schemaForkIndex with | .amsterdam => true | _ => false
#guard schemaForkIndex.toIndex.toNat == 21
#guard schemaRevision.toNat == 1
#guard schemaId.toNat == 5377
#guard schemaIdSize == 2
#guard schemaIdBytes == ⟨#[0x15, 0x01]⟩
#guard schemaIdBytes.size == 2

#check_failure STFSpec.Stateless.supportedForks
#check_failure STFSpec.Stateless.pick
#check_failure STFSpec.Stateless.pick_toIndex
#check_failure STFSpec.Stateless.pick_proof_irrelevance
#check_failure STFSpec.Stateless.selected_bound
#check_failure STFSpec.Stateless.selected_coherence
#check_failure STFSpec.Stateless.id_coherence
#check_failure STFSpec.Stateless.bytes_coherence
#check_failure STFSpec.Stateless.bytes_size
