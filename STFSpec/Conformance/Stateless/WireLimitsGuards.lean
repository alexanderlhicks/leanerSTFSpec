/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Fork
import STFSpec.Stateless

/-!
# Stateless input wire-limit alias controls

Library `EthConformance`. Private facade clients for exact types, values and aliases.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3–4.
-/

open STFSpec STFSpec.Stateless

private def headerCountType : Nat := maxWitnessHeaders
private def codeBytesType : Nat := maxBytesPerCode
private def headerBytesType : Nat := maxBytesPerHeader
private def nodeBytesType : Nat := maxBytesPerWitnessNode
private def extraDataBytesType : Nat := maxExtraDataBytes

private theorem header_count_alias :
    maxWitnessHeaders = Fork.Amsterdam.MAX_WITNESS_HEADERS := rfl
private theorem code_bytes_alias : maxBytesPerCode = Fork.Amsterdam.MAX_BYTES_PER_CODE := rfl
private theorem header_bytes_alias : maxBytesPerHeader = Fork.Amsterdam.MAX_BYTES_PER_HEADER := rfl
private theorem node_bytes_alias :
    maxBytesPerWitnessNode = Fork.Amsterdam.MAX_BYTES_PER_WITNESS_NODE := rfl
private theorem extra_data_bytes_alias :
    maxExtraDataBytes = Fork.Amsterdam.MAX_EXTRA_DATA_BYTES := rfl

private theorem header_count_value : maxWitnessHeaders = 256 := rfl
private theorem code_bytes_value : maxBytesPerCode = 65536 := rfl
private theorem header_bytes_value : maxBytesPerHeader = 1024 := rfl
private theorem node_bytes_value : maxBytesPerWitnessNode = 1024 := rfl
private theorem extra_data_bytes_value : maxExtraDataBytes = 32 := rfl

#guard maxWitnessHeaders == 256
#guard maxBytesPerCode == 65536
#guard maxBytesPerHeader == 1024
#guard maxBytesPerWitnessNode == 1024
#guard maxExtraDataBytes == 32
