/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Fork

/-!
# Amsterdam input wire-limit controls

Library `EthConformance`. Private exact-type and complete-value facade clients.
Spec guidance: `STFSpec/informal/modules/EthFork.md` §§3–4.
-/

open STFSpec.Fork.Amsterdam

private def headerCountType : Nat := MAX_WITNESS_HEADERS
private def codeBytesType : Nat := MAX_BYTES_PER_CODE
private def headerBytesType : Nat := MAX_BYTES_PER_HEADER
private def nodeBytesType : Nat := MAX_BYTES_PER_WITNESS_NODE
private def extraDataBytesType : Nat := MAX_EXTRA_DATA_BYTES

private theorem header_count_value : MAX_WITNESS_HEADERS = 256 := rfl
private theorem code_bytes_value : MAX_BYTES_PER_CODE = 65536 := rfl
private theorem header_bytes_value : MAX_BYTES_PER_HEADER = 1024 := rfl
private theorem node_bytes_value : MAX_BYTES_PER_WITNESS_NODE = 1024 := rfl
private theorem extra_data_bytes_value : MAX_EXTRA_DATA_BYTES = 32 := rfl

#guard MAX_WITNESS_HEADERS == 256
#guard MAX_BYTES_PER_CODE == 65536
#guard MAX_BYTES_PER_HEADER == 1024
#guard MAX_BYTES_PER_WITNESS_NODE == 1024
#guard MAX_EXTRA_DATA_BYTES == 32
