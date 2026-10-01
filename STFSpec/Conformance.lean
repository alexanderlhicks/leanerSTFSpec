/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Conformance.Base.BytesCallerProofs
import STFSpec.Conformance.Base.BytesGuards
import STFSpec.Conformance.Base.FixedBytesCallerProofs
import STFSpec.Conformance.Base.FixedBytesGuards
import STFSpec.Conformance.Base.IntegerBytesCallerProofs
import STFSpec.Conformance.Base.IntegerBytesGuards
import STFSpec.Conformance.Base.NarrowCallerProofs
import STFSpec.Conformance.Base.NarrowGuards
import STFSpec.Conformance.Base.NumericCallerProofs
import STFSpec.Conformance.Base.NumericGuards
import STFSpec.Conformance.Base.U256ArithmeticCallerProofs
import STFSpec.Conformance.Base.U256ArithmeticGuards
import STFSpec.Conformance.Base.U256BitwiseCallerProofs
import STFSpec.Conformance.Base.U256BitwiseGuards
import STFSpec.Conformance.Base.U256CallerProofs
import STFSpec.Conformance.Base.U256ExpCallerProofs
import STFSpec.Conformance.Base.U256ExpGuards
import STFSpec.Conformance.Base.U256Guards
import STFSpec.Conformance.Base.U256ShiftCallerProofs
import STFSpec.Conformance.Base.U256ShiftGuards
import STFSpec.Conformance.Base.U256SignedCallerProofs
import STFSpec.Conformance.Base.U256SignedGuards
import STFSpec.Conformance.Base.ValueRecordsCallerProofs
import STFSpec.Conformance.Base.ValueRecordsGuards
import STFSpec.Conformance.Hash.KeccakPermutationCallerProofs
import STFSpec.Conformance.Hash.KeccakPermutationGuards
import STFSpec.Conformance.Hash.Sha256CompressionCallerProofs
import STFSpec.Conformance.Hash.Sha256CompressionGuards
import STFSpec.Conformance.Hash.Blake2ParametersGuards
import STFSpec.Conformance.Hash.Blake2ParametersCallerProofs
import STFSpec.Conformance.Hash.Ripemd160DigestGuards
import STFSpec.Conformance.Hash.Ripemd160DigestCallerProofs
import STFSpec.Conformance.Hash.Sha256DigestGuards
import STFSpec.Conformance.Hash.Sha256DigestCallerProofs
import STFSpec.Conformance.Hash.KeccakSpongeGuards
import STFSpec.Conformance.Hash.KeccakSpongeCallerProofs
import STFSpec.Conformance.Hash.Ripemd160CompressionCallerProofs
import STFSpec.Conformance.Hash.Ripemd160CompressionGuards
import STFSpec.Conformance.Hash.Blake2CompressionGuards
import STFSpec.Conformance.Hash.Blake2CompressionCallerProofs
import STFSpec.Conformance.Hash.KeccakQueryGuards
import STFSpec.Conformance.Hash.KeccakQueryCallerProofs
import STFSpec.Conformance.Hash.PackedKeccakGuards
import STFSpec.Conformance.Hash.PackedKeccakCallerProofs

import STFSpec.Conformance.Codec.RlpEncodeGuards
import STFSpec.Conformance.Codec.RlpEncodeCallerProofs
import STFSpec.Conformance.Codec.RlpTypedGuards
import STFSpec.Conformance.Codec.RlpTypedCallerProofs
import STFSpec.Conformance.Codec.RlpHeaderGuards
import STFSpec.Conformance.Codec.RlpHeaderCallerProofs
import STFSpec.Conformance.Codec.RlpDecodeGuards
import STFSpec.Conformance.Codec.RlpDecodeCallerProofs
import STFSpec.Conformance.Codec.RlpCanonicalCallerProofs
import STFSpec.Conformance.Codec.AddressGuards
import STFSpec.Conformance.Codec.AddressCallerProofs
import STFSpec.Conformance.Fixtures.Extract
import STFSpec.Conformance.Fixtures.Index
import STFSpec.Conformance.Fixtures.Tests

/-!
# STFSpec.Conformance

Conformance: EEST fixture runners and `core` `#guard` suites.

Library `EthConformance`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). Implementation status is owned by the
spec guidance document.
Spec guidance: `STFSpec/informal/modules/EthConformance.md`.
Base guards, public-law callers and differential drivers are owned by
`STFSpec/informal/modules/EthBase.md` §3.
-/
