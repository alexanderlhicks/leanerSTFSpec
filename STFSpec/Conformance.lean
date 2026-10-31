/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Conformance.Vm.Core.FrameErrorCallerProofs
import STFSpec.Conformance.Vm.Core.FrameErrorGuards
import STFSpec.Conformance.Vm.Runner.BudgetCallerProofs
import STFSpec.Conformance.Vm.Runner.BudgetGuards
import STFSpec.Conformance.Vm.Runner.ExecKindCallerProofs
import STFSpec.Conformance.Field.ModuliCallerProofs
import STFSpec.Conformance.Field.ModuliGuards
import STFSpec.Conformance.Field.ReferenceCallerProofs
import STFSpec.Conformance.Field.ReferencePowerCallerProofs
import STFSpec.Conformance.Field.ReferencePowerGuards
import STFSpec.Conformance.Field.ReferenceInverseCallerProofs
import STFSpec.Conformance.Field.ReferenceInverseGuards
import STFSpec.Conformance.Field.ReferenceDivisionCallerProofs
import STFSpec.Conformance.Field.ReferenceDivisionGuards
import STFSpec.Conformance.Field.ReferenceSignCallerProofs
import STFSpec.Conformance.Field.ReferenceSignGuards
import STFSpec.Conformance.Field.ReferenceDecodeCallerProofs
import STFSpec.Conformance.Field.ReferenceDecodeGuards
import STFSpec.Conformance.Field.ReferenceArithmeticCallerProofs
import STFSpec.Conformance.Field.ReferenceArithmeticGuards
import STFSpec.Conformance.Field.ReferenceGuards
import STFSpec.Conformance.Stateless.OutputCallerProofs
import STFSpec.Conformance.Stateless.OutputGuards
import STFSpec.Conformance.Vm.Runner.EnvironmentCallerProofs
import STFSpec.Conformance.Vm.Core.SatisfiesMCallerProofs
import STFSpec.Conformance.Vm.Core.PrecompileCallerProofs
import STFSpec.Conformance.Block.BlockParamsCallerProofs
import STFSpec.Conformance.Fork.AmsterdamBlockParamsGuards
import STFSpec.Conformance.Vm.Core.TransactionGasAllocationCallerProofs
import STFSpec.Conformance.Vm.Core.PreparationFailureGasCallerProofs
import STFSpec.Conformance.Vm.Core.TransactionGasAllocationGuards
import STFSpec.Conformance.Base.BytesCallerProofs
import STFSpec.Conformance.Base.BytesGuards
import STFSpec.Conformance.Base.BytesOrderCallerProofs
import STFSpec.Conformance.Base.BytesOrderGuards
import STFSpec.Conformance.Base.FixedBytesCallerProofs
import STFSpec.Conformance.Base.FixedBytesGuards
import STFSpec.Conformance.Base.Hash32TableCallerProofs
import STFSpec.Conformance.Base.Hash32TableGuards
import STFSpec.Conformance.Base.IntegerBytesCallerProofs
import STFSpec.Conformance.Base.IntegerBytesGuards
import STFSpec.Conformance.Base.NarrowCallerProofs
import STFSpec.Conformance.Base.NarrowGuards
import STFSpec.Conformance.Base.NumericCallerProofs
import STFSpec.Conformance.Base.NumericGuards
import STFSpec.Conformance.Base.TaylorExponentialCallerProofs
import STFSpec.Conformance.Base.TaylorExponentialGuards
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
import STFSpec.Conformance.Codec.RlpEncodeOfCallerProofs
import STFSpec.Conformance.Codec.RlpEncodeOfGuards
import STFSpec.Conformance.Codec.RlpByteArrayCallerProofs
import STFSpec.Conformance.Codec.RlpByteArrayGuards
import STFSpec.Conformance.Codec.RlpBoolCallerProofs
import STFSpec.Conformance.Codec.RlpBoolGuards
import STFSpec.Conformance.Codec.RlpU256CallerProofs
import STFSpec.Conformance.Codec.RlpU256Guards
import STFSpec.Conformance.Codec.RlpTypedGuards
import STFSpec.Conformance.Codec.RlpTypedCallerProofs
import STFSpec.Conformance.Codec.RlpHeaderGuards
import STFSpec.Conformance.Codec.RlpHeaderCallerProofs
import STFSpec.Conformance.Codec.RlpDecodeGuards
import STFSpec.Conformance.Codec.RlpDecodeCallerProofs
import STFSpec.Conformance.Codec.RlpCanonicalCallerProofs
import STFSpec.Conformance.Codec.AddressGuards
import STFSpec.Conformance.Codec.AddressCallerProofs
import STFSpec.Conformance.Codec.SszModelCallerProofs
import STFSpec.Conformance.Codec.SszModelGuards
import STFSpec.Conformance.Codec.SszEncodeControls
import STFSpec.Conformance.Codec.SszEncodeCallerProofs
import STFSpec.Conformance.Codec.SszSchemaCallerProofs
import STFSpec.Conformance.Codec.SszSchemaControls
import STFSpec.Conformance.Codec.SszCountRecoverableControls
import STFSpec.Conformance.Codec.SszCountRecoverableCallerProofs
import STFSpec.Conformance.Codec.SszWellTypedControls
import STFSpec.Conformance.Codec.SszWellTypedCallerProofs
import STFSpec.Conformance.Codec.SszWellFormedControls
import STFSpec.Conformance.Codec.SszWellFormedCallerProofs
import STFSpec.Conformance.Codec.SszRootableControls
import STFSpec.Conformance.Codec.SszRootableCallerProofs
import STFSpec.Conformance.Codec.SszRootControls
import STFSpec.Conformance.Codec.SszRootCallerProofs
import STFSpec.Conformance.Codec.SszFixedSizeGuards
import STFSpec.Conformance.Codec.SszFixedSizeCallerProofs
import STFSpec.Conformance.Commit.NodeDBGuards
import STFSpec.Conformance.Commit.NodeDBCallerProofs
import STFSpec.Conformance.Commit.NodeCallerProofs
import STFSpec.Conformance.Commit.IncrementalMPTCallerProofs
import STFSpec.Conformance.Commit.DecoderCallerProofs
import STFSpec.Conformance.Commit.DecoderGuards
import STFSpec.Conformance.Commit.LookupCallerProofs
import STFSpec.Conformance.Commit.LookupGuards
import STFSpec.Conformance.Commit.LeafCallerProofs
import STFSpec.Conformance.Commit.LeafGuards
import STFSpec.Conformance.Commit.ChildRefCallerProofs
import STFSpec.Conformance.Commit.ChildRefGuards
import STFSpec.Conformance.Commit.ExtensionCallerProofs
import STFSpec.Conformance.Commit.ExtensionGuards
import STFSpec.Conformance.Commit.BranchCallerProofs
import STFSpec.Conformance.Commit.BranchGuards
import STFSpec.Conformance.Fixtures.Extract
import STFSpec.Conformance.Fixtures.Index
import STFSpec.Conformance.Fixtures.Tests
import STFSpec.Conformance.Commit.NibblesOperationsGuards
import STFSpec.Conformance.Commit.NibblesOperationsCallerProofs
import STFSpec.Conformance.Commit.NibblesGuards
import STFSpec.Conformance.Commit.DecoderDiagnosticGuards
import STFSpec.Conformance.Commit.DecoderDiagnosticCallerProofs
import STFSpec.Conformance.Commit.CompactGuards
import STFSpec.Conformance.Commit.CompactCallerProofs
import STFSpec.Conformance.Commit.NibblesCallerProofs
import STFSpec.Conformance.Commit.InternalNodeGuards
import STFSpec.Conformance.Commit.InternalNodeCallerProofs
import STFSpec.Conformance.Commit.RootDomainGuards
import STFSpec.Conformance.Commit.RootDomainCallerProofs
import STFSpec.Conformance.Commit.RootPrefixGuards
import STFSpec.Conformance.Commit.RootBranchGuards
import STFSpec.Conformance.Commit.RootBranchCallerProofs
import STFSpec.Conformance.Commit.RootPrefixCallerProofs
import STFSpec.Conformance.Commit.RootConstructionGuards
import STFSpec.Conformance.Commit.RootConstructionCallerProofs
import STFSpec.Conformance.Commit.MathRootGuards
import STFSpec.Conformance.Commit.MathRootCallerProofs
import STFSpec.Conformance.Commit.TrieGuards
import STFSpec.Conformance.Commit.TrieCallerProofs
import STFSpec.Conformance.Commit.PreparationGuards
import STFSpec.Conformance.Commit.TypedRootGuards
import STFSpec.Conformance.Commit.TypedRootCallerProofs
import STFSpec.Conformance.Commit.PreparationCallerProofs
import STFSpec.Conformance.State.WitnessAncestorsCallerProofs
import STFSpec.Conformance.State.WitnessAncestorsGuards
import STFSpec.Conformance.State.AccountCallerProofs
import STFSpec.Conformance.State.AccountGuards

import STFSpec.Conformance.State.WriteOrderCallerProofs
import STFSpec.Conformance.State.WriteOrderGuards

import STFSpec.Conformance.State.MathStateCallerProofs
import STFSpec.Conformance.State.MathStateGuards

import STFSpec.Conformance.State.BlockDiffCallerProofs
import STFSpec.Conformance.State.BlockDiffGuards
import STFSpec.Conformance.State.ApplyCallerProofs
import STFSpec.Conformance.State.ApplyGuards
import STFSpec.Conformance.State.PreStateCallerProofs
import STFSpec.Conformance.State.PreStateGuards
import STFSpec.Conformance.State.StateErrorGuards
import STFSpec.Conformance.State.StructuralCallerProofs
import STFSpec.Conformance.State.StructuralGuards
import STFSpec.Conformance.State.ModelsLookupsCallerProofs
import STFSpec.Conformance.State.ModelsLookupsGuards

import STFSpec.Conformance.StateCommit.StorageCallerProofs
import STFSpec.Conformance.StateCommit.StorageGuards
import STFSpec.Conformance.StateCommit.StorageDecodeCallerProofs
import STFSpec.Conformance.StateCommit.StorageDecodeGuards
import STFSpec.Conformance.StateCommit.AccountCallerProofs
import STFSpec.Conformance.StateCommit.AccountGuards
import STFSpec.Conformance.StateCommit.AccountDecodeCallerProofs
import STFSpec.Conformance.StateCommit.AccountDecodeGuards

import STFSpec.Conformance.Commit.IncrementalRootCallerProofs
import STFSpec.Conformance.Commit.IncrementalRootGuards
import STFSpec.Conformance.Commit.UpdateCallerProofs
import STFSpec.Conformance.Commit.UpdateGuards
import STFSpec.Conformance.Commit.DeleteCallerProofs
import STFSpec.Conformance.Commit.DeleteGuards
import STFSpec.Conformance.Commit.SetCallerProofs
import STFSpec.Conformance.Commit.SetGuards

import STFSpec.Conformance.StateCommit.StorageEncodingCallerProofs
import STFSpec.Conformance.StateCommit.StorageEncodingGuards

import STFSpec.Conformance.StateCommit.AccountEncodingCallerProofs
import STFSpec.Conformance.StateCommit.AccountEncodingGuards

import STFSpec.Conformance.Vm.Core.JumpdestCallerProofs
import STFSpec.Conformance.Vm.Core.JumpdestGuards
import STFSpec.Conformance.Vm.Core.LogsCallerProofs
import STFSpec.Conformance.Vm.Core.LogsGuards
import STFSpec.Conformance.Vm.Core.FrameCallerProofs
import STFSpec.Conformance.Vm.Core.FrameGuards
import STFSpec.Conformance.Vm.Core.EnvironmentsCallerProofs
import STFSpec.Conformance.Vm.Core.EnvironmentsGuards
import STFSpec.Conformance.Vm.Core.ContextCallerProofs
import STFSpec.Conformance.Vm.Core.ContextGuards
import STFSpec.Conformance.Vm.Core.StackSwapCallerProofs
import STFSpec.Conformance.Vm.Core.StackSwapGuards
import STFSpec.Conformance.Vm.Core.StackCallerProofs
import STFSpec.Conformance.Vm.Core.StackDepthLimitCallerProofs
import STFSpec.Conformance.Vm.Core.StackGuards
import STFSpec.Conformance.Vm.Core.StackDecoderCallerProofs
import STFSpec.Conformance.Vm.Core.StackDecoderGuards
import STFSpec.Conformance.Vm.Core.BufferReadCallerProofs
import STFSpec.Conformance.Vm.Core.BufferReadGuards
import STFSpec.Conformance.Vm.Core.MemoryCallerProofs
import STFSpec.Conformance.Vm.Core.MemoryGuards
import STFSpec.Conformance.Vm.Core.GasMeterCallerProofs
import STFSpec.Conformance.Vm.Core.GasCostsCallerProofs
import STFSpec.Conformance.Vm.Core.ConfigCallerProofs
import STFSpec.Conformance.Vm.Core.BlockGasCallerProofs
import STFSpec.Conformance.Vm.Core.BlockGasGuards
import STFSpec.Conformance.Vm.Core.GasMeterGuards

import STFSpec.Conformance.Vm.Core.GasRollbackCallerProofs
import STFSpec.Conformance.Vm.Core.GasRollbackGuards
import STFSpec.Conformance.Vm.Core.GasRefundCallerProofs
import STFSpec.Conformance.Vm.Core.GasTransferCallerProofs
import STFSpec.Conformance.Vm.Core.GasTransferGuards
import STFSpec.Conformance.Vm.Core.GasAccountingCallerProofs
import STFSpec.Conformance.Vm.Core.GasAccountingGuards
import STFSpec.Conformance.Vm.Core.TxStateGasUsageCallerProofs
import STFSpec.Conformance.Vm.Core.TxStateGasUsageGuards
import STFSpec.Conformance.Vm.Core.GasRefundGuards

import STFSpec.Conformance.Vm.Core.MemoryGasCallerProofs
import STFSpec.Conformance.Vm.Core.MemoryGasGuards
import STFSpec.Conformance.Vm.Core.TransactionGasSettlementCallerProofs
import STFSpec.Conformance.Vm.Core.TransactionGasSettlementGuards
import STFSpec.Conformance.Vm.Core.CallGasCallerProofs
import STFSpec.Conformance.Vm.Core.CallGasGuards

import STFSpec.Conformance.Codec.RlpDecodeOfCallerProofs
import STFSpec.Conformance.Codec.RlpDecodeOfGuards

import STFSpec.Conformance.Codec.RlpNarrowUnsignedCallerProofs
import STFSpec.Conformance.Codec.RlpNarrowUnsignedGuards
import STFSpec.Conformance.Codec.RlpFixedBytesCallerProofs
import STFSpec.Conformance.Codec.RlpFixedBytesGuards
import STFSpec.Conformance.Codec.RlpListCallerProofs
import STFSpec.Conformance.Codec.RlpListGuards
import STFSpec.Conformance.Codec.RlpAddressCallerProofs
import STFSpec.Conformance.Codec.RlpAddressGuards
import STFSpec.Conformance.Codec.RlpHash32CallerProofs
import STFSpec.Conformance.Codec.RlpHash32Guards

import STFSpec.Conformance.Codec.SszZeroHashControls
import STFSpec.Conformance.Codec.SszZeroHashCallerProofs
import STFSpec.Conformance.Codec.SszPackControls
import STFSpec.Conformance.Codec.SszPackCallerProofs

import STFSpec.Conformance.Codec.SszMerkleizeControls
import STFSpec.Conformance.Codec.SszMerkleizeCallerProofs

import STFSpec.Conformance.Codec.SszMerkleizeProgressiveControls
import STFSpec.Conformance.Codec.SszMerkleizeProgressiveCallerProofs
import STFSpec.Conformance.Codec.SszMixInActiveFieldsControls
import STFSpec.Conformance.Codec.SszMixInActiveFieldsCallerProofs
import STFSpec.Conformance.Codec.SszMixInLengthControls
import STFSpec.Conformance.Codec.SszMixInLengthCallerProofs

import STFSpec.Conformance.Block.LogsBloomCallerProofs
import STFSpec.Conformance.Block.LogsBloomGuards
import STFSpec.Conformance.Block.RequestsHashCallerProofs
import STFSpec.Conformance.Block.RequestsHashGuards
import STFSpec.Conformance.Block.DepositDataCallerProofs
import STFSpec.Conformance.Block.DepositDataGuards
import STFSpec.Conformance.Block.CalldataTokensCallerProofs
import STFSpec.Conformance.Block.CalldataTokensGuards

import STFSpec.Conformance.Fork.AmsterdamVmGuards
import STFSpec.Conformance.Fork.AmsterdamVmCallerProofs
import STFSpec.Conformance.Block.TxParamsCallerProofs
import STFSpec.Conformance.Block.SystemAddrsCallerProofs
import STFSpec.Conformance.Fork.AmsterdamTxParamsGuards
import STFSpec.Conformance.Fork.AmsterdamSystemAddrsGuards

import STFSpec.Conformance.Precompiles.KzgVersionedHashCallerProofs
import STFSpec.Conformance.Precompiles.KzgVersionedHashGuards

import STFSpec.Conformance.Vm.Core.TransferLogCallerProofs
import STFSpec.Conformance.Vm.Core.TransferLogGuards

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
