/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Stateless

/-!
# Concrete stateless output literals
Library `EthConformance`. Complete byte expectations frozen independently in WI356;
each root/boolean/chain/schema carrier is supplied directly through public constructors.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §4/§7.
-/
namespace STFSpec.Conformance.Stateless.OutputNative
open STFSpec.Base STFSpec.Stateless

private def vectors : List (String × StatelessValidationResult) := [
  ("zero_false", {
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0x0000000000000000000000000000000000000000000000000000000000000000),
    successfulValidation := false,
    chainId := U64.ofNat 0x0000000000000000, schemaId := 0x0000 }),
  ("zero_true", {
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0x0000000000000000000000000000000000000000000000000000000000000000),
    successfulValidation := true,
    chainId := U64.ofNat 0x0000000000000000, schemaId := 0x0000 }),
  ("base_false", {
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f),
    successfulValidation := false,
    chainId := U64.ofNat 0x0123456789abcdef, schemaId := 0x1234 }),
  ("bool_only", {
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f),
    successfulValidation := true,
    chainId := U64.ofNat 0x0123456789abcdef, schemaId := 0x1234 }),
  ("root_only", {
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0x1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100),
    successfulValidation := false,
    chainId := U64.ofNat 0x0123456789abcdef, schemaId := 0x1234 }),
  ("chain_only", {
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f),
    successfulValidation := false,
    chainId := U64.ofNat 0x0123456789abcdee, schemaId := 0x1234 }),
  ("schema_only", {
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f),
    successfulValidation := false,
    chainId := U64.ofNat 0x0123456789abcdef, schemaId := 0x1235 }),
  ("schema_zero_nonzero_fields", {
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f),
    successfulValidation := true,
    chainId := U64.ofNat 0x0123456789abcdef, schemaId := 0x0000 }),
  ("schema_amsterdam", {
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f),
    successfulValidation := false,
    chainId := U64.ofNat 0x0123456789abcdef, schemaId := 0x1501 }),
  ("maximum", {
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff),
    successfulValidation := true,
    chainId := U64.ofNat 0xffffffffffffffff, schemaId := 0xffff }),
  ("known_eels_literal", {
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0x0d663a7de3d811fbc797f605a65d2745df3a97d9f1994dfb685ff66d2917009f),
    successfulValidation := true,
    chainId := U64.ofNat 0x0000000000000001, schemaId := 0x1501 }),
  ("root_20_3f", {
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0x202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f),
    successfulValidation := false,
    chainId := U64.ofNat 0x0123456789abcdef, schemaId := 0x1234 }),
  ("root_40_5f", {
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0x404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f),
    successfulValidation := false,
    chainId := U64.ofNat 0x0123456789abcdef, schemaId := 0x1234 }),
  ("root_60_7f", {
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0x606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f),
    successfulValidation := false,
    chainId := U64.ofNat 0x0123456789abcdef, schemaId := 0x1234 }),
  ("root_80_9f", {
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0x808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f),
    successfulValidation := false,
    chainId := U64.ofNat 0x0123456789abcdef, schemaId := 0x1234 }),
  ("root_a0_bf", {
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0xa0a1a2a3a4a5a6a7a8a9aaabacadaeafb0b1b2b3b4b5b6b7b8b9babbbcbdbebf),
    successfulValidation := false,
    chainId := U64.ofNat 0x0123456789abcdef, schemaId := 0x1234 }),
  ("root_c0_df", {
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0xc0c1c2c3c4c5c6c7c8c9cacbcccdcecfd0d1d2d3d4d5d6d7d8d9dadbdcdddedf),
    successfulValidation := false,
    chainId := U64.ofNat 0x0123456789abcdef, schemaId := 0x1234 }),
  ("root_e0_ff", {
    newPayloadRequestRoot := Hash32.ofBytes32 (FixedBytes.ofNat
      0xe0e1e2e3e4e5e6e7e8e9eaebecedeeeff0f1f2f3f4f5f6f7f8f9fafbfcfdfeff),
    successfulValidation := false,
    chainId := U64.ofNat 0x0123456789abcdef, schemaId := 0x1234 })]

private def hex (bytes : ByteArray) : String :=
  String.ofList (bytes.data.toList.flatMap fun byte ↦
    let digits := "0123456789abcdef".toList
    [(digits[byte.toNat / 16]?).getD '0', (digits[byte.toNat % 16]?).getD '0'])

private def emit (name : String) (value : StatelessValidationResult) : IO Unit :=
  IO.println ("{\"name\":\"" ++ name ++ "\",\"actual_hex\":\"" ++
    hex (serializeStatelessOutput value) ++ "\"}")

def run : IO Unit := do
  for (name, value) in vectors do
    emit name value
  emit "zero_sentinel" zeroSentinel

end STFSpec.Conformance.Stateless.OutputNative

def main : IO Unit := STFSpec.Conformance.Stateless.OutputNative.run
