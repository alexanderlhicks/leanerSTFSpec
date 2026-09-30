# `EthStateless`: the stateless guest (bytes → bytes), payload validation and header chain

*Status: informal specification, draft. Date: 2026-09-30. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F1, F2, F4, F13, F14, F18, F20 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D3, D5, D8, D13, D14, D18, D19 · questions: B12 (Q4), Q5, Q6/Q20, O2, O13.*

Source references are to `src/ethereum/forks/amsterdam/` at e1a316a0 unless another path is given. **[V]** marks a claim checked by reading the pinned source or by running the pinned EELS or the pinned fixtures (environment and reproduction: [REVIEW §2](../REVIEW.md)); **[I]** marks an inference.

## 1. Purpose

`EthStateless` is layer L7 of `ARCHITECTURE.md` §2: the guest. It owns the wire types of the stateless protocol (`StatelessInput`, `ExecutionWitness`, `StatelessValidationResult`, and the engine-API `NewPayloadRequest`/`ExecutionPayload`/`ExecutionRequests` containers they embed), their decoding from `schema_id ++ SSZ` and encoding of the 43-byte result, the witness header-chain check, the conversion of a `NewPayloadRequest` into an execution-layer `Block` (block-hash and versioned-hash checks), and the composition of these with the witness-state backend and `executeBlock`. Its public seam is `runStatelessGuest : ByteArray → ByteArray` (`STFSpec/informal/CONTRACT.md` §1), split into decode, verify and encode, with a checked runner `runStatelessGuestChecked` that separates spec-internal errors (O11) from Ethereum outcomes. It is the top-level refinement target for evm-asm and pancaketh.

## 2. Requirements

**R1. Signature and totality.** `runStatelessGuest` must be a total, deterministic Lean function `ByteArray → ByteArray` that reads no environment and always returns exactly 43 bytes (`stateless_guest.py:53–64` [V]; CONTRACT §1, §3). It must be defined as the projection of `runStatelessGuestChecked : ByteArray → Except InternalError ByteArray`, mapping `.error _` to the zero sentinel (CONTRACT O11). Conformance must call the checked runner.

**R2. Input decoding (O1).** `deserializeStatelessInput` must follow `stateless_guest.py:26–38` [V], in order:
1. fewer than 2 bytes → `DecodeError.missingSchemaId`;
2. the first two bytes read **big-endian** must equal `STATELESS_INPUT_SCHEMA_ID = (ProtocolFork.Amsterdam = 0x15) << 8 | 0x01 = 0x1501` (`stateless.py:131–140`), else `unsupportedSchema id`;
3. the rest must be the **canonical** SSZ encoding of `StatelessInput`. `SszContainer.decode_bytes` (`utils/ssz.py:138–146` [V]) decodes with remerkleable and then rejects any input whose re-encoding differs ("offset gaps and … bytes unread"). So offset gaps, shifted offsets, trailing bytes, oversize items and oversize lists all fail here. The spec's SSZ decoder (owned by `EthCodec`) must accept exactly the canonical encodings; `EthStateless` requires the law `decode b = .ok x ↔ encode x = b` (with `x` satisfying the type limits).

Limits that must be enforced by decoding, not later: witness state nodes ≤ `MAX_BYTES_PER_WITNESS_NODE = 2^10` bytes each; codes ≤ `MAX_BYTES_PER_CODE = 2^16`; headers ≤ `MAX_BYTES_PER_HEADER = 2^10` each and at most `MAX_WITNESS_HEADERS = 256` of them (`ssz_list(256)`); `public_keys` elements are exactly `PUBLIC_KEY_BYTES = 65` bytes (`byte_vector(65)`); `extra_data` ≤ `MAX_EXTRA_DATA_BYTES = 32` (`execution_engine/types.py:33, 62`). The `state`, `codes`, `public_keys`, `versioned_hashes`, `transactions`, `withdrawals`, `block_access_list` and all request lists are **progressive lists** (EIP-7916 shape) with no length limit, and each transaction is a `progressive_byte_list` with no size limit (`types.py:65–72` [V]). `ExecutionPayload` and `ExecutionRequests` are **progressive containers** (`ProgressiveSszContainer`, all fields active; `utils/ssz.py:250–251` [V]); the other containers are ordinary SSZ containers. Any failure maps to the zero sentinel.

**R3. Request root (O2).** `computeNewPayloadRequestRoot` must return SSZ `hash_tree_root(new_payload_request)` (`stateless.py:220–226`). It is outside the inner handler in EELS (`stateless.py:269–271`), so a failure there gives the sentinel. In the spec it is a total function of a decoded value, so O2 has no reachable constructor; the spec must *prove* this ([T] L-root) rather than silently drop the row, and adds a constructor only if that proof fails (DECISIONS §3, O2). L-root must discharge the two candidate sites that the failure ledger (maintained outside this repository) leaves unresolved at `stateless.py:226` (the `hash_tree_root()` call and the `Hash32(…)` constructor). The only EELS test reaching O2 monkeypatches `hash_tree_root` to raise (`tests/json_loader/test_stateless_guest.py:571–591` [V]); it has no spec analogue.

**R4. Header chain (O3, O3a).** `validateHeaders` must follow `stateless.py:240–260` [V] exactly:
1. assert `len ≤ 256` (defensive: unreachable from valid SSZ; CONTRACT §4 precedence);
2. decode **every** header first, each by `_decode_header` (`:229–237`): try the Amsterdam `Header`, and on `rlp.DecodingError` only, the previous-fork header `forks/bpo5/blocks.py::Header` (owned by `EthBlock`). The first failing header (in list order) fails the phase;
3. compute `block_hashes[i] = keccak256(encoded_headers[i])` of the **raw bytes** (not a re-encoding);
4. for `i ≥ 1`, require `headers[i].parent_hash = block_hashes[i-1]`, failing at the first `i`.

Because all decodes precede all contiguity checks, a malformed header at position j beats a contiguity break at i < j. The previous-fork fallback is what admits the BPO2→Amsterdam transition parent: in the pinned corpus 186 guest records in `for_bpo2toamsterdamattime15k` have a last witness header that does not decode as an Amsterdam header [V].

An **empty** header list passes `validate_headers`, and EELS then fails on `decoded_headers[-1]` (`stateless.py:282`, `IndexError`) inside the inner handler. The spec must have an explicit constructor `StatelessError.missingParentHeader` with output `(root, false, chain_id, 0x1501)` (O3a). The fixture `validation_headers_empty_block_missing_mandatory_parent` pins this [V].

**R5. Guest composition (`verify_stateless_new_payload`, `stateless.py:263–311`).** After R3, and all inside the inner phase:
- `parent_header := decoded_headers[-1]`;
- `ChainContext{chain_id := input.chain_id, block_hashes := all witness header hashes, oldest first, parent_header}` (`fork.py:152–164`). `block_hashes` has between 1 and 256 entries; `BLOCKHASH` indexes it from the end (`vm/instructions/block.py:56–64` [V]), and an ancestor missing from the witness is a Python `IndexError` (`vm/instructions/block.py:58`) consumed by the inner handler → failure (fixture `validation_headers_missing_oldest_blockhash_ancestor` [V]). It is a **CONTRACT O13** fault, not a witness error: the constructor is `VmFault.ancestorHashUnavailable` (`EthVmCore`), reaching this module as `.block (.vmFault (.ancestorHashUnavailable _))`;
- acquire `consts ← HashConsts.query` once after R4 succeeds and the nonempty parent is selected, before either witness DB is built (F20; Lean seam, no EELS step). Earlier failures make no acquisition; a run that fails after acquisition has still made the constant queries. Each run acquires independently, without caching the record;
- the pre-state is `WitnessState(node_db = build_node_db(witness.state), state_root = parent_header.state_root, code_db = build_code_db(witness.codes))` (`witness_state.py:37–50`; `build_node_db` is specified by `EthCommit` as `NodeDB.build`, the rest by `EthStateWitness`). In the spec, `NodeDB.build` (`EthCommit`) and `CodeDB.build` (`EthStateWitness`) hash through the oracle and are monadic (D5, F4), and the already-acquired `consts` is stored in the backend. Identical duplicate preimages collapse. Distinct preimages with the same hash use last-wins dictionary insertion, so order independence requires excluding such collisions (EthCommit C12);
- call `executeNewPayloadRequest consts req preState ctx (some input.public_keys)`. The hint is **always** supplied in the guest, so the count check (`fork.py:312–317`) and per-transaction key check (`transactions.py:916–934`) are always active (O5);
- success → `(root, true, chain_id, 0x1501)` (O10); any failure → `(root, false, chain_id, 0x1501)` (O3–O7, O13).

**R6. No fork-activation check.** The spec must **not** check the payload timestamp against fork activation, following `stateless.py:275–277` ("A real implementation MUST do these checks!"). This is recorded as an explicit exclusion (CONTRACT §5; Gaps).

**R7. `execute_new_payload_request` (`execution_engine/new_payload.py:75–136` [V]).** In order:
1. if any payload transaction is the empty byte string → `InvalidBlock("Empty transaction in payload")`;
2. `is_valid_block_hash` (`:28–47`): build the implied header with `_payload_header` (`validation_helpers.py:23–85`): transactions root and withdrawals root as unsecured tries keyed by `rlp(Uint(i))` (with `rlp(withdrawal)` values), `requests_hash = compute_requests_hash(encode_execution_requests(requests))`, `block_access_list_hash = keccak256(payload.block_access_list)` of the **raw bytes**, the fixed post-merge fields (`ommers_hash = EMPTY_OMMER_HASH`, in the spec `HashConsts.emptyOmmerHash`, F2; `difficulty = 0`, `nonce = 0^8`), and the rest copied from the payload; then require `keccak256(rlp(header)) = payload.block_hash`. Any exception while building the header returns `False` [V]; in the spec `payloadHeader` is total on decoded values [I], so `isValidBlockHash` is an equality test;
3. `is_valid_versioned_hashes` (`:50–72`): decode **every** transaction with `decode_transaction` (`transactions.py:562–587`); any failure (unknown type byte, `assert tx[0] ≤ 0xFE`, RLP error, `RecursionError` from deep nesting) → `False` (`except Exception`, `:60–68`). Otherwise concatenate `blob_versioned_hashes` of blob transactions in order and compare with `versioned_hashes` as sequences. So, on the guest path, **every** deterministic payload-transaction decode failure is reported in *this* phase, as `invalidVersionedHashes` (O6), and `EthBlock`'s `txDecode` constructors are reachable only from a standalone `executeBlock` (EthBlock R-TX-DEC). The same catch-all also absorbs host failures (`MemoryError`, `RecursionError`), which then look like O6 (DISC-006; O12 stays unresolved, DISC-001);
4. `_payload_block` (`validation_helpers.py:100–122`): the block's transactions are the raw bytes, except that a transaction whose first byte is ≥ `0xC0` becomes a decoded `LegacyTransaction` (`:88–97`), `ommers = ()`, withdrawals as given;
5. `execute_block(block, pre_state, chain_context, transaction_public_keys)` (`fork.py:281`, owned by `EthBlock`), whose `BlockDiff` and the block are returned.

The payload's BAL bytes are only hashed at this level; `execute_block` compares the hash of the *computed* BAL with the header's (`fork.py:380–381`). Execution requests are committed only through `requests_hash` in the header, hence through `block_hash` (docstring `types.py:215–218`).

**R8. Outcome mapping.** Every CONTRACT §4 row must be an explicit path (§7 table), including each enumerated O13 fault. No catch-all; phase precedence as in the pinned EELS order (CONTRACT §4 "Failure precedence"). All inner failures (O3–O7, O13) produce byte-identical outputs, so fixtures cannot observe the constructor chosen; constructor order is a spec-fidelity obligation checked by `core` tests against a reading of EELS, not by the corpus.

**R9. O12 (Python runtime failures).** No behaviour may be derived from Python recursion or memory limits without a DISC entry and accepted decision (CONTRACT §6; DISC-001). Witness-reference cycles are O4 (`ARCHITECTURE.md` §5.4). See Gaps for two classes of finite acyclic inputs where host limits and the spec may differ.

## 3. EELS source map

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `forks/amsterdam/stateless.py::MAX_WITNESS_HEADERS` | 33 | `maxWitnessHeaders : Nat := 256` | SSZ list limit and R4 assert |
| `forks/amsterdam/stateless.py::MAX_BYTES_PER_CODE` | 34 | `maxBytesPerCode := 2^16` | |
| `forks/amsterdam/stateless.py::MAX_BYTES_PER_HEADER` | 35 | `maxBytesPerHeader := 2^10` | |
| `forks/amsterdam/stateless.py::MAX_BYTES_PER_WITNESS_NODE` | 36 | `maxBytesPerWitnessNode := 2^10` | |
| `forks/amsterdam/stateless.py::PUBLIC_KEY_BYTES` | 37 | `publicKeyBytes := 65` | |
| `forks/amsterdam/stateless.py::ExecutionWitness` | 43 | `structure ExecutionWitness` | |
| `forks/amsterdam/stateless.py::ProtocolFork` | 103 | `inductive ProtocolFork` + `toIndex` | only `amsterdam` is used |
| `forks/amsterdam/stateless.py::STATELESS_INPUT_SCHEMA_FORK_INDEX` | 131 | `schemaForkIndex := ProtocolFork.amsterdam` | |
| `forks/amsterdam/stateless.py::STATELESS_INPUT_SCHEMA_REVISION` | 132 | `schemaRevision : UInt8 := 1` | |
| `forks/amsterdam/stateless.py::STATELESS_INPUT_SCHEMA_ID` | 133 | `schemaId : UInt16 := 0x1501` | `#guard`/`decide` |
| `forks/amsterdam/stateless.py::STATELESS_INPUT_SCHEMA_ID_SIZE` | 136 | `schemaIdSize := 2` | |
| `forks/amsterdam/stateless.py::STATELESS_INPUT_SCHEMA_ID_BYTES` | 137 | `schemaIdBytes : ByteArray := ⟨#[0x15, 0x01]⟩` | big-endian |
| `forks/amsterdam/stateless.py::StatelessInput` | 146 | `structure StatelessInput` | incl. `publicKeys` |
| `forks/amsterdam/stateless.py::StatelessValidationResult` | 181 | `structure StatelessValidationResult` | fixed size 43 |
| `forks/amsterdam/stateless.py::compute_new_payload_request_root` | 220 | `computeNewPayloadRequestRoot` | total (R3) |
| `forks/amsterdam/stateless.py::_decode_header` | 229 | `decodeHeader` (internal) | fallback only on RLP error |
| `forks/amsterdam/stateless.py::validate_headers` | 240 | `validateHeaders` | R4 |
| `forks/amsterdam/stateless.py::verify_stateless_new_payload` | 263 | `verifyStatelessNewPayload{,Checked}` | R5 |
| `forks/amsterdam/stateless_guest.py::*` | 19–64 | `serializeStatelessOutput`, `deserializeStatelessInput`, `zeroSentinel` (= `_default_failed_stateless_output`), `runStatelessGuest{,Checked}` | whole file |
| `forks/amsterdam/execution_engine/new_payload.py::is_valid_block_hash` | 28 | `isValidBlockHash` | |
| `forks/amsterdam/execution_engine/new_payload.py::is_valid_versioned_hashes` | 50 | `isValidVersionedHashes` | |
| `forks/amsterdam/execution_engine/new_payload.py::execute_new_payload_request` | 75 | `executeNewPayloadRequest` | backend-generic |
| `forks/amsterdam/execution_engine/types.py::MAX_EXTRA_DATA_BYTES` | 33 | `maxExtraDataBytes := 32` | SSZ limit |
| `forks/amsterdam/execution_engine/types.py::ExecutionPayload` | 39 | `structure ExecutionPayload` | progressive container |
| `forks/amsterdam/execution_engine/types.py::NewPayloadRequest` | 78 | `structure NewPayloadRequest` | |
| `forks/amsterdam/execution_engine/validation_helpers.py::*` | 23–122 | `payloadHeader`, `payloadTransactionToBlockTransaction`, `payloadBlock` (internal) | whole file |
| `forks/amsterdam/execution_engine/requests.py::DepositRequest` | 42 | `structure DepositRequest` | |
| `forks/amsterdam/execution_engine/requests.py::WithdrawalRequest` | 55 | `structure WithdrawalRequest` | |
| `forks/amsterdam/execution_engine/requests.py::ConsolidationRequest` | 66 | `structure ConsolidationRequest` | |
| `forks/amsterdam/execution_engine/requests.py::BuilderDepositRequest` | 77 | `structure BuilderDepositRequest` | EIP-8282 |
| `forks/amsterdam/execution_engine/requests.py::BuilderExitRequest` | 89 | `structure BuilderExitRequest` | EIP-8282 |
| `forks/amsterdam/execution_engine/requests.py::ExecutionRequests` | 99 | `structure ExecutionRequests` | progressive container |
| `forks/amsterdam/execution_engine/requests.py::_encode_deposit` | 119 | `encodeDeposit` (internal) | 192 bytes |
| `forks/amsterdam/execution_engine/requests.py::_encode_withdrawal` | 129 | `encodeWithdrawal` (internal) | 76 bytes |
| `forks/amsterdam/execution_engine/requests.py::_encode_consolidation` | 137 | `encodeConsolidation` (internal) | 116 bytes |
| `forks/amsterdam/execution_engine/requests.py::_encode_builder_deposit` | 145 | `encodeBuilderDeposit` (internal) | 184 bytes |
| `forks/amsterdam/execution_engine/requests.py::_encode_builder_exit` | 154 | `encodeBuilderExit` (internal) | 68 bytes |
| `forks/amsterdam/execution_engine/requests.py::encode_execution_requests` | 200 | `encodeExecutionRequests` | empty lists omitted, ascending type |

The decoders and size constants of `execution_engine/requests.py` (engine wire form → typed) are host-side and claimed by `EthConformance`; `verify_and_notify_new_payload` (the stateful path) is claimed by `EthConformance`. Scaffolding types, `forkchoice_update.py`, `get_payload.py` and the unused engine types are excluded in `STFSpec/informal/EXCLUDED.md` with reasons.

**External semantics.** The inventory lists these external uses in the claimed files:
- `ethereum_rlp.rlp` (`stateless.py:9`, `new_payload.py:7`, `validation_helpers.py:7`): `decode_to(Header, ·)` and `encode`. Canonical-form and `DecodingError` behaviour are specified by `EthCodec`; `EthStateless` needs (a) `decode_to` failure on the Amsterdam shape is a *DecodingError* in every case where the fallback must fire [I: needs a check of `ethereum-rlp` 0.1.6 for non-`DecodingError` exceptions, e.g. from field constructors]; (b) `rlp.encode(decode b) = b` for successfully decoded headers, which makes `keccak(raw bytes)` (R4) and `keccak(rlp(parent_header))` (`fork.py:516`) agree.
- `ethereum_types` `Bytes`, `U16`, `U64`, `slotted_freezable`: plain value types; `U16(STATELESS_INPUT_SCHEMA_ID)` and `int.from_bytes(·, "big")` fix the schema-id encoding. `slotted_freezable` has no semantic content.
- SSZ via `eth-remerkleable` 0.1.31 (through `utils/ssz.py`, owned by `EthCodec`): canonical decoding, progressive list/container merkleization and `hash_tree_root`.

## 4. Tests

**EEST fixture areas.** Every guest record (29,030, all in `blockchain_tests`) passes through this library. Areas that target it specifically (`STFSpec/informal/eest-fixture-index.txt`): `blockchain_tests/for_amsterdam/amsterdam/eip8025_optional_proofs` (100 files), in particular `stateless_input_bytes/` (the 9 zero-sentinel records: empty input, 1-byte input, schema only, wrong fork byte `0x16`, wrong revision `0x02`, truncated body, trailing garbage, invalid first offset, shifted offsets [V]), `witness_validation_headers/` (non-contiguous chain, missing parent header, empty headers, missing oldest BLOCKHASH ancestor, malformed RLP header), `witness_headers/`, `witness_public_keys/`, `witness_validation_chain_id/`, `stateless_input_versioned_hashes/`, `witness_validation_state/`, `witness_validation_codes/`; and the transition directory `for_bpo2toamsterdamattime15k/*` (previous-fork parent header). Payload conversion is exercised by `prague/eip7685_general_purpose_el_requests`, `eip6110_deposits`, `eip7002_*`, `eip7251_*`, `amsterdam/eip8282_builder_execution_requests`, `cancun/eip4844_blobs` (versioned hashes) and `amsterdam/eip7928_block_level_access_lists` (BAL bytes and hash).

Corpus facts relevant here [V]: 27,822 records succeed, 1,199 fail with schema `0x1501`, 9 are the zero sentinel; the largest input is 8,396,936 bytes; one record has an empty header list; 28,975 of 29,030 records carry exactly one witness header.

**EELS unit tests** at e1a316a0: `tests/json_loader/test_stateless_guest.py` (schema-id identity, round trips, known encoding and request root, empty witness, 65-byte key enforcement, oversize witness items, >256 headers rejected, empty/1-byte/wrong-revision/wrong-fork/legacy raw-SSZ inputs rejected, non-canonical shifted offsets → sentinel, decodable input reports schema on failure, public-key count too few/too many); `tests/json_loader/test_execution_requests.py` (wire round trip). Port each as a `core` case where it does not depend on monkeypatching.

**`core` `#guard` cases.**
- Typical: a minimal valid input (one parent header, empty block, empty witness DB except the root node) → `(root, true, 1, 0x1501)`; the expected root computed independently.
- Edge: header list of length 0 (O3a), 1, 256; a BPO5-shape parent header; `public_keys` empty with empty block; payload with zero requests (all lists empty → `encodeExecutionRequests = #[]`); `extra_data` of 32 bytes.
- Adversarial: every O1 variant above; 257 headers (O1, not O3); a header decodable only as the previous fork in the middle of the chain; decode failure at j and contiguity break at i < j (decode wins); an empty transaction together with a wrong block hash (empty tx wins); an unknown tx type byte `0x05` (reported as `invalidVersionedHashes`); tx byte `0xFF`; one key too few/too many (O5); wrong key with right count (O5 at that tx).
- Structural: `(serializeStatelessOutput r).size = 43` for all `r`; `zeroSentinel` bytes are 43 zeros.
- F20 composition cases to implement, using the R5 query order:
  - Decode, header-decode, empty-header and contiguity failures acquire no record. A contiguity failure still has its preceding raw-header hashes.
  - Pass successful nonempty headers; acquisition precedes witness construction and payload guards.
  - Use a synthetic record differing from literals; the witness backend, both payload-header constructions, block validation and context consumers receive or observe that record.
  - Repeat an ordinary constant preimage query; it is not a second record acquisition.
  - Fail the empty-transaction, payload-hash and versioned-hash guards separately; prior queries remain in the trace and the first guard determines the error.
  - Raise a provider or fuel error; prior queries remain in the trace and the error stays in its inner or outer checked channel, respectively.
  - Run twice; each run acquires independently.
  - Exercise the actual shared payload and block kernels with test codec and body callbacks; their traces contain no reacquisition. Replacing an entire kernel with a test callback would not check this property.

**Properties and differential checks.** Round trip `deserialize (serializeStatelessInput x) = .ok x` for generated well-formed `x` (serializer from `EthConformance`); `validateHeaders` against a model on generated chains; differential against EELS `run_stateless_guest` on mutated inputs (bug-finding only; `EthConformance`).

## 5. Interface

Reference field order, widths and inherited records are catalogued in [REFERENCE-RECORDS](../REFERENCE-RECORDS.md), generated from the exact pin. Wire-schema owners must use those layouts and prove their codec instances. Runtime records may use the explicit abstraction below; omitted fields or `…` remain implementation blockers, not implicit freedom to choose semantics.

All in namespace `STFSpec.Stateless`; public unless marked.

```lean
-- constants (public)
def maxWitnessHeaders : Nat := 256
def maxBytesPerCode : Nat := 2^16
def maxBytesPerHeader : Nat := 2^10
def maxBytesPerWitnessNode : Nat := 2^10
def publicKeyBytes : Nat := 65
def maxExtraDataBytes : Nat := 32
inductive ProtocolFork | frontier | homestead | daoFork | tangerineWhistle | spuriousDragon
  | byzantium | stPetersburg | istanbul | muirGlacier | berlin | london | arrowGlacier
  | grayGlacier | paris | shanghai | cancun | prague | osaka | bpo1 | bpo2 | amsterdam
def ProtocolFork.toIndex : ProtocolFork → UInt8          -- 0x01 … 0x15
def schemaId : UInt16 := (ProtocolFork.amsterdam.toIndex.toUInt16 <<< 8) ||| 0x01
def schemaIdBytes : ByteArray                            -- big-endian, size 2

-- wire types (public)
abbrev PublicKey := { b : ByteArray // b.size = publicKeyBytes }
structure ExecutionWitness where
  state   : Array ByteArray
  codes   : Array ByteArray
  headers : Array ByteArray
structure DepositRequest where pubkey : Bytes48; withdrawalCredentials : Bytes32; amount : U64; signature : Bytes96; index : U64
structure WithdrawalRequest where sourceAddress : Address; validatorPubkey : Bytes48; amount : U64
structure ConsolidationRequest where sourceAddress : Address; sourcePubkey : Bytes48; targetPubkey : Bytes48
structure BuilderDepositRequest where pubkey : Bytes48; withdrawalCredentials : Bytes32; amount : U64; signature : Bytes96
structure BuilderExitRequest where sourceAddress : Address; pubkey : Bytes48
structure ExecutionRequests where
  deposits : Array DepositRequest; withdrawals : Array WithdrawalRequest
  consolidations : Array ConsolidationRequest; builderDeposits : Array BuilderDepositRequest
  builderExits : Array BuilderExitRequest
structure ExecutionPayload where
  parentHash : Hash32; feeRecipient : Address; stateRoot : Hash32; receiptsRoot : Hash32
  logsBloom : Bloom; prevRandao : Bytes32; blockNumber : U64; gasLimit : U64; gasUsed : U64
  timestamp : U64; extraData : ByteArray; baseFeePerGas : U256; blockHash : Hash32
  transactions : Array ByteArray; withdrawals : Array Withdrawal; blobGasUsed : U64
  excessBlobGas : U64; blockAccessList : ByteArray; slotNumber : U64
structure NewPayloadRequest where
  executionPayload : ExecutionPayload; versionedHashes : Array VersionedHash
  parentBeaconBlockRoot : Hash32; executionRequests : ExecutionRequests
structure StatelessInput where
  newPayloadRequest : NewPayloadRequest; witness : ExecutionWitness
  chainId : U64; publicKeys : Array PublicKey
structure StatelessValidationResult where
  newPayloadRequestRoot : Hash32; successfulValidation : Bool; chainId : U64; schemaId : UInt16
def StatelessInput.WF : StatelessInput → Prop            -- all SSZ limits (§6)
instance : SszSchema StatelessInput                      -- from EthCodec; also for every wire type above
abbrev AnyHeader := ParentHeader

-- errors (public, one constructor per EELS failure site)
inductive DecodeError | missingSchemaId | unsupportedSchema (id : UInt16) | ssz (e : SszError)
inductive HeaderError | tooMany (n : Nat) | undecodable (i : Nat) (amsterdam prev : RlpError)
  | notContiguous (i : Nat)
inductive PayloadError | emptyTransaction (i : Nat) | invalidBlockHash
  | invalidVersionedHashes (cause : Option (Nat × TxDecodeError))
  | legacyDecode (i : Nat) (e : TxDecodeError)           -- dead after invalidVersionedHashes [I]
inductive StatelessError | headers (e : HeaderError) | missingParentHeader
  | payload (e : PayloadError) | block (e : BlockError)  -- BlockError (EthBlock) embeds WitnessError (O4), key errors (O5) and the O13 fault constructors
-- InternalError and CheckedResult are imported from EthVmRunner, never redeclared here.
inductive GuestOutcome
  | decodeFailed (e : DecodeError)                                       -- O1
  | invalid (root : Hash32) (chainId : U64) (e : StatelessError)          -- O3–O7, O13
  | valid (root : Hash32) (chainId : U64)                                 -- O10

-- functions. Everything that hashes is generic in the oracle monad (D5); the public
-- functions below the `classifyWith` line are their `m := Id` instances.
variable {m : Type → Type} [Monad m] [KeccakQuery m]
def deserializeStatelessInput : ByteArray → Except DecodeError StatelessInput          -- public
def serializeStatelessOutput : StatelessValidationResult → ByteArray                    -- public
def zeroSentinel : StatelessValidationResult                                            -- public
def computeNewPayloadRequestRoot : StatelessInput → Hash32                              -- public, total
def decodeHeader : ByteArray → Except (RlpError × RlpError) AnyHeader                   -- internal
def validateHeaders : Array ByteArray → m (Except HeaderError (Array AnyHeader × Array Hash32)) -- public; hashes queried
def encodeExecutionRequests : ExecutionRequests → Array ByteArray                       -- public
def payloadHeader (consts : HashConsts) : ExecutionPayload → Hash32 → ExecutionRequests → m Header            -- internal, total; trie roots queried
def payloadTransactionToBlockTransaction : ByteArray → Except TxDecodeError BlockTx     -- internal
def payloadBlock (consts : HashConsts) : ExecutionPayload → Hash32 → ExecutionRequests → m (Except PayloadError Block) -- internal
def isValidBlockHash (consts : HashConsts) : ExecutionPayload → Hash32 → ExecutionRequests → m Bool           -- public; block hash queried
def isValidVersionedHashes : NewPayloadRequest → Bool                                   -- public
def executeNewPayloadRequest (consts : HashConsts) (req : NewPayloadRequest) (pre : PreState m)
    (ctx : ChainContext) (keys : Option (Array PublicKey)) :
    m (CheckedResult StatelessError (BlockDiff × Block))                               -- public (both backends)
structure GuestLeaves (m) where                                                         -- testing seam
  decodeInput : ByteArray → Except SszError StatelessInput
  requestRoot : NewPayloadRequest → Hash32
  decodeHeader : ByteArray → Except (RlpError × RlpError) AnyHeader
  executePayload : HashConsts → NewPayloadRequest → PreState m → ChainContext → Option (Array PublicKey)
    → m (CheckedResult StatelessError (BlockDiff × Block))
def amsterdamLeaves : GuestLeaves m                                                    -- the real phases
def classifyWith (L : GuestLeaves m) : ByteArray → m (Except InternalError GuestOutcome)
def runStatelessGuestWith (L : GuestLeaves m) : ByteArray → m ByteArray              -- sentinel on .error
-- public, at m := Id
def verifyStatelessNewPayloadChecked : StatelessInput → Except InternalError GuestOutcome -- public
def verifyStatelessNewPayload (x : StatelessInput) : StatelessValidationResult          -- public projection
def classify : ByteArray → Except InternalError GuestOutcome :=                          -- public: the O-row
  classifyWith (m := Id) amsterdamLeaves
def GuestOutcome.toResult : GuestOutcome → StatelessValidationResult                    -- public
def runStatelessGuestChecked (input : ByteArray) : Except InternalError ByteArray :=
  (classify input).map (serializeStatelessOutput ∘ GuestOutcome.toResult)
def runStatelessGuest (input : ByteArray) : ByteArray :=
  match runStatelessGuestChecked input with
  | .ok out => out | .error _ => serializeStatelessOutput zeroSentinel
theorem runStatelessGuest_eq : runStatelessGuest = runStatelessGuestWith (m := Id) amsterdamLeaves
```

The payload entry and helpers take `consts : HashConsts` with local EELS notation (CONTRIBUTING §7.2, F20). `isValidBlockHash` and `payloadBlock` each build `payloadHeader`, so both take the record explicitly. `executeNewPayloadRequest` forwards that record through these helpers and `Amsterdam.executeBlock`; none of those kernels acquires it. `classifyWith` follows R5 and supplies the record to the witness backend and `L.executePayload`. Consumers whose state or backend already holds the record read its fields.

Use `ParentHeader` from `EthBlock` for the Amsterdam/BPO5 sum; `AnyHeader` above is an alias for that type. `ChainContext`, `Block`, `BlockTx`, `BlockError`, transaction-decode diagnostics and `executeBlock` come from `EthBlock`/`EthFork`; `PreState`/`BlockDiff` from `EthState`; `WitnessBackend.build` and `CodeDB.build` from `EthStateWitness`, `NodeDB.build` from `EthCommit` (both monadic, F4); `HashConsts` from `EthBase` and `HashConsts.query`/`KeccakQuery` from `EthHash`. The executable seam uses `CheckedResult` (from `CheckedT`, `EthVmRunner`, F14): validation errors are the inner `Except`, and internal failures, including fuel exhaustion, the outer `InternalError`. There is no separate `FuelM`. `classifyWith` is the leaf-parametric composition; the real composition code runs unchanged under test leaves, and `runStatelessGuest_eq` ties the public function to it at `Id`.

## 6. Data structures

| Type | Representation | Model | Abstraction | Invariant | Persistence | Complexity |
|---|---|---|---|---|---|---|
| `ExecutionWitness` | three `Array ByteArray` | a triple of finite lists | identity | `WF`: node/code/header size limits, `headers.size ≤ 256` | linear-only (read once to build DBs) | decode O(n); DB build O(total bytes) keccak |
| `StatelessInput` and the wire containers | Lean structures over `ByteArray`/`Array`/fixed-width words | the SSZ value | identity; SSZ `encode`/`decode` | `WF` (limits; `PublicKey` size by subtype; `extraData.size ≤ 32`) | immutable after decode | decode O(input); `hash_tree_root` O(size) SHA-256 compressions |
| `StatelessValidationResult` | structure | 4-tuple | `serialize` = fixed 43-byte layout (LE `chainId`, LE `schemaId`, boolean byte) | none | value | O(1) |
| `GuestOutcome` | inductive | the O-row plus fields | `toResult` | `valid`/`invalid` only carry `schemaId = 0x1501` implicitly | value | O(1) |
| header chain result | `Array AnyHeader × Array Hash32` | a list of headers with hashes | `hashes[i] = keccak(raw[i])` | contiguity (R4) | linear-only | O(Σ header bytes) keccak |
| requests wire form | `Array ByteArray` | list of `type ++ body` blobs | `encodeExecutionRequests` | strictly ascending type, non-empty bodies | value | O(total bytes) |

Widths: `blockNumber`, `gasLimit`, `gasUsed` are `Uint` in EELS but SSZ `uint64` (`types.py:226–229`); `timestamp` is `U256` with SSZ `uint(64)`; `baseFeePerGas` is SSZ `uint256`. The spec stores the SSZ width and widens explicitly where `Header` needs `Uint`/`U256`; a decoded value is always in range, so no check is lost [V: SSZ decoding rejects values outside the declared field widths]. Consequently the NUMBER, GASLIMIT and BASEFEE `U256` conversions in the VM cannot overflow; only BLOBBASEFEE (computed, not decoded) can (O13).

## 7. Contract and laws

**Outcome mapping (D14).**

| Row | Spec path | Output |
|---|---|---|
| O1 | `classify` → `.decodeFailed e` | `zeroSentinel` |
| O2 | no constructor: `computeNewPayloadRequestRoot` is total ([T] L-root; to be proved, DECISIONS §3 O2) | — |
| O3 | `.invalid r c (.headers e)` | `(r, false, c, 0x1501)` |
| O3a | `.invalid r c .missingParentHeader` | same |
| O4 | `.invalid r c (.block (.witness e))` (constructors in `EthStateWitness`/`EthCommit`) | same |
| O5 | `.invalid r c (.block .publicKeyCountMismatch)` or `.block (.invalidPublicKeyHint i e)` (EthBlock) | same |
| O6 | `.invalid r c (.payload e)` or `.invalid r c (.block e)` for header/body/root errors; on the guest path every payload-transaction decode failure is `.payload (.invalidVersionedHashes cause)` | same |
| O7 | `.invalid r c (.block (.invalidTransaction i e))` | same |
| O8, O9 | no outcome here: consumed inside `EthVmRunner`/`EthPrecompiles` | — |
| O10 | `.valid r c` | `(r, true, c, 0x1501)` |
| O11 | `classify input = .error e` | checked runner `.error e`; public function `zeroSentinel` |
| O12 | none authorized (DISC-001, unresolved) | — |
| O13 | `.invalid r c (.block e)` with the named fault constructor: `.vmFault (.ancestorHashUnavailable _)` (BLOCKHASH, `vm/instructions/block.py:58`), `.arith .chainIdOverflow` (`transactions.py:878`), and the other enumerated sites (EthBlock §2.12); never a catch-all | same |

**Laws.**
- [T] **L-total**: `runStatelessGuest` is a total `def` (structural/well-founded; no `partial`).
- [T] **L-root**: `computeNewPayloadRequestRoot` is total on decoded values, discharging `stateless.py:226`; consequently O2 is unreachable. If the proof fails, O2 gets a constructor instead (DECISIONS §3, O2).
- [T] **L-internal** ([REVIEW §7](../REVIEW.md#7-acceptance-criteria-proof-gates-composition-cases-replacement-and-cost-checks) G7): `∀ input, ∃ out, runStatelessGuestChecked input = .ok out`. Discharged from `EthVmRunner` fuel sufficiency plus the absence of any other `InternalError` source here. Consumers refine the public function through it: `runStatelessGuest input = out ↔ runStatelessGuestChecked input = .ok out`.
- [R] **L-size**: `(runStatelessGuest input).size = 43`.
- [R] **L-decode-phase**: `deserializeStatelessInput input = .error e → runStatelessGuest input = serialize zeroSentinel`.
- [R] **L-fields**: `deserializeStatelessInput input = .ok x →` the output decodes to a result with `root = computeNewPayloadRequestRoot x`, `chainId = x.chainId`, `schemaId = 0x1501`. So the non-validity fields depend only on the decoded input (the property verifiers rely on).
- [R] **L-valid**: `successfulValidation = true ↔` `validateHeaders` succeeds with non-empty headers and `executeNewPayloadRequest` over the witness backend succeeds. Stated as an equation on `classify`, this is the top-level seam equation.
- [C] **L-decode-canonical**: `deserializeStatelessInput b = .ok x ↔ b = schemaIdBytes ++ encode x ∧ x.WF` (from `EthCodec` SSZ laws).
- [C] **L-output-codec**: `serializeStatelessOutput` is injective, and the host-side decoder (`EthConformance`) is its left inverse.
- [C] **L-headers**: `validateHeaders hs = .ok (ds, bh) → ds.size = hs.size ∧ bh = hs.map keccak256 ∧ ∀ i, 0 < i → ds[i].parentHash = bh[i-1]`, and conversely on success of every decode; error precedence as in R4.
- [C] **L-requests**: `encodeExecutionRequests` emits one blob per non-empty list, strictly ascending type bytes `0x00…0x04` (`forks/amsterdam/requests.py:71–100`, owned by `EthBlock` [V]), each body a concatenation of fixed-size items; `decodeExecutionRequests ∘ encodeExecutionRequests = .ok` (`EthConformance`).
- [C] **L-payload-header**: `isValidBlockHash consts p pbr rq = (keccak256 (rlp (payloadHeader consts p pbr rq)) == p.blockHash)`.
- [C] **L-versioned**: `isValidVersionedHashes req = true ↔` every tx decodes and the concatenated blob hashes equal `req.versionedHashes`.
- [R] **L-constants** (F20): prove the acquisition and effect order in R5 as implementation equations, and prove preservation of one supplied record through witness construction, both payload-header constructions, block entry and context consumers. Check these equations with a synthetic oracle whose constants differ from literals (§4). Generic interpretation coupling remains D5/X7.
- [R] **L-backend-generic**: `executeNewPayloadRequest` uses `pre` only through the `PreState m` operations (it forwards the same `consts` to `executeBlock` after ordered payload checks). This is what `EthSecurity` needs to move from the witness backend to the full-state backend.
- [R] **L-hint-equivalence** (from `EthBlock`): with `keys = some ks` accepted, the result equals the result with `keys = none`. This bridges the guest (hint always present) and the stateful path (no hint).
- [S] consumed by `EthSecurity`: the three §7 CONTRACT obligations. Nothing here is stated under a collision assumption.

### Informal correctness argument

**Claim.** Given codec domain/totality, block refinement, complete error projection and fuel sufficiency, the guest returns exactly the 43-byte reference result on the agreed input/host domain.

**Premises.** Exact schema ID and schema instances; rootability of decoded requests; reference header fallback/check order; checked block/error adapters; the accepted D14/O12 policy. Accepted-chain, chain-id and fork activation anchoring are external hypotheses for security.

**Argument.** Partition execution by its ordered phases. Decode/schema failures select the zero sentinel. Compute and retain the request root before inner validation. Header, witness, payload and block errors then select false with that root and chain ID; valid execution selects true. Header fallback catches the designated decoding error only, and an empty header array has its own outcome. Payload checks preserve the reference order before constructing Block. The shared CheckedResult adapter separates validation errors from InternalError, so fuel exhaustion cannot silently become false or success. With runner sufficiency the internal branch is unreachable on well-formed contexts; proving that arbitrary accepted input constructs those contexts is an additional step. SSZ encoding of the final fixed-width result gives 32 root bytes, one boolean byte, eight little-endian chain-ID bytes and two little-endian schema-ID bytes, in that order.

**Open obligations.** Finish the per-phase error enumeration and decoded-input well-formedness/rootability proof, including implicit failures and host-dependent cases. The current informal argument is conditional; it does not by itself establish O11 freedom for every byte array or validate an externally supplied parent.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthFork`, `EthStateWitness`
- **Used by:** `EthConformance`; `EthSecurity` (security package); consumers evm-asm and pancaketh (the `Faithful`/refinement target).
- **Seams consumed:** `executeBlock` and `ChainContext` (`EthBlock`, via the `EthFork` Amsterdam composition); the witness-state `PreState` constructor `WitnessBackend.build` (pure: it takes already-built DBs) and the monadic builders `CodeDB.build` (`EthStateWitness`) and `NodeDB.build` (`EthCommit`) (F4); `HashConsts.query`; SSZ `SszType` instances, `hashTreeRoot`, RLP `decodeTo`/`encode` and keccak (`EthCodec`/`EthHash`, reachable transitively); unsecured-trie `root` for the transactions and withdrawals roots (`EthCommit`, via `EthBlock`); `computeRequestsHash` (`EthBlock`).
- **Seam provided:** `runStatelessGuest` (L7), `classify` (diagnostic O-row), `executeNewPayloadRequest` (payload → block, backend-generic).
- **Cross-module invariants relied on:** the witness backend never throws outside `Except`; every `WitnessError` is a value (D8); `executeBlock` reports all failures as `BlockError` constructors; `EthVmRunner` reports fuel exhaustion only as `InternalError`, never as an EVM outcome (O11). **Guaranteed:** every `PreState` passed to `executeBlock` is the witness backend rooted at `parent_header.state_root`; `ChainContext.blockHashes` equals `witness.headers.map keccak256` with `last = keccak(rlp parent)`.

## 9. Open decisions

- **D14** (accepted): this module is where the O-table becomes constructors, including the enumerated O13 faults. Local choices: O2 is represented by a totality theorem, not a constructor (open: prove it, DECISIONS §3 O2); every payload-transaction decode failure is attributed to `invalidVersionedHashes` because that is where EELS first consumes it.
- **D5** (provisional, broad): every keccak here goes through `KeccakQuery`: the header-chain hashes (R4), the block-hash check (`isValidBlockHash`), the transactions/withdrawals trie roots in `payloadHeader`, the BAL hash and the witness DB builds (F18). See `EthSecurity`.
- **D13** (runner shape): fuel is internal to the runner; fuel exhaustion reaches this module only as `InternalError` in `CheckedT` (O11).
- **D8**, **D19** (witness errors, eager decoding): consumed through `BlockError.witness`.
- **D3** (Amsterdam only): the previous-fork header is the one place a second fork's type appears; it is decoded only, never executed.
- **D18** (implementation policy): no local debt expected.
- Public diagnostic `classify`: resolved, DECISIONS B12 (Q4).
- Fork-activation check: resolved, DECISIONS Q5 (follow the reference; explicit exclusion, CONTRACT §5).

## 10. Gaps

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **Fork activation (explicit exclusion).** The guest never checks the payload timestamp against Amsterdam activation (`stateless.py:275–277`), and nothing checks that witness headers belong to the forks their shape suggests. A payload from before activation, or a chain whose parent header is of the previous-fork shape at any timestamp, is validated with Amsterdam rules. The spec follows the reference; any consumer claiming "valid Ethereum block" must add this check or take it as an external anchor (CONTRACT §7).
- **Previous-fork fallback is shape-based.** `_decode_header` tries the BPO5 header shape only. The BPO2 and BPO5 `Header` classes have the same 21 fields (checked by parsing both at e1a316a0 [V]), and the shape has been unchanged since `requests_hash` was added, so any post-Prague header decodes through the fallback [I: Prague/Osaka not parsed]; an older shape (fewer fields) is O3. Whether the fallback should be restricted to the *parent* position, or to headers before activation, is unspecified upstream; the spec accepts it anywhere, as EELS does.
- **`DecodingError` versus other exceptions in `_decode_header`.** The fallback fires only on `rlp.DecodingError`. If `ethereum-rlp` 0.1.6 raises another exception type for some malformed Amsterdam header (for example from a field constructor), EELS skips the fallback; the output is the same (inner failure), but the constructor differs. Unchecked.
- **Missing BLOCKHASH ancestor** is a Python negative-index `IndexError` (`vm/instructions/block.py:58`), fixture-witnessed. It is O13 with the named constructor `VmFault.ancestorHashUnavailable` (`EthVmCore`/`EthVmInstructions`), not O4 or O6 (R5). Note that an ancestor deeper than the witness but within 256 blocks fails the block, while one beyond 256 returns zero without touching the witness.
- **O2** has no fixture and no reachable spec path; L-root is unproved (open, DECISIONS §3 O2). If a future SSZ type made `hash_tree_root` partial (e.g. a resource limit), the constructor would be needed.
- **O12 candidates (DISC-001, unresolved).** The guest-process recursion limit is 100,000 (py_ecc raises it; `import ethereum` alone gives 12,288). (a) Deep RLP nesting in a witness header or transaction: 20,000 levels decode and 40,000 raise `RecursionError` in `ethereum-rlp` (witnessed by probe inputs). For a transaction it is caught inside `is_valid_versioned_hashes` and becomes O6 (DISC-006); for a header, in the inner phase. Since valid headers and transactions have bounded nesting, the output probably coincides with the spec's structural failure [I]. (b) Eager witness decoding (`incremental_mpt.py:892–1026`) has no depth or key-length bound; a finite, acyclic DB with a deep chain of nested hashed nodes reachable from a crafted parent `state_root` would make EELS raise `RecursionError` (→ `false`), while a spec decoder without a depth limit could accept it. The depth at which this happens under the 100,000 limit has not been re-measured (the earlier "~1,000 nodes" estimate predates it). This is a guest-level divergence on crafted inputs, uncovered by fixtures, and needs a reproducer and a decision with `EthStateWitness`.
- **Input size envelope.** Transactions, the BAL bytes and the progressive lists are unbounded in SSZ; the largest fixture input is 8.4 MB. There is no stated maximum input, memory or cycle envelope; `EthBase`'s `Envelope` record does not yet cover the guest.
- **SSZ progressive types.** Correctness of `ProgressiveContainer`/progressive-list decoding and merkleization rests on `eth-remerkleable` 0.1.31 (EIP-7495/EIP-7916 as implemented there). `EthCodec` must specify them; no independent reference is pinned.
- **`payloadHeader` totality** is inferred: EELS catches any exception there, and the spec asserts none can occur on decoded values. Needs a line-by-line check of `Header` field constructors (e.g. `Uint`/`U256` widening, `Bytes8`).
- **Order of `legacyDecode`.** `_payload_transaction_to_block_transaction` asserts the decoded type is legacy; after `is_valid_versioned_hashes` succeeds this is believed dead [I]; unproved.
- **Hint equivalence** (L-hint-equivalence) depends on `EthBlock` proving that the reference key check (`transactions.py:931–932`) accepts exactly the recovered key; the cheaper checks CONTRACT §2 permits are not specified.
- **Error-constructor fidelity is untestable by fixtures** (R8); only reading and `core` cases check it.
- **F20 implementation/refinement:** implement L-constants and establish witness, provider and context coherence at the R5 boundary. DECISIONS §6 records the design; production refinement and generic oracle coupling remain open.
- **Consumer seams.** The exact `Faithful` statement evm-asm and pancaketh want (bytes-level equality versus `classify`-level) is not agreed with them; toolchain skew (they are on v4.33.x) is not addressed here.
- **Upstream churn.** `ExecutionPayloadHeader`/`NewPayloadRequestHeader` are TODO scaffolding (`stateless.py:78–100`) and EIP-7709 may empty `headers`; either change alters this module's wire types.
