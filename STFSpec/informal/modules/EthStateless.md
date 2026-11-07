# `EthStateless`: the stateless guest (bytes → bytes), payload validation and header chain

*Status: informal specification, draft; protocol fork metadata, input wire-limit aliases, raw execution witness, five request-item carriers, request aggregate, raw payload/request carriers, raw StatelessInput and actual input/witness/payload/request-item/aggregate/new-payload SSZ dictionaries with Q81 certificates, output record, serializer and zero sentinel supplied; guest unimplemented. Date: 2026-11-07. Pin: `tests-zkevm@v21.0.6` @59c1473d. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F1, F2, F4, F13, F14, F18, F20 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D3, D5, D8, D13, D14, D18, D19 · questions: B12 (Q4), Q5, Q6/Q20, Q80, Q81, Q87, Q88, O2, O13.*

Source references are to `src/ethereum/forks/amsterdam/` unless another path is given. **[V]** marks a claim checked by reading the pinned source or by running the pinned EELS or the pinned fixtures (environment and reproduction: [REVIEW §2](../REVIEW.md)); **[I]** marks an inference. EELS `file:line` citations are at `59c1473d` except where marked and those listed in `STFSpec/informal/citation-remap-manual.txt`, which are still at `e1a316a0` (`tests-zkevm@v21.0.0`); verified observations are at `e1a316a0` unless marked as at `59c1473d` (GAPS-CROSSCUTTING X16).

## 1. Purpose

`EthStateless` is layer L7 of `ARCHITECTURE.md` §2: the guest. It owns the wire types of the stateless protocol (`StatelessInput`, `ExecutionWitness`, `StatelessValidationResult`, and the engine-API `NewPayloadRequest`/`ExecutionPayload`/`ExecutionRequests` containers they embed), their decoding from `schema_id ++ SSZ` and encoding of the 43-byte result, the witness header-chain check, the conversion of a `NewPayloadRequest` into an execution-layer `Block` (block-hash and versioned-hash checks), and the composition of these with the witness-state backend and `executeBlock`. Its public seam is `runStatelessGuest : ByteArray → ByteArray` (`STFSpec/informal/CONTRACT.md` §1), split into decode, verify and encode, with a checked runner `runStatelessGuestChecked` that separates spec-internal errors (O11) from Ethereum outcomes. It is the top-level refinement target for evm-asm and pancaketh.

## 2. Requirements

**R1. Signature and totality.** `runStatelessGuest` must be a total, deterministic Lean function `ByteArray → ByteArray` that reads no environment and always returns exactly 43 bytes (`stateless_guest.py:53–64` [V]; CONTRACT §1, §3). It must be defined as the projection of `runStatelessGuestChecked : ByteArray → Except InternalError ByteArray`, mapping `.error _` to the zero sentinel (CONTRACT O11). Conformance must call the checked runner.

**R2. Input decoding (O1).** `deserializeStatelessInput` must follow `stateless_guest.py:26–38` [V], in order:
1. fewer than 2 bytes → `DecodeError.missingSchemaId`;
2. the first two bytes read **big-endian** must equal `STATELESS_INPUT_SCHEMA_ID = (ProtocolFork.Amsterdam = 0x15) << 8 | 0x01 = 0x1501` (`stateless.py:129–138`), else `unsupportedSchema id`;
3. the rest must be the **canonical** SSZ encoding of `StatelessInput`. `SszContainer.decode_bytes` (`utils/ssz.py:133–141` [V]) decodes with remerkleable and then rejects any input whose re-encoding differs ("offset gaps and … bytes unread"). So offset gaps, shifted offsets, trailing bytes, oversize items and oversize lists all fail here. The spec's SSZ decoder (owned by `EthCodec`) must accept exactly the canonical encodings; `EthStateless` requires the law `decode b = .ok x ↔ encode x = b` (with `x` satisfying the type limits).

Limits that must be enforced by decoding, not later: witness state nodes ≤ `MAX_BYTES_PER_WITNESS_NODE = 2^10` bytes each; codes ≤ `MAX_BYTES_PER_CODE = 2^16`; headers ≤ `MAX_BYTES_PER_HEADER = 2^10` each and at most `MAX_WITNESS_HEADERS = 256` of them (`ssz_list(256)`); `extra_data` ≤ `MAX_EXTRA_DATA_BYTES = 32` (`execution_engine/types.py:33, 62`). The `state`, `codes`, `versioned_hashes`, `transactions`, `withdrawals`, `block_access_list` and all request lists are **progressive lists** (EIP-7916 shape) with no length limit, and each transaction is a `progressive_byte_list` with no size limit (`types.py:65–72` [V]). `ExecutionPayload` and `ExecutionRequests` are **progressive containers** (`ProgressiveSszContainer`, all fields active; `utils/ssz.py:245–246` [V]); the other containers are ordinary SSZ containers. Any failure maps to the zero sentinel.

**R3. Request root (O2).** `computeNewPayloadRequestRoot` must return SSZ `hash_tree_root(new_payload_request)` (`stateless.py:210–216`). It is outside the inner handler in EELS (`stateless.py:261–263`), so a failure there gives the sentinel. In the spec it is a total function of a decoded value, so O2 has no reachable constructor; the spec must *prove* this ([T] L-root) rather than silently drop the row, and adds a constructor only if that proof fails (DECISIONS §3, O2). L-root must discharge the two candidate sites that the failure ledger (maintained outside this repository) leaves unresolved at `stateless.py:216` (the `hash_tree_root()` call and the `Hash32(…)` constructor). The only EELS test reaching O2 monkeypatches `hash_tree_root` to raise (`tests/json_loader/test_stateless_guest.py:558–578` [V]); it has no spec analogue.

**R4. Header chain (O3, O3a).** `validateHeaders` must follow `stateless.py:230–252` [V] exactly:
1. assert `len ≤ 256` (defensive: unreachable from valid SSZ; CONTRACT §4 precedence);
2. decode **every** header first, each by `_decode_header` (`:219–227`): try the Amsterdam `Header`, and on `rlp.DecodingError` only, the previous-fork header `forks/bpo5/blocks.py::Header` (owned by `EthBlock`). The first failing header (in list order) fails the phase;
3. compute `block_hashes[i] = keccak256(encoded_headers[i])` of the **raw bytes** (not a re-encoding);
4. for `i ≥ 1`, require `headers[i].parent_hash = block_hashes[i-1]`, failing at the first `i`.

Because all decodes precede all contiguity checks, a malformed header at position j beats a contiguity break at i < j. The previous-fork fallback is what admits the BPO2→Amsterdam transition parent: in the pinned corpus 186 guest records in `for_bpo2toamsterdamattime15k` have a last witness header that does not decode as an Amsterdam header [V].

An **empty** header list passes `validate_headers`, and EELS then fails on `decoded_headers[-1]` (`stateless.py:274`, `IndexError`) inside the inner handler. The spec must have an explicit constructor `StatelessError.missingParentHeader` with output `(root, false, chain_id, 0x1501)` (O3a). The fixture `validation_headers_empty_block_missing_mandatory_parent` pins this [V].

**R5. Guest composition (`verify_stateless_new_payload`, `stateless.py:255–302` at `59c1473d` [V: read]).** After R3, and all inside the inner phase:
- `parent_header := decoded_headers[-1]`;
- `ChainContext{chain_id := input.chain_id, block_hashes := all witness header hashes, oldest first, parent_header}` (`fork.py:138–150`). `block_hashes` has between 1 and 256 entries; `BLOCKHASH` indexes it from the end (`vm/instructions/block.py:56–63` [V]), and an ancestor missing from the witness is a Python `IndexError` (`vm/instructions/block.py:58`) consumed by the inner handler → failure (fixture `test_validation_headers_invalid_ancestor_chain[…-missing_oldest_blockhash_ancestor]` (`eip8025_optional_proofs/witness_validation_headers/validation_headers_invalid_ancestor_chain.json`; `validation_headers_missing_oldest_blockhash_ancestor` at v21.0.0); [V] at v21.0.0 under the old name). It is a **CONTRACT O13** fault, not a witness error: the constructor is `VmFault.ancestorHashUnavailable` (`EthVmCore`), reaching this module as `.block (.vmFault (.ancestorHashUnavailable _))`;
- acquire `consts ← HashConsts.query` once after R4 succeeds and the nonempty parent is selected, before either witness DB is built (F20; Lean seam, no EELS step). Earlier failures make no acquisition; a run that fails after acquisition has still made the constant queries. Each run acquires independently, without caching the record;
- the pre-state is `WitnessState(node_db = build_node_db(witness.state), state_root = parent_header.state_root, code_db = build_code_db(witness.codes))` (`witness_state.py:28–35`; `build_node_db` is specified by `EthCommit` as `NodeDB.build`, the rest by `EthStateWitness`). In the spec, `NodeDB.build` (`EthCommit`) and `CodeDB.build` (`EthStateWitness`) hash through the oracle and are monadic (D5, F4), and the already-acquired `consts` is stored in the backend. Identical duplicate preimages collapse. Distinct preimages with the same hash use last-wins dictionary insertion, so order independence requires excluding such collisions (EthCommit C12);
- call `executeNewPayloadRequest consts req preState ctx`, following the three source arguments at `stateless.py:288–292` and `execution_engine/new_payload.py:70–74` at `59c1473d` [V: read]. Input hint retirement follows CONTRACT §2/P1 and CONTRACT O5; the caller and execution kernels remain unimplemented;
- success → `(root, true, chain_id, 0x1501)` (O10); any failure → `(root, false, chain_id, 0x1501)` (O3–O7, O13).

**R6. No fork-activation check.** The spec must **not** check the payload timestamp against fork activation, following `stateless.py:267–269` ("A real implementation MUST do these checks!"). This is recorded as an explicit exclusion (CONTRACT §5; Gaps).

**R7. `execute_new_payload_request` (`execution_engine/new_payload.py:70–127` at `59c1473d` [V: read]).** In order:
1. if any payload transaction is the empty byte string → `InvalidBlock("Empty transaction in payload")`;
2. `is_valid_block_hash` (`:23–42`): build the implied header with `_payload_header` (`validation_helpers.py:23–85`): transactions root and withdrawals root as unsecured tries keyed by `rlp(Uint(i))` (with `rlp(withdrawal)` values), `requests_hash = compute_requests_hash(encode_execution_requests(requests))`, `block_access_list_hash = keccak256(payload.block_access_list)` of the **raw bytes**, the fixed post-merge fields (`ommers_hash = EMPTY_OMMER_HASH`, in the spec `HashConsts.emptyOmmerHash`, F2; `difficulty = 0`, `nonce = 0^8`), and the rest copied from the payload; then require `keccak256(rlp(header)) = payload.block_hash`. Any exception while building the header returns `False` [V]; in the spec `payloadHeader` is total on decoded values [I], so `isValidBlockHash` is an equality test;
3. `is_valid_versioned_hashes` (`:45–67`): decode **every** transaction with `decode_transaction` (`transactions.py:557–582`); any failure (unknown type byte, `assert tx[0] ≤ 0xFE`, RLP error, `RecursionError` from deep nesting) → `False` (`except Exception`, `new_payload.py:55–63`). Otherwise concatenate `blob_versioned_hashes` of blob transactions in order and compare with `versioned_hashes` as sequences. So, on the guest path, **every** deterministic payload-transaction decode failure is reported in *this* phase, as `invalidVersionedHashes` (O6), and `EthBlock`'s `txDecode` constructors are reachable only from a standalone `executeBlock` (EthBlock R-TX-DEC). The same catch-all also absorbs host failures (`MemoryError`, `RecursionError`), which then look like O6 (DISC-006; O12 stays unresolved, DISC-001);
4. `_payload_block` (`validation_helpers.py:100–122`): the block's transactions are the raw bytes, except that a transaction whose first byte is ≥ `0xC0` becomes a decoded `LegacyTransaction` (`:88–97`), `ommers = ()`, withdrawals as given;
5. `execute_block(block, pre_state, chain_context)` (`execution_engine/new_payload.py:122–127` at `59c1473d` [V: read], owned by `EthBlock`), whose `BlockDiff` and the block are returned.

The payload's BAL bytes are only hashed at this level; `execute_block` compares the hash of the *computed* BAL with the header's (`fork.py:355–356`). Execution requests are committed only through `requests_hash` in the header, hence through `block_hash` (docstring `types.py:215–218`).

**R8. Outcome mapping.** Every CONTRACT §4 row must be an explicit path (§7 table), including each enumerated O13 fault. No catch-all; phase precedence as in the pinned EELS order (CONTRACT §4 "Failure precedence"). All inner failures (O3–O7, O13) produce byte-identical outputs, so fixtures cannot observe the constructor chosen; constructor order is a spec-fidelity obligation checked by `core` tests against a reading of EELS, not by the corpus.

**R9. O12 (Python runtime failures).** No behaviour may be derived from Python recursion or memory limits without a DISC entry and accepted decision (CONTRACT §6; DISC-001). Witness-reference cycles are O4 (`ARCHITECTURE.md` §5.4). See Gaps for two classes of finite acyclic inputs where host limits and the spec may differ.

## 3. EELS source map

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `forks/amsterdam/stateless.py::MAX_WITNESS_HEADERS` | 32 | `maxWitnessHeaders : Nat` | supplied transparent alias of `Fork.Amsterdam.MAX_WITNESS_HEADERS` (F8); SSZ list limit and R4 assert remain future consumers |
| `forks/amsterdam/stateless.py::MAX_BYTES_PER_CODE` | 33 | `maxBytesPerCode : Nat` | supplied transparent alias of `Fork.Amsterdam.MAX_BYTES_PER_CODE` (F8) |
| `forks/amsterdam/stateless.py::MAX_BYTES_PER_HEADER` | 34 | `maxBytesPerHeader : Nat` | supplied transparent alias of `Fork.Amsterdam.MAX_BYTES_PER_HEADER` (F8) |
| `forks/amsterdam/stateless.py::MAX_BYTES_PER_WITNESS_NODE` | 35 | `maxBytesPerWitnessNode : Nat` | supplied transparent alias of `Fork.Amsterdam.MAX_BYTES_PER_WITNESS_NODE` (F8) |
| `forks/amsterdam/stateless.py::ExecutionWitness` | 41–69 | `ExecutionWitness` (`STFSpec/Stateless/ExecutionWitness.lean`) | supplied unrestricted three-field carrier and actual Q81 dictionary/certificates below |
| `forks/amsterdam/stateless.py::ProtocolFork` | 101–126 | `ProtocolFork`, `ProtocolFork.toIndex : ProtocolFork → UInt8` (`STFSpec/Stateless/ProtocolFork.lean`) | discharged historical 21-constructor carrier and total forward observation of the numeric assignments at 106–126; complete contract and private controls below |
| `forks/amsterdam/stateless.py::STATELESS_INPUT_SCHEMA_FORK_INDEX` | 129 | `schemaForkIndex := ProtocolFork.amsterdam` | |
| `forks/amsterdam/stateless.py::STATELESS_INPUT_SCHEMA_REVISION` | 130 | `schemaRevision : UInt8 := 1` | |
| `forks/amsterdam/stateless.py::STATELESS_INPUT_SCHEMA_ID` | 131 | `schemaId : UInt16 := 0x1501` | `#guard`/`decide` |
| `forks/amsterdam/stateless.py::STATELESS_INPUT_SCHEMA_ID_SIZE` | 134 | `schemaIdSize := 2` | |
| `forks/amsterdam/stateless.py::STATELESS_INPUT_SCHEMA_ID_BYTES` | 135 | `schemaIdBytes : ByteArray := ⟨#[0x15, 0x01]⟩` | big-endian |
| `forks/amsterdam/stateless.py::StatelessInput` | 144–166 | `StatelessInput` (`STFSpec/Stateless/Input.lean`) | supplied exact three-field raw carrier and actual ordinary Q81 dictionary/certificates below; guest remains separate |
| `forks/amsterdam/stateless.py::StatelessValidationResult` | 171–206 | `StatelessValidationResult` (`STFSpec/Stateless/Output.lean`) | supplied: complete four-field carrier; §7 output laws and §4 controls |
| `forks/amsterdam/stateless.py::compute_new_payload_request_root` | 210 | `computeNewPayloadRequestRoot` | total (R3) |
| `forks/amsterdam/stateless.py::_decode_header` | 219 | `decodeHeader` (internal) | fallback only on RLP error |
| `forks/amsterdam/stateless.py::validate_headers` | 230 | `validateHeaders` | R4 |
| `forks/amsterdam/stateless.py::verify_stateless_new_payload` | 255 | `verifyStatelessNewPayload{,Checked}` | R5 |
| `forks/amsterdam/stateless_guest.py::serialize_stateless_output` | 19–23 | `serializeStatelessOutput` (`STFSpec/Stateless/Output.lean`) | supplied on every raw carrier value; §7 complete layout/size/injectivity laws; §4 whole-byte controls |
| `forks/amsterdam/stateless_guest.py::_default_failed_stateless_output` | 41–50 | `zeroSentinel` (`STFSpec/Stateless/Output.lean`) | supplied; §7 complete field and byte equations; §4 controls |
| `forks/amsterdam/stateless_guest.py::deserialize_stateless_input` | 26–38 | `deserializeStatelessInput` | open |
| `forks/amsterdam/stateless_guest.py::run_stateless_guest` | 53–64 | `runStatelessGuest{,Checked}` | open |
| `forks/amsterdam/execution_engine/new_payload.py::is_valid_block_hash` | 23 | `isValidBlockHash` | |
| `forks/amsterdam/execution_engine/new_payload.py::is_valid_versioned_hashes` | 45 | `isValidVersionedHashes` | |
| `forks/amsterdam/execution_engine/new_payload.py::execute_new_payload_request` | 70 | `executeNewPayloadRequest` | backend-generic |
| `forks/amsterdam/execution_engine/types.py::MAX_EXTRA_DATA_BYTES` | 33 | `maxExtraDataBytes : Nat` | supplied transparent alias of `Fork.Amsterdam.MAX_EXTRA_DATA_BYTES` (F8); payload SSZ limit |
| `forks/amsterdam/execution_engine/types.py::ExecutionPayload` | 39–72 | `ExecutionPayload` (`STFSpec/Stateless/Payload.lean`) | supplied exact unrestricted nineteen-field carrier and actual progressive Q81 dictionary/certificates below |
| `forks/amsterdam/execution_engine/types.py::NewPayloadRequest` | 78–96 | `NewPayloadRequest` (`STFSpec/Stateless/Payload.lean`) | supplied exact unrestricted four-field carrier and actual ordinary Q81 dictionary/certificates below |
| `forks/amsterdam/execution_engine/validation_helpers.py::*` | 23–122 | `payloadHeader`, `payloadTransactionToBlockTransaction`, `payloadBlock` (internal) | whole file |
| `forks/amsterdam/execution_engine/requests.py::DepositRequest` | 42 | `DepositRequest` (`STFSpec/Stateless/RequestItems.lean`) | supplied raw carrier; exact constructor/projection domain and private clients below |
| `forks/amsterdam/execution_engine/requests.py::WithdrawalRequest` | 55 | `WithdrawalRequest` (`STFSpec/Stateless/RequestItems.lean`) | supplied raw carrier; exact constructor/projection domain and private clients below |
| `forks/amsterdam/execution_engine/requests.py::ConsolidationRequest` | 66 | `ConsolidationRequest` (`STFSpec/Stateless/RequestItems.lean`) | supplied raw carrier; exact constructor/projection domain and private clients below |
| `forks/amsterdam/execution_engine/requests.py::BuilderDepositRequest` | 77 | `BuilderDepositRequest` (`STFSpec/Stateless/RequestItems.lean`) | supplied raw carrier; exact constructor/projection domain and private clients below |
| `forks/amsterdam/execution_engine/requests.py::BuilderExitRequest` | 89 | `BuilderExitRequest` (`STFSpec/Stateless/RequestItems.lean`) | supplied raw carrier; exact constructor/projection domain and private clients below |
| `forks/amsterdam/execution_engine/requests.py::ExecutionRequests` | 99 | `ExecutionRequests` (`STFSpec/Stateless/ExecutionRequests.lean`) | supplied unrestricted five-array carrier; actual Q81 dictionary and certificates below |
| `forks/amsterdam/execution_engine/requests.py::encode_execution_requests` | 148 | `encodeExecutionRequests` | empty lists omitted, ascending type |

**Supplied wire-limit aliases.** `STFSpec/Stateless/WireLimits.lean` exports the
five §5 `Nat` aliases through `STFSpec.Stateless`. Their bodies are exactly the
qualified Fork constants in the source-map rows, with no local numeric literals.
The lowerCamelCase names retain the planned consumer interface and deliberately
depart from EELS constant spelling (CONTRIBUTING §7.2). EthFork §3 owns the values.
The aliases have no inputs, effects, failures or proof premises. They enforce no
bounds on the raw witness; the actual witness dictionary below consumes them, independently of decoding.

**Supplied protocol fork metadata.** `STFSpec.Stateless.ProtocolFork` admits exactly
the 21 nullary constructors below, with no precondition or default. The explicit
total match `ProtocolFork.toIndex` returns the corresponding core `UInt8` literal:

```text
frontier=0x01, homestead=0x02, daoFork=0x03, tangerineWhistle=0x04,
spuriousDragon=0x05, byzantium=0x06, stPetersburg=0x07, istanbul=0x08,
muirGlacier=0x09, berlin=0x0a, london=0x0b, arrowGlacier=0x0c,
grayGlacier=0x0d, paris=0x0e, shanghai=0x0f, cancun=0x10,
prague=0x11, osaka=0x12, bpo1=0x13, bpo2=0x14, amsterdam=0x15.
```

EELS `stateless.py:101–126` at `59c1473d` supplies this complete inventory and its
explicit tags [V: read]. All historical values are admitted; tags are not zero-based
constructor ordinals. Constructor names use lowerCamelCase, including `DAOFork` →
`daoFork`, `StPetersburg` → `stPetersburg`, `BPO1` → `bpo1` and `BPO2` → `bpo2`.
`toIndex` is a Lean forward observation of source `IntEnum` values, not a source
function. Construction and observation have no effects, failures, handler or O-row.
Ordinary reduction and the private complete clients in §4 discharge this finite
data contract; no public law family or instance is added. Python integer equality,
arithmetic, reflection and numeric construction are outside this correspondence.
Schema selection, wire admission and guest execution remain separate (§10).

**Supplied raw execution witness.** `STFSpec.Stateless.ExecutionWitness` has exactly
`state`, `codes`, `headers : Array ByteArray`, in that order, with required independent
arguments and no defaults or derived instances. EELS `stateless.py:41–69` at
`59c1473d` supplies the source field names/order and raw byte collections [V: read].
The accepted raw domain is every triple of finite arrays of complete byte arrays,
including empty arrays, empty members, duplicates, malformed RLP and lengths outside
the wire limits. Construction/projection retain the supplied arrays exactly;
reconstruction and each independent update reduce to the complete expected record.
There are no effects or failures, hence no handler or O-row. This raw contract is
discharged by the structure and the private facade clients in §4; it adds no public
helper laws, wire admission or source-runtime agreement claim. The separate dictionary below supplies its Q81 certificates.

**Supplied raw request items.** `STFSpec/Stateless/RequestItems.lean`, exported by
`STFSpec.Stateless`, supplies exactly the five distinct nominal structures below.
All field names and their source order come from EELS
`execution_engine/requests.py:42–95` at `59c1473d` [V: read]. Underscored source
fields use the lowerCamelCase spelling in §5 (CONTRIBUTING §7.2).

| Public constructor | Complete type | Private evidence |
|---|---|---|
| `DepositRequest.mk` | `Bytes48 → Bytes32 → U64 → Bytes96 → U64 → DepositRequest` | complete five-field construction, reconstruction, observations and each update; independent amount/index controls |
| `WithdrawalRequest.mk` | `Address → Bytes48 → U64 → WithdrawalRequest` | complete three-field clients and controls |
| `ConsolidationRequest.mk` | `Address → Bytes48 → Bytes48 → ConsolidationRequest` | complete three-field clients and controls, including distinct source/target keys |
| `BuilderDepositRequest.mk` | `Bytes48 → Bytes32 → U64 → Bytes96 → BuilderDepositRequest` | complete four-field clients and controls; no index |
| `BuilderExitRequest.mk` | `Address → Bytes48 → BuilderExitRequest` | complete two-field clients and controls; no amount or signature |

Each field in §5 has the projection type `RequestType → FieldType`, with the
corresponding nominal request type. Credentials are `Bytes32`, independently of
`Hash32`. The domain is every combination of canonical existing Base values:
complete 20/32/48/96-byte contents and all `U64` observations. This includes leading
zeros, cryptographically invalid keys/signatures/credentials, zero amounts and
unrelated amount/index values. Amounts are stored unchanged, without unit conversion.
There are no effects, failures, handlers or O-rows for raw construction/projection.
The identity model is the ordered tuple of whole fields, observed through complete
byte lists and unsigned numbers. Ordinary generated structure operations and the
private §4 clients discharge this contract. No authored public helper, law, instance,
default, proof argument, validator or schema is supplied.

Static source reading establishes this field correspondence. Python reflection,
mutable/frozen dataclass behaviour, annotation enforcement, cached SSZ views and
source-host execution agreement remain separate. The raw carriers supply no BLS,
credential-prefix, builder-eligibility, balance or index-relation admission. The five actual Q81 dictionaries/certificates, private operation-support clients
and aggregate schema are supplied independently below. Wire constants/engine
encoding, raw decoding, roots, payload/input and guest remain open (§10).

**Supplied raw execution requests.** `STFSpec/Stateless/ExecutionRequests.lean`,
exported by `STFSpec.Stateless`, supplies exactly the §5 five-array structure.
EELS `execution_engine/requests.py:99–121` at `59c1473d` fixes the complete order
and nominal item types [V: read]. Source `builder_deposits` and `builder_exits`
use `builderDeposits` and `builderExits` (CONTRIBUTING §7.2).

| EELS source at `59c1473d` | Lean declaration | Domain, effects and failures | Law and regression |
|---|---|---|---|
| `execution_engine/requests.py:99–121` | `ExecutionRequests.mk : Array DepositRequest → Array WithdrawalRequest → Array ConsolidationRequest → Array BuilderDepositRequest → Array BuilderExitRequest → ExecutionRequests`; the five projections have exactly the corresponding `ExecutionRequests → Array Item` types | every independent ordered array of existing nominal items, including empty arrays, duplicates and unequal counts; pure construction/projection with no failures or O-row | generated structure operations and private arbitrary complete clients (§7); whole finite controls (§4) |

The identity model is the ordered tuple of all five complete arrays. Each array
retains the raw item domain described above, without an additional invariant,
count cap, normalization, cryptographic check or amount conversion. Static reading
establishes field correspondence; source reflection, class/cache/coercion/backing
and host agreement remain separate. No schema, codec, helper, derived instance or
authored public law is supplied by this carrier.

**Supplied raw payload and request.** `STFSpec/Stateless/Payload.lean`, exported
by `STFSpec.Stateless`, supplies exactly the two nominal structures in §5.
Their field order and lowerCamelCase names correspond to EELS
`execution_engine/types.py:39–96` at `59c1473d` [V: static reading].

| EELS source at `59c1473d` | Lean declaration | Domain, effects and failures | Contract and regression |
|---|---|---|---|
| `execution_engine/types.py:39–72` | `ExecutionPayload.mk`, exactly the nineteen ordered §5 field types; each projection is `ExecutionPayload → FieldType` | all existing Base values, finite byte arrays and ordered arrays of complete actual `Block.Withdrawal`; pure raw storage, no failure, effect, handler or O-row | ordered whole-field identity model; private arbitrary complete constructor/projection, reconstruction/determination, update/observation and conversion clients, plus whole finite controls (§4/§7) |
| `execution_engine/types.py:78–96` | `NewPayloadRequest.mk : ExecutionPayload → Array Base.VersionedHash → Base.Hash32 → ExecutionRequests → NewPayloadRequest`; four exact projections in §5 | every independent combination of whole payload, versioned hashes, beacon root and actual aggregate; pure raw storage, no failure, effect, handler or O-row | ordered whole-field identity model; private complete clients and nested-value controls (§4/§7) |

All nineteen/four fields are independent. The raw domain includes extraData longer
than 32 bytes, empty or malformed transaction and BAL bytes, gasUsed greater than
gasLimit, unrelated roots/hashes/bloom, arbitrary fees and unsigned endpoints,
duplicate/reordered withdrawals and versioned hashes, including version bytes other
than 0x01. No normalization, sorting, truncation, hashing, parsing, validation, cap,
amount conversion, proof field, default, derived instance or authored public helper
or law is supplied. Actual `Block.Withdrawal` and `ExecutionRequests` retain their
owners; neither is duplicated or replaced by a lookalike.

The chosen `U64` payload timestamp follows §5's uint64 annotation despite the
source's broader Python U256 class; baseFeePerGas retains the guided `U256`.
Static field correspondence does not establish runtime/source-object agreement
outside annotated wire domains, Python class/reflection/coercion/cache/backing
behaviour or host agreement. Progressive masks and SSZ limits belong to separate
schemas; the actual payload and request dictionaries are supplied below. Support, codecs/roots, request validation, conversion to Header,
guest composition and resource/security/readiness remain separate (§10).

**Supplied raw stateless input.** `STFSpec/Stateless/Input.lean`, exported by
`STFSpec.Stateless`, supplies exactly the three-field nominal structure in §5.
EELS `stateless.py:144–166` at `59c1473d` fixes the source order and types [V: read].
Source `new_payload_request` and `chain_id` use the lowerCamelCase names below
(CONTRIBUTING §7.2).

| EELS source at `59c1473d` | Lean declaration | Domain, effects and failures | Contract and regression |
|---|---|---|---|
| `stateless.py:144–166` | `StatelessInput.mk : NewPayloadRequest → ExecutionWitness → Base.U64 → StatelessInput`; `newPayloadRequest : StatelessInput → NewPayloadRequest`, `witness : StatelessInput → ExecutionWitness`, `chainId : StatelessInput → Base.U64` | every independent combination of the actual complete providers; pure raw storage, no failure, effect, handler or O-row | ordered whole-three-field identity model; private arbitrary construction/reconstruction/determination and each whole-field update (§7); complete nested finite controls (§4) |

The raw domain includes every provider value: malformed/oversized opaque bytes,
empty/duplicate/reversed/unequal nested arrays and every `Base.U64`, including zero
and maximum. The chain ID is the existing nominal unsigned type, with no conversion
or chain policy. There is no additional invariant, default, derived instance,
proof field, helper or authored public law family. Construction/projection retain
each whole field, and each update preserves both siblings. Static field
correspondence supplies no Python class/reflection/cache/coercion/backing, host,
decoding or guest agreement. Input schemas, support, codecs/roots, validation and
all resource/security/readiness obligations remain separate (§10).

**Supplied execution witness SSZ dictionary.**
`STFSpec/Stateless/ExecutionWitnessSsz.lean`, exported by `STFSpec.Stateless`, supplies
exactly the named `ExecutionWitness.instSszSchema` and the three §7 certificates.
The actual five fields are specified in §5. The descriptor is an ordinary container,
with progressive state/code lists and a bounded header list. Validity imposes only
the four payload bounds, with no outer state/code count bound, serialization/root
support or source-host premise. The raw carrier remains unrestricted.

| EELS source at `59c1473d` | Lean declaration | Domain, effects and failures | Law and regression |
|---|---|---|---|
| `stateless.py:41–69`; `src/ethereum/utils/ssz.py:174–253,258–320` | `ExecutionWitness.instSszSchema : Codec.SszSchema ExecutionWitness` | pure metadata and complete ordered adapters; payload domain in §5; no decoder, runtime bounds validator or O-row | three actual-dictionary certificates below; complete facade clients and controls in §4 |
| `src/ethereum/utils/ssz.py:174–253` (structural interpretation, Q81) | `ExecutionWitness.ssz_type_wellFormed` | no premise; actual descriptor WF | §7 exact type; independent descriptor/names/Fork-limit controls |
| `src/ethereum/utils/ssz.py:258–320` (typed adapters, Q81) | `ExecutionWitness.ssz_ofValue_toValue` | actual validity premise; complete reconstruction and WT image | §7 exact type; arbitrary whole-array clients and full finite recovery controls |
| `src/ethereum/utils/ssz.py:258–320` (typed adapters, Q81) | `ExecutionWitness.ssz_toValue_ofValue` | actual WT plus successful reconstruction; validity and complete value preservation | §7 exact type; arbitrary whole-value clients and malformed-shape controls |

These names identify the Lean dictionary/certificates, rather than separate EELS
functions. The private total inverse accepts exactly three list-shaped fields,
extracts every byte-tagged member unchanged and converts each whole ordered list
to an Array. A wrong shape/tag returns `none`. Its shape-only behaviour on overbound
byte-tagged values is checked privately; Q81's public reverse certificate retains
both WT and successful reconstruction. No additional public rejection/image policy
or completeness law is supplied. The forward adapter visits each member once per
field, with no byte copying, sorting, deduplication, hashing or RLP/header decoding.

[V: static source reading at the pin] The correspondence uses the actual annotations,
normal dataclass field order/type-hint reflection, coherent source caches and intended
byte values. Typed view construction, uint256-backed progressive counts, dependency
endian/offset behaviour and sufficient host memory/stack remain source-host premises.
Installed dependency RECORD agreement is self-consistency, rather than independent
archive authentication. No EELS/dependency/guest execution is claimed for this slice.
Payload validity and the three certificates supply neither Serializable nor Rootable.
Q80 separately requires every emitted inner and outer start below 2^32, without
a final whole-size bound. Q78's count bounds and source backing representability
remain separate. No such condition is added to this carrier or validity predicate.

**Supplied execution payload SSZ dictionary.** `STFSpec/Stateless/PayloadSsz.lean`,
exported by `STFSpec.Stateless`, supplies exactly `ExecutionPayload.instSszSchema`
and the three Q81 certificates in §7. Its five metadata fields are given in §5.
The model is the complete ordered nineteen-member container. The actual Block-owned
Withdrawal dictionary supplies its descriptor and both adapters; no child schema
is duplicated. Construction and observation preserve every byte, unsigned value,
ordered member, duplicate and empty member.

| EELS source at `59c1473d` | Lean declaration | Domain, effects and failures | Law and regression |
|---|---|---|---|
| `execution_engine/types.py:39–72`; `src/ethereum/utils/ssz.py:174–255` | `ExecutionPayload.instSszSchema : Codec.SszSchema ExecutionPayload` | pure metadata and complete ordered adapters; validity is exactly §5's extra-data bound; no effect, handler or O-row | discharged descriptor/model; private complete clients and controls in §4 |
| `src/ethereum/utils/ssz.py:174–255` (structural interpretation, Q81) | `ExecutionPayload.ssz_type_wellFormed` | no premise; actual descriptor WF | discharged §7 certificate; actual mask, names and child-provider clients |
| `src/ethereum/utils/ssz.py:258–320` (typed adapters, Q81) | `ExecutionPayload.ssz_ofValue_toValue` | actual wire-valid premise; whole reconstruction and WT image | discharged §7 certificate; arbitrary complete model and checked finite construction/recovery controls |
| `src/ethereum/utils/ssz.py:258–320` (typed adapters, Q81) | `ExecutionPayload.ssz_toValue_ofValue` | actual WT and successful reconstruction, in one conjunction; wire validity and complete re-forwarding | discharged §7 certificate; arbitrary complete value clients and malformed controls |

These are Lean dictionary/certificate names for source structure and typed conversion,
not extra source functions. The private total inverse matches exactly nineteen fields
with their declared tags, checks every fixed byte width and unsigned range using Base
constructors, extracts every transaction byte array and traverses the actual Withdrawal
inverse in order. It preserves extraData and BAL bytes. A shape/tag/constructor failure
returns `none`. This Option adapter is neither a byte decoder nor a guest rejection.
The extra-data bound belongs to validity/WT; private controls exercise the selected
shape-only completion at length 33. The public certificates specify no off-WT
completion or additional rejection/image policy.

Static source correspondence uses intended annotated fields and normal ordered
reflection, coherent source classes/caches/coercions and backing, dependency endian
and serializer behavior, and sufficient host resources. Locally installed dependency
RECORD agreement establishes self-consistency, not wheel-origin authentication. Broader
manual Python numeric objects remain outside the guided seven-U64/one-U256 wire
correspondence. This slice executes no EELS/dependency encoder, parser or guest.

Operation domains remain separate. Q80 requires the four emitted starts
`540`, `540+e`, `540+e+T`, `540+e+T+44w` below `2^32`, with
`T = 4n + sum(transaction lengths)`, and the nested transaction starts owned by Codec.
It adds no final BAL/end cap. Q78 root counts and source backing/host bounds are not
validity conditions. Source parser per-field progressive extents at most `2^32` and
its nonempty variable-list strict scope check remain source-refinement premises,
separate from the mathematical Q80/Q88 domains. No O12 or decoder policy is changed.

**Supplied request-item dictionaries (Q81).**
`STFSpec/Stateless/RequestItemSsz.lean`, reexported by `STFSpec.Stateless`, supplies
exactly five actual dictionaries and three ordinary certificates per dictionary.
Each row lists all four authored public declarations. These are pure metadata
and adapters on every raw typed record, with no execution effects or public error.

| EELS source at the pin | Supplied declarations | Domain, laws and complete controls |
|---|---|---|
| `execution_engine/requests.py:42`; `src/ethereum/utils/ssz.py:174–320` | `DepositRequest.instSszSchema`, `DepositRequest.ssz_type_wellFormed`, `DepositRequest.ssz_ofValue_toValue`, `DepositRequest.ssz_toValue_ofValue` | All `DepositRequest` values; exact §5 metadata and §7 certificate types; full 192-byte comparisons and every field/shape/width/range control in §4 |
| `execution_engine/requests.py:55`; `src/ethereum/utils/ssz.py:174–320` | `WithdrawalRequest.instSszSchema`, `WithdrawalRequest.ssz_type_wellFormed`, `WithdrawalRequest.ssz_ofValue_toValue`, `WithdrawalRequest.ssz_toValue_ofValue` | All `WithdrawalRequest` values; exact §5 metadata and §7 certificate types; full 76-byte comparisons and every field/shape/width/range control in §4 |
| `execution_engine/requests.py:66`; `src/ethereum/utils/ssz.py:174–320` | `ConsolidationRequest.instSszSchema`, `ConsolidationRequest.ssz_type_wellFormed`, `ConsolidationRequest.ssz_ofValue_toValue`, `ConsolidationRequest.ssz_toValue_ofValue` | All `ConsolidationRequest` values; exact §5 metadata and §7 certificate types; full 116-byte comparisons and every field/shape/width/range control in §4 |
| `execution_engine/requests.py:77`; `src/ethereum/utils/ssz.py:174–320` | `BuilderDepositRequest.instSszSchema`, `BuilderDepositRequest.ssz_type_wellFormed`, `BuilderDepositRequest.ssz_ofValue_toValue`, `BuilderDepositRequest.ssz_toValue_ofValue` | All `BuilderDepositRequest` values; exact §5 metadata and §7 certificate types; full 184-byte comparisons and every field/shape/width/range control in §4 |
| `execution_engine/requests.py:89`; `src/ethereum/utils/ssz.py:174–320` | `BuilderExitRequest.instSszSchema`, `BuilderExitRequest.ssz_type_wellFormed`, `BuilderExitRequest.ssz_ofValue_toValue`, `BuilderExitRequest.ssz_toValue_ofValue` | All `BuilderExitRequest` values; exact §5 metadata and §7 certificate types; full 68-byte comparisons and every field/shape/width/range control in §4 |

The source declares ordinary fixed containers [V: source reading at the pin].
Every descriptor retains source order and source field names. Byte vectors use the
complete Base byte observation, and uint fields use the complete `U64.toNat`.
The wire-domain predicate is `True`, because the Base types already enforce all
mathematical lengths and ranges. It imposes no protocol, BLS, signature, credential,
nonzero, amount-scale or cross-field condition.

The private total inverse matches exact container arity and leaf tags. It checks
all byte leaves with `FixedBytes.ofBytes? (Bytes.ofByteArray b)` or nominal
`Address.ofBytes?`, and every uint with `U64.ofNat?`. It constructs the whole raw
record only after all checks succeed. Other patterns or failed checks return
`none`. This completion is private implementation behaviour. Q81 publishes only
the three §7 certificates, retaining the forward validity hypothesis and the
reverse WT-and-success conjunction. No public rejection/image law is added.

The five complete fixed products have widths 192/76/116/184/68 bytes in the row
order. Private public-Codec-law clients establish actual Serializable and
CountRecoverable support and full fixed concatenation on arbitrary records.
Every quantity contributes exactly eight little-endian bytes. No offset or length
prefix is emitted. These are mathematical wire facts, without an EELS/dependency
runtime comparison. Source reflection/cache/class/backing and host agreement,
raw byte decoding (Q88), Rootable and guest composition remain
separate. The aggregate dictionary is supplied below. Installed dependency RECORD agreement does not authenticate a locked
wheel. No resource, security, performance or readiness result follows.


**Supplied execution-request aggregate schema (Q81).**

| EELS source at the pin | Supplied Lean declaration in `STFSpec/Stateless/ExecutionRequestsSsz.lean` | Domain, effects and failures | Law, model and controls |
|---|---|---|---|
| `execution_engine/requests.py:99–121`; `src/ethereum/utils/ssz.py:174–320` | `ExecutionRequests.instSszSchema` | All finite existing aggregates; pure ordered adapters, no public diagnostic or O-row | Exact §5 model/metadata; three §7 certificates; every complete input/field/recovery and all 150780 bytes of the 80 mathematical cases in §4 |
| `src/ethereum/utils/ssz.py:174–253` (structural interpretation) | `ExecutionRequests.ssz_type_wellFormed` | No premise; actual descriptor WF | Exact §7 type; private actual child/mask/field-name clients |
| `src/ethereum/utils/ssz.py:258–291` (forward interpretation) | `ExecutionRequests.ssz_ofValue_toValue` | Actual validity premise; complete reconstruction and WT image; pure | Exact §7 type; private arbitrary whole-array/model clients and complete §4 finite controls |
| `src/ethereum/utils/ssz.py:294–320` (reverse interpretation) | `ExecutionRequests.ssz_toValue_ofValue` | Actual WT-and-success conjunction; complete model preservation and validity; pure | Exact §7 type; actual child certificates with paired WT/success; §4 recovery/malformed controls |

The descriptor uses five progressive lists of the actual named item dictionary
types, in source field order, and a progressive container with five true active
bits [V: pinned source reading]. Names retain source snake_case. The ordered
model maps every complete array member through its actual child dictionary.
Validity is exactly `True`. Counts, ordering, duplicates, empty arrays, unequal
counts, opaque fixed bytes and full unsigned fields add no condition.

The private total inverse matches exactly five list-valued fields, traverses each
actual child inverse in order and constructs all five arrays after complete
success. Other patterns or child failure return `none`. This completion adds no
public rejection or image law. The reverse certificate derives each child's
WellTyped premise from public typing equations and pairs it with actual inverse
success before applying the child's public reverse certificate. The implementation
unfolds no foreign private inverse. All adapters are pure, without hashes,
validation effects or a public diagnostic.

Private ordinary clients establish CountRecoverable on every forward aggregate
and Serializable under exactly the five emitted-start bounds in §5. Mathematical
full-wire controls use actual `SszSchema.encodeBytes`. Rootable, source reflection,
class/coercion/backing, per-field decoder scopes and host success remain separate.
No source/dependency encoder, raw byte decoder, root or guest is executed here.

**Supplied new-payload request dictionary (Q81).**
`STFSpec/Stateless/NewPayloadSsz.lean`, exported by `STFSpec.Stateless`, supplies
exactly `NewPayloadRequest.instSszSchema` and the three §7 certificates. The four-field
ordinary descriptor uses the actual Payload and ExecutionRequests dictionaries,
without an outer progressive mask. §5 gives all five metadata fields.

| EELS source at `59c1473d` | Lean declaration | Domain, effects and failures | Law and regression |
|---|---|---|---|
| `execution_engine/types.py:78–96`; `src/ethereum/utils/ssz.py:174–320` | `NewPayloadRequest.instSszSchema : Codec.SszSchema NewPayloadRequest` | pure ordered metadata/adapters; validity composes both actual child predicates; no effect, handler or O-row | complete §5 model; private facade, boundary and complete wire controls in §4 |
| `src/ethereum/utils/ssz.py:174–255` (structural interpretation, Q81) | `NewPayloadRequest.ssz_type_wellFormed` | no premise; actual descriptor WF | discharged §7 certificate; actual provider identities/order/names |
| `src/ethereum/utils/ssz.py:258–320` (typed adapters, Q81) | `NewPayloadRequest.ssz_ofValue_toValue` | actual validity premise; complete reconstruction and WT image | discharged §7 certificate; arbitrary whole model and finite complete recovery |
| `src/ethereum/utils/ssz.py:258–320` (typed adapters, Q81) | `NewPayloadRequest.ssz_toValue_ofValue` | actual WT and successful reconstruction, in one conjunction | discharged §7 certificate; actual child validity and whole-value re-forwarding |

The model delegates whole child models and retains every versioned hash and root
byte, ordered occurrence, duplicate and empty collection. Validity composes actual
child predicates; their contracts reduce it to the payload extra-data bound. It adds
no version-byte predicate, hash/gas/execution check, count, root, host or final-size
condition. The private total inverse matches exactly four fields and the list/byte
leaf tags, delegates both actual child inverses, traverses checked Base Hash32
constructors for every versioned hash, and checks the root through the same nominal
Base constructor. Wrong shape or a failed checked construction returns `none`.
Public off-WT completion remains unspecified. The reverse certificate derives each
child WT from outer WT independently of reconstruction success, then passes both
premises to each public child reverse certificate. No foreign private helper unfolds.

[V: static reading at the pin] Correspondence assumes intended annotated values,
normal ordered reflection, coherent classes/coercions/caches/backing, dependency
endian/serializer behavior and sufficient host resources. Installed dependency RECORD
agreement is self-consistency, not independent archive authentication. This slice
executes no EELS/dependency encoder, parser or guest. Q80's exact outer head is 44
bytes and its emitted starts are `44`, `44+P`, `44+P+32h`, for actual payload length P
and versioned-hash count h. Every actual nested start retains its own Q80 bound,
including the actual 540-byte payload and 20-byte aggregate heads. There is no final
request/tail cap. Private CountRecoverable holds for every whole forward value,
separately from actual validity, Serializable, Q78 Rootable and source-host bounds.
Q88, O2/O12, F20/D5, fuel/S2, security, resources and readiness remain unchanged.

The decoders and size constants of `execution_engine/requests.py` (engine wire form → typed) are host-side and claimed by `EthConformance`; `verify_and_notify_new_payload` (the stateful path) is claimed by `EthConformance`. Scaffolding types, `forkchoice_update.py`, `get_payload.py` and the unused engine types are excluded in `STFSpec/informal/EXCLUDED.md` with reasons.

**External semantics.** The inventory lists these external uses in the claimed files:
- `ethereum_rlp.rlp` (`stateless.py:9`, `new_payload.py:7`, `validation_helpers.py:7`): `decode_to(Header, ·)` and `encode`. Canonical-form and `DecodingError` behaviour are specified by `EthCodec`; `EthStateless` needs (a) `decode_to` failure on the Amsterdam shape is a *DecodingError* in every case where the fallback must fire [I: needs a check of `ethereum-rlp` 0.1.6 for non-`DecodingError` exceptions, e.g. from field constructors]; (b) `rlp.encode(decode b) = b` for successfully decoded headers, which makes `keccak(raw bytes)` (R4) and `keccak(rlp(parent_header))` (`fork.py:491`) agree.
- `ethereum_types` `Bytes`, `U16`, `U64`, `slotted_freezable`: plain value types; `U16(STATELESS_INPUT_SCHEMA_ID)` and `int.from_bytes(·, "big")` fix the schema-id encoding. `slotted_freezable` has no semantic content.
- SSZ via `eth-remerkleable` 0.1.31 (through `utils/ssz.py`, owned by `EthCodec`): canonical decoding, progressive list/container merkleization and `hash_tree_root`.

**Supplied stateless input dictionary (Q81).**
`STFSpec/Stateless/InputSsz.lean` supplies the actual ordinary three-field
`StatelessInput.instSszSchema` and exactly its three external certificates.

| EELS source at the pin | Lean declaration | Domain, effects and failures | Law and controls |
|---|---|---|---|
| `stateless.py:144–166`; `src/ethereum/utils/ssz.py:174–253` | `StatelessInput.instSszSchema` | exact ordinary three-field descriptor; actual request/witness validity; total pure adapters | §5 complete metadata; private actual facade and complete wire controls (§4) |
| `src/ethereum/utils/ssz.py:174–253` (structural interpretation, Q81) | `StatelessInput.ssz_type_wellFormed` | no premise; actual descriptor WF | §7 exact certificate; actual provider/order/name controls |
| `src/ethereum/utils/ssz.py:258–320` (typed adapters, Q81) | `StatelessInput.ssz_ofValue_toValue` | actual composed validity; complete reconstruction and WT image | §7 exact certificate; arbitrary whole-field and finite complete recovery |
| `src/ethereum/utils/ssz.py:258–320` (typed adapters, Q81) | `StatelessInput.ssz_toValue_ofValue` | actual WT and successful reconstruction, in one conjunction | §7 exact certificate; complete child validity and whole-value preservation |

The private inverse matches exactly `container [request, witness, uint chainId]`,
invokes both actual child inverses in field order and uses checked `Base.U64.ofNat?`.
Wrong outer/scalar tags, wrong arity, reached child failure and unsigned overflow
return `none`; no scalar wraps. Reverse derives actual child WT independently of
child success before passing both to its public certificate. Shape-only child
reconstruction can retain wire-invalid values: it does not imply WT or validity.
All complete bytes, unsigned observations, ordered arrays and duplicates are retained.
No public off-WT completion or new whole-input WF predicate is supplied.

Private count recovery inspects the complete actual child descriptor tree: fixed
Withdrawal width is 44; hash width is 32; request-item widths are 192/76/116/184/68;
variable byte-list/progressive-byte-list elements have `fixedSize? = none`.
No immediate list element has fixed width zero. CountRecoverable holds for every
forward input without a wire-validity or operation-support premise.
Q80's outer head is 16 and emitted starts are 16 and 16+R for request byte length R.
Each recursively emitted child start retains its own bound below 2^32. There is no
final witness/end cap or root-count premise; schema-ID bytes are outside this body
and do not shift its offset origin. Private structural support reflection proves an
ordinary equality with the complete public Codec support equation. This supplies
mathematical serialization only; Q88 decoding, root/O2, source reflection/coercion/
backing/cache/host correspondence, admission, guest/security/resources and C1–C4
remain separate. Source correspondence here is static: no EELS algorithm executes.


**Private encoding-size foundation.** `InputSszCallerProofs.lean` supplies a local
logical byte-length model with the complete recursor in public
`Ssz.serializable_iff`, including unmatched zero. Ordinary private proofs derive
actual `Ssz.encode` length, fixed-class length and the exact public layout-fold
length from `Ssz.encode_eq`, `Ssz.serializable_iff`, `SszType.fixedSize?_eq` and
public data laws. Ordered actual child-byte certificates retain every occurrence;
proof irrelevance identifies different support proofs. Section 7 states the local
premises. This foundation is co-located with the actual input clients for later
private composition; it exports no provider or caller API.

The domain is arbitrary raw supported type/value pairs. Zero-byte vectors,
nonempty fixed-zero-child lists/products, empty ordinary containers and malformed
raw progressive masks remain supported where Q80 permits them. No WF,
CountRecoverable, Rootable, positive-width, uint256-count or final-size premise is
added. Actual request-count bounds, decoded-input support, rootability, schema-ID
joins, source-host agreement and guest/resource/security/readiness obligations
remain separate (§10).


**Private actual request sizes.** The same caller module specializes that foundation
using the public actual dictionary types and models. Section 7 owns the raw logical
formulas, operation-local encoded-size laws, six fixed-width classifications and
inherited child/member support. These are mathematical caller proofs, without a
new public declaration or production operation.

| Pinned source metadata | Private Lean client | Domain and result | Controls |
|---|---|---|---|
| `execution_engine/types.py:65`, `utils/ssz.py:258–291` | `transactionSize`, `transactions_logical_size`, `transactions_encoded_size` | raw transaction array formula; actual bytes require only its own Serializable proof | arbitrary repeated empties and arbitrary final transaction |
| `execution_engine/types.py:39–72`, `utils/ssz.py:258–291` | `payloadSize`, `payload_logical_size`, `payload_encoded_size` | every raw payload; actual bytes require only payload Serializable | arbitrary BAL and extra-data replacement, including over-limit raw extra data |
| `execution_engine/requests.py:99–121`, `utils/ssz.py:258–291` | `requestsSize`, `requests_logical_size`, `requests_encoded_size` | every raw aggregate; actual bytes require only aggregate Serializable | one arbitrary item appended to each of the five arrays |
| `execution_engine/types.py:78–96`, `utils/ssz.py:258–291` | `requestSize`, `request_logical_size`, `request_encoded_size` | every raw request; actual bytes require only request Serializable | universal formula and local proof parameter |
| `blocks.py:38–66`, `execution_engine/requests.py:42–96` | `withdrawal_fixed_size`, the five item `*_fixed_size` and corresponding `*_encoded_size` clients | actual descriptor widths; each actual item encoding uses only its own Serializable proof | public classifier equations and universal local-width consequences |
| actual container/list models above | `request_children_serializable`, `payload_children_serializable`, `requests_children_serializable` and their member clients | enclosing actual Serializable projects only to the actual children and array members | public support equation and membership-local projections |

These clients have no effects or error results. They establish neither source
execution nor source serialization agreement. Whole-input request support, later
outer-start and count/leaf bounds, Rootable assembly and decoded-value bridges
remain open (§10).

## 4. Tests

**Protocol fork metadata controls.**
`STFSpec/Conformance/Stateless/ProtocolForkCallerProofs.lean` imports the public
Stateless facade and privately checks every constructor's exact type and the complete
`ProtocolFork → UInt8` observer type. Its arbitrary `ProtocolFork → Sort u` eliminator
handles every constructor, with every dependent branch equation. Separate literal
observer equations, a quantified exhaustive mapping equation and tag injectivity
check the entire domain without a public equality instance.
`ProtocolForkGuards.lean` interprets all 21 complete `UInt8.toNat` observations against
independently written source literals, including `0x0f`/`0x10` and final `0x15`.
Compilation, declaration audit and kernel replay check these ordinary private clients.
These controls execute no EELS algorithm, guest or schema decoder.

**Wire-limit alias controls.** `STFSpec/Conformance/Stateless/WireLimitsGuards.lean`
imports the public facades and privately checks each exact `Nat` type, definitional
alias equation and independent numeric value, with interpreted guards for all five
values. Owner-body inspection checks exact qualified aliases and independence of
the Fork literals. These controls implement no decoding or runtime admission.

**Raw execution witness controls.**
`STFSpec/Conformance/Stateless/ExecutionWitnessCallerProofs.lean` imports the public
facade and privately checks the complete constructor/projection types, arbitrary
reconstruction, determination by all fields and each independent whole-record update.
These quantified clients cover every array/member length without wire-bound premises.
`ExecutionWitnessGuards.lean` checks complete byte-list triples for empty arrays,
empty members in each field, unequal array/member lengths, repeated and reordered
distinct members, zero/nonzero/asymmetric bytes and each field update while retaining
both other arrays. Compilation checks the ordinary Lean proofs and evaluates the
interpreted `#guard` controls. The declaration audit examines declarations, and kernel replay rechecks
constants. These are raw storage controls, not executed EELS or guest comparisons.

**Raw request-item controls.**
`STFSpec/Conformance/Stateless/RequestItemsCallerProofs.lean` imports only the public
Stateless facade. Private arbitrary clients check all five complete constructor
types, every one of the 17 projection types, whole-record reconstruction and
determination by all fields. Each independent update retains the complete other
fields, both as a record equation and as the entire observable tuple. Public Base
byte-injectivity, checked-constructor inverse, size and range laws establish complete
observation injectivity and every field's checked recovery. Each `U64` field retains
both its unsigned and bit-vector observations without a raw-record premise.
`RequestItemsGuards.lean` compares complete tuples for all five mixed, zero and
maximum-content records and all 17 independent updates. Literal asymmetric byte
lists retain leading/trailing zeros at widths 20/32/48/96. Indexed controls inspect
every position of a representative field at each width. Distinct same-width
consolidation keys detect swaps, and separate asymmetric deposit amount/index
values detect conflation. Zero, maximum and asymmetric unsigned words are observed
completely. Compilation evaluates the interpreted guards and checks the ordinary
private proofs. Declaration audit and kernel replay examine these declarations.
These are raw storage controls, with no EELS/dependency, fixture or guest execution.

**Raw execution-request aggregate controls.**
`STFSpec/Conformance/Stateless/ExecutionRequestsCallerProofs.lean` imports the public
Stateless facade. Private clients check the actual constructor and all five exact
projection types, arbitrary complete construction/reconstruction, determination
by all five arrays and by their complete `Array.toList` observations. Each
independent whole-record update preserves the other four fields, both as a record
and as the entire list tuple. Public Array conversion laws recover every complete
field without a bound or equality instance for nominal request records.
`ExecutionRequestsGuards.lean` observes every byte/unsigned value in all 17 item
fields through the public Base observers. Complete tuple comparisons cover all
five empty, each independently nonempty, all five populated with distinct unequal
lengths, duplicates, reordered distinct items in each field and all five updates
with all siblings retained. Independent zero, ff and asymmetric opaque byte vectors
and zero/maximal/asymmetric U64 values retain separate amount/index and source/target
fields. Compilation checks the private ordinary clients and interprets the guards;
declaration audit and kernel replay examine the resulting declarations. These are
raw storage controls, without EELS/dependency, fixture, codec or guest execution.

**Raw payload/request controls.**
`STFSpec/Conformance/Stateless/PayloadCallerProofs.lean` imports the public Stateless
facade. Private clients check both complete constructor types and all 23 exact
projection types, arbitrary whole construction/reconstruction, determination by
every field and by complete byte/word/ordered nested observations. Each of the
23 independent updates retains every sibling as a whole record and as the complete
observation tuple. Public Base and Array conversions recover the raw fields; whole
request clients retain the complete nested payload and actual five-array aggregate.
Observation injectivity uses only public Base laws and ordinary provider fields.

`PayloadGuards.lean` compares complete independent literal observations for zero,
maximum and two asymmetric values, down to every nested withdrawal and request-item
byte/word. Leading, internal and trailing zeros, full U64/U256 endpoints, independent
same-typed roots/gas/times, gasUsed greater than gasLimit, oversized extraData,
empty/malformed opaque transactions/BAL, all-empty and nonempty collections,
duplicates, reordering and unusual version bytes are retained. All 23 single-field
updates compare the whole result with all nested/sibling values retained; separate
array-emptying updates preserve every other field. Finite word builders require
explicit in-range proofs and have ordinary exact-observation proofs, preventing
wrapping test inputs. Compilation checks ordinary private proofs and interprets
the guards; declaration audit and kernel replay examine the declarations. These
controls establish raw storage, without EELS/dependency, codec, fixture or guest
execution or a native-cost claim.

**Execution witness SSZ controls.**
`ExecutionWitnessSszCallerProofs.lean` imports the Stateless facade and privately
checks the actual named dictionary, full descriptor/names/Fork-backed limits and
all three exact certificate types. Arbitrary whole-array/value clients use those
certificates for complete recovery and re-forwarding. A separate private ordinary
public-Codec-law proof establishes CountRecoverable for every actual forward image,
without a validity or serialization premise.
`ExecutionWitnessSszControls.lean` compares complete raw values and recovered arrays,
including duplicates, empty members, ordered 00/ff bytes, independent field changes
and retained siblings. Each state/header width 1023/1024/1025, code width
65535/65536/65537 and header count 255/256/257 is checked. State and code counts 257
remain payload-valid. Overbound raw construction, false validity and shape-only
successful recovery are checked together. Malformed controls cover every wrong
outer tag, arities 0/1/2/4, each wrong field tag and non-byte members in first/middle/
last positions of each field. These are private implementation controls, rather
than a new public off-WT contract.
`ExecutionWitnessSszWireControls.lean` compares all 7159 bytes of 25 complete small
wire cases through the actual `SszSchema.encodeBytes`, each with its own private
ordinary Serializable proof. Whole inputs and expected offsets/field bytes/wire
bytes were frozen and independently computed before implementation, by two
source-free mathematical calculations. Expectations are literal byte arrays,
independent of the target/helper. These controls cover empty/equal offsets, ordered
and duplicate payloads, 00/ff bytes, independent field changes and little-endian
carry boundaries. They run no source encoder, guest or fixture corpus, and close
no general source, decoder, root, host-resource or readiness obligation.

**Execution payload SSZ controls.** `PayloadSszCallerProofs.lean` imports the public
Stateless facade. All clients are private: actual inference and named dictionary,
complete descriptor/mask/names/Fork-backed validity, all three exact law types,
arbitrary whole-model observation, reconstruction/re-forwarding, and CountRecoverable
for every forward image without an extra-data-validity premise.
`PayloadSszControls.lean` checks each outer/field tag, arities below/above nineteen,
every fixed-byte width, every scalar overflow and maximum, and malformed transaction
and actual Withdrawal members. Extra-data lengths 0/32/33 distinguish complete raw
retention, validity and private inverse completion without a public off-WT promise.

`PayloadSszWireControls.lean` transports 129 independent complete mathematical cases
through its own private checked parser. Nineteen natural-token rows retain scalar
singletons, all byte digits, transaction count/length frames and whole fixed Withdrawal
records. Exact arity, every digit/width/range and complete consumption are checked before
Base construction. Complete raw observations and the ordered model are compared with
the input, as are both reconstruction and re-forwarding paths. Every actual
`SszSchema.encodeBytes` byte is compared with the independent expectation: 79014 bytes,
2451 payload fields, 248 transactions, 132 withdrawals, 1428 unsigned values and 764
offsets. Inputs/expected bytes were frozen and calculated independently before this
implementation. Literal sharing and chunking preserve all values; a separate complete
transport readback authenticates every case. A shared private interpreted runner
rejects every parse, validity or operation-support failure, then supplies an ordinary
generic Serializable composition through the public Codec equation. Its executable
structural length has an ordinary all-constructor equality to the complete local
logical-length reference; fits reflection preserves every emitted-start bound without
a final-tail cap. Negative controls check strict start bounds and reject altered complete
expectations and extra-data overflow. These finite interpreted controls
cover empty/nested-empty and duplicate lists, leading zeros, independent same-typed
fields, maximum words, extra-data endpoints and offset carries. No source/native/guest,
general decoder/root, giant-input, host-resource, security or cost result follows.

**Request-item SSZ controls.**
`RequestItemSszCallerProofs.lean` imports the public Stateless facade and privately
checks all five actual dictionary types, exact descriptors/names/validity, all
fifteen certificate types, arbitrary complete forward models, checked recovery,
reverse preservation, CountRecoverable and fixed sizes.
`RequestItemSszWireControls.lean` proves actual Serializable support and the whole
fixed wire for arbitrary records, using public Base and Codec laws. It compares
all 681 independently frozen mathematical whole inputs and all 100476 expected
wire bytes through the actual `SszSchema.encodeBytes`. Checked Base constructors
and complete field observations protect against wrapping or content loss. The
ordered model and its complete reconstructed observations are also compared.
The case counts are 201/83/129/193/75 in §3 order. They cover asymmetric, zero and
maximum values, all U64 carry boundaries in the catalogue, each byte position,
every whole-field zero/ff change and source/target swaps. Closed literal sharing
retains every byte of each input and expected wire. A separate complete parse and
expansion check verifies that transport against the independently frozen inputs
and expectations. Expectations do not use the target, its projections or encoder.
`RequestItemSszControls.lean` evaluates 178 private controls for wrong outer/leaf
tags, exact arity, extra trailing fields, each byte width n−1/n+1 with zero and
indexed contents, unsigned 2^64/2^64+1 and combined malformed leaves. Exact-width
arbitrary cryptographic bytes and maximum quantities still succeed. Compilation
evaluates these interpreted guards and checks ordinary private proofs. Declaration
audit and kernel replay inspect their declarations. These controls execute no
EELS/dependency algorithm, native request-item producer, fixture or guest.


**Execution-request aggregate SSZ controls.**
`ExecutionRequestsSszCallerProofs.lean` imports the public Stateless facade and
privately checks actual dictionary inference, the complete descriptor/mask/names,
validity and all three exact certificate types. Arbitrary complete forward models,
construction from all five arrays, recovery of all arrays and reverse re-forwarding
use those actual certificates. Private public-Codec-law clients prove positive
192/76/116/184/68 child widths and CountRecoverable for every forward aggregate.
`ExecutionRequestsSszWireControls.lean` proves actual child support/full fixed wires,
fixed-list concatenation and aggregate Serializable under precisely the five local
emitted starts in §5. All supplementary declarations remain private.

Its 80 complete mathematical cases compare every one of 816 items, 3891 fields,
1489 unsigned fields and 150780 expected wire bytes through actual
`SszSchema.encodeBytes`. Checked Base constructors prevent wrapping. The controls
compare complete raw observations, ordered models and both recovery paths against
independently frozen inputs. Literal byte/item sharing retains complete finite
transport, without digest or length substitutes. The catalogue covers all empty,
each independently populated, all five populated with unequal counts, internal
empties, duplicates, independent reversals/changes, opaque bytes, unsigned boundaries
and offset carries. A separate complete transport expansion checks every literal
against the frozen mathematical inputs and expectations.

`ExecutionRequestsSszControls.lean` checks wrong outer tags, arities 0–4/6 and each
wrong field tag. Every child's wrong tags, arity, byte width and uint overflow is
placed at first/middle/last collection positions, with mixed malformed collections.
Exact-width arbitrary cryptographic bytes and maximum uint64 values succeed.
Compilation evaluates these interpreted controls and checks ordinary proofs.
Declaration audit and kernel replay inspect their declarations. These controls
establish no public off-WT contract, EELS/dependency, native request producer,
fixture, decoder, root, resource or readiness result.

**New-payload request SSZ controls.** `NewPayloadSszCallerProofs.lean` imports the
public Stateless facade. Its private clients check actual inference, exact four-field
metadata and provider identities, composed validity and the three exact law types.
Arbitrary whole forward models, valid reconstruction/WT and WT-plus-success reverse
clients retain both complete children, all hashes and the root. Private ordinary
public-Codec-law clients establish CountRecoverable for every forward value, the
44-byte head and its three emitted starts, separately from validity and operation support.

`NewPayloadSszControls.lean` checks every wrong outer tag and arity, each incompatible
field tag, malformed root widths, malformed hash tags/widths at first/middle/last
positions, mixed malformed members and failures of both actual children. Complete
opaque zero/ff/indexed/leading-zero, reversed and duplicate arrays retain every byte;
no version predicate applies. Extra-data 0/32/33 controls preserve complete raw values
and private inverse completion, while length 33 fails actual validity and WT. This
supplies no public success-implies-validity or off-WT promise.

`NewPayloadSszWireControls.lean` transports all 96 independently frozen mathematical
whole requests through private checked parsers and existing Base constructors.
Shared bounded natural literals retain all 384 outer fields, 1824 payload fields,
480 aggregate fields, 332 transactions, 168 withdrawals, 1294 request items,
4004 item fields, 1990 unsigned values and 280 versioned hashes. Exact shape,
byte digits/widths, unsigned ranges and complete framed consumption precede
construction. Complete raw observations, whole models, both reconstruction paths
and re-forwarding are compared against the inputs. Actual `SszSchema.encodeBytes`
compares every one of 365636 independent expected bytes, including all 1484 offsets.
Expectations were independently calculated before implementation, without the target,
its projections/encoder or EELS. A separate complete literal-expansion readback
checks transport against those frozen inputs/expectations. Each finite call has an
ordinary private Serializable proof using actual child descriptors and public Codec
equations; only recursively emitted starts are bounded, without a final-size cap.
Compilation executes these interpreted guards. No source/native/fixture/guest,
general decoder/root, host-resource, security, cost or readiness result follows.
**Raw stateless input controls.**
`STFSpec/Conformance/Stateless/InputCallerProofs.lean` imports the public Stateless
facade. Private ordinary clients check the exact constructor and three projection
types, arbitrary complete construction/reconstruction/determination, each independent
whole-field update with both siblings retained, and public U64/Array recovery.
`InputGuards.lean` compares complete nested request/witness observations, retaining
every byte, word and ordered array occurrence. Controls include zero/max/asymmetric
chain IDs, independent request/witness/chain updates, empty and unequal arrays,
duplicates, reversals, malformed transaction/BAL/header bytes, 33-byte extraData
and a 1025-byte witness node. Compilation evaluates these interpreted controls;
declaration audit and kernel replay examine the ordinary clients. No source runtime,
wire codec, fixture or guest executes in these raw storage controls.

**Stateless input SSZ controls.** `InputSszCallerProofs.lean` imports the public
Stateless facade. All clients are private: exact actual inference/descriptor/names,
composed validity, complete model, all three certificate types, arbitrary complete
construction/recovery/re-forwarding, CountRecoverable and 16-byte head/emitted starts.
Symbolic endpoint controls distinguish second starts 2^32−1/2^32 and permit an
unbounded final witness end while retaining every child support premise.
`InputSszControls.lean` checks wrong outer/field tags, arities 0/1/2/4/5, swapped and
duplicated children, both actual child failures and chain-ID 0/1/2^64−1/2^64/2^64+1/2^128.
Separate controls retain complete extraData33, witness member lengths 1025/65537/1025
and 257 headers through inverse completion while validity and typing fail; exact
wire endpoints 32/1024/65536/1024/256 remain valid. No public completion law follows.


The same caller module also checks 30 independently frozen raw supported cases
against 183 complete handwritten byte literals, with actual size and logical-size
controls. The cases cover all nine descriptor families, every supported scalar
width, zero/exact/fixed/variable children, empty/duplicate members, equal starts,
empty containers and malformed progressive masks. Each support proof uses the
public support equation. Generic symbolic probes allow an arbitrary final byte
tail, retain the emitted-start bound without a final-end cap, separate fixed-zero
forward support from count recovery, and rule out unsupported widths/tags and
wrong byte lengths. These controls supply no decoder or protocol admission claim.


The actual-size specializations add ordinary symbolic probes in that same caller
module. `empty_transactions_logical_size` counts the offset table for any number
of repeated empty transactions; `final_transaction_logical_size` retains an
arbitrary last transaction's complete length. The BAL and extra-data replacement
laws retain the complete replacement length, with no support premise or wire
limit on the raw extra data. Five `*_append_logical_size` laws append one arbitrary
item to each actual aggregate array and check its distinct fixed-width increment.
These universal probes allocate no large list and add no second finite wire
catalogue. The existing complete byte, malformed-mask, zero-width and final-tail
controls remain in place.

`InputSszWireControls.lean` transports all 48 independently frozen mathematical
whole inputs through private checked Base construction. Shared complete natural
literals retain all 2987 recursive nodes, 523 unsigned leaves, 1597 byte leaves and
1682 offsets. Every byte digit, fixed width, scalar range and framed consumption is
checked. Complete raw observations, ordered models, both reconstruction paths and
re-forwarding are compared with the input. Actual `SszSchema.encodeBytes` compares
all 385957 independent expected bytes. A private interpreted support decision has
an ordinary universal reflection proof against public `Ssz.serializable_iff`,
including every recursive child and emitted start; unsupported cases return false.
Literal sharing preserves complete cases, and separate full transport expansion
checks every raw input and byte expectation. Inputs/expectations were frozen before
implementation, independently of the target, its projections/encoder and EELS.
Compilation executes these interpreted guards; declaration audit and kernel replay
inspect the declarations. These finite controls close no source/native/fixture/guest,
general decoder/root, host-resource, security, cost or readiness obligation.

**EEST fixture areas.** Every guest record (67,685 at this pin, in `blockchain_tests` and `blockchain_tests_engine`; `reference.toml`) passes through this library. Areas that target it specifically (`STFSpec/informal/eest-fixture-index.txt`): `blockchain_tests/for_amsterdam/amsterdam/eip8025_optional_proofs` (96 files), in particular `stateless_input_bytes/` (the zero-sentinel records: at v21.0.0 these were 9, empty input, 1-byte input, schema only, wrong fork byte `0x16`, wrong revision `0x02`, truncated body, trailing garbage, invalid first offset, shifted offsets [V, v21.0.0]; at this pin there are 10 per format, without trailing garbage and with two witness-header SSZ limit cases, EthCodec §4), `witness_validation_headers/` (non-contiguous chain, missing parent header, empty headers, missing oldest BLOCKHASH ancestor, malformed RLP header), `witness_headers/`, `witness_validation_chain_id/`, `stateless_input_versioned_hashes/`, `witness_validation_state/`, `witness_validation_codes/`; and the transition directory `for_bpo2toamsterdamattime15k/*` (previous-fork parent header). Payload conversion is exercised by `prague/eip7685_general_purpose_el_requests`, `eip6110_deposits`, `eip7002_*`, `eip7251_*`, `amsterdam/eip8282_builder_execution_requests`, `cancun/eip4844_blobs` (versioned hashes) and `amsterdam/eip7928_block_level_access_lists` (BAL bytes and hash).

Corpus facts relevant here [V, v21.0.0; not recomputed at this pin, §10]: 27,822 records succeed, 1,199 fail with schema `0x1501`, 9 are the zero sentinel; the largest input is 8,396,936 bytes; one record has an empty header list; 28,975 of 29,030 records carry exactly one witness header.

**EELS unit tests** at e1a316a0: `tests/json_loader/test_stateless_guest.py` (schema-id identity, round trips, known encoding and request root, empty witness, 65-byte key enforcement, oversize witness items, >256 headers rejected, empty/1-byte/wrong-revision/wrong-fork/legacy raw-SSZ inputs rejected, non-canonical shifted offsets → sentinel, decodable input reports schema on failure, public-key count too few/too many); `tests/json_loader/test_execution_requests.py` (wire round trip). Port the cases compatible with CONTRACT §2/P1 as `core` cases where they do not depend on monkeypatching. The hint-only cases in this dated record are outside the current input contract (CONTRACT O5).

**Supplied output slice.** `STFSpec/Conformance/Stateless/OutputCallerProofs.lean`
uses only the `STFSpec.Stateless` facade and public laws for complete field preservation,
layout, size, injectivity and the zero sentinel. `OutputGuards.lean` and
`scripts/StatelessOutputNativeTests.lean` compare every byte against an independently
frozen 18-case matrix
plus the sentinel. Cases cover both booleans; all 256 root-byte values across eight
patterns; one-field root/bool/chain/schema changes; asymmetric and maximal uint64/uint16
values; arbitrary schema IDs, including zero with nonzero other fields; and the pinned
known encoding (`tests/json_loader/test_stateless_guest.py:523–539`). The strict
`output_differential.py` consumer and normal/`-O` parser regression controls check complete
native output against `output_literals.json` (18 frozen cases and one sentinel).
These bounded serializer checks do not run a guest or establish EEST
outcomes. No in-tree check replays the pinned EELS serializer; the frozen literals,
including the known encoding above, are the source evidence.

**`core` `#guard` cases.**
- Typical: a minimal valid input (one parent header, empty block, empty witness DB except the root node) → `(root, true, 1, 0x1501)`; the expected root computed independently.
- Edge: header list of length 0 (O3a), 1, 256; a BPO5-shape parent header; payload with zero requests (all lists empty → `encodeExecutionRequests = #[]`); `extra_data` of 32 bytes.
- Adversarial: every O1 variant above; 257 headers (O1, not O3); a header decodable only as the previous fork in the middle of the chain; decode failure at j and contiguity break at i < j (decode wins); an empty transaction together with a wrong block hash (empty tx wins); an unknown tx type byte `0x05` (reported as `invalidVersionedHashes`); tx byte `0xFF`.
- Structural: `(serializeStatelessOutput r).size = 43` for all `r`; `zeroSentinel` bytes are 43 zeros.
- F20 composition cases to implement, using the R5 query order:
  - Decode, header-decode, empty-header and contiguity failures acquire no record. A contiguity failure has hashed every raw header before checking contiguity.
  - Pass successful nonempty headers; acquisition precedes witness construction and payload guards.
  - Use a synthetic record differing from literals; the witness backend, both payload-header constructions, block validation and context consumers receive or observe that record.
  - Repeat an ordinary constant preimage query; it is not a second record acquisition.
  - Fail the empty-transaction, payload-hash and versioned-hash guards separately; prior queries remain in the trace and the first guard determines the error.
  - Raise a provider or fuel error; prior queries remain in the trace and the error stays in its inner or outer checked channel, respectively.
  - Run twice; each run acquires independently.
  - Use the existing `GuestLeaves.decodeInput`, `requestRoot` and `decodeHeader` hooks
    to drive the cases, with `GuestLeaves.executePayload` bound to the actual
    `executeNewPayloadRequest` and its shared block kernel. Their traces contain no
    reacquisition. Replacing `executePayload` with a test callback checks the caller
    only; it does not establish that the actual kernels avoid reacquisition. Until
    those kernels are implemented, this composition case remains an open obligation.

**Properties and differential checks.** Round trip `deserialize (serializeStatelessInput x) = .ok x` for generated well-formed `x` (serializer from `EthConformance`); `validateHeaders` against a model on generated chains; differential against EELS `run_stateless_guest` on mutated inputs (bug-finding only; `EthConformance`).

## 5. Interface

Core §3/§4/§5/§7 supplies nominal OverflowSite/VmFault values, retaining whole StateError, raw Nat offset or conversion site. The complete block/guest adapters and O4/O13 outcome projection remain unimplemented; this storage slice proves no classification, reachability or B14 freezing.

Reference field order, widths and inherited records are catalogued in [REFERENCE-RECORDS](../REFERENCE-RECORDS.md), generated from the exact pin. Wire-schema owners must use those layouts and prove their codec instances. Runtime records may use the explicit abstraction below; omitted fields or `…` remain implementation blockers, not implicit freedom to choose semantics.

All in namespace `STFSpec.Stateless`; public unless marked.

`ExecutionWitness` below is supplied as a raw carrier. Its fields retain arbitrary
complete `Array ByteArray` values without bounds, validation, decoded `Header`,
database or hashing dependency. The five wire-limit aliases below are supplied
from Fork-owned values (F8). The actual dictionaries are supplied
below, including StatelessInput; raw byte decoding remains prospective.
The complete `ProtocolFork` carrier and forward observer below are supplied with
the exact mapping in §3; schema constants below remain prospective under F8 (§10).

The five request-item structures below are supplied with exactly the ordered field
types in §3. They add no defaults, proof fields, derived instances or validation.
The aggregate `ExecutionRequests` below is supplied with exactly the five independent
Array fields. Its actual Q81 dictionary is supplied below. Byte decoding remains prospective.
The nineteen-field `ExecutionPayload` and four-field `NewPayloadRequest` below are
supplied by `Payload.lean` exactly as written, using existing Base types, actual
`Block.Withdrawal` and actual `ExecutionRequests`. Their actual dictionaries are supplied below.
The three-field `StatelessInput` below is supplied by `Input.lean` over those actual
providers and existing `Base.U64`. Its actual dictionary is supplied below; the broader
WF predicate remains prospective.

```lean
-- constants (public)
abbrev maxWitnessHeaders : Nat := Fork.Amsterdam.MAX_WITNESS_HEADERS
abbrev maxBytesPerCode : Nat := Fork.Amsterdam.MAX_BYTES_PER_CODE
abbrev maxBytesPerHeader : Nat := Fork.Amsterdam.MAX_BYTES_PER_HEADER
abbrev maxBytesPerWitnessNode : Nat := Fork.Amsterdam.MAX_BYTES_PER_WITNESS_NODE
abbrev maxExtraDataBytes : Nat := Fork.Amsterdam.MAX_EXTRA_DATA_BYTES
inductive ProtocolFork | frontier | homestead | daoFork | tangerineWhistle | spuriousDragon
  | byzantium | stPetersburg | istanbul | muirGlacier | berlin | london | arrowGlacier
  | grayGlacier | paris | shanghai | cancun | prague | osaka | bpo1 | bpo2 | amsterdam
def ProtocolFork.toIndex : ProtocolFork → UInt8          -- 0x01 … 0x15
def schemaId : UInt16 := (ProtocolFork.amsterdam.toIndex.toUInt16 <<< 8) ||| 0x01
def schemaIdBytes : ByteArray                            -- big-endian, size 2

-- wire types (public)
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
  deposits : Array DepositRequest
  withdrawals : Array WithdrawalRequest
  consolidations : Array ConsolidationRequest
  builderDeposits : Array BuilderDepositRequest
  builderExits : Array BuilderExitRequest
structure ExecutionPayload where
  parentHash : Hash32; feeRecipient : Address; stateRoot : Hash32; receiptsRoot : Hash32
  logsBloom : Bloom; prevRandao : Bytes32; blockNumber : U64; gasLimit : U64; gasUsed : U64
  timestamp : U64; extraData : ByteArray; baseFeePerGas : U256; blockHash : Hash32
  transactions : Array ByteArray; withdrawals : Array Block.Withdrawal; blobGasUsed : U64
  excessBlobGas : U64; blockAccessList : ByteArray; slotNumber : U64
structure NewPayloadRequest where
  executionPayload : ExecutionPayload; versionedHashes : Array VersionedHash
  parentBeaconBlockRoot : Hash32; executionRequests : ExecutionRequests
structure StatelessInput where
  newPayloadRequest : NewPayloadRequest; witness : ExecutionWitness
  chainId : Base.U64
structure StatelessValidationResult where
  newPayloadRequestRoot : Hash32; successfulValidation : Bool; chainId : U64; schemaId : UInt16
def StatelessInput.WF : StatelessInput → Prop            -- prospective; all SSZ limits (§6)
instance StatelessInput.instSszSchema : SszSchema StatelessInput -- supplied below (Q81)
abbrev AnyHeader := ParentHeader

-- errors (public, one constructor per EELS failure site)
inductive DecodeError | missingSchemaId | unsupportedSchema (id : UInt16) | ssz (e : SszError)
inductive HeaderError | tooMany (n : Nat) | undecodable (i : Nat) (amsterdam prev : RlpError)
  | notContiguous (i : Nat)
inductive PayloadError | emptyTransaction (i : Nat) | invalidBlockHash
  | invalidVersionedHashes (cause : Option (Nat × TxDecodeError))
  | legacyDecode (i : Nat) (e : TxDecodeError)           -- dead after invalidVersionedHashes [I]
inductive StatelessError | headers (e : HeaderError) | missingParentHeader
  | payload (e : PayloadError) | block (e : BlockError)  -- BlockError (EthBlock) embeds WitnessError (O4) and the O13 fault constructors; CONTRACT O5 is retired
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
    (ctx : ChainContext) :
    m (CheckedResult StatelessError (BlockDiff × Block))                               -- public (both backends)
structure GuestLeaves (m) where                                                         -- testing seam
  decodeInput : ByteArray → Except SszError StatelessInput
  requestRoot : NewPayloadRequest → Hash32
  decodeHeader : ByteArray → Except (RlpError × RlpError) AnyHeader
  executePayload : HashConsts → NewPayloadRequest → PreState m → ChainContext
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

**Supplied actual witness dictionary (Q81).** With
`s := ExecutionWitness.instSszSchema : Codec.SszSchema ExecutionWitness`, the five
fields have exactly these meanings:

```text
s.type = container [progressiveList (byteList maxBytesPerWitnessNode),
  progressiveList (byteList maxBytesPerCode),
  list (byteList maxBytesPerHeader) maxWitnessHeaders]
s.fieldNames = ["state", "codes", "headers"]
s.valid a = (∀ b ∈ a.state.toList, b.size ≤ maxBytesPerWitnessNode) ∧
  (∀ b ∈ a.codes.toList, b.size ≤ maxBytesPerCode) ∧
  a.headers.size ≤ maxWitnessHeaders ∧
  (∀ b ∈ a.headers.toList, b.size ≤ maxBytesPerHeader)
s.toValue a = container [list (a.state.toList.map bytes),
  list (a.codes.toList.map bytes), list (a.headers.toList.map bytes)]
s.ofValue? : Codec.SszValue → Option ExecutionWitness
```

The private inverse's complete shape-only algorithm is described in §3. Both
adapters are total and pure. The dictionary exposes no decoder, bound-checking
validator, operation-support field or extra law class. Its only authored public
certificates are the three §7 declarations.

**Supplied actual payload dictionary (Q81).** With
`s := ExecutionPayload.instSszSchema : Codec.SszSchema ExecutionPayload` and
`w := Block.Withdrawal.instSszSchema`, its metadata is exactly:

```text
s.type = progressiveContainer (replicate 19 true) [
  byteVector 32, byteVector 20, byteVector 32, byteVector 32,
  byteVector 256, byteVector 32, uint 8, uint 8, uint 8, uint 8,
  byteList maxExtraDataBytes, uint 32, byteVector 32,
  progressiveList progressiveByteList, progressiveList w.type,
  uint 8, uint 8, progressiveByteList, uint 8]
s.fieldNames = ["parent_hash", "fee_recipient", "state_root", "receipts_root",
  "logs_bloom", "prev_randao", "block_number", "gas_limit", "gas_used", "timestamp",
  "extra_data", "base_fee_per_gas", "block_hash", "transactions", "withdrawals",
  "blob_gas_used", "excess_blob_gas", "block_access_list", "slot_number"]
s.valid a = a.extraData.size ≤ maxExtraDataBytes
s.toValue a = container [
  bytes a.parentHash.toBytes.toByteArray, bytes a.feeRecipient.toBytes.toByteArray,
  bytes a.stateRoot.toBytes.toByteArray, bytes a.receiptsRoot.toBytes.toByteArray,
  bytes a.logsBloom.toBytes.toByteArray, bytes a.prevRandao.toBytes.toByteArray,
  uint a.blockNumber.toNat, uint a.gasLimit.toNat, uint a.gasUsed.toNat,
  uint a.timestamp.toNat, bytes a.extraData, uint a.baseFeePerGas.toNat,
  bytes a.blockHash.toBytes.toByteArray, list (a.transactions.toList.map bytes),
  list (a.withdrawals.toList.map w.toValue), uint a.blobGasUsed.toNat,
  uint a.excessBlobGas.toNat, bytes a.blockAccessList, uint a.slotNumber.toNat]
s.ofValue? : Codec.SszValue → Option ExecutionPayload
```

Widths are bytes. There is no encoded mask member. Validity contains no transaction,
withdrawal or BAL count/size cap, gas relation, hash consistency, execution validity,
serialization/root support or source-host premise. §3 owns the private inverse algorithm.

**Supplied actual request-item dictionaries (Q81).** Each namespace `X` in the
following table supplies exactly `X.instSszSchema : Codec.SszSchema X`. Write
`B x := Codec.SszValue.bytes x.toBytes.toByteArray` and
`N x := Codec.SszValue.uint x.toNat` in this table only. These are explanatory
notation, with no additional public helper.

| X | `s.type` (ordinary container) | `s.fieldNames` | `s.toValue a` (ordered container) |
|---|---|---|---|
| `DepositRequest` | `container [byteVector 48, byteVector 32, uint 8, byteVector 96, uint 8]` | `["pubkey", "withdrawal_credentials", "amount", "signature", "index"]` | `container [B a.pubkey, B a.withdrawalCredentials, N a.amount, B a.signature, N a.index]` |
| `WithdrawalRequest` | `container [byteVector 20, byteVector 48, uint 8]` | `["source_address", "validator_pubkey", "amount"]` | `container [B a.sourceAddress, B a.validatorPubkey, N a.amount]` |
| `ConsolidationRequest` | `container [byteVector 20, byteVector 48, byteVector 48]` | `["source_address", "source_pubkey", "target_pubkey"]` | `container [B a.sourceAddress, B a.sourcePubkey, B a.targetPubkey]` |
| `BuilderDepositRequest` | `container [byteVector 48, byteVector 32, uint 8, byteVector 96]` | `["pubkey", "withdrawal_credentials", "amount", "signature"]` | `container [B a.pubkey, B a.withdrawalCredentials, N a.amount, B a.signature]` |
| `BuilderExitRequest` | `container [byteVector 20, byteVector 48]` | `["source_address", "pubkey"]` | `container [B a.sourceAddress, B a.pubkey]` |

For each row, `s.valid a = True`, and `s.ofValue? : Codec.SszValue → Option X`
is the checked inverse in §3. `.uint 8` means eight bytes. Credentials retain
`Bytes32`, and source addresses retain nominal `Address`. Builder deposits have
no index, and builder exits have no amount or signature. All supplementary
support, layout, count-recovery and malformed facts remain private.


**Supplied actual aggregate dictionary (Q81).** With
`s := ExecutionRequests.instSszSchema : Codec.SszSchema ExecutionRequests`:

```text
s.type = progressiveContainer [true, true, true, true, true] [
  progressiveList DepositRequest.instSszSchema.type,
  progressiveList WithdrawalRequest.instSszSchema.type,
  progressiveList ConsolidationRequest.instSszSchema.type,
  progressiveList BuilderDepositRequest.instSszSchema.type,
  progressiveList BuilderExitRequest.instSszSchema.type]
s.fieldNames = ["deposits", "withdrawals", "consolidations", "builder_deposits", "builder_exits"]
s.valid a = True
s.toValue a = container [
  list (a.deposits.toList.map DepositRequest.instSszSchema.toValue),
  list (a.withdrawals.toList.map WithdrawalRequest.instSszSchema.toValue),
  list (a.consolidations.toList.map ConsolidationRequest.instSszSchema.toValue),
  list (a.builderDeposits.toList.map BuilderDepositRequest.instSszSchema.toValue),
  list (a.builderExits.toList.map BuilderExitRequest.instSszSchema.toValue)]
s.ofValue? : Codec.SszValue → Option ExecutionRequests
```

The inverse algorithm is described in §3. Private Serializable clients require
only each emitted start below 2^32. For counts d/w/c/b/e in source order, these
starts are 20, 20+192d, 20+192d+76w, 20+192d+76w+116c and
20+192d+76w+116c+184b. The first bound is automatic. There is no final 68e/end
bound or additional count<2^256 condition. Rootable owns its separate actual-count
premise. Source deserialization's per-field extents/backing/host premises remain
separate correspondence assumptions, including for the final field. Neither these
private proofs nor the dictionary changes Q88 or O12.

**Supplied actual new-payload request dictionary (Q81).** With
`s := NewPayloadRequest.instSszSchema : Codec.SszSchema NewPayloadRequest`,
`p := ExecutionPayload.instSszSchema` and `r := ExecutionRequests.instSszSchema`:

```text
s.type = container [p.type, progressiveList (byteVector 32), byteVector 32, r.type]
s.fieldNames = ["execution_payload", "versioned_hashes", "parent_beacon_block_root",
  "execution_requests"]
s.valid a = p.valid a.executionPayload ∧ r.valid a.executionRequests
s.toValue a = container [p.toValue a.executionPayload,
  list (a.versionedHashes.toList.map (fun h => bytes h.toBytes.toByteArray)),
  bytes a.parentBeaconBlockRoot.toBytes.toByteArray, r.toValue a.executionRequests]
s.ofValue? : Codec.SszValue → Option NewPayloadRequest
```

The private inverse and separated operation/source domains are described in §3.
The actual child descriptors retain their own progressive masks. The ordinary outer
container emits no mask or count prefix and adds no version-byte predicate.

**Supplied actual input dictionary (Q81).** With
`s := StatelessInput.instSszSchema : Codec.SszSchema StatelessInput`,
`r := NewPayloadRequest.instSszSchema` and `w := ExecutionWitness.instSszSchema`:

```text
s.type = container [r.type, w.type, uint 8]
s.fieldNames = ["new_payload_request", "witness", "chain_id"]
s.valid a = r.valid a.newPayloadRequest ∧ w.valid a.witness
s.toValue a = container [r.toValue a.newPayloadRequest,
  w.toValue a.witness, uint a.chainId.toNat]
s.ofValue? : Codec.SszValue → Option StatelessInput
```

The private checked inverse is described in §3. The scalar width is eight bytes.
No chain-ID relation, hash/version/gas relation, witness execution invariant,
source-host limit, global WF, Serializable or Rootable premise enters validity.
The schema ID is outside the body, and the descriptor contains no mask or fourth field.

The payload entry and helpers take `consts : HashConsts` with local EELS notation (CONTRIBUTING §7.2, F20). `isValidBlockHash` and `payloadBlock` each build `payloadHeader`, so both take the record explicitly. `executeNewPayloadRequest` forwards that record through these helpers and `Amsterdam.executeBlock`; none of those kernels acquires it. `classifyWith` follows R5 and supplies the record to the witness backend and `L.executePayload`. Consumers whose state or backend already holds the record read its fields.

Use `ParentHeader` from `EthBlock` for the Amsterdam/BPO5 sum; `AnyHeader` above is an alias for that type. `ChainContext`, `Block`, `BlockTx`, `BlockError`, transaction-decode diagnostics and `executeBlock` come from `EthBlock`/`EthFork`; `PreState`/`BlockDiff` from `EthState`; `WitnessBackend.build` and `CodeDB.build` from `EthStateWitness`, `NodeDB.build` from `EthCommit` (both monadic, F4); `HashConsts` from `EthBase` and `HashConsts.query`/`KeccakQuery` from `EthHash`. The executable seam uses `CheckedResult` (from `CheckedT`, `EthVmRunner`, F14): validation errors are the inner `Except`, and internal failures, including fuel exhaustion, the outer `InternalError`. There is no separate `FuelM`. `classifyWith` is the leaf-parametric composition; the real composition code runs unchanged under test leaves, and `runStatelessGuest_eq` ties the public function to it at `Id`.

## 6. Data structures

| Type | Representation | Model | Abstraction | Invariant | Persistence | Complexity |
|---|---|---|---|---|---|---|
| `ProtocolFork` | 21 nullary constructors | the complete §3 historical inventory | explicit `toIndex : ProtocolFork → UInt8` | none beyond the constructor domain | immutable value | O(1) construction/observation |
| `ExecutionWitness` | three `Array ByteArray` | ordered triple of complete finite byte-array lists | identity, including order/duplicates/empty members | none on the raw carrier; the actual schema has exactly the §5 payload bounds | immutable value; later DB builders consume the raw preimages | O(1) construction/projection; adapters O(total member count), retaining byte payloads; decoding and DB building unimplemented |
| five raw request items | five nominal structures over existing Base fields (§5) | ordered tuple of whole fields | identity; public complete byte/unsigned observations | none beyond each Base field domain | immutable values | O(1) construction/projection/update at fixed field counts; no byte traversal |
| `ExecutionRequests` | five independent typed Arrays (§5) | ordered tuple of complete item lists | identity, retaining order/duplicates/empty arrays | none beyond each raw item domain | immutable record | O(1) construction/projection/update at five fields; no traversal or list conversion |
| `ExecutionPayload`, `NewPayloadRequest` | nominal nineteen-/four-field structures (§5) | ordered tuple of all whole fields | identity; complete byte/word/ordered nested observations | none beyond existing field domains | immutable records; read-only payloads may be shared | O(1) structural field work at fixed field counts; no byte/member traversal; allocation, retention and discarded-payload reclamation remain unmeasured (C1–C4, ARCHITECTURE §5.0) |
| `ExecutionPayload` SSZ adapters | nineteen-member progressive value (§5) | complete ordered field/container model | public Base observers and actual Withdrawal adapters | exactly extraData bound in wire validity | immutable raw bytes/ordered arrays retained | O(transaction + withdrawal count) traversal plus fixed-field conversion; no extra/BAL byte copy; native allocation/retention/reclamation costs unmeasured |
| `ExecutionRequests` SSZ adapters | five lists of actual item models (§5) | complete ordered aggregate | actual child dictionaries | wire validity is True | immutable record | O(total items) traversal at fixed field widths, preserving every item |
| `NewPayloadRequest` SSZ adapters | ordinary four-member value (§5) | whole actual child models and ordered hash bytes | public provider models/inversion certificates and Base checked constructors | composed actual child wire validity | immutable bytes and arrays retained | O(payload transactions + withdrawals + hashes + request items) traversal plus fixed-field conversions; allocation/retention/reclamation unmeasured (C1–C4) |
| `StatelessInput` | nominal three-field structure over actual request/witness/Base.U64 providers | ordered tuple of all three whole fields | identity, preserving all nested bytes/words/ordered arrays | none beyond provider domains | immutable record; read-only payloads may be shared | O(1) structural field work at three fields; no byte/member traversal; allocation, retention and discarded-payload reclamation remain unmeasured (C1–C4, ARCHITECTURE §5.0) |
| `StatelessInput` SSZ adapters | ordinary three-member value (§5) | complete actual request/witness models and unsigned chain ID | actual public provider models/inversion certificates and checked Base constructor | composed actual child wire validity | immutable payloads retained | O(request adapter work + witness member count); no additional member-byte copy; allocation/retention/reclamation unmeasured (C1–C4) |
| prospective input wire codecs | SSZ descriptors over the raw carriers | the SSZ value | SSZ `encode`/`decode` | prospective `WF`: witness bounds, payload `extraData.size ≤ maxExtraDataBytes` and other schema obligations | immutable after decode | prospective decode O(input); `hash_tree_root` O(size) SHA-256 compressions |
| `StatelessValidationResult` | structure | 4-tuple | `serialize` = fixed 43-byte layout (LE `chainId`, LE `schemaId`, boolean byte) | none | value | O(1) |
| `GuestOutcome` | inductive | the O-row plus fields | `toResult` | `valid`/`invalid` only carry `schemaId = 0x1501` implicitly | value | O(1) |
| header chain result | `Array AnyHeader × Array Hash32` | a list of headers with hashes | `hashes[i] = keccak(raw[i])` | contiguity (R4) | linear-only | O(Σ header bytes) keccak |
| requests wire form | `Array ByteArray` | list of `type ++ body` blobs | `encodeExecutionRequests` | strictly ascending type, non-empty bodies | value | O(total bytes) |

Widths: `blockNumber`, `gasLimit`, `gasUsed` are `Uint` in EELS but SSZ `uint64` (`types.py:57–62`); `timestamp` is `U256` with SSZ `uint(64)`; `baseFeePerGas` is SSZ `uint256`. The spec stores the SSZ width and widens explicitly where `Header` needs `Uint`/`U256`; a decoded value is always in range, so no check is lost [V: SSZ decoding rejects values outside the declared field widths]. Consequently the NUMBER, GASLIMIT and BASEFEE `U256` conversions in the VM cannot overflow; only BLOBBASEFEE (computed, not decoded) can (O13).

## 7. Contract and laws

The supplied `ProtocolFork` carrier admits all and only the 21 §3 identifiers.
Its explicit `toIndex` match is the legible executable reference. Private facade
clients establish arbitrary dependent elimination, each branch, the complete
quantified mapping and tag injectivity by ordinary cases/reduction. There are no
proof premises or additional public laws. This finite contract supplies no inverse,
schema selector, decoder or guest/refinement theorem.

The supplied wire-limit aliases reduce to the five Fork-owned constants (§3/§5).
This data contract adds no public law family, schema certification or wire admission.

**Supplied raw execution witness contract.** The public constructor/projections have
exactly the §5 types. For arbitrary arrays, construction retains all three complete
values, reconstruction returns the original record and updating any one field retains
the other two. Private facade clients discharge these equations directly, without
additional admission or a public law family. The raw model has no wire-size, nonempty,
RLP, header-chain, database or hash invariant. The separate actual schema is certified below; decoding and guest composition remain
open, and no execution or refinement theorem follows.

**Supplied raw stateless input contract.** The §5 constructor accepts the three
arbitrary complete independent provider values in source order. Reconstruction
returns the original record; equality of all three whole fields determines it.
Each independent update retains the other two whole fields. The §4 private facade
clients prove these equations by ordinary structure operations and public provider
laws. The identity model has no wire-size, validity or consistency premise, effect
or failure; it adds no authored public law family. Prospective input WF/schema,
decoding, root support, guest composition and backend/security/resource gates
remain open (§10).


**Private encoding-size laws.** In `InputSszCallerProofs.lean`, let `L(t,v)` denote
the complete local logical-size recursor from §3. For every raw `t`, `v` and
`h : Ssz.Serializable t v`, the ordinary private law is
`(Ssz.encode t v h).size = L(t,v)`. If additionally `t.fixedSize? = some n`, the
actual encoded size is `n`, including `n = 0`. The fixed-width model argument uses
supported container arity and the public structural-width fold; it adds no
positive-width or child-root premise.

For the exact layout fold in public `Ssz.encode_eq`, the private length equation
is the sum over `ps.zip bs` of each actual child byte length plus four precisely
when that child's descriptor is variable. This equation needs no declared-width
assumption and describes only the zipped occurrences if lengths differ. Applying
it to an encoder result constructs a length-aligned ordered child-byte certificate
from actual child support. Each certificate identifies complete child bytes for
every support proof. Replacing a fixed child's actual length by its declared width
then uses the supported fixed-width law; replacing a variable child's length uses
the induction hypothesis. Thus no fixed child is silently assumed to have its
declared width. These private laws neither complete unsupported encodings nor
establish actual input-to-Rootable or decoder success.


**Private actual request size laws.** For raw payload `p`, aggregate `a` and request
`q`, define the following ordinary natural expressions in the same caller module:

```text
T(transactions) = 4 * transactions.size + sum(transactions.toList.map ByteArray.size)
P(p) = 540 + p.extraData.size + T(p.transactions) + 44 * p.withdrawals.size +
  p.blockAccessList.size
A(a) = 20 + 192 * a.deposits.size + 76 * a.withdrawals.size +
  116 * a.consolidations.size + 184 * a.builderDeposits.size + 68 * a.builderExits.size
R(q) = 44 + P(q.executionPayload) + 32 * q.versionedHashes.size + A(q.executionRequests)
```

The private `transactionSize`, `payloadSize`, `requestsSize` and `requestSize`
definitions express `T`, `P`, `A` and `R`. Their `*_logical_size` laws equate each
expression to `L` of the actual transaction model or actual named dictionary/model.
They hold for every raw array/record, without Serializable, validity, WF, Rootable
or count hypotheses. Empty transaction occurrences still contribute their offset
table entries. Raw extra data above its wire limit still contributes its complete
length; this formula supplies no encoding for that unsupported value.

Each corresponding `*_encoded_size` law needs only
`h : Ssz.Serializable t v` for exactly the encoded member's actual `t` and `v`.
It composes the generic private encoded-length theorem with the raw formula,
without an enclosing-input, validity or unrelated support premise. The actual
Withdrawal classifier gives `some 44`; the five actual request-item classifiers
give `some 192`, `some 76`, `some 116`, `some 184` and `some 68` in source order.
The corresponding item encoded-width laws use only that item's local support.
These classifications concern the actual descriptors and preserve arbitrary
zero-width generic schemas.

The three private `*_children_serializable` laws project actual enclosing support
through public `Ssz.serializable_iff`. A request supplies support for its actual
payload, hash list, parent root and aggregate. A payload supplies its actual
transaction list, Withdrawal list, extra-data leaf and BAL leaf. An aggregate
supplies all five actual lists. The corresponding member laws retain the actual
arrays and public item models, with support for every member of each mapped list,
including the hash members. No empty, duplicate or reordered occurrence is removed,
and no `.valid` hypothesis is turned into operation support. These projections
supply no whole-input support, count/leaf bound, later outer-start bound, request
Rootable or decoder/WF result.

**Supplied raw payload/request contract.** Each §5 constructor accepts all
nineteen/four arbitrary independent raw fields with their exact types and order,
retaining every complete value. Reconstruction returns the whole record; equality
of all fields or complete byte/unsigned/nested ordered observations determines it.
Each single-field update preserves every sibling, including whole nested payload
and execution-request values. The §4 private clients prove these equations and
public conversion recovery without unfolding Base representation internals.
ByteArray and Array observations retain all bytes, member order and duplicates.
Generated structure operations suffice; all supplementary clients, observations,
determination proofs and controls remain private. There is no extra raw invariant,
validation, schema, failure/effect or public law family. Root support, wire
admission, request validation and guest composition remain separate (§10).

**Supplied raw execution-request aggregate contract.** The §5 constructor accepts
five arbitrary independent arrays of the exact existing nominal item types and
retains every array unchanged. Reconstruction returns the complete record, and
equality of all five fields or all five complete `Array.toList` observations
determines the record. Updating any one field preserves the other four arrays.
The private facade clients in §4 prove these equations and public Array conversion
recovery. No count, wire-size, nonempty, validity, sorting or deduplication premise
is required. Ordinary generated structure support suffices, without an authored
public law family. The actual aggregate schema and private operation-support clients
are supplied below. Roots, raw decoding and guest composition remain separate (§10).


**Supplied stateless input certificates (Q81).** With
`s := StatelessInput.instSszSchema`, exactly these three public laws are supplied:

```lean
theorem StatelessInput.ssz_type_wellFormed : s.type.WellFormed
theorem StatelessInput.ssz_ofValue_toValue (a : StatelessInput) (h : s.valid a) :
  s.ofValue? (s.toValue a) = some a ∧ Codec.SszValue.WellTyped s.type (s.toValue a)
theorem StatelessInput.ssz_toValue_ofValue (v : Codec.SszValue) (a : StatelessInput)
    (h : Codec.SszValue.WellTyped s.type v ∧ s.ofValue? v = some a) :
  s.valid a ∧ s.toValue a = v
```

WF and forward reconstruction/typing compose the actual child certificates and
public U64 laws. Reverse derives each child's actual WT from outer WT, obtains
its successful reconstruction independently, and passes both to the child's public
certificate. The result retains both child validity predicates and the complete
three-member model. All support/count/layout/control facts remain private; no
unconditional inverse success, off-WT completion, decoder or root law is published.

**Supplied new-payload request certificates (Q81).** With
`s := NewPayloadRequest.instSszSchema`, exactly these three public laws are supplied:

```lean
theorem NewPayloadRequest.ssz_type_wellFormed : s.type.WellFormed
theorem NewPayloadRequest.ssz_ofValue_toValue (a : NewPayloadRequest) (h : s.valid a) :
  s.ofValue? (s.toValue a) = some a ∧ Codec.SszValue.WellTyped s.type (s.toValue a)
theorem NewPayloadRequest.ssz_toValue_ofValue (v : Codec.SszValue) (a : NewPayloadRequest)
    (h : Codec.SszValue.WellTyped s.type v ∧ s.ofValue? v = some a) :
  s.valid a ∧ s.toValue a = v
```

WF composes actual child WF. Forward reconstruction/typing uses actual child
validity and certificates, with complete Base byte observations. Reverse derives
actual child WT from outer WT and separately obtains inverse success, retaining
both when applying each child's public reverse certificate. Count/support/layout
facts remain private. These laws add no decoder completeness, rejection or root law.

**Supplied aggregate schema certificates (Q81).** With
`s := ExecutionRequests.instSszSchema`, exactly these three public laws are supplied:

```lean
theorem ExecutionRequests.ssz_type_wellFormed : s.type.WellFormed
theorem ExecutionRequests.ssz_ofValue_toValue (a : ExecutionRequests) (h : s.valid a) :
  s.ofValue? (s.toValue a) = some a ∧ Codec.SszValue.WellTyped s.type (s.toValue a)
theorem ExecutionRequests.ssz_toValue_ofValue (v : Codec.SszValue) (a : ExecutionRequests)
    (h : Codec.SszValue.WellTyped s.type v ∧ s.ofValue? v = some a) :
  s.valid a ∧ s.toValue a = v
```

The descriptor proof uses every actual child WF certificate and public mask equations.
Private ordinary traversal induction lifts each public child adapter certificate.
The reverse direction retains the single WT-and-success conjunction and uses both
premises for every child. Both directions preserve complete records and all ordered
members. Count, support, layout and control facts remain private and supply no
additional public helper or law class. No byte inverse, root or source-host theorem
follows from these certificates.

**Supplied raw request-item contract.** Each of the five §5 constructors admits
arbitrary independently supplied Base fields and retains every field exactly.
Reconstruction returns the whole record, and updating one field preserves every
sibling. Complete byte/unsigned observations determine the record through public
Base laws. The private facade clients in §4 prove these equations for arbitrary
values, together with each field's checked recovery, size/range and `U64` model
observations. This identity contract has no additional invariant or authored public
law family. All five types remain nominally distinct, and the request withdrawal
is separate from the EthBlock `Withdrawal`. The actual item dictionaries and their certificates are supplied below. Wire
admission, execution and source-host correspondence remain separate obligations.

**Supplied request-item schema certificates (Q81).** For each block below,
`s` denotes that block's actual `X.instSszSchema`, without an arbitrary dictionary.
Exactly these fifteen public theorem types are supplied:

```lean
-- s := DepositRequest.instSszSchema
 theorem DepositRequest.ssz_type_wellFormed : s.type.WellFormed
 theorem DepositRequest.ssz_ofValue_toValue (a : DepositRequest) (h : s.valid a) :
  s.ofValue? (s.toValue a) = some a ∧ Codec.SszValue.WellTyped s.type (s.toValue a)
 theorem DepositRequest.ssz_toValue_ofValue (v : Codec.SszValue) (a : DepositRequest)
    (h : Codec.SszValue.WellTyped s.type v ∧ s.ofValue? v = some a) :
  s.valid a ∧ s.toValue a = v

-- s := WithdrawalRequest.instSszSchema
 theorem WithdrawalRequest.ssz_type_wellFormed : s.type.WellFormed
 theorem WithdrawalRequest.ssz_ofValue_toValue (a : WithdrawalRequest) (h : s.valid a) :
  s.ofValue? (s.toValue a) = some a ∧ Codec.SszValue.WellTyped s.type (s.toValue a)
 theorem WithdrawalRequest.ssz_toValue_ofValue (v : Codec.SszValue) (a : WithdrawalRequest)
    (h : Codec.SszValue.WellTyped s.type v ∧ s.ofValue? v = some a) :
  s.valid a ∧ s.toValue a = v

-- s := ConsolidationRequest.instSszSchema
 theorem ConsolidationRequest.ssz_type_wellFormed : s.type.WellFormed
 theorem ConsolidationRequest.ssz_ofValue_toValue (a : ConsolidationRequest) (h : s.valid a) :
  s.ofValue? (s.toValue a) = some a ∧ Codec.SszValue.WellTyped s.type (s.toValue a)
 theorem ConsolidationRequest.ssz_toValue_ofValue (v : Codec.SszValue) (a : ConsolidationRequest)
    (h : Codec.SszValue.WellTyped s.type v ∧ s.ofValue? v = some a) :
  s.valid a ∧ s.toValue a = v

-- s := BuilderDepositRequest.instSszSchema
 theorem BuilderDepositRequest.ssz_type_wellFormed : s.type.WellFormed
 theorem BuilderDepositRequest.ssz_ofValue_toValue (a : BuilderDepositRequest) (h : s.valid a) :
  s.ofValue? (s.toValue a) = some a ∧ Codec.SszValue.WellTyped s.type (s.toValue a)
 theorem BuilderDepositRequest.ssz_toValue_ofValue (v : Codec.SszValue) (a : BuilderDepositRequest)
    (h : Codec.SszValue.WellTyped s.type v ∧ s.ofValue? v = some a) :
  s.valid a ∧ s.toValue a = v

-- s := BuilderExitRequest.instSszSchema
 theorem BuilderExitRequest.ssz_type_wellFormed : s.type.WellFormed
 theorem BuilderExitRequest.ssz_ofValue_toValue (a : BuilderExitRequest) (h : s.valid a) :
  s.ofValue? (s.toValue a) = some a ∧ Codec.SszValue.WellTyped s.type (s.toValue a)
 theorem BuilderExitRequest.ssz_toValue_ofValue (v : Codec.SszValue) (a : BuilderExitRequest)
    (h : Codec.SszValue.WellTyped s.type v ∧ s.ofValue? v = some a) :
  s.valid a ∧ s.toValue a = v
```

Private ordinary checked-constructor lemmas preserve all 17 field occurrences
and complete ByteArray/Nat observations. The public Base inverse, size and range
laws and public Codec WF/WT equations establish these certificates, without
foreign private unfolding. Private §4 clients separately establish actual support,
count recovery and complete fixed wire layout. Those facts add no public theorem
family, schema field, decoder, root or execution guarantee.

**Supplied witness schema certificates (Q81).** For the actual named dictionary
`s := ExecutionWitness.instSszSchema`, exactly these public types are supplied:

```lean
theorem ExecutionWitness.ssz_type_wellFormed : s.type.WellFormed
theorem ExecutionWitness.ssz_ofValue_toValue (a : ExecutionWitness) (h : s.valid a) :
  s.ofValue? (s.toValue a) = some a ∧ Codec.SszValue.WellTyped s.type (s.toValue a)
theorem ExecutionWitness.ssz_toValue_ofValue (v : Codec.SszValue) (a : ExecutionWitness)
    (h : Codec.SszValue.WellTyped s.type v ∧ s.ofValue? v = some a) :
  s.valid a ∧ s.toValue a = v
```

Private ordinary structural extractor proofs preserve every byte-tagged member,
whole list and whole recovered record. Public Array laws and the public Codec WF/WT
equations establish all three certificates. No foreign private recursor is unfolded.
The validity and reverse WT-plus-success hypotheses are retained. Serializable,
Rootable, decoder admission/canonicality, source backing and host premises remain
separate; no wire/root theorem family or public helper is supplied.

**Supplied payload schema certificates (Q81).** For the actual named dictionary
`s := ExecutionPayload.instSszSchema`, exactly these public types are supplied:

```lean
theorem ExecutionPayload.ssz_type_wellFormed : s.type.WellFormed
theorem ExecutionPayload.ssz_ofValue_toValue (a : ExecutionPayload) (h : s.valid a) :
  s.ofValue? (s.toValue a) = some a ∧ Codec.SszValue.WellTyped s.type (s.toValue a)
theorem ExecutionPayload.ssz_toValue_ofValue (v : Codec.SszValue) (a : ExecutionPayload)
    (h : Codec.SszValue.WellTyped s.type v ∧ s.ofValue? v = some a) :
  s.valid a ∧ s.toValue a = v
```

Private ordinary traversal proofs preserve every complete transaction/Withdrawal and
all nineteen positions. Descriptor WF consumes the actual Withdrawal WF certificate.
Forward conversion uses public Base constructor/observer laws and each actual child
forward certificate. Reverse conversion obtains every positional WT fact from Codec's
public equation, then pairs each Withdrawal WT fact with its successful actual inverse
before applying that child's public reverse certificate. It unfolds no foreign private
inverse and assumes no general typing or surjectivity from reconstruction success.
Exact byte recovery transfers the extra-data WT bound to recovered validity. All
support, layout, count and finite control facts remain private; no extra API is supplied.

**Supplied output laws.** `STFSpec/Stateless/Output.lean` supplies the ordinary
`serializeStatelessOutput_eq` complete byte-list equation, `serializeStatelessOutput_size`
for every carrier value, and `serializeStatelessOutput_inj` (equal bytes iff equal records).
The latter discharges only the serialization direction of L-output-codec.
`zeroSentinel_fields` specifies all four fields and `serializeStatelessOutput_zeroSentinel`
specifies all 43 zero bytes. The private concrete Q80 schema/value/support and child
certificates consume `Ssz.serializable_iff`, `Ssz.encode_eq`, structural classifier laws
and public Base laws; no generic schema instance or raw decoder is supplied. All
UInt16 schema IDs serialize without guest-policy restrictions. The boolean and integer
byte equations establish output layout, without asserting that a supplied root commits
to any request.

**Outcome mapping (D14).**

| Row | Spec path | Output |
|---|---|---|
| O1 | `classify` → `.decodeFailed e` | `zeroSentinel` |
| O2 | no constructor: `computeNewPayloadRequestRoot` is total ([T] L-root; to be proved, DECISIONS §3 O2) | — |
| O3 | `.invalid r c (.headers e)` | `(r, false, c, 0x1501)` |
| O3a | `.invalid r c .missingParentHeader` | same |
| O4 | `.invalid r c (.block (.witness e))` (constructors in `EthStateWitness`/`EthCommit`) | same |
| O5 | retired by CONTRACT O5 and P1; ID retained, no current input-hint path | — |
| O6 | `.invalid r c (.payload e)` or `.invalid r c (.block e)` for header/body/root errors; on the guest path every payload-transaction decode failure is `.payload (.invalidVersionedHashes cause)` | same |
| O7 | `.invalid r c (.block (.invalidTransaction i e))` | same |
| O8, O9 | no outcome here: consumed inside `EthVmRunner`/`EthPrecompiles` | — |
| O10 | `.valid r c` | `(r, true, c, 0x1501)` |
| O11 | `classify input = .error e` | checked runner `.error e`; public function `zeroSentinel` |
| O12 | none authorized (DISC-001, unresolved) | — |
| O13 | `.invalid r c (.block e)` with the named fault constructor: `.vmFault (.ancestorHashUnavailable _)` (BLOCKHASH, `vm/instructions/block.py:58`), `.arith .chainIdOverflow` (`transactions.py:873`), and the other enumerated sites (EthBlock §2.12); never a catch-all | same |

**Laws.**
- [T] **L-total**: `runStatelessGuest` is a total `def` (structural/well-founded; no `partial`).
- [T] **L-root**: `computeNewPayloadRequestRoot` is total on decoded values, discharging `stateless.py:216`; consequently O2 is unreachable. If the proof fails, O2 gets a constructor instead (DECISIONS §3, O2).
- [T] **L-internal** ([REVIEW §7](../REVIEW.md#7-acceptance-criteria-proof-gates-composition-cases-replacement-and-cost-checks) G7): `∀ input, ∃ out, runStatelessGuestChecked input = .ok out`. Discharged from `EthVmRunner` fuel sufficiency plus the absence of any other `InternalError` source here. Consumers refine the public function through it: `runStatelessGuest input = out ↔ runStatelessGuestChecked input = .ok out`.
- [R] **L-size**: `(runStatelessGuest input).size = 43`.
- [R] **L-decode-phase**: `deserializeStatelessInput input = .error e → runStatelessGuest input = serialize zeroSentinel`.
- [R] **L-fields**: `deserializeStatelessInput input = .ok x →` the output decodes to a result with `root = computeNewPayloadRequestRoot x`, `chainId = x.chainId`, `schemaId = 0x1501`. So the non-validity fields depend only on the decoded input (the property verifiers rely on).
- [R] **L-valid**: `successfulValidation = true ↔` `validateHeaders` succeeds with non-empty headers and `executeNewPayloadRequest` over the witness backend succeeds. Stated as an equation on `classify`, this is the top-level seam equation.
- [C] **L-decode-canonical**: `deserializeStatelessInput b = .ok x ↔ b = schemaIdBytes ++ encode x ∧ x.WF` (from `EthCodec` SSZ laws; Q88 fixes the success domain, and every rejection is O1 whatever its `SszError` tag).
- [C] **L-output-codec**: `serializeStatelessOutput` is injective, and the host-side decoder (`EthConformance`) is its left inverse.
- [C] **L-headers**: `validateHeaders hs = .ok (ds, bh) → ds.size = hs.size ∧ bh = hs.map keccak256 ∧ ∀ i, 0 < i → ds[i].parentHash = bh[i-1]`, and conversely on success of every decode; error precedence as in R4.
- [C] **L-requests**: `encodeExecutionRequests` emits one blob per non-empty list, strictly ascending type bytes `0x00…0x04` (`forks/amsterdam/requests.py:71–100`, owned by `EthBlock` [V]), each body a concatenation of fixed-size items; `decodeExecutionRequests ∘ encodeExecutionRequests = .ok` (`EthConformance`).
- [C] **L-payload-header**: `isValidBlockHash consts p pbr rq = (keccak256 (rlp (payloadHeader consts p pbr rq)) == p.blockHash)`.
- [C] **L-versioned**: `isValidVersionedHashes req = true ↔` every tx decodes and the concatenated blob hashes equal `req.versionedHashes`.
- [R] **L-constants** (F20): prove the acquisition and effect order in R5 as implementation equations, and prove preservation of one supplied record through witness construction, both payload-header constructions, block entry and context consumers. Check these equations with a synthetic oracle whose constants differ from literals (§4). Generic interpretation coupling remains D5/X7.
- [R] **L-backend-generic**: `executeNewPayloadRequest` uses `pre` only through the `PreState m` operations (it forwards the same `consts` to `executeBlock` after ordered payload checks). This is what `EthSecurity` needs to move from the witness backend to the full-state backend.
- **L-hint-equivalence:** retired for this input under CONTRACT §2/O5 and P1. Backend-generic agreement and sender-recovery correctness remain separate obligations.
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
- **Seams consumed:** the five Fork-owned input wire limits through the supplied §5 aliases (F8); `executeBlock` and `ChainContext` (`EthBlock`, via the `EthFork` Amsterdam composition); the witness-state `PreState` constructor `WitnessBackend.build` (pure: it takes already-built DBs) and the monadic builders `CodeDB.build` (`EthStateWitness`) and `NodeDB.build` (`EthCommit`) (F4); `HashConsts.query`; SSZ `SszType` instances, `hashTreeRoot`, RLP `decodeTo`/`encode` and keccak (`EthCodec`/`EthHash`, reachable transitively); unsecured-trie `root` for the transactions and withdrawals roots (`EthCommit`, via `EthBlock`); `computeRequestsHash` (`EthBlock`).
- **Seam provided:** `runStatelessGuest` (L7), `classify` (diagnostic O-row), `executeNewPayloadRequest` (payload → block, backend-generic).
- **Cross-module invariants relied on:** the witness backend never throws outside `Except`; every `WitnessError` is a value (D8); `executeBlock` reports all failures as `BlockError` constructors; `EthVmRunner` reports fuel exhaustion only as `InternalError`, never as an EVM outcome (O11). **Guaranteed:** every `PreState` passed to `executeBlock` is the witness backend rooted at `parent_header.state_root`; `ChainContext.blockHashes` equals `witness.headers.map keccak256` with `last = keccak(rlp parent)`.

## 9. Open decisions

- **D14** (accepted): this module is where the O-table becomes constructors, including the enumerated O13 faults. Local choices: O2 is represented by a totality theorem, not a constructor (open: prove it, DECISIONS §3 O2); every payload-transaction decode failure is attributed to `invalidVersionedHashes` because that is where EELS first consumes it.
- **D5** (provisional, broad): every keccak here goes through `KeccakQuery`: the header-chain hashes (R4), the block-hash check (`isValidBlockHash`), the transactions/withdrawals trie roots in `payloadHeader`, the BAL hash and the witness DB builds (F18). See `EthSecurity`.
- **Q88** (accepted): the SSZ decoder accepts exactly the canonical encodings of
  Serializable, CountRecoverable values, with unordered rejection tags. `decodeInput`
  is its first implementation; every rejection is O1.
- **D13** (runner shape): fuel is internal to the runner; fuel exhaustion reaches this module only as `InternalError` in `CheckedT` (O11).
- **D8**, **D19** (witness errors, eager decoding): consumed through `BlockError.witness`.
- **D3** (Amsterdam only): the previous-fork header is the one place a second fork's type appears; it is decoded only, never executed.
- **D18** (implementation policy): no local debt expected.
- Public diagnostic `classify`: resolved, DECISIONS B12 (Q4).
- Fork-activation check: resolved, DECISIONS Q5 (follow the reference; explicit exclusion, CONTRACT §5).

## 10. Gaps

- **Implemented protocol fork metadata.** The complete 21-constructor carrier,
  total forward tag observation and private complete facade proofs/guards are supplied
  in §3–§7. Amsterdam schema-index/revision/ID values remain a separate F8 follow-on:
  Fork cannot import this Stateless-owned enum, and the planned nominal
  `schemaForkIndex` selector has no specified dependency-safe bridge. Reconcile that
  seam without inferring an inverse, moving ownership or changing the selector type.
  This metadata closes no schema, admission, guest, resource or readiness gate.

- **Implemented raw execution witness.** The exact three-field carrier and private
  complete facade clients/finite controls are supplied in §3–§7. The actual witness SSZ dictionary and exactly its three Q81 certificates are supplied
  in §3/§5/§7, with complete private controls in §4. Input wire
  admission, RLP/header validation, database construction,
  hashing and guest composition remain unimplemented. The five size-limit aliases
  are supplied under F8 (§3/§5), without implementing those consumers. Input hint retirement follows CONTRACT §2/O5 and P1, as recorded below. This carrier
  closes no input, guest, resource or readiness gate.

- **Implemented raw request items.** The five nominal carriers and all 17 complete
  independent fields are supplied under §3/§5/§7, with private arbitrary facade
  clients and whole finite controls in §4. Their five actual Q81 dictionaries and
  fifteen ordinary descriptor/adapter certificates are supplied in §3/§5/§7, with
  private actual Serializable, CountRecoverable and whole-wire clients/controls
  in §4. Root support, Q88 raw decoding, request wire constants,
  `encodeExecutionRequests`, roots and payload/input/guest composition remain
  unimplemented. Source class/reflection/cache/coercion/backing and host agreement
  remain separate. No runtime admission, protocol validation, resource, security,
  cost or readiness obligation is discharged by these raw carriers.

- **Implemented raw execution requests.** The exact five-array aggregate and private
  arbitrary complete facade clients/finite controls are supplied in §3–§7. Its
  actual aggregate Q81 dictionary and three certificates, with private Q80 support,
  count recovery and full-wire controls, are supplied in §3/§4/§5/§7. Root support
  and source-decoder correspondence remain separate. Request wire constants/encoding,
  roots and payload/request/input/guest composition remain unimplemented. No admission,
  effect, resource, security, cost or readiness gate is discharged by this raw carrier.

- **Implemented raw payload/request carriers.** The exact nineteen-field
  ExecutionPayload and four-field NewPayloadRequest over actual provider types,
  private complete arbitrary facade clients and whole finite controls are supplied
  in §3–§7. The actual payload dictionary and its three Q81 certificates are supplied in
  §3/§5/§7, with private complete clients/count recovery and finite wire controls in §4.
  The actual NewPayloadRequest dictionary and its three Q81 certificates are supplied
  in §3/§5/§7, with private complete clients/count/layout and 96-case whole-wire
  controls in §4. General Q80 source refinement,
  Q88 raw decoding, root support/O2, block/header adapters and validation,
  request encoding, F20/D5, input/guest/errors/fuel/S2/security and resources/costs
  remain separate. Static source-field correspondence supplies no source runtime,
  backing/coercion/cache/host or guest agreement; O12 remains with its owner.
  No execution, resource, security, cost or readiness gate closes.

- **Implemented raw stateless input.** The exact three-field carrier, identity
  model, private arbitrary complete facade clients and nested finite controls are
  supplied in §3–§7. This module's input hint fields, arguments, limits, cases,
  O5 mapping and L-hint-equivalence guidance follow CONTRACT §2/O5 and P1.
  The actual input dictionary and three Q81 certificates, private count/support/layout
  clients and complete 48-input/385957-byte mathematical wire controls are supplied
  in §3/§4/§5/§7. The private generic public-law encoding-size foundation and its
  30-case/183-byte controls, actual raw request-size formulas, operation-local
  encoded-size laws, fixed classifications and inherited child/member support are
  supplied in §3/§4/§7. Whole-input request support, later outer-start and count/leaf
  bounds, decoded support and input-to-Rootable bridges remain open. Q87/Q88 decoding, general source serialization agreement, root/O2, caller/guest execution, errors/fuel/F20/D5/backend/S2,
  source-host agreement and resource/security/cost/readiness obligations remain open.
  Other owners' X16 execution/hint migration remains separate, as recorded below.

- **Implemented output slice.** The concrete output record, serializer and sentinel, with their ordinary laws, are supplied in §3/§7 and bounded controls in §4. The host-side decoder left inverse in L-output-codec remains open. Decoder-to-Rootable bridges, request-root computation, guest classification/execution, F20 composition and O-row/fuel/backend/resource gates are separate; this slice closes none of those obligations.

- **Checked control handoff:** Runner §3/§5/§7 supplies minimal source-free internal-error and checked carriers. Actual classification/propagation and O11 checked/public guest projection remain unimplemented; no internal-error-freedom result follows, and F11/G2–G7 remain open.

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **Fork activation (explicit exclusion).** The guest never checks the payload timestamp against Amsterdam activation (`stateless.py:267–269`), and nothing checks that witness headers belong to the forks their shape suggests. A payload from before activation, or a chain whose parent header is of the previous-fork shape at any timestamp, is validated with Amsterdam rules. The spec follows the reference; any consumer claiming "valid Ethereum block" must add this check or take it as an external anchor (CONTRACT §7).
- **Previous-fork fallback is shape-based.** `_decode_header` tries the BPO5 header shape only. The BPO2 and BPO5 `Header` classes have the same 21 fields (checked by parsing both at e1a316a0 [V]), and the shape has been unchanged since `requests_hash` was added, so any post-Prague header decodes through the fallback [I: Prague/Osaka not parsed]; an older shape (fewer fields) is O3. Whether the fallback should be restricted to the *parent* position, or to headers before activation, is unspecified upstream; the spec accepts it anywhere, as EELS does.
- **`DecodingError` versus other exceptions in `_decode_header`.** The fallback fires only on `rlp.DecodingError`. If `ethereum-rlp` 0.1.6 raises another exception type for some malformed Amsterdam header (for example from a field constructor), EELS skips the fallback; the output is the same (inner failure), but the constructor differs. Unchecked.
- **Missing BLOCKHASH ancestor** is a Python negative-index `IndexError` (`vm/instructions/block.py:58`), fixture-witnessed. It is O13 with the named constructor `VmFault.ancestorHashUnavailable` (`EthVmCore`/`EthVmInstructions`), not O4 or O6 (R5). Note that an ancestor deeper than the witness but within 256 blocks fails the block, while one beyond 256 returns zero without touching the witness.
- **O2** has no fixture and no reachable spec path; L-root is unproved (open, DECISIONS §3 O2). If a future SSZ type made `hash_tree_root` partial (e.g. a resource limit), the constructor would be needed.
- **O12 candidates (DISC-001, unresolved).** The guest-process recursion limit is 100,000 (py_ecc raises it; `import ethereum` alone gives 12,288). (a) Deep RLP nesting in a witness header or transaction: 20,000 levels decode and 40,000 raise `RecursionError` in `ethereum-rlp` (witnessed by probe inputs). For a transaction it is caught inside `is_valid_versioned_hashes` and becomes O6 (DISC-006); for a header, in the inner phase. Since valid headers and transactions have bounded nesting, the output probably coincides with the spec's structural failure [I]. (b) Eager witness decoding (`incremental_mpt.py:892–1026`) has no depth or key-length bound; a finite, acyclic DB with a deep chain of nested hashed nodes reachable from a crafted parent `state_root` would make EELS raise `RecursionError` (→ `false`), while a spec decoder without a depth limit could accept it. The depth at which this happens under the 100,000 limit has not been re-measured (the earlier "~1,000 nodes" estimate predates it). This is a guest-level divergence on crafted inputs, uncovered by fixtures, and needs a reproducer and a decision with `EthStateWitness`.
- **Input size envelope.** Transactions, the BAL bytes and the progressive lists are unbounded in SSZ; the largest fixture input is 8.4 MB. There is no stated maximum input, memory or cycle envelope; `EthBase`'s `Envelope` record does not yet cover the guest.
- **SSZ progressive types.** Correctness of `ProgressiveContainer`/progressive-list decoding and merkleization rests on `eth-remerkleable` 0.1.31 (EIP-7495/EIP-7916 as implemented there). EthCodec implements progressive merkleization, roots and forward encoding (Q75, Q79, Q80); progressive decoding is specified (Q88) but unimplemented, and no independent reference beyond `eth-remerkleable` 0.1.31 is pinned.
- **`payloadHeader` totality** is inferred: EELS catches any exception there, and the spec asserts none can occur on decoded values. Needs a line-by-line check of `Header` field constructors (e.g. `Uint`/`U256` widening, `Bytes8`).
- **Order of `legacyDecode`.** `_payload_transaction_to_block_transaction` asserts the decoded type is legacy; after `is_valid_versioned_hashes` succeeds this is believed dead [I]; unproved.
- **Input hint retirement.** CONTRACT §2/O5 and P1 retire this module's L-hint-equivalence obligation. This supplies no sender-recovery proof or backend/security theorem; the other owners' migration remains X16 work.
- **Error-constructor fidelity is untestable by fixtures** (R8); only reading and `core` cases check it.
- **F20 implementation/refinement:** implement L-constants and establish witness, provider and context coherence at the R5 boundary. DECISIONS §6 records the design; production refinement and generic oracle coupling remain open.
- **Consumer seams.** The exact `Faithful` statement evm-asm and pancaketh want (bytes-level equality versus `classify`-level) is not agreed with them; toolchain skew (they are on v4.33.x) is not addressed here.
- **Upstream churn.** `ExecutionPayloadHeader`/`NewPayloadRequestHeader` are TODO scaffolding (`stateless.py:76–98`) and EIP-7709 may empty `headers`; either change alters this module's wire types.
- **Re-pin to `tests-zkevm@v21.0.6` (GAPS-CROSSCUTTING X16).** This module's raw input and hint-only guidance follow CONTRACT §2/O5 and P1 (§3–§7); no caller, guest or sender recovery is implemented. EthBlock, EthVmCore, EthSecurity and EthConformance retain their separately owned execution/hint migration, together with COMPOSITION's historical hint-adapter paragraphs. Public cryptographic key types elsewhere are outside this input slice. **Request encoding:** `execution_engine/requests.py` uses `REQUEST_ITEM_TYPES` and `SszContainer.encode_bytes` (PR #3658); the §3 `_encode_*` rows are absent. The fixed-size containers retain the field order of the old encoders, so bytes are unchanged [by reading at `59c1473d`; not run]. **Renames:** `PreviousForkHeader` is `PreviousHeader`, and `validate_headers` names `MAX_WITNESS_HEADERS` (still 256) (PR #3655). **Corpus facts:** the §4 facts and zero-sentinel list retain their stated pins; recomputing the v21.0.0 figures is EthConformance's re-pin item.
