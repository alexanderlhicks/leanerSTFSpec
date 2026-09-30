# `EthConformance`: EEST runners, conformance tiers, replayable failures and differential oracles

*Status: informal specification, draft. Date: 2026-09-30. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F16, F20 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: P1, P2, P4, D3, D10, D14, D18 · questions: B14, Q7, Q8, Q9.*

**[V]** marks a claim checked against the pinned archive (`fixtures_zkevm.tar.gz`, sha256 `44cfcb54…be1a`), the pinned source, or by running pinned EELS on fixture inputs; **[I]** marks an inference.

## 1. Purpose

`EthConformance` makes the golden rule (`CONTRIBUTING.md` §1) executable: it runs the spec against the pinned EEST zkevm corpus and reports, per record, whether `runStatelessGuestChecked statelessInputBytes = .ok statelessOutputBytes` byte for byte. It also runs the ordinary blockchain fixtures through the full-state backend (D10), provides the `core` `#guard` suites for the guest, the host-side codecs needed to build and inspect guest inputs, and the drivers for differential testing and fuzzing against external oracles, which find bugs but never decide behaviour (CONTRACT §6.4). It is the top of the core graph (`ARCHITECTURE.md` §3) and is checked as part of the core (`CONTRIBUTING.md` §4).

## 2. Requirements

**R1. Guest runner (decisive).** For every record in `blockchain_tests/**.json`, block entry `b` with fields `statelessInputBytes` and `statelessOutputBytes`, the runner must hex-decode both, call `EthStateless.runStatelessGuestChecked` (never the public projection), and report:
- **pass** iff the result is `.ok out` and `out` equals the expected bytes exactly (43 bytes);
- **mismatch** otherwise, with expected and actual decoded as `StatelessValidationResult` and the spec's `classify` outcome (the O-row and error constructor) for diagnosis;
- **spec bug** on `.error e` (O11; CONTRACT §4): never treated as a guest output, never retried with more fuel.

A mismatch is a failure of the spec (or of the pin), never of the fixture (P2). The runner must not consult `executionWitness` (debug-only, `reference.toml` `debug_only_fields`; guest handbook: "No host manipulation of these bytes is allowed") except to render diagnostics.

**R2. The fixture format consumed** [V, pinned archive]:
- 6,875 JSON files: `blockchain_tests` 3,435, `blockchain_tests_engine` 3,439, `.meta/index.json` 1 (`root_hash 0xa67a1a37…`, `test_count 53419`, forks `Amsterdam` and `BPO2ToAmsterdamAtTime15k`, per-test `fixture_hash`).
- A `blockchain_tests` file maps test ids (`tests/<fork>/<eip>/<file>.py::<test>[fork_…-blockchain_test…]`) to objects with `network`, `genesisBlockHeader`, `genesisRLP`, `pre`, `postState`, `lastblockhash`, `config{network, chainid, blobSchedule}`, `sealEngine`, `_info{hash, fixture-format, filling-transition-tool, …}` and `blocks`.
- A valid block entry has `blockHeader`, `transactions`, `uncleHeaders`, `withdrawals`, `rlp`, `blocknumber`, optionally `receipts`, and (for Amsterdam blocks) `executionWitness{state, codes, headers}`, `statelessInputBytes`, `statelessOutputBytes`, `blockAccessList`. An invalid block entry has `rlp`, `expectException`, optionally `rlp_decoded`, and optionally the three stateless fields (`packages/testing/src/execution_testing/fixtures/blockchain.py:840–925` [V]).
- **All 29,030 guest records are in `blockchain_tests`; `blockchain_tests_engine` carries none** (0 occurrences of `statelessInputBytes` in 3,439 files). The engine format has `engineNewPayloads[]` entries with `params` = `[executionPayload (JSON, camelCase), versionedHashes, parentBeaconBlockRoot, executionRequests (wire-form list)]`, `newPayloadVersion "5"`, `forkchoiceUpdatedVersion "4"`, optional `validationError`/`errorCode`, 29,048 `executionWitness` objects and 25 `executionWitnessMutated: true` flags; top-level keys replace `blocks`/`genesisRLP`/`sealEngine` by `engineNewPayloads`. The two formats are generated from the same test functions (ids differ only in the `-blockchain_test` / `-blockchain_test_engine` suffix), so they duplicate test *cases*, not guest records. `reference.toml` records the corrected counts and location.
- Outputs [V]: 27,822 `(root, true, chain_id, 0x1501)`; 1,199 `(root, false, chain_id, 0x1501)`; 9 zero sentinels (all from `eip8025_optional_proofs/stateless_input_bytes`). **24,283 distinct inputs** among the 29,030 records.
- **Guest records need not describe the fixture's block.** 138 records sit on block entries with `expectException` yet have `successful_validation = true` (85 `INVALID_BLOCK_ACCESS_LIST`, 49 `INVALID_REQUESTS`, 2 `INCORRECT_BLOCK_FORMAT`, 2 combined). In 60 of these checked, the payload `block_hash` in the decoded input differs from the hash of the fixture block's header, and pinned EELS reproduces the recorded output [V]. So a runner must **not** assert `successful_validation = ¬ expectException`, and must not reconstruct the guest input from the block. Conversely, 39 records on valid blocks have `false` (witness/public-key/chain-id/header mutation tests in `eip8025_optional_proofs`).
- 4,807 block entries have no guest record [V]: 4,408 invalid blocks and 399 valid ones, of which 162 are pre-activation blocks of the transition fixtures; the rest (mostly `cancun/eip4844_blobs`, 216) have not been explained (Gaps).

**R3. Stateful blockchain runner via `EthStateFull`.** For each `blockchain_tests` case: build the full state from `pre`, check `genesisRLP` and the genesis hash, then for each block entry decode `rlp` into a `Block` (`EthBlock`), run `executeBlockStandalone` with the provider factory `fun consts ↦ pure (fullState.toPreState consts)`, the chain's last 256 hashes and parent header, and apply the diff (`stateTransition` composes this path). A block with `expectException` must fail (the specific exception class is compared through a mapping table and a class mismatch is reported as a warning only, since EEST exception names are test-framework artefacts; DECISIONS Q9); a block without it must succeed. At the end `postState` (or `postStateHash`) and `lastblockhash` must match. These fixtures are decisive for *block validity and post-state* where they speak (P2), but they are a second test of the same `executeBlock`, not of the guest. Transition fixtures (`for_bpo2toamsterdamattime15k`) contain pre-activation BPO2 blocks that this Amsterdam-only spec cannot execute (D3): the runner must report them as **skipped (fork not instantiated)**, not as failures, and must still run the Amsterdam blocks after them if the pre-state can be obtained (it cannot without BPO2 execution unless the fixture's intermediate state is reconstructed; Gaps).

**R4. Engine runner.** For `blockchain_tests_engine`, convert each `params` into `NewPayloadRequest` (JSON → typed, with `decodeExecutionRequests` for the wire-form requests; `execution_engine/requests.py:236–296`), then run the stateful new-payload path `verifyAndNotifyNewPayload` (`execution_engine/new_payload.py:139–169`) over `EthStateFull`, which catches only `InvalidBlock` and keeps the last 255 blocks. For each request, first derive its chain context (`new_payload.py:146–150`), then acquire `consts ← HashConsts.query` once, build `fullState.toPreState consts`, and call `executeNewPayloadRequest consts req pre ctx none` (`:156–157`; Lean acquisition boundary, F20). The provider and payload kernel receive the same record, and the kernel performs no acquisition. Runs acquire independently; later failures have still made the queries. The runner must report internal failures as spec bugs; the result/error adapter is an implementation gap (§10). `validationError` present ⇔ result `false`. This exercises `executeNewPayloadRequest` with `keys = none`, the payload-to-block conversion and request decoding without the guest. It adds no guest records; its main use is cross-checking the payload path and building extra *non-decisive* guest inputs (R7).

**R5. Tiers** (adopting the tiers of [kim-em/hex-dev](https://github.com/kim-em/hex-dev) @76780a50, `SPEC/testing.md`):
- **`core`** (every push, merge-gating): Lean-only `#guard`/`#guard_msgs` on committed inputs. For the guest: the 9 sentinel inputs (≤ 10,736 bytes each), the O3a record, one record per O-row reachable from fixtures (including the O13 BLOCKHASH fault, fixture `validation_headers_missing_oldest_blockhash_ancestor`), the EELS unit-test inputs ported from `tests/json_loader/test_stateless_guest.py`, round trips of the host codecs, and hand-built adversarial inputs (EthStateless §4). No IO, no archive. `#guard`/`decide` cannot evaluate a term whose dependencies reach a `sorry` leaf, even on a path never taken (F16); schedule such cases after their dependencies are implemented. A `lean_exe` does not make evaluating a proof hole valid; core proof holes are banned.
- **`ci`** (per pull request): a **bounded, deterministic slice** of the corpus: all records under `eip8025_optional_proofs` (the guest-specific area) plus the first *k* records per fixture directory in sorted order (k chosen for a time budget), plus randomized differential checks with a logged seed against the available oracles. A missing optional oracle skips only its differential component; required fixtures never become optional.
- **`local`** (developer-run, weekly per P4): the full 29,030 records, the stateful and engine runners, and long fuzzing campaigns. Reports must state *executed* guest records separately from archive counts and from the 24,283 distinct inputs.

**R6. Replayable failures.** Every failure record must contain: fixture file path and test id, block index, `_info.hash`, the input bytes (or their sha256 and a path into the verified archive), expected and actual outputs, the `classify` outcome, the spec commit, the pin (tag, commit, archive sha256), the Lean toolchain, and, for differential or fuzz findings, the seed, the mutation chain, the oracle name, its version/commit and its output. A failure must be reproducible by one command from that record alone.

**R7. Differential oracles (bug-finding only).**
- **EELS** at the pin (`run_stateless_guest`, and `verify_and_notify_new_payload` for the stateful path), run in the locked Python environment (dependency versions in `reference.toml`; host OpenSSL recorded because `hashlib` supplies SHA-256, RIPEMD-160 and possibly keccak). It is the strongest oracle outside the corpus, but its *execution* is not the reference: disagreements are adjudicated by reading the pinned source, and host-dependent behaviour (O12) is logged under DISC-001. The guest-process recursion limit is 100,000 (py_ecc raises it; `import ethereum` alone gives 12,288), so each oracle run records its environment (Python version, dependency versions, OpenSSL version, `hashlib` capabilities, EELS keccak backend and recursion limits).
- **evm-sail's C build**, **SpecRef's executable** (while it exists), **native clients** (reth/ethrex stateless validators from `eth-act/ere-guests` built for the host; evmone/revm for EVM-level workloads). An oracle lacking Amsterdam semantics (2-D gas, BAL, EIP-8282) is used only on the components it implements.
- Every disagreement produces an R6 record and is settled by the fixtures or, where they are silent, by the pinned source and an upstream report (CONTRACT §6). No oracle output is ever committed as an expected value.

**R8. Fuzzing.** Two input classes:
- *byte/SSZ-level mutation* of corpus inputs (schema bytes, offsets, list lengths, witness nodes, headers, public keys, chain id, payload fields); expected output only from oracles; the spec must never report O11.
- *new blocks*: generate a block by executing a fuzzed transaction list on a known pre-state with the full-state backend, then assemble a `StatelessInput` with `buildStatelessInput` (claimed here, `stateless_host.py:48`) from a witness produced by the **pinned EELS host** (`stateless_host_exec_witness.build_execution_witness`, run out of process). The Lean witness generator is excluded for now (`STFSpec/informal/EXCLUDED.md`).

**R9. Fixture pin verification.** Before any run the tooling must check: archive sha256 = `reference.toml` `release.fixtures.sha256`; archive size; JSON file count 6,875 and guest-record count 29,030; `.meta/index.json` `test_count` and, per test, that `_info.hash` equals the index's `fixture_hash`. Archive integrity is checked by a script (Lean has no gzip); the extracted tree is then consumed by the Lean runner, which rechecks the counts. Passing verification proves nothing about conformance ([REVIEW §7](../REVIEW.md#7-acceptance-criteria-proof-gates-composition-cases-replacement-and-cost-checks), "Report and implementation handoff").

**R10. Host-side codecs.** `serializeStatelessInput` (`stateless_host.py:34–40`) must be the exact inverse of `deserializeStatelessInput`; `deserializeStatelessOutput` (`:43–45`) the left inverse of `serializeStatelessOutput`; `decodeExecutionRequests` must reject empty blobs, non-strictly-ascending type bytes, unknown types and bodies whose length is not a multiple of the item size (`requests.py:236–296`), raising `InvalidBlock`.

**R11. Failure ledger (X1 tooling).** This module coordinates X1 (`STFSpec/informal/GAPS-CROSSCUTTING.md`; REVIEW §5). X1 is served by the failure ledger (maintained outside this repository): from a reviewed annotation input it generates a per-site report combining a static pass over the pinned EELS, a dynamic pass over the full fixture corpus and targeted deterministic probes, and it records a reproduction command. The recorded full-corpus run of pinned EELS matches `statelessOutputBytes` on all 24,283 distinct inputs. Its per-site counts and statuses are **provisional** and are being regenerated, so cite EELS `file:line`, not its entry IDs. Each module freezes its error types once its ledger entries close (DECISIONS B14). Promoting the tooling into this module's `lean_exe`/CI is outstanding.

## 3. EELS source map

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `forks/amsterdam/stateless_host.py::*` | 34–133 | `serializeStatelessInput`, `deserializeStatelessOutput`, `buildStatelessInput` | host tooling; not on the guest path |
| `forks/amsterdam/execution_engine/requests.py::decode_execution_requests` | 236 | `decodeExecutionRequests` | engine wire form → typed; outside the guest call closure (a name-based static call-graph pass from `run_stateless_guest`) |
| `forks/amsterdam/execution_engine/requests.py::_decode_deposit` | 158 | `decodeDeposit` (internal) | |
| `forks/amsterdam/execution_engine/requests.py::_decode_withdrawal` | 168 | `decodeWithdrawal` (internal) | |
| `forks/amsterdam/execution_engine/requests.py::_decode_consolidation` | 176 | `decodeConsolidation` (internal) | |
| `forks/amsterdam/execution_engine/requests.py::_decode_builder_deposit` | 184 | `decodeBuilderDeposit` (internal) | |
| `forks/amsterdam/execution_engine/requests.py::_decode_builder_exit` | 193 | `decodeBuilderExit` (internal) | |
| `forks/amsterdam/execution_engine/requests.py::DEPOSIT_REQUEST_SIZE` | 32 | `depositRequestSize := 192` | |
| `forks/amsterdam/execution_engine/requests.py::WITHDRAWAL_REQUEST_SIZE` | 33 | `withdrawalRequestSize := 76` | |
| `forks/amsterdam/execution_engine/requests.py::CONSOLIDATION_REQUEST_SIZE` | 34 | `consolidationRequestSize := 116` | |
| `forks/amsterdam/execution_engine/requests.py::BUILDER_DEPOSIT_REQUEST_SIZE` | 35 | `builderDepositRequestSize := 184` | |
| `forks/amsterdam/execution_engine/requests.py::BUILDER_EXIT_REQUEST_SIZE` | 36 | `builderExitRequestSize := 68` | |
| `forks/amsterdam/execution_engine/new_payload.py::verify_and_notify_new_payload` | 139 | `verifyAndNotifyNewPayload` | engine runner over `EthStateFull` |

**Decision on `stateless_host*.py`.** `stateless_host.py` is **claimed** as conformance tooling: it is small, pure and deterministic; its two codecs are the inverses the codec laws need and the only way to build `core` inputs in Lean; and `buildStatelessInput` turns any block plus witness into a guest input, which fuzzing of new blocks and the engine fixtures need. Claiming it does not make it normative: `runStatelessGuest` never calls it. `stateless_host_exec_witness.py` is **excluded** for now (reasons in `STFSpec/informal/EXCLUDED.md`): its choice of nodes is not a validity criterion (the guest accepts any sufficient witness, and fixtures already carry the witness inside the input bytes); it depends on access-recording in `incremental_mpt.py` and on `state_tracker.py` observation sets owned by other groups; and the pinned EELS host already provides it out of process for fuzzing. A Lean witness generator is deferred (DECISIONS Q7; §9).

**External semantics.** In `stateless_host.py`: `ethereum_rlp.rlp` (`rlp.encode(header)` for the block hash, `rlp.encode(tx)` for legacy transactions, `rlp.encode(block_access_list)`), `ethereum_types` `Bytes`/`U64`; behaviour specified by `EthCodec`/`EthBase`. In `requests.py` decoders: `ethereum_types` `Bytes32/48/96`, `U64.from_le_bytes` (little-endian), `slotted_freezable` (no semantics). JSON parsing (`Lean.Json`, allowed as part of `Lean`) and hex decoding are local and must reject odd-length and non-hex strings as *fixture malformed*.

## 4. Tests

- **Fixture areas.** All of `STFSpec/informal/eest-fixture-index.txt`: `blockchain_tests/**` (R1, R3) and `blockchain_tests_engine/**` (R4), both for `for_amsterdam` and `for_bpo2toamsterdamattime15k`.
- **EELS unit tests** to port as `core` cases: `tests/json_loader/test_stateless_guest.py` (host serializer round trip, `build_stateless_input` omitting keys of rejected transactions: ids `invalid-signature`, `wrong-chain-id`; legacy transaction RLP preserved through the payload); `tests/json_loader/test_execution_requests.py` (wire-form round trip).
- **Implementer guidance (F16).** Implement every dependency before running a guard or executable check. Core definitions may not contain `sorry`; evaluate only complete definitions. Prototype observations about proof-hole evaluation do not authorize executable stubs in the specification.
- **`core` cases.** Runner self-tests: a synthetic fixture file with one passing, one mismatching and one malformed record, checking the verdicts and the R6 record fields; hex decoding edge cases; `decodeExecutionRequests` on empty blob, duplicate type, descending types, unknown type `0x05`, a body one byte short, and each type's size multiple; `encode ∘ decode` and `decode ∘ encode` on all five types.
- **Property checks.** `deserializeStatelessInput (serializeStatelessInput x) = .ok x` for generated well-formed `x`; `deserializeStatelessOutput (serializeStatelessOutput r) = .ok r`; `decodeExecutionRequests (encodeExecutionRequests rq) = .ok rq`.
- **Differential.** R7 oracles on the `ci` slice and on fuzzed inputs; the stateful-vs-stateless cross-check on engine fixtures (build an input from `params` + `executionWitness` + recovered keys, compare `successful_validation` with `¬ validationError`), reported as bug-finding only because R2 shows guest records and block validity can legitimately differ.

## 5. Interface

Namespace `STFSpec.Conformance`; public unless marked. IO drivers live in a `lean_exe` target, the rest in the library.

```lean
-- host codecs (public)
def serializeStatelessInput : StatelessInput → ByteArray
def deserializeStatelessOutput : ByteArray → Except SszError StatelessValidationResult
def buildStatelessInput (blk : Block) (witness : ExecutionWitness) (rq : ExecutionRequests)
    (bal : BlockAccessList) (chainId : U64) : StatelessInput
def decodeExecutionRequests : Array ByteArray → Except BlockError ExecutionRequests
def depositRequestSize : Nat := 192   -- and the other four sizes

-- fixtures (public)
structure FixtureId where file : String; testId : String; blockIndex : Nat; infoHash : String
structure GuestRecord where id : FixtureId; input : ByteArray; expected : ByteArray
inductive BlockEntry | valid (hdr : Json) (rlp : ByteArray) (guest : Option GuestRecord)
  | invalid (rlp : ByteArray) (expectException : String) (guest : Option GuestRecord)
structure BlockchainFixture where
  id : String; network : String; chainId : U64; pre : Json; genesisRlp : ByteArray
  blocks : Array BlockEntry; postState : Option Json; lastBlockHash : Hash32
structure EngineFixture where id : String; network : String; chainId : U64; pre : Json
  payloads : Array (Json × Option String)            -- params, validationError
def parseBlockchainFile : Json → Except FixtureError (Array BlockchainFixture)
def parseEngineFile : Json → Except FixtureError (Array EngineFixture)

-- verdicts (public)
inductive Verdict
  | pass
  | mismatch (expected actual : ByteArray) (outcome : GuestOutcome)
  | specBug (e : InternalError)
  | fixtureMalformed (e : FixtureError)
  | skipped (reason : SkipReason)                      -- e.g. fork not instantiated
def runGuestRecord (r : GuestRecord) : Verdict         -- R1, pure
def runBlockchainFixture (f : BlockchainFixture) : Array (Nat × Verdict)   -- R3, pure
def runEngineFixture (f : EngineFixture) : Array (Nat × Verdict)           -- R4, pure
def verifyAndNotifyNewPayload (chain : FullChain) (req : NewPayloadRequest) : Bool × FullChain
  -- result/error adapter unresolved: see §10; R4 requires checked failures to stay visible

-- tiers, replay, oracles (public; IO)
inductive Tier | core | ci | local
def selectSlice (tier : Tier) (index : Array FixtureId) : Array FixtureId   -- deterministic
structure FailureRecord where
  id : FixtureId; input : ByteArray; inputSha256 : Hash32
  expected : ByteArray; actual : Option ByteArray; outcome : Option GuestOutcome
  internalError : Option InternalError
  specCommit pinTag pinCommit archiveSha256 toolchain : String
  oracle : Option OracleRun; seed : Option UInt64; mutations : List Mutation
structure OracleRun where name version : String; output : ByteArray
def verifyPin (root : System.FilePath) : IO (Except PinError PinReport)       -- R9
def runTier (tier : Tier) (root : System.FilePath) : IO Report
def replay (r : FailureRecord) : IO Verdict
class Oracle (o : Type) where run : o → ByteArray → IO (Except String ByteArray)  -- out of process
```

## 6. Data structures

| Type | Representation | Model | Abstraction | Invariant | Persistence | Complexity |
|---|---|---|---|---|---|---|
| `GuestRecord` | `ByteArray` input and expected | pair of byte strings | identity | `expected.size = 43` (else `fixtureMalformed`) | linear-only, one per record, dropped after the verdict | O(input) decode + guest cost |
| `BlockchainFixture` | parsed `Json` plus decoded bytes | the fixture object | JSON field projection | keys as R2 | linear-only; a file is parsed, run, dropped | O(file size) parse |
| full chain state | `EthStateFull` backend plus last 255 blocks (`Array`) | `MathState × List Block` | `EthStateFull`'s | `Models` (from `EthStateFull`) | snapshot-reachable within a block (via `EthState` overlays); across blocks linear | per block: `executeBlock` cost |
| `Verdict`, `FailureRecord` | inductive/structure | as declared | identity | a `pass` carries no data | value | O(1) |
| slice selection | sorted `Array FixtureId` | a finite set | `toList` | sorted, deduplicated | value | O(n log n) once |

Large inputs (up to 8.4 MB) must be read into a `ByteArray` once and passed by ownership; JSON parsing of multi-megabyte hex strings must not be quadratic [I: `Lean.Json` parser performance on such strings is unmeasured].

## 7. Contract and laws

- [R] **L-golden**: for every `GuestRecord r` of the pinned corpus, `runGuestRecord r = .pass`. This is the conformance statement; it is checked by execution (`local` tier), not proved.
- [C] **L-verdict**: `runGuestRecord r = .pass ↔ runStatelessGuestChecked r.input = .ok r.expected`. In particular a `specBug` verdict never counts as a pass, and the public `runStatelessGuest` is not used.
- [C] **L-host-inverse**: `deserializeStatelessInput (serializeStatelessInput x) = .ok x` for `x.WF`; `deserializeStatelessOutput (serializeStatelessOutput r) = .ok r`.
- [C] **L-requests-roundtrip**: `decodeExecutionRequests (encodeExecutionRequests rq) = .ok rq`. For accepted wire forms, `decodeExecutionRequests w = .ok rq → encodeExecutionRequests rq = normalizeRequests w`, where normalization removes type-only blobs. Equality with `w` requires non-empty bodies. The counterexample `w = #[00]` is accepted and re-encodes as `#[]`; the decoder must retain that acceptance.
- [C] **L-build**: `buildStatelessInput` sets `blockHash := keccak256 (rlp blk.header)`, lists transaction bytes in block order (legacy transactions re-encoded), collects public keys only for transactions whose signature recovers, and collects versioned hashes only from those. So for blocks with an unrecoverable signature, the key count differs from the transaction count, and the guest fails with O5 by design (`stateless_host.py:81–92` [V]).
- [C] **L-slice-deterministic**: `selectSlice t idx` depends only on `t` and `idx`.
- [C] **L-replay**: `replay r` recomputes the verdict from `r` alone and equals the original for deterministic runners.
- [T] every runner function in the library is total; IO drivers may fail only on IO errors, reported separately from verdicts.

### Informal correctness argument

**Claim.** A verdict checks the specified observable bytes against the pinned fixture record, and a failure record contains enough information to reproduce that comparison.

**Premises.** Verified release/corpus pin, locked Python dependency versions, deterministic selection/replay, and exact guest output encoding. Stateful fixture execution additionally requires a valid reconstructed pre-state and all prior dependent blocks.

**Argument.** Guest records are evaluated independently from their containing block's expected validity: the raw input and expected 43 bytes define the comparison. A checked InternalError is a failing verdict even if an unchecked fallback matches the expected bytes. FailureRecord retains the raw input, expected/actual bytes and checked outcome; replay reruns the same pure comparison. For stateful tests, induction over blocks maintains the full-state invariant after successful transitions. A skipped pre-fork block breaks that induction, so dependent Amsterdam blocks must be skipped too unless their authenticated pre-state is independently reconstructed. Request conversion has asymmetric inverse laws: decode(encode rq) = rq, while encode(decode wire) removes accepted type-only blobs. Its wire round trip is identity only on that canonical subset.

**Open obligations.** Implement the corpus/exception-label adapters, fixture slice, transition policy and malformed-input cases. Passing fixtures provides differential evidence; it is not a proof of module laws or a substitute for adversarial cases absent from the corpus.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthStateless`, `EthStateFull`
- **Used by:** nothing in the core; CI workflows and developers; benchmark packages may reuse its fixture parser.
- **Seams consumed:** `runStatelessGuestChecked`, `classify`, `deserializeStatelessInput`, `serializeStatelessOutput`, `executeNewPayloadRequest`, `encodeExecutionRequests` (`EthStateless`); the full-state `PreState` and state application (`EthStateFull`); `executeBlock`, `executeBlockStandalone`, `Block` RLP decoding, `recoverTransactionPublicKey`, `getLast256BlockHashes`, `BlockChain` (`EthBlock`/`EthFork`, transitively). R3 uses the standalone wrapper and its provider factory; R4 owns the engine driver's acquisition. Guest acquisition follows EthStateless R5 (F20).
- **Invariants relied on:** the checked runner reports every internal failure as `.error` (never as an output); every full-state `PreState` built from `pre` satisfies `Models` (from `EthStateFull`). **Guaranteed:** no verdict is derived from an oracle; required fixtures are never skipped for lack of an oracle; skipped items are counted and reported.

## 9. Open decisions

- **P1**, **P2**: the pin and the authority order this module enforces. R2's corpus facts are tied to P1; a new pin reruns the counts.
- **P4**: the weekly corpus verification job is this module's `local` tier on CI.
- **D10** (full-state instance, accepted): R3 and R4.
- **D14** (accepted): the verdicts report `classify` outcomes, which depend on the D14 constructors, including the named O13 faults. Error types are frozen per module once its failure-ledger entries close (DECISIONS B14, R11).
- **D3**: transition fixtures' BPO2 blocks are skipped, not executed.
- **D18**: no debt expected; JSON performance may need a streaming parser.
- Lean-native witness generator: resolved, DECISIONS Q7 (EELS host out of process for now).
- Transition-fixture pre-state: resolved, DECISIONS Q8 (skip and count).
- EEST exception-name mapping: resolved, DECISIONS Q9 (warning-only).

## 10. Gaps

- **Engine result/error adapter.** R4 catches only EELS `InvalidBlock` (`execution_engine/new_payload.py:161–162`); `InvalidTransaction` has a separate base class (`src/ethereum/exceptions.py:13,25`). The informal `Bool × FullChain` result in §5 cannot yet express all propagated payload faults or `InternalError`. Expand its checked adapter and exception mapping before implementation; internal failures must be spec-bug verdicts, and other faults must retain the pinned handler behaviour rather than all becoming `false`.

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **Engine fixtures carry no guest records.** Only `blockchain_tests` exercises the guest; `blockchain_tests_engine` duplicates the test cases for the stateful payload path. `reference.toml` already records this distinction.
- **Unexplained missing guest records.** 237 valid Amsterdam block entries have no stateless fields (216 in `cancun/eip4844_blobs`, plus `eip8282`, `eip4895`, `eip7002`, `eip7251`); the filler returns `None` when request bytes cannot be decoded or the parent header is unavailable (`packages/testing/src/execution_testing/specs/blockchain_stateless.py:868–916` [V]), but which cause applies to these entries is not established. 4,408 invalid blocks have no guest record, so guest-side coverage of invalid blocks is limited to 1,199 records.
- **Guest records versus fixture blocks.** 138 records describe a payload different from the invalid fixture block (R2). The filler's rules for which payload is recorded (canonical rebuild versus modified block) are not documented upstream; this matters for anyone reading fixture ids as guest-test descriptions.
- **External-filler trust path.** `build_amsterdam_stateless_artifacts_from_t8n` writes `successful_validation = True` without running the guest ("Temporary trust path for external benchmark filling until Geth emits both stateless byte fields", `blockchain_stateless.py:944–951` [V]). All 53,419 fixtures in this release record `filling-transition-tool: 2.19.0` [V], which is believed to be the EELS t8n [I]; that path runs `run_stateless_guest` and asserts consistency with block validity (`execution_testing/evm_tools/t8n/result.py:193–230` [V]). That no record came through the trust path is inferred from this, not verified per record.
- **Missing fixture categories for the guest.** None exercise: >1 witness header beyond ~10 (31 records have ≥10; none near 256); a witness cycle or deep acyclic chain (O12, DISC-001); O2; an unknown transaction type inside a payload; `extra_data` of exactly 32 bytes in a guest record [I]; the previous-fork header in a non-parent position; a payload before the activation timestamp (fork-activation exclusion); `chain_id` values other than 1 except the chain-id tests. Deterministic probe inputs run through the pinned EELS supply non-fixture evidence for some of these (for example an unknown transaction type, deep RLP nesting and the legacy-`v` chain-id overflow); they are not fixtures and are not decisive.
- **Transition fixtures.** 162 pre-activation BPO2 blocks cannot be executed statefully (D3), so the stateful runner cannot reach the post-transition Amsterdam blocks of those tests without a pre-state reconstruction; they are skipped and counted (DECISIONS Q8). The guest runner is unaffected: its 222 transition records are self-contained (186 of them with a previous-fork parent header [V]).
- **Request decoding round trip.** EELS accepts a blob that is a type byte with an empty body (length 0 is a multiple of every size), producing an empty list, while `encode_execution_requests` omits empty lists. So `decode` is not injective on wire forms; whether the CL ever emits such blobs, and whether the engine fixtures contain one, is unchecked.
- **Oracle availability.** No oracle other than EELS is known to implement all of Amsterdam at this pin (2-D gas, BAL, EIP-8282); evm-sail's and SpecRef's Amsterdam coverage is unknown; native stateless validators' input formats may differ from `statelessInputBytes` and need adapters.
- **EELS host environment.** The oracle's `hashlib`/OpenSSL (RIPEMD-160 availability, keccak source) and recursion limit are host-dependent and not pinned; each oracle run must record them (R7).
- **Performance of the runner itself.** Parsing 6,875 JSON files (inputs up to 8.4 MB of hex) with `Lean.Json` is unmeasured; there is no Lean gzip, so extraction is scripted and must be covered by the pin check.
- **Witness generator** excluded: fuzzing new blocks depends on the Python host; there is no Lean statement that the fixtures' witnesses are *minimal* or *sufficient* beyond the recorded outputs.
- **Exception-name mapping** is warning-only (DECISIONS Q9); the table itself is unwritten, so the stateful runner currently checks only validity.
- **No conformance statement for consumers.** evm-asm/pancaketh guests are not run by this module; running their ELFs on the same records is out of scope and has no owner.
