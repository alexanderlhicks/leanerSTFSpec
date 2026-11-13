# Informal specification review and implementation gates

*Status: live implementation gates; dated findings retained. Date: 2026-11-13.*

**Structure.** §1–§2 are a dated record of the review of 2026-09-28; do not update them except to mark supersession. §3–§5 are **live**: the per-module gates and the implementation contract, kept current. §6 is a dated readiness assessment (2026-11-04); replace it, rather than patching it, when readiness changes. §7 (acceptance criteria) is **live**.

Review of 2026-09-28; exact reference commit `e1a316a06fc3d3e0a5da36fdc78580811e9d8a36` (`tests-zkevm@v21.0.0`). The pin has since moved to `tests-zkevm@v21.0.6` (`59c1473ddfba341babaeca1c97a50e996f639a0b`, DECISIONS P1); the live sections apply at the current pin, and the re-pin follow-up is GAPS-CROSSCUTTING X16. All 24 module documents now contain conditional correctness arguments in §7. [COMPOSITION](COMPOSITION.md) connects their premises, common types, error adapters and the complete byte-level guest. **The design remains a draft requiring the gates below.** Owning every reference declaration does not mean specifying every operation completely or proving it correct.

## 1. Findings and changes

| Finding | Consequence | Working correction / remaining gate |
|---|---|---|
| Precompile result/table shapes differed between modules | Runner could double charge or omit meter fields | One Core-owned API returns the updated GasMeter; successful meter law and config coherence must be proved per entry. |
| World duplicated state observations/ancestor tracking | Revert and BLOCKHASH could observe inconsistent stores | VmWorld owns one TxState; snapshots contain only TxRevertible. Audit every constructor/restore. |
| InternalError/FuelM definitions did not compose | Internal fuel exhaustion could disappear at a caller | Runner owns CheckedResult/InternalError; canonical monad/error adapters are in COMPOSITION. Compile the full path before opcode implementation (done in a compiled interface prototype, 2026-09-29; DECISIONS §3). |
| BLS map/cofactor boundary was ambiguous | Applying clearing twice changes EIP-2537 output | mapToCurve is uncleared, mapFp wrappers clear once; add concrete counterexample as a future guard. |
| Storage diff was treated as order-free | Partial trie updates can fail in a different order | Preserve account, storage-address and slot first-write orders, including clear/merge/rollback metadata. Any order erasure needs a proof. |
| Root laws were applied to all accepted witness encodings | No-op delete can change a noncanonical root | Separate canonical mathematical tries from raw accepted witnesses and preserve raw encoding caches. |
| Models omitted full-state code authenticity | The code store can contain arbitrary bytes under a committed hash | Add CodeAuthentic; include both code stores in collision extraction. Structural WF alone is insufficient. |
| Gas-schedule positivity was called termination readiness | Complete calls return gas, with stipend and spill interactions | Prove whole-iteration progress, the structural measure and four fuel guarantees separately. |
| Request wire conversion was called an exact inverse | Accepted type-only blobs are erased on encoding | Value round trip is exact; wire round trip is a stated normalisation. |
| Failure records omitted raw input | Replay could not work from the record alone | Retain raw input and all checked result information. |
| Coverage checker only checked headings/dependency text | Duplicate common types, proof imports and missing arguments escaped checks | Add explicit ownership/import registry and structural proof-argument checks. These still do not verify Lean typing or mathematical truth. |
| Several records had only placeholder declarations | Schema field order/types were left to implementation agents | Add a generated reference field catalogue; fully expand each actual wire record/instance before implementation. |

*(Superseded: D14 (structure and guidelines), D18, D21, D26 and D27 have since been accepted; see `STFSpec/informal/DECISIONS.md`.)* At the time of this review, D14, D18, D21, D26 and D27 retained their recorded statuses, and applying the provisional import/Log placement did not approve those decisions. Newly exposed ambiguities remain proposals/gaps, not silent protocol changes.

## 2. Evidence reproduced for this review

**Probe supersession (2026-11-06).** The observations and reproduction commands below describe `tests-zkevm@v21.0.0` (`e1a316a0`). The maintained `scripts/spec_review.py` follows `reference.toml` (P1). At `tests-zkevm@v21.0.6` (`59c1473d`), it checks rejection of type-only request blobs (`execution_engine/requests.py:203–204`) and list-valued storage leaves (`witness_state.py:127`), and constructs `IncrementalMPT` without the removed `_data` field (`incremental_mpt.py:116–127`). Its other source probes remain. Run it as its docstring specifies, with the frozen EELS interpreter and assertions enabled. The historical acceptance claims below do not apply to those two decoders at this pin.

The checkout was clean at the exact pin. Python dependencies were installed from its unchanged `uv.lock`: ethereum-types 0.4.1, ethereum-rlp 0.1.6, eth-remerkleable 0.1.31, py-ecc 8.0.0, pycryptodome 3.23.0, spec256k1 0.2.3 and cryptography 45.0.7. The run recorded Python 3.12.3 / OpenSSL 3.0.13. These observations describe this review environment, not all possible reference hosts. **Independent re-run (2026-09-28):** [`scripts/spec_review.py`](../../scripts/spec_review.py) was run again against the same clean pin from a fresh `uv sync --frozen --no-dev` environment (identical locked versions) on Python 3.13.7 / OpenSSL 3.0.16. All five checks returned `True`: `double_cofactor_changes_output`, `request_type_only_blob_is_normalized_away`, `insert_before_delete_avoids_stub_collapse`, `noncanonical_noop_delete_changes_root`, `account_root_update_depends_on_prior_lookup`.

[`scripts/spec_review.py`](../../scripts/spec_review.py) verifies the source pin, records dependency/runtime versions and asserts five counterexamples:

1. Clearing `map_to_curve_G1(FQ(0))` twice differs from clearing it once.
2. Execution-request wire `[0x00]` decodes, then re-encodes to an empty sequence.
3. In a partial branch, deleting before inserting fails while inserting before deleting succeeds.
4. Deleting an absent key from an accepted noncanonical leaf changes its root.
5. Updating a witness account has a different root with and without its earlier account lookup.

Reproduce with the pinned checkout's locked Python environment:

```sh
UV_CACHE_DIR=/tmp/stfspec-review-cache uv sync --frozen --no-dev --python /usr/bin/python3
```

Run that setup command in the EELS checkout, then from this repository:

```sh
/path/to/eels/.venv/bin/python scripts/spec_review.py /path/to/eels
uv run --no-project --python 3.12 python scripts/gen_eels_inventory.py /path/to/eels --check
uv run --no-project --python 3.12 python scripts/gen_reference_records.py /path/to/eels --check
```

The fresh inventory comparison covers 717 nonexternal declarations and 304 external-use entries across 74 files. The field catalogue records source order/annotations and inherited bases. It is not a generated Lean implementation or a complete type-mapping proof. The five examples are regression evidence, not a complete conformance run. The fixture archive was not re-executed during this review; its existing verified counts remain in `reference.toml`.

The local validation completed successfully: `check_spec.py` (23 libraries, 717/717 ownership coverage), 16 mutation regression tests in `test_spec_checks.py`, generated-gap freshness, source inventory/record comparison, all five counterexamples, core dependency boundaries, protocol consistency, architecture diagram freshness and `git diff --check`. CI is configured to run the document guards/regressions; this review does not claim a remote CI run or a Lean semantic implementation test.

## 3. Per-module gates

Every row is required before claiming that module's corresponding refinement, in addition to its existing §10 gaps. A gate may be completed incrementally for a precisely bounded public API, with uncompleted operations labelled explicitly.

| Module | Remaining design/proof work |
|---|---|
| EthBase | Q54’s functional Bytes order/export provider, public-only clients and source/compiled ordering cases are supplied by EthBase §3; actual consumer/replacement/C1–C4 costs remain open. Q51 table-support and Q84 canonical Address/Bytes32 functional seams are supplied by EthBase §3; actual observation-set construction/distribution/ownership/C1–C4 remain open; concrete NodeDB/adversarial-distribution cost evidence and fixed-byte representation gates remain open. Taylor's positive-denominator totality/two zero-value laws and bounded controls are supplied by EthBase §3/§7; DISC-002 practical feasibility remains open. Enumerate checked integer operations and failure sites; specify Envelope's role. |
| EthHash | Prove padding/round/byte correspondence; fix RIPEMD capability policy (DISC-005); monad-parametric interfaces with `Id` specialisation and lift instances (D5; DECISIONS F1, F15). |
| EthField | The reference-only carrier, basic residue arithmetic, natural powers, canonical sign, checked byte decoding, Q86 graph-specified inverse and reference division, their observer laws/delegating instances, eight exact Nat modulus constants and private facade clients/complete controls are supplied by EthField §3/§7; no executable aliases or whole-module result is supplied. Certify primality/tower irreducibility; qualify sqrt choices and encoding widths; finish public equations; complete the Montgomery backend's `sub`/`neg` and `W12` laws, observers and inversion (D6). |
| EthCurve | Fix general-a versus a=0 formulas; prove exact SSWU/sign/once-clearing adapters; specify recovery-compatible domain and dependency rejection behaviour. |
| EthPairing | Pin literal default Miller algorithms; establish concrete bilinearity/nondegeneracy before convention replacement; separate KZG completeness from binding. |
| EthCodec | Q87 local count recovery and its complete ordinary constructor law are supplied (EthCodec §3/§7). Instantiate the remaining schemas; prove both inverse directions and strict acceptance; complete the raw decoder; establish actual rootable/encodable domains, progressive lengths and host-depth policy. |
| EthState | EthState §3/§7.2 supplies the mathematical block view and exactly its ordinary apply_extractBlockDiff equation on every raw state/carrier, without class premises. Private complete public-law clients and independent numerical/list interpreted `#guard` controls establish bounded mathematical composition; full WF/history, witness failure/observation agreement and other live gates remain open. Q85 raw extraction and exactly seven complete equations are supplied under EthState §3/§7: direct ordered observers and domain-preserving slot mapping over arbitrary raw inputs. Private public-law clients and complete independent full-output controls do not establish reachable history, full WF or F7. Q84 supplies the canonical Base key dictionaries for the supplied TxObs and BlockState raw Std observation fields; Base support alone supplies no State carrier, tracker, lifecycle or replay-order theorem. The separate bounded four-field TxObs and thirteen-field arbitrary-m BlockState carriers preserve arbitrary whole fields; private complete constructor/reconstruction/update/commutation and full-byte/key controls supply nominal storage only. State §3 separately supplies class-free BlockState.new and only its explicit F20 new_consts public law; whole arbitrary provider retention and all guided defaults are verified owner-privately, with complete finite controls. State §3/§5/§7 also supplies two class-free logical block account/storage read views and exactly their membership iff laws. Private public-law clients and complete independent full-key interpreted `#guard` vectors validate this projection seam without a Set provider, decidability API, raw-set equality or BAL construction. Further consumer-law basis requires a named consumer and separate review. Raw TxState/StateM assembly and exact transformer wiring are supplied separately (EthState §3/§5/§7), retaining the current-pin X16(b) provider mismatch. Tracker operations and D23 ownership/monotonicity remain open. Supplied component contracts are owned by EthState §3/§7: Account/emptyAccount, internal WriteOrder, raw MathState observers/structural WF, raw BlockDiff, raw mathematical application, the raw PreState and eight-field TxRevertible carriers, nominal StateError values, Q58 bounded structural preservation and supplied-record ModelsLookups. Arbitrary supplied functions have ordinary record laws without a Monad premise; public-only generic clients and complete guard/native callbacks preserve every input/result/error tag and payload. Coarse WitnessItem/WitnessError and StateError values add no diagnostic/outcome adapter or EELS Protocol-body execution; private StateError structural proofs and complete-payload guard/native cases cover supplied tags and all bytes; carrier equality adds no action-effect interpretation. Source correspondence retains typed finite nonaliasing dictionaries, None/zero defaults, pinned fixed-width/Uint/U256 interpretation and coherent F20 constants, without local hashing. MathState raw equality retains whole optional inner maps and every code hash; structural WF supplies no code authenticity/completeness, and fixed-constants observer equality need not imply raw equality. Raw diff fields and application supply no reachable WF, hash authenticity, history or clear-order guarantee. Define Reachable; discharge account-read/write and balance preconditions at callers; implement/prove model mutation, actual providers and context coherence, StateError operation/adapter semantics and freezing, witness diagnostic refinement, tracker effects/errors, coupled ordered-write/clear/restore/incorporation/extraction and state lifetimes. The EELS default-empty BlockDiff convenience constructor remains deferred. S1/S2 and composed C1/C4 remain open; these contracts supply no whole-State readiness result. |
| EthCommit | The supplied local incremental-root contract is owned by [EthCommit §3/§7.0.9](modules/EthCommit.md#3-eels-source-map); whole root/source/cache refinement remains open. Nominal Enc/Node/Ref and secured/root IncrementalMPT carriers with private full-field/variant/recursive-array clients are supplied (EthCommit §3); complete generic decoding and local laws are supplied separately there; shape/cache admission, exact Node.WF interpretation and remaining partial-trie operations stay open, with no whole gate/readiness closure. Q59 supplies local total pure bare lookup, one selected-slot diagnostic, seven defining laws and private all-bare offset/reference equality with structural proper-child descent. Complete-value clients/source controls retain the valid-selected-access Hash32/source-class/host boundary; whole source/map agreement and guest projection remain open without eager WF/cache admission. Complete whole-source C7–C8 constructor/root and decoder refinement, WitnessError/O4 adapters and W1; compose Q53's supplied generic storage/safety, lawful byte-key, pure unsecured preparation and typed-root laws (EthCommit §3); implement/prove concrete encoding/key bridges and consumer instances with caller F20 coherence, exact source equality/dispatch and schema/assembled Encodable/host premises. Distinguish canonicality from lookup equivalence; compose Q55's supplied generic pre-RLP occurrence acquisition and local raw/inline/error laws with explicit Id-run consumer agreement and cache/whole-source refinement; any B15 memo refinement additionally covers effects/path/first error; specify secure-key collision folding, source history and order-sensitive collapse; validate table and composed resource bounds. |
| EthStateCommit | Total U256 storage encoding, all-value validity/nonempty and wire injectivity are supplied by EthStateCommit §3 independently of supplied-default deletion. Contextual Account encoding, unconditional nonempty and pair binding under both complete assembled Q47 premises are supplied in EthStateCommit §3. Implement callback/root integration, without a bare Account instance or secured-policy claim. SC6 and nonzero storage SC10 are supplied locally in EthStateCommit §3, with public bounded typed admission, complete full-value equations and full-parser-first rejection. SC5 and conditional account SC10 are supplied locally in EthStateCommit §3, with caller-owned defaults, unbounded nonce, bounded numerical balance and complete assembled Q47 premises. Finish code-authenticity/root clauses, triggered backend/shared error integration and computable collision extraction including full-state code. |
| EthStateFull | Require CodeComplete for progress; prove applyChanges preservation and raw-helper WF premises; finish full-root folding model. |
| EthStateWitness | Prove reachable cache history, ordered update phases and storage-root-only rewrite commutation; establish eager availability requirements and Q55 action/result-cache ownership, lifetime, first failures and Id thunk adaptation; settle the storage-trie memo (F6) and clear order (F7). |
| EthVmCore | The raw one-field VmWorld and exact VmM StateT-over-ExceptT alias are supplied under EthVmCore §3/§4/§5/§7, with private complete public-facade wiring clients and no class/WF/coherence premises. State X16(b), initialization/liftState/error routing, trackers/lifetimes and all execution/resource/readiness obligations remain separate. The two nominal OverflowSite/VmFault carriers and private complete facade clients/controls are supplied under EthVmCore §3/§4/§5/§7; actual fault producers, state lifts, propagation/outcome adapters, reachability and B14 classification/freezing remain open. The raw ChildSettled predicate and constructive Decidable instance, with private clause/all-frame/decision and conditional public rollback/forfeit clients, are supplied under EthVmCore §3/§5/§7; actual non-top committed-spill-zero preservation, incorporation, settlement/snapshots, proof production and F11 remain open. The exact raw eleven-field BlockEnvironment and sixteen-field TransactionEnvironment, private complete facade constructor/projection/type/reconstruction/update clients and full-value controls are supplied under EthVmCore §3/§5/§7; intended history/source coherence, actual assembly/admission/lookup and consumers remain open. The exact two persistent ExtTreeSet aliases and raw nine-field mutable Frame with private complete construction/projection/reconstruction/update/set clients and nontrivial full-field controls are supplied under EthVmCore §3/§5/§7; actual creation, whole source-Evm refinement/control/parent integration, F8 transport/actual producer emission and execution/resource/readiness gates remain open. The exact fifteen-data-field FrameCtx with its sole local literal depth proof and two-field Evm, private complete facade clients and boundary controls are supplied under EthVmCore §3/§5/§7; raw config limits and code/maps remain independent. Actual creation/inheritance, source coherence, read-only handler signatures, world/control/parent integration and F8 transport/actual producer emission remain open. The supplied nominal ExceptionalHalt and raw halt/revert FrameError carriers (private complete-payload clients/guards; producers, gas/settlement and adapters remain open), complete six-field GasMeter and ten all-raw-meter charge/check laws, plus commit/two rollback boundaries and eight laws on their local proof domains, and refund/repay with seven all-raw-meter laws, plus four local transfer operations with eight laws (forfeit only on pending-spill-zero), plus signed refund addition/scalar maximum with four unconditional laws and transaction state-gas usage with one equation on its local baseline-to-grant proof, are owned by EthVmCore §3/§7; partial G1 only. The bounded Stack carrier/seven operations/ten laws (Q82) are additionally supplied under EthVmCore §3/§7; actual handler/frame ownership and composed allocation costs remain open. The pure supplied-address `emitTransferLog` and its two ordinary whole-Frame laws are supplied under EthVmCore §3/§5/§7; actual producers and context transport remain open. Q83 `SatisfiesM` and `satisfiesM_id_iff` are supplied under EthVmCore §3/§5/§7; table/adapter construction and Runner bridges remain open. The shared PrecompileResult/PrecompileFn/MeterOk/PrecompileTable carriers are supplied under EthVmCore §3/§5/§7; installed-table construction, entry proofs, effect bridges and halt settlement remain open. The two scalar immediate decoders and eight ordinary laws are supplied under EthVmCore §3/§7. The standalone bufferRead and its three ordinary bridge/List/size laws are supplied under EthVmCore §3/§7. Q62’s private aligned Memory, exact six-operation API and ten ordinary laws are supplied (EthVmCore §5/§7); actual caller windows/alignment and compiled ownership remain open. The complete raw Log, public empty/leaf/concat rope constructors, two operations and six ordinary laws with private all-tree workstack refinement are supplied under EthVmCore §3/§5/§7; finite C3 traversal/cleanup evidence retains sharing and metric limits, while real producers/frame incorporation/receipt integration and general resource bounds remain open. The abstract immutable JumpdestMap, existing two operations and three ordinary all-code/all-Nat lookup equations are supplied under EthVmCore §3/§5/§7; code/map/cache provenance, actual JUMP/JUMPI ordering and compiled/resource costs remain open. The raw 144-field GasCosts data record and two ordinary ext/eta laws are supplied under EthVmCore §3/§5/§7; broader B8 classification, fork initialization and supported consumers remain open. The raw-four StateGasCosts, raw-three VmLimits and complete three-field VmConfig data with six ordinary ext/eta laws are supplied under EthVmCore §3/§5/§7; actual values, state amounts and configuration/frame consistency remain open. The raw BlockGasCounters carrier and two ordinary ext/eta laws are supplied under EthVmCore §3/§7; full EthBlock.BlockOutput and capacity arithmetic/failures remain separate. F8 Fork→Block→Runner transport and FrameCtx creation/child inheritance remain unimplemented (EthVmCore §7/§10). Implement/prove every remaining meter operation, error fields, FrameCtx/Evm creation, caller premises and refund sign; align memory allocation with charging and compiled container costs. |
| EthVmInstructions | The 153-member Ops enum, total UInt8 conversions and exactly two ordinary round-trip laws with complete literal byte controls are supplied under EthVmInstructions §3/§5/§7. Dispatch, step and opcode effects remain open. The exact raw seven-field CreateRequest and fourteen-field CallRequest and private complete facade clients are supplied under EthVmInstructions §3/§5/§7, with unrestricted independent grants/values/addresses/bytes/flags/output windows and no added admission or public helper laws. The exact four-field ChildOutcome with its supplied Core ChildSettled frame error.isSome proof and private complete/dependent/boundary/negative elaboration clients is supplied there; no producer, runtime guard or F11 route follows. Producers, StepResult, child context/frame and resume remain unimplemented; no source/admission or gas/staticness policy follows from the carriers. F8 child-context systemAddress inheritance and SELFDESTRUCT use remain unimplemented (§7/§10). Expand grouped handler claims into guard/effect/error equations and prove per-opcode source refinement; fuel/resource/guest gates remain open. |
| EthPrecompiles | The raw KZG versioned hash is supplied (EthPrecompiles §3). Prove every adapter and returned-meter law; thread pricing config consistently; verify multi-error priority and all accepted infinity/subgroup cases. |
| EthVmRunner | The minimal source-free InternalError/CheckedResult/CheckedT control shapes and private complete facade/Id composition clients are supplied (EthVmRunner §3/§5/§7); adapters, actual caller propagation, execution and guest projection remain open, with F11 and G2–G7 unchanged. The three selectable mathematical budget declarations and their private clients/complete finite interpreted/native controls are supplied in EthVmRunner §3/§5/§7; no default, runner integration or adequacy claim. The nominal three-constructor ExecKind carrier and private exhaustive/disjointness facade clients are also supplied; no Exec relation or choice of its form follows. B11 remains an unproved candidate. The exact three-field Monad-only raw RunnerEnv carrier and private complete facade construction/projection/reconstruction/update and stored-table-certificate clients are supplied (EthVmRunner §3/§5/§7). Actual config/table assembly, F8 successful createEvm copy, child inheritance and processCall context-address emission remain unimplemented (EthVmRunner §7/§10), without a new global Step/Exec or gas/fuel premise. Define Exec/measure and TerminationReady; prove complete call/create progress and all four fuel guarantees; verify every InternalError path; choose how `ChildSettled` is produced (F11). |
| EthBlock | The raw R-BLK Withdrawal carrier and actual certified Q81 SSZ dictionary with private complete facade proofs, support/layout/count clients and interpreted controls are supplied under EthBlock §3/§4/§5/§7; RLP, raw/guest decoding, root laws, processing and Q53 withdrawal root-input composition remain open. The raw R-HDR carriers and nine common parent projections, private complete facade clients and finite native/interpreted/source observations are supplied under EthBlock §3/§4/§5/§7; codecs, hashing, validation, authentication, consumers and execution/resource gates remain open. The raw unrestricted three-Nat BlockParams and TxParams and eight-Address/two-Nat SystemAddrs providers are supplied with private complete facade controls (EthBlock §3); F8 runnerEnv address projection at both actual runner entries, actual consumers and full configuration remain open. The standalone all-finite `countTokensInData`, `extractDepositData`, `computeRequestsHash` and `logsBloom` operations, whole result/action laws, extraction success-size law, lawful Bloom empty/sequential-append laws, private packed/reference equalities and bounded complete controls are supplied under EthBlock §3/§5/§7. Bloom preserves address-then-topic query order, every duplicate/current answer, the complete 256-byte result and supplied underlying failures/effects; its operation remains plain-Monad, and its laws use lawful sequencing without oracle purity/stability. EthBlock §4 owns the precise independent single-log known-answer provenance repair; no published EIP vector is claimed. Actual receipt/block composition, generic oracle coupling and compiled ownership/C1–C4 remain open. Deposit extraction retains all eleven ordered error identities and complete bytes; fixture literal provenance supplies no fixture/EVM/guest execution claim. The request commitment retains ordered complete inner digests, every empty/duplicate request and exact outer digest bytes; Q46 inner/outer bounds, source host/API/native agreement, streaming/resource and cryptographic binding remain separate. Intrinsic gas/floor, actual callers, source/runtime and resource correspondence remain separate. Implement/prove Q53's actual Bytes/legacy/typed/withdrawal encoding bridges and dense safe root-input composition using lawful byte keys and context empty root. Implement and prove F20 acquisition/threading and context coherence; expand every record/codec and admission arithmetic failure; prove BAL/index/receipt ordering, unchecked-system fault propagation and backend simulation. |
| EthFork | The five Amsterdam input wire-limit values and private complete facade controls are supplied under EthFork §3; the actual witness and payload schemas consume them, and the input schemas and their Q81 certifications are supplied in EthStateless and EthBlock. Q88 decoding and the remaining consumers stay separate. Complete Amsterdam block parameters (including the two actual private subtraction operands and all five quantity controls) and transaction parameters are supplied with private complete facade controls (EthFork §3); block size/base-fee consumers, division safety and full coherence remain open. Complete stored Amsterdam VM GasCosts/StateGasCosts/VmLimits/VmConfig values and the definitional F8 depth law are supplied with full literal/native/parser controls (EthFork §3). Complete Amsterdam R-F2 systemAddrs data and private full-byte/budget controls are supplied (EthFork §3). Compare remaining parameter tables with source; construct coherent BlockConfig/precompile table, F8 context assembly and actual consumers; specialise behavioural termination proof; verify previous-header compatibility. |
| EthStateless | The exact three-field raw StatelessInput, private arbitrary whole-field clients and complete nested finite controls are supplied under EthStateless §3–§7; the actual input dictionary and three Q81 certificates, private count/support/layout clients and complete 48-input/385957-byte mathematical controls are supplied there; the co-located private generic size foundation and 30-case/183-byte controls, actual raw request-size formulas, operation-local encoded-size laws, fixed classifications and inherited child/member support are supplied in EthStateless §3/§4/§7, while whole-input request support, later outer-start and count/leaf bounds, decoded-support and input-to-Rootable bridges remain open; raw decoding/roots and caller/guest/security/resource/readiness remain separate (§10). The exact nineteen-field ExecutionPayload and four-field NewPayloadRequest raw carriers, actual Payload/NewPayloadRequest Q81 dictionaries with three certificates each, and private complete count/support/layout clients and whole mathematical wire controls are supplied under EthStateless §3/§4/§5/§7. The five nominal raw request-item carriers and private complete facade clients/controls are supplied under EthStateless §3/§4/§5/§7; the five actual Q81 dictionaries and fifteen certificates, with private actual Serializable/CountRecoverable/full-wire clients and complete finite controls, are supplied there. The raw five-array ExecutionRequests aggregate and its private complete clients/controls are also supplied there; its actual Q81 dictionary/three certificates and private CountRecoverable/Serializable/full-wire clients with complete 80-input/150780-byte mathematical controls are supplied there. Raw decoding, roots, source-host agreement and input/guest composition remain separate (§10). The complete historical ProtocolFork carrier and forward UInt8 tag observer, with private complete facade proofs/guards, are supplied under EthStateless §3/§4/§7; schema selection and the F8 bridge remain separate (§10). The raw ExecutionWitness carrier and private complete facade clients/controls are supplied under EthStateless §3/§4/§7; the five transparent wire-limit aliases are supplied under F8 (EthStateless §3/§5), while the actual witness dictionary and its three Q81 certificates are supplied under EthStateless §3/§5/§7 with complete private controls in §4. General source support correspondence, backing/host premises, raw decoding, guest integration and readiness remain open. The concrete output slice is supplied under EthStateless §3/§4/§7; host decoder inverse and whole-guest encoding composition remain open. Implement and prove F20 acquisition/threading and context coherence; complete phase-to-outcome projection and input-to-context WF/rootability; typecheck subtype/header/request adapters; compose the supplied exact output encoding with actual guest outcomes; prove O2 unreachable on decoded values. |
| EthConformance | Guest-record extraction from both fixture formats is supplied (EthConformance §3). Co-ordinate closing X1 in the failure ledger (maintained outside this repository); implement exact label/replay handling, locked environment and dependent-transition policy. |
| EthFieldMathlib | Build public-operation bridges without circular typeclass premises; certify all primes/extensions and sqrt lemmas. |
| EthCurveMathlib | Prove valid-point operation bridges, group/subgroup orders, exact map/decompression and qualified ECDSA laws. |
| EthPairingMathlib | Supply concrete pairing laws/group/setup premises; complete convention-independence and honest-opening proofs. |
| EthSecurity | Consume bounded local ToVCVio RLP/reference laws without inferring whole-map binding; establish nonvacuous directional simulation, whole-trie extractors, oracle closure and budgets; keep chain anchoring and cryptographic security assumptions explicit. |
| ToVCVio | Certified RLP facade, child-reference threshold/effect laws, explicit query-morphism transport, local same-h raw-pair extraction and same-query InternalNode adapter are supplied (own guidance §7). Faithful Patricia shell/assembly/preimage injection, separate finite resolved canonical shape facts and a pure nonempty safe prepared-image bridge are supplied (own guidance §§5/7); total finite resolved lookup, packed/List join equality and one-step prefix lookup/canonical preservation and complete-key support for actual canonical trees/two distinct keys for canonical branches are also supplied, together with canonical resolved-tree observational extensionality under both actual canonicality premises and all-finite full-value/byte observations; ordinary Prop finite resolved-map existence for actual maps satisfying `NonemptyValues`, including the empty map, with complete optional bytes at every finite key is also supplied (own guidance §§5/7); conditional structural node/reference Prop derivations also supply admissibility, exact presence occupancy and canonical-to-local-shell laws under the complete present-shell certificate and fixed pure-h premises (own guidance §§5/7); top Fits remains separate from bare node derivation, while logical C/D width and exact inhabitation support is supplied by PatriciaRlpDomain (Q56; own guidance §§5/7). All complete domain/action premises remain explicit. Installed VCV-io pin/QueryHom adapter/import audit, a public resolved-map uniqueness corollary, executable C7/C6 reference/effect realization, C8 hashing/source agreement, recursive binding, witness agreement, whole-kernel coupling and consumer/cost gates remain open. |

The Q60 direct insertion slice is supplied locally: update and exactly the approved
update_branch_oob law under plain Monad/KeccakQuery, with private proper-child
totality and ordinary all-input offset/List CPS equality.
[EthCommit §3](modules/EthCommit.md#3-eels-source-map) owns its complete-field,
query-answer, failure, nonlawful-monad, parser and conditional pinned-source
controls, including the source cache/embedding premises and history boundaries.
All helper/reference/test support remains private. Direct empty values remain
insertions. Deletion and its two equations are supplied separately below;
Encoded mptSet and its remaining equation are supplied separately below.

The Q60 direct deletion slice is supplied locally, owned by
[EthCommit C19/C24/C25/§§3/4/5/7.0.10/10](modules/EthCommit.md#3-eels-source-map):
total delete and both approved bare root equations, private source-control metadata,
strict visited/no-op completion and independent List-wire/continuation/set versus
bounded packed-offset whole CPS action equality under plain Monad. Proper-child
totality includes empty extensions; structural or allocation equality does not
implement source changedness. Public-law clients and complete deletion controls
are supplied; EthCommit §3 owns the deletion-family 01–32 map and distinguishes copied
regression expectations, independent literals and source/Lean-only cases. EthCommit §3
owns the frozen typed catalog/premises, strict normal/-O parser controls, actual
source/runtime identity preflight and completed finite original observations.
The local observed-clean source guard, consulted embedding/cache, complete
Encodable/class/Id/host premises and boundary/materialization stages remain
explicit. Source mutable history, witness/partial state and generic coupling,
frontend/map/root/WF/security/W1/S2/R2/O12/C1–C4/EEST/guest gates remain open.

EthCommit §3 supplies local reached mkBranch, its occupancy/collapseIndex emission,
private all-input ordinary List/wire literal action equality under plain Monad and
complete-field public-import/generic/source/parser controls. All support remains
private. Declaration/strict reason 12 parser controls retain old tags/full Nat fields;
decoder and lookup never emit collapseIndex. Source comparison retains the exact
clean/cache/consulted-embedding/retained-parent premises owned by EthCommit §3.
Direct deletion dispatch, its no-change handling, proper-child descent and both
bare root equations are supplied above. The encoded frontend worker and its secure-key/empty dispatch equation are
supplied separately below. Whole mutation change/cache/source
realization remains open. No broader gate or readiness closes.

The Q60 encoded setter slice is supplied locally: exactly mptSet and
mptSet_emptyEncoding under plain Monad/KeccakQuery, with private arbitrary-provider
copying List/full-action equality retaining the actual bind/pure/map syntax.
[EthCommit C22/§3/§7.0.10/§10](modules/EthCommit.md#3-eels-source-map) owns its
156 opaque-provider and 376 public-composition frozen full-field/query/error/state/
failure/nonlawful controls, public-law clients and strict normal/-O parser.
Focused warning-fatal controls/callers and declaration audit pass. The bounded
frontend catalog passes with 26 successful completed projections, eight source-only
encoding/default boundaries and 20 explicit diagnostics under the premises there.
Source value/default/map/Account callback/dirty/witness/partial-state histories
remain separate from the already-encoded nominal secured/root projection. No new
public helper, source/WF predicate, policy, dependency or broader readiness is supplied.

Q64's local call/init-code pricing slice is supplied by
[EthVmCore §3/§5/§7](modules/EthVmCore.md#3-eels-source-map): two VmConfig-first
pure helpers, the complete cost/subCall result and six discharged ordinary laws.
Private public-law clients derive complete checked-charge/error, affordability,
read-set, init rounding and explicitly financed local-potential consequences.
Core §3 owns the thirty-two literal controls, complete charge witnesses and strict
reader scope, and identifies the dated external interpreted/native/twenty-five
original comparisons and their source/default/host premises.
Relevant-price congruence supplies no global WF or whole payment/settlement/G2
claim. Actual caller/coherence/composition, compiled/resource and whole VM/guest
gates remain open.

The separate private CALL preflight numeric composition is owned by
[EthVmCore §3/§4/§7/§10](modules/EthVmCore.md#private-call-preflight-numeric-composition).
It composes exact successful overhead/optional-state/current-budget forwarding
charges, reservoir drain, full grant return and optional credit through public
laws. The identity returned.phi+E=initial.phi+t needs local t+1≤E for strict
progress or t≤E for nonincrease; complete field observations and finite controls
retain old spills and signed refund. Source ZERO coherence, actual handler/access/
failure/effect order, cfg/grant identity, child execution/return bounds and
incorporation/settlement/step/loop remain open. This closes no G2–G7 gate.

That owner also supplies private clients for arbitrary supplied execution g and
reservoir R after the actual drain. They prove returned.phi+E+cost=initial.phi+g
and strict progress iff g+1≤E+cost. Only g≤subCall is needed for the worst-case
stipend bound and the same financed consequences. Phi excludes reservoir, baseline
and refund, so no reservoir bound is used. Complete whole-field equations and
fifty-five six-stage/six-field successes plus two shortages retain the actual
numeric operations and pre-target mathematical expectations. A supplied child-phi
bound implies its execution bound locally. The arbitrary-Frame ChildSettled
countermodel shows that settlement alone provides neither bound. Actual child and
handler effects, returned-phi preservation, successful-child credit bookkeeping,
F11 proof production, source/default/host agreement, F11/B11/D5/S2/G2–G7,
resources, security and guest integration remain open, with no readiness increase.

Q65's local allocation slice is supplied by
[EthVmCore §3/§5/§7](modules/EthVmCore.md#3-eels-source-map): unrestricted raw
execution/reservoir carrier, VmConfig-first helper with exactly two local bounds,
and four discharged ordinary laws. Nine private clients consume public allocation,
record/config and meter laws throughout. EthVmCore §3 owns 36 complete interpreted/
native groups, strict normal/`-O` parser controls, 14 whole successful original
comparisons and three source-only typed underflows. Full declaration types/proof
values/privacy/generated raw-record and script support/axiom closure were audited;
no public conformance helper was added. Local constructed entry/charge facts prove
no actual Runner reachability, admission/allocation cap consistency, settlement,
transaction conservation, resource or whole G1/G2–G7 result. Q66 is unchanged.

Q66's local settlement slice is supplied by
[EthVmCore §3/§5/§7](modules/EthVmCore.md#3-eels-source-map): unrestricted raw
four-Nat result, U256 refund, signed state usage, exactly three local bounds and
five discharged ordinary laws. Private clients derive sender ranges/conservation,
independent dimensions/read sets/state erasure/floor branches, and conditional
entry-meter and allocation-cap composition through public equations. Core §3 owns
the complete 44 helper/six raw interpreted/native controls, strict parser scope and
44 authenticated whole successful original comparisons plus eight source-only
typed arithmetic failures.
Actual caller bounds/refund range and cast ordering, provider/fee effects, whole
G1/G2–G7, compiled/resource and VM/guest/readiness gates remain open.

The supplied Runner entry-kind carrier is project vocabulary, with no original
EELS enum or source call. [EthVmRunner §3/§5/§7](modules/EthVmRunner.md#3-eels-source-map)
owns its exact inventory and private exhaustive/dependent elimination, three branch
equations and six ordered disjointness clients. This closes only the nominal tag
slice; `Exec`, its relation form, D13/B11, F11 and G2–G7 remain unchanged.

EthVmCore §3/§5/§7 owns the supplied raw immutable FrameCtx and assembled Evm
view of EELS `src/ethereum/forks/amsterdam/vm/__init__.py:147–185`: exactly fifteen
data fields plus the sole local depth proof, and exactly two Evm fields. The
existing Limits literal admits depths 0 through 1024 independently of raw config
limits. Private complete facade constructor/projection/type/reconstruction and
independent-update clients retain every whole provider input; three complete
boundary controls, public map observations and byte/address guards are supplied.
Source evidence is the static 13-context/9-frame/4-control partition; config and
systemAddress are supplied policy fields. No source runtime or whole-Evm execution
comparison is claimed. Actual creation/inheritance, source/config/history/code
coherence, read-only handler signatures, world/control/parent integration,
F8 address transport/actual producer emission, F20, F11, gas/fuel/resources and
VM/guest/EEST/readiness remain open.

EthVmCore §3/§5/§7 owns the supplied raw eleven-field BlockEnvironment and
sixteen-field TransactionEnvironment from EELS
`src/ethereum/forks/amsterdam/vm/__init__.py:44–61,119–142`. Private complete
constructor/projection/type/reconstruction/update clients and full-value controls
retain independent quantities/address roles, ordered duplicates, complete
six-component authorizations, persistent sets and Option distinctions. Raw 257
history and noncanonical parity are carrier controls only. No new defaults,
instances, proof fields, public laws or admission/WF predicate are supplied;
oldest-first/at-most-256 history belongs to intended construction/source
correspondence. Actual frame/world construction, history lookup/admission,
capacity/intrinsic/settlement consumers, F8 transport, F20 lifetime, F11,
gas/fuel/resources and VM/guest/EEST/readiness remain separate obligations.

EthState §3/§4/§5/§7 owns the supplied raw eight-field TxRevertible carrier,
following D22/D23/B1 without extra fields, authored public laws, instances or
operations. Private facade clients check its exact constructor type, complete
projections/reconstruction and eight independent updates for arbitrary inputs.
Ordinary kernel controls retain all complete fields, raw malformed/sparse order
indexes, tombstones, zero/empty inners, arbitrary complete bytecode, independent
clears/transient keys and retained parent/siblings. These are carrier controls,
with no source runtime, snapshot/restore or tracker evidence. Its §10 retains
order/value coupling, lifetime/Reachable/AccountWritesLookedUp and error/provider
obligations, S1/S2/W1, F6/F7/F11 and C1–C4. No whole-State claim changes.

EthState §3/§4/§5/§7 owns the supplied raw three-field TxState and exact StateM
transformer alias. Private facade clients check exact arities, complete arbitrary
BlockState/TxRevertible/TxObs retention, reconstruction and independent replacements,
including a contravariant type constructor without Monad. Whole alias/run types
and underlying supplied actions need no classes; Id pure/put/get/error clients
check complete returned values/states and exact StateError/WitnessError payloads
after a put. Failure returns no transaction state. This is nominal assembly and
ordinary transformer wiring, with no authored public law, initialization, tracker
algorithm, source runtime or underlying-effect rollback claim. The unchanged
providers retain the current-pin codeReads mismatch X16(b); full-state refinement
is not supplied. EthState §10 keeps initialization/coherence, tracker/lifetimes,
observations/errors/freezing and all live integration/resource/readiness gates open.

EthVmRunner §3/§5/§7 owns the supplied source-free checked control carriers:
exactly InternalError.fuelExhausted with full Nat depth, CheckedResult and CheckedT
with Type-level domains and no Monad/hash/lawful premise. Private facade clients
check complete payloads, exact alias unfoldings, actual `.run.run` order and whole
base action preservation; local Id binds distinguish the two failure channels and
success. No EELS runtime operation corresponds to these carriers. No authored public
law, default, instance, adapter, budget or guest projection is supplied. Actual caller
propagation, execution, F11's conditional future invariant and G2–G7 remain open.

EthVmRunner §3/§5/§7 owns the supplied source-free raw RunnerEnv carrier:
exactly complete Core PrecompileTable, complete VmConfig and Base Address, in
that order under Monad alone. Private facade clients check exact signatures,
whole construction/reconstruction and every whole-field update, actual stored
lookup-domain and certified-action witnesses, and local Id/nonliteral-address/
raw-policy controls. No authored public law/factory, selected installed table,
coherence predicate or runtime assembly is added. Actual Block/Fork assembly,
createEvm copying, child inheritance, emission, effect/dispatch/settlement,
F11/D5 coupling and fuel/resource/VM/guest readiness remain open.

EthVmCore §3/§5/§7 supplies the four source-free shared precompile declarations:
exact result constructors, function alias, transparent MeterOk and ordered
four-field Monad-only table carrier, reusing Q83 unchanged. Private facade clients
check complete payloads, all six meter dimensions, arbitrary output/unconstrained
halts, exact table construction/projection/reconstruction, generic proof fields
and local empty/Id-singleton inhabitants. These supply no actual installed table,
source/normal-form/adapter law, arbitrary-monad observer, effect/dispatch/settlement
bridge, F11/D5 choice or fuel/resource/VM/guest readiness result.

EthVmCore §3/§5/§7 owns the supplied raw mutable Frame partition of EELS
`src/ethereum/forks/amsterdam/vm/__init__.py:147–185`: exactly two ExtTreeSet
aliases and nine independent fields, without extra admission/proof fields,
defaults, instances or manually authored public laws. Private complete constructor,
reconstruction and nine-update clients use public record reduction; set clients
use Std/Base public laws. Nontrivial controls retain all provider values, six meter
fields including negative refund, huge independent Nat pc, distinct sets and full
duplicate logs. This is bounded carrier evidence only: actual creation, context
integration, control outcomes, parent recursion, F8 transport/actual producer emission
and whole VM/guest/EEST/resource/readiness remain separate obligations.

EthVmCore §3/§5/§7 supplies the pure supplied-address `emitTransferLog` helper
and exactly two ordinary whole-Frame laws. Private public-facade clients derive
chronology and each unchanged field and prove the exact padding bridge. Complete
guards and the finite interpreted source binding (out of tree: its inputs are not
committed, so it cannot be reproduced from this repository) retain the explicit
Stack reversal and three finite-membership adapters, including the SOURCE
preparation/literal-order limitations recorded by that owner. Actual producers,
context/transport/value assembly, F20, F11, D5 coupling, fuel and cost gates remain
open.

EthVmInstructions §3/§5/§7 supplies the exact 153-member `Ops` vocabulary, total
`Ops.toByte`/`Ops.ofByte?` and exactly two ordinary round-trip laws (the second
conditioned only on a successful decode). Private facade clients use the laws for
generic consequences; exhaustive constructor coverage, 153 literal encoder pairs
and all 256 literal decoder equations bind the 153 positives and 103 holes to a
transcription of the pinned static source table; the comparison against the source
itself is out of tree: nothing for it is committed, so it cannot be reproduced
from this repository. The actual compiled leaf/facade/clients are warning-fatal
and declaration-audited. There is no instance/default/alias or new policy.
Dispatch, `step`, invalid-opcode halting, handlers and all
source-runtime/execution/fuel/resource/guest obligations remain open.

EthVmInstructions §3/§5/§7 supplies the raw seven-field `CreateRequest` at the
creation suspension split of EELS
`src/ethereum/forks/amsterdam/vm/instructions/system.py:59–185`.
Private facade clients preserve every constructor/projection, full reconstruction
and all seven independent updates. Complete deterministic controls retain huge
independent Nat grants, nominal full-width words/addresses, ordered complete init
bytes and both charging flags. No authored public law/default/instance or raw
admission is added. This is carrier evidence only: preflight, gas withholding,
collision/state effects, source/admission bridges, actual child context/frame,
handlers and resume remain unimplemented. It selects no CallRequest/staticness or
F11 option and closes no fuel/resource/guest/EEST/readiness gate.

EthVmInstructions §3/§5/§7 also supplies the exact raw fourteen-field
`CallRequest` at the call suspension split, with contexts in EELS
`src/ethereum/forks/amsterdam/vm/instructions/system.py:340–462` at `59c1473d`.
Private public-facade clients prove whole-field construction, reconstruction,
determination and every independent update; complete asymmetric and negative
controls retain huge independent grants, nominal full-width values/addresses and
windows, all four independent flags and complete ordered input/code bytes.
This is storage evidence only, with no Python CallRequest class or oracle
execution claim. No admission, default, instance, public helper law or new
producer/staticness policy follows. Actual handlers, child context/frame,
source/admission, gas, F11, rollback, lifetime, fuel/resource/guest and readiness
obligations remain open.

EthVmInstructions §3/§4/§5/§7 supplies exactly the four-field `ChildOutcome`:
complete frame/output/optional frame error and the supplied local Core settlement
proof. Private facade clients cover dependent reconstruction and proof-aware
updates, both predicate branches, complete retained payloads and missing/mismatched
proof diagnostics. No semantic producer, runtime guard, stronger admission,
public helper law or F11 proof-production route is added. Actual reachability,
rollback, source-Evm refinement, runner settlement/proof production, adapters,
incorporation and resume remain open; no execution/resource/readiness gate closes.

EthVmCore §3/§5/§7 supplies the raw ChildSettled assertion boundary and its
constructive Decidable instance. Private facade clients cover all raw Frames and
both flags, each clause and conditional whole-frame rollback/forfeit consequences;
the complete committed-spill counterexample remains rejected after both operations.
This supplies no actual execution/settlement proof, F11 choice, Q83 bridge, new
public law or G1/G2–G7/S2/resource/guest readiness result.

F8's system-address guidance is supplied by EthVmCore/EthVmRunner/EthVmInstructions/
EthBlock/EthFork §5/§7, with ownership in DECISIONS F8. The literal stays in Fork; the
supplied raw RunnerEnv storage, intended immutable FrameCtx transport and the address
argument after Frame in emitTransferLog leave VmConfig and request/handler/runner
parameter lists unchanged. The helper's zero identity and complete chronological nonzero
Frame/log equations quantify arbitrary local address/topic. Actual creation, child
inheritance, both producer source refinements and full config assembly remain
unimplemented. EthFork §3 supplies the complete concrete systemAddrs value and private
controls. Future controls independently vary address/topic through user/system entry,
nested CALL/CREATE and SELFDESTRUCT, retaining guard/effect order and log discard.
Intended construction/source coherence supplies the pinned address and F20 topic; no
global raw admission, gas/fuel premise, arbitrary StateT preservation, new hash query or
readiness result follows.

## 4. Agent implementation contract

EthVmCore §3/§4/§5/§7 supplies exactly the raw VmWorld carrying one complete
State.TxState m and the VmM StateT-over-ExceptT VmFault alias. Private facade
clients check arbitrary whole transaction retention, reconstruction/replacement,
the exact constructor/projection/alias/run types, a contravariant non-Monad
constructor and arbitrary supplied underlying action. Complete Id controls retain
success values/worlds and arbitrary faults, including nested witness errors after
put. No authored public law, default, instance, state lift or extra world field is
supplied. No underlying-effect rollback is inferred. Initialization, complete
StateError routing, trackers/snapshots/observation lifetimes, actual handlers/runner,
State X16(b), generic D5/S1/S2/W1, F6/F7/F11, fuel/guest and C1–C4 remain open.

EthStateless §3–§7 supplies the exact raw StatelessInput over the actual
NewPayloadRequest, ExecutionWitness and Base.U64 providers. Private ordinary
clients check the exact constructor/projection types, arbitrary whole-field
construction/reconstruction/determination and each independent update with both
siblings retained. Complete nested finite controls retain every byte/word/array
occurrence, including empty/duplicate/reversed/unequal arrays, malformed/oversized
raw bytes and zero/max/asymmetric chain IDs. CONTRACT §2/O5 and P1 determine this
module's input hint retirement; other owners' X16 migration stays separate.
The actual input dictionary and exactly three Q81 certificates are supplied there.
Private clients prove complete actual count recovery and the 16-byte outer head/
emitted starts. Ordinary structural support reflection and complete interpreted
48-input/385957-byte controls compare raw/model/both recovery paths/re-forwarding
and actual encoded bytes. Reverse supplies independent actual child WT and success.
Every recursive Q80 start bound remains; there is no final witness cap or root-count
premise. The co-located private generic public-law size foundation in EthStateless
§3/§4/§7 proves actual encoded length, supported fixed width and the exact layout
fold length, with ordered child certificates and 30-case/183-byte controls. It
retains the entire raw Q80 domain. The same private module supplies actual raw
request-size formulas, operation-local encoded-size laws, fixed classifications and
inherited child/member support, with ordinary symbolic probes. EthStateless §7 owns
their exact statements and hypotheses. Whole-input request support, later outer-start
and count/leaf bounds, decoded support, WF/decoder/root wrappers, schema-ID joins
and input-to-Rootable remain separate.
Raw decoding/roots, source-host agreement, caller/guest, F20/D5/fuel/backend/
security/resources and readiness remain open in EthStateless §10.

EthStateless §3/§4/§5/§7 supplies exactly the nineteen-field ExecutionPayload
and four-field NewPayloadRequest raw structures, reusing actual Block.Withdrawal
and ExecutionRequests providers. Private complete arbitrary facade clients check
every constructor/projection type, reconstruction/determination, all 23 independent
updates, complete nested byte/word/ordered observations and public conversions.
Whole finite controls retain independent asymmetric/zero/max fields, oversized and
malformed opaque bytes, empty/duplicate/reordered arrays, unusual version bytes
and every sibling through updates. Raw storage supplies no schema, validator,
hash, failure, effect, cap, public helper/law or readiness result. The actual Payload
and NewPayloadRequest dictionaries and exactly three Q81 certificates each are
supplied there. The request descriptor delegates actual children;
composed child validity and reverse WT-plus-success remain explicit. Private clients
establish CountRecoverable and exact 44-byte outer head/emitted starts; ordinary
support proofs and complete 96-case/365636-byte mathematical controls remain separate
from source-host agreement, Q88 raw decoding, roots and guest/resource/readiness.
The remaining obligations stay with EthStateless §10.

EthStateless §3/§4/§5/§7 owns the five supplied nominal raw execution-request item
carriers, with all 17 independent Base fields and their identity models. Private
facade clients prove arbitrary full construction/reconstruction, every independent
update, complete observation injectivity and Base checked recovery/size/range
properties. Whole finite controls retain every byte/word and all sibling fields.
These carriers add no admission, public helper/law/instance or amount conversion.
The five actual Q81 item dictionaries and fifteen ordinary certificates are
supplied there, with private actual Serializable/CountRecoverable/full-wire
clients and complete 681-input/100476-byte mathematical controls.
The raw five-array ExecutionRequests aggregate is also supplied there, with private
complete arbitrary construction/reconstruction, determination, independent updates
and public Array conversion recovery. Whole finite controls retain complete ordered
item observations, empty/unequal arrays, duplicates and independent field changes.
The actual aggregate Q81 dictionary and three certificates, with private complete
CountRecoverable/Serializable/full-wire clients and 80-input/150780-byte mathematical
controls, are supplied there. Raw decoding, root support, source-host
agreement and payload/input/guest composition remain open in
EthStateless §10. No execution, resource, security, cost or readiness gate closes.

EthBlock §3/§4/§5/§7 owns the supplied raw R-BLK Withdrawal carrier. Its private
public-facade clients check all constructor/projection types, arbitrary complete
construction/reconstruction, equality determined by all four fields and each
independent update. Interpreted controls retain all three unsigned values and all
twenty address bytes, including zero/max words and asymmetric addresses. No raw
admission or processing premise follows from raw storage. The separate actual
Q81 Withdrawal dictionary and its three external certificates are supplied there.
Private facade clients derive actual Serializable/count support and the complete
wire layout through public laws. Whole-value controls compare 44 independent
mathematical inputs and all 1936 bytes, with 34 local malformed-value guards.
Typed source-view scope adds no arbitrary Python/coercion/cache/host claim or
public off-WT guarantee. RLP, raw/guest decoding, root laws, Q53 root-input
composition and execution/resource/readiness gates remain open.

The eight exact natural moduli are supplied by EthField §3, in a separate leaf
reexported by the public Field facade. Private clients check complete `Nat` literal
equalities; complete guards/interpreted/native observations distinguish base/scalar
values and elementary widths/ranges/residues against authenticated pinned source.
No new public law, field instance, alias, primality/square-root metadata, backend,
replacement, resource/C1–C4 or whole-module/readiness gate is discharged.

The bounded initial natural-reference carrier is supplied by [EthField
§3/§5/§7](modules/EthField.md#supplied-initial-natural-reference-carrier). It admits
every modulus greater than one and arbitrary unread square-root metadata. Exactly five
operations, six ordinary observer laws and actual DecidableEq/zero-default/
canonical-Nat Repr families are supplied. Private facade-only clients derive checked
rejection, ordinary/checked roundtrips, success preservation and equality recognition.
The complete 42-row controls run under all three metadata choices with actual pairwise
equality; original optimized FQ synthetic parameter-class comparisons are distinct from
original EELS concrete-field globals, and checked admission is mathematical support with
zero original checked-helper executions. Basic reference add/sub/neg/mul/isZero, five
ordinary observer laws and four delegating operator instances are additionally supplied
there, with generic signed-model/cancellation clients and complete
small-pair/reducing/literal controls under arbitrary metadata. Its complete
interpreted/native observations agree with both authenticated original normal/optimized
streams on the independently frozen catalogue (EthField §4), retaining full raw
constructor inputs and every named/notation result. The separate reference-power leaf
also supplies exactly pow/toNat_pow/direct HPow, with an ordinary all-Nat-exponent
proof, generic public-law clients, 4,863 complete finite controls and full 48,696-row
interpreted/native comparisons per mode against both original streams and fresh original
replays (EthField §4; those comparisons are out of tree and not reproducible from this
repository). This admits every p>1 and arbitrary unread metadata, without a public
powMod-zero choice. The separate canonical-sign leaf supplies exactly sgn0/sgn0_eq,
admitting every p>1 and arbitrary unread metadata. Public-law clients derive Boolean
recognition, zero/one, construction parity and metadata irrelevance without equating
differently parameterized carriers. Its 945 finite controls are checked in tree; its
complete 2,298-row interpreted/native observations per mode, which agree with both
original normal/optimized streams and unchanged-producer replays, are out of tree and
not reproducible from this repository. EthField §3/§4/§7 owns the exact scope and
evidence limits. The separate checked-reference decoder supplies exactly ByteArray
ofBytesBE? and its complete ordinary success iff, with public-law
rejection/range/zero/leading-zero/positional/metadata clients. Its 762 literal rows (665
distinct inputs), each checked under three metadata choices, are in tree; its finite
interpreted/native comparisons of the same rows are out of tree. Original typed KZG/BLS
results retain assertion-mode and exact-width correspondence premises; EthField §3/§4/§7
owns these claims and limits. The separate Q86 inverse leaf supplies the ten authored
public declarations and two finite graph constructors owned by EthField §5/§7, with
ordinary totality, uniqueness, complete executable/model, range, zero and local gcd-unit
proofs. Private facade-only clients and all 2,055 in-tree complete controls retain every
composite nonunit result and arbitrary metadata; the per-mode interpreted/native
observations of the same rows are out of tree. Full comparison against all four sealed
and four fresh original 685-row streams uses the explicit reducing-input bridge
(EthField §4; out of tree, not reproducible from this repository). The approved
inverse-only low-remainder totality exception grants no runtime fuel, resource/time
bound or backend permission. The separate reference-division leaf supplies exactly
div/toNat_div/direct Div, composing the existing multiplication and Q86 inverse on every
canonical same-p pair at every p>1. Private facade clients, 54 literal controls and
complete 2,787-row interpreted/native observations preserve all zero/nonunit results and
arbitrary unread metadata; the committed 929-pair baseline supplies bounded
correspondence, while the four sealed original streams and independent complete Bezout
controls behind it are out of tree (EthField §3/§4/§7). The runtime producer reads
input-only rows; the strict full-value comparator and malformed CLI controls are
separate. No inverse/model/policy or ordinary-caller premise changes. Remaining field
operations, executable Montgomery/D6, concrete aliases, byte encoding/paired laws,
field/tower/Mathlib and C1–C4/replacement/guest gates remain open.

Read CONTRACT and `reference.toml`, the current decision statuses and DECISIONS dispositions, COMPOSITION, this review, the module's §2/§5/§7/§8/§10 and its providers' laws, the interface findings listed on the module's navigation line (DECISIONS §3), and the module's failure-ledger entries (X1) before implementing. Grouped inventory claims assign responsibility; expand them into a local declaration checklist, recording inputs, result/error types, ordered guards, observations, state effects and source/test references. Resolve `…`, bare structures, inferred/dead branches and undefined error types *in the Lean code* before treating an interface as frozen. The markdown specs are informal (`CONTRIBUTING.md` §5.4) and are not expected to reach that level themselves; where the spec is ambiguous rather than merely informal, raise it as a spec question instead of guessing.

The local SSZ count-recovery seam is bounded by Q87 and
[EthCodec §3/§5/§7](modules/EthCodec.md#local-ssz-count-recovery-q87): exactly the
actual-value predicate and complete ordinary iff, structural actual-child recursion,
private all-tag controls and symbolic public-law clients. The future inverse retains
Serializable plus CountRecoverable; its theorem, decoder completion/diagnostics,
source/schema/root/guest bridges and larger readiness gates remain open. This logical
seam supplies no native runtime operation or source-refinement theorem.

The generic SSZ schema forward seam is bounded by Q81 and
[EthCodec §3/§5/§7](modules/EthCodec.md#generic-ssz-schema-forward-seam-q81):
five metadata fields, two direct wrappers and two ordinary raw-call equations.
Private facade clients retain actual dictionaries/values and operation-local proofs;
explicit uncertified controls supply full small bytes/roots. Every actual instance
still owes external descriptor WF and both adapter certifications; none is supplied
by this generic carrier. The actual ExecutionWitness dictionary and all three
certificates are supplied by EthStateless §3/§5/§7, with private complete facade
clients, boundary controls and independent whole-wire comparisons in §4.
The five request-item dictionaries and fifteen certificates are also supplied
there, with private actual support/count/layout clients and complete mathematical
wire controls. No raw decoder, aggregate request, guest/resource/security/cost
or readiness gate closes.

EthState §3/§5/§7 owns the supplied raw four-field TxObs carrier, partitioning
TransactionState account_reads/storage_reads/code_reads/created_accounts under
D22/D23. It reuses canonical Base/Q84/Q51 and existing product dictionaries, with
no parameters, normalization, WF, authored public law, default or instance.
Private State-facade clients quantify arbitrary actual sets and prove complete
construction/reconstruction, all four full updates and six disjoint commutations;
public Std/Base laws and complete byte-content controls cover all key domains,
independent pair components, duplicates/unions/misses and retained siblings.
Membership agreement is not raw HashSet equality. Original source records and
copy/restore/incorporation context are read for binding; no EELS function execution
or lifecycle equivalence is claimed. Nominal TxState/StateM are supplied separately;
actual tracker operations,
D23 ownership/monotonicity, F7, S1/S2/W1 and C1–C4/resource/guest gates remain open.

EthState §3/§5/§7 supplies the exact thirteen-field raw BlockState for arbitrary m
without Monad/hash-query premises: complete PreState, F20 constants, persistent
writes/clears/three B1 order indexes, independent canonical Std read sets and
optional unbounded offset. Private State-facade clients check exact
constructor/projection types, whole eta/component reconstruction, every full update
and disjoint commutations, including a non-Monad type constructor. Complete
independent payload controls retain callback successes/errors, all constant/key
bytes, tombstones/zero/empty inners, raw order maps/counters/duplicate occurrences,
None/Some 0/huge offsets and siblings. State §3 binds the nine EELS fields and the
four deliberate guidance additions. The separate State/BlockInitialization leaf
supplies exactly BlockState.new and its explicit F20 new_consts law without class
premises. Whole arbitrary provider/constants retention and all eleven default
fields are privately verified in the owner; facade proof clients use only
new_consts. Complete independent interpreted `#guard` outputs cover arbitrary
constants, all four 32-byte fields, callback inputs/success/error payloads, empty
B1 maps/counters, None versus Some 0 and retained siblings/providers. Static source
reading fixes the original defaults; no Python runtime/allocation identity is
claimed. Further stable public consumer laws await a named consumer and separately
reviewed contract. No tracker operation or invariant is supplied.
Acquisition/coherence, actual providers/sharing/linear ownership/order history,
D22/D23, F7, D5/S1/S2/W1, replacement and C1–C4/resource/guest gates remain open.

EthState §3/§5/§7 owns the two supplied logical block read predicates and exactly
accountReadSet_iff/storageReadSet_iff. All raw blocks and complete keys are admitted,
class-free; all other fields remain unrestricted. Private facade clients consume
both directions of the public laws, including a non-Monad constructor, and prove
independence under every other field update. Private controls compare complete
independent membership vectors with IDs/full queried key bytes, all byte positions,
high bits, pair components, duplicates, field changes and retained siblings.
Runtime controls transport existing Std membership decidability through the public
iff laws, with no new instance/API. Source fields and incorporation/BAL contexts
are statically bound at the pin; no original tracker execution is claimed. No set
provider, enumeration/order, codeReadSet, raw-set equality or lifecycle/ownership/
monotonicity/resource/whole-State result follows.

EthBase §3/§5/§7 owns Q84's exactly ten canonical Address/Bytes32 table-support
declarations, with legible complete 20/32-digit models, structural streaming and
ordinary all-input executable/reference/canonical-hash equations. All helpers and
public-facade clients stay private. Validate exact names/types/instance identity,
existing actual equality and lawful classes, alias reach and other/variable-width
negative guards. In tree, 19 literal vectors per type compare whole UInt64
executable, reference and actual-hash results as interpreted guards; the
every-bit/byte, random and compiled-mode comparisons are out of tree: nothing for them
is committed, so they cannot be reproduced from this repository. Public Std clients
cover member/insert/union/duplicate/unequal preservation and map lookup/overwrite for
all three observation domains, without a distinct-hash premise. Preserve Q51's Hash32
model and existing expectations. This is functional support only: the raw TxObs and
BlockState and nominal TxState/StateM carriers are supplied separately; D22/D23
lifecycle/ownership, F7 replay failures/observations, actual distributions,
construction/resizing/allocation, replacement and C1–C4 remain separate obligations.

EthBase's `utils/numeric.py:177–216` operation is supplied as
`STFSpec.Base.taylorExponential (factor numerator denominator : Nat)
(h : 0 < denominator) : Nat`, with exactly the two ordinary public zero-factor
and zero-numerator laws owned by [EthBase §3/§5/§7](modules/EthBase.md#implemented-taylor-exponential).
All loop/equation/descent helpers are private; the source-order iterated floors
and arbitrary-natural domain are preserved, with no fuel/error/policy argument.
Eleven ordinary public-only clients and 28 full literal guards are supplied.
EthBase §3 owns the complete interpreted/native target recipe, dated external
source evidence and the committed reader's authentication boundary. Normal and `-O` strict parser runs each pass 122 cases plus 122 actual CLI
invocations, including explicit uniform LF/CRLF acceptance and malformed framing,
field/type/value/order/binding rejection. The private logical lexicographic
measure proves mathematical totality, not DISC-002 practical large-input cost,
stack/cycle feasibility or caller-exception reachability. No broader Base,
G1–G7, EEST/guest or dated §6 readiness claim follows.

The supplied numeric charge, rollback, refund and local transfer algebra's exact source-to-Lean/domain/error/law/test rows
are owned by [EthVmCore §3/§7](modules/EthVmCore.md#3-eels-source-map). Its ordinary
public-only clients and complete controls retain all fields, signed refunds, both spill
pools, raw unusual meters and unbounded amounts, plus complete nominal exception
payloads. Numeric helper correspondence excludes diagnostic trace wrappers and frame
settlement; the `check_gas` holder is only its meter-field projection. The three new
rollback helpers preserve Φ; ordinary restore retains committed spill while entry
restore returns both pools. Their eight laws use exactly the source assertion proof
arguments, with source-only invalid probes retaining assertion order and all fields.
Refund/repay preserve Φ and B/q/C on every raw meter, with min-based complete equations,
zero-credit neutrality, universal repayment exhaustion and idempotence. Public clients
compose actual providers and prove conditional charge/refund inversion under local initial
pending spill zero; the unconditional claim has a full-field counterexample. The source
repayment assertion is a postcondition, without a new input proof or failure.
The eight local transfer laws retain every untouched field, account for returned
value-first grants, and prove exact potential effects: forfeit retains C under S=0,
withhold removes only its returned execution grant, drain preserves Φ, and restore
adds its execution amount. Public clients derive retained E/64 and complete saved-amount
withhold/drain/restore inversion; actual rollback post laws supply the forfeit premise.
Thirty complete return/meter controls and three source-only invalid-forfeit probes
retain assertion :674 before mutation. No actual CREATE return or child settlement
claim follows. Signed refund addition and the standalone scalar maximum supply four
additional unconditional ordinary laws. Public-only clients derive complete Nat-field
retention, signed zero/composition/inverse and actual rollback/reset order, plus both
complementary-share equations. Twelve complete signed cases and fourteen scalar cases
include R>B, both spills, cancellation, rounding boundaries and beyond-U256 values.
The source adapter projects only the exact original refund AugAssign at :242 on distinct
typed parent/child meters with unchanged child; it does not replay whole incorporation.
The unchanged scalar helper is called directly. Normal/-O complete-frame parsing rejects
boolean/float substitutes and malformed streams. No top-level refund sign, storage
history, source caller assertion, or message-call affordability/stipend theorem follows.
Q61 supplies the `txStateGasUsed` observer and single ordinary signed equation
on only the local baseline-to-grant proof. Public-only clients derive insensitivity
to execution gas/refund/baseline with separate proofs, additive spills, grant/reservoir
order and a valid negative witness. Twenty complete literal guards and strict normal/`-O`
whole frames include negative/beyond-U256 returns and unchanged full meters. Authenticated
original comparison passed twenty direct unchanged helper calls with exact builtin `int`
results and three source-only assertion-597 cases, all with unchanged complete meters
and source/runtime identities; no invalid Lean proof or other original helper replay. Caller
reachability, remaining operations and transaction conservation remain open. These local laws
close no whole G1/G2–G7, VmFault ledger, F11/B11, resource or guest/EEST gate.

The bounded Stack slice's seven source/model rows and ten ordinary public laws (Q82) are
owned by [EthVmCore §3/§7](modules/EthVmCore.md#3-eels-source-map). Its private Array
carrier enforces size≤1024 and observes top first. Error iff laws quantify over all
ExceptionalHalt values, so public clients derive successful operation availability
and both conditional inverses with actual Stack equality. Forty-one whole-model
controls cover empty/full transitions, complete returned words/remainders, huge
Nat depths and sequence intermediates. Source correspondence covers only fresh typed
bounded lists and unchanged pop/push helpers; peek is a labelled List-index adapter.
The exchange laws additionally support private public-only availability/size/all-cell,
equal-valid actual identity, commutation and involution clients and 29 complete-model
controls. All-Nat mathematical cases are distinct from original opcode execution;
the pure helper implements no gas/decode/PC behavior. Actual handler order, frame
reachability, compiler allocations and
C1–C4 remain open; this is no whole VM or guest readiness claim.

The raw StateGasCosts/VmLimits/VmConfig data seam is owned by
[EthVmCore §3/§5/§7](modules/EthVmCore.md#3-eels-source-map): the exact existing
four-Nat state inputs, three-Nat limits and three complete record fields, with
six ordinary ext/eta laws and private generic constructor/projection/law clients.
Selected cfg.costs.opcodeAdd congruence retains the complete existing chargeGas
result on the same meter, with arbitrary unused stateCosts/limits; public
success/error laws retain every meter field and the exclusive shortage result.
There are no defaults/instances/proof fields/factory/WF/extra amount observations,
new Stack or literal-depth behavior, source-value imports, runtime mirror suite,
native data protocol or pricing operations. Remaining StateGasCosts representation
work concerns the three amount-provider observations and their generic versus
specialization equations; it does not unsupply the four-input data carrier.
Actual EthFork values and configuration, F8 limits, consumers/frame/target
consistency, actual pricing callers, ordering/resource/C1–C4 and VM/guest
gates remain open.

The raw GasCosts data seam is owned by
[EthVmCore §3/§5/§7](modules/EthVmCore.md#3-eels-source-map): the complete class
plus seven explicit BLS fields, with 137 Nat, one Int, four existing Base.U64 and
two Array Nat fields, no defaults/instances/factory/global policy invariant.
Exactly two ordinary ext/eta laws and private public-only full-constructor/law
clients are supplied. A selected-cost client uses the existing chargeGas operation
and public success/error laws to retain the complete result on the same arbitrary
meter when the selected opcodeAdd projection agrees. This is not an opcode handler,
source-value acquisition, record-only native protocol or pricing operation.
MODEXP classification, module-derived maximum placement, StateGasCosts
representation, BLS index/denominator support and actual EthFork factory/config
coherence remain open for the claims that need them. Memory pricing's policy
disposition is owned separately by Q63. No broad B8, termination, resource, C1–C4 or guest
readiness gate follows.

The two scalar immediate decoder APIs and eight ordinary laws are owned by
[EthVmCore §3/§7](modules/EthVmCore.md#3-eels-source-map). They retain actual UInt8
inputs, Nat/ordered-Nat-pair successes and the existing nullary invalidParameter.
Public-only clients derive successful progress, exclusive errors, bounded successor
indices and actual input equality. All 512 complete literal guards and interpreted
target frames agree with authenticated unchanged original helper calls on fresh
pinned U8 inputs; exact result classes, both tuple coordinates, exception args and
unchanged full inputs are retained before nominal projection. Strict normal/`-O`
parsing rejects malformed, reordered, truncated and changed middle results. No
other original helper or handler was replayed. This supplies local decoder
semantics, not native cost, handler/frame, resource, G1–G7 or guest readiness.

The independent `bufferRead` adapter and its three ordinary public laws are
supplied under [EthVmCore §3/§7](modules/EthVmCore.md#3-eels-source-map), using the
existing Base padded-window provider and exact U256.toNat operands. Public-only
clients consume the bridge, complete List/size models and Base's extension law
with its explicit window premise. Thirty-two whole-byte controls and strict
normal/`-O` framing retain huge offsets with small requested outputs. Huge-start
cases do not discriminate endpoint wrapping; the all-domain laws and code/provider
inspection establish the intended Nat semantics. Successful source correspondence
requires actual pinned arguments/dependencies, representable width and successful
allocation. No compiled cost, Memory carrier, R1/C1–C4, G1–G7 or guest claim follows.

Q62’s supplied aligned Memory/local-window contract is owned by
[EthVmCore §5/§7](modules/EthVmCore.md#5-interface), with its handoff in COMPOSITION
§2. Its private carrier, six public APIs and ten ordinary laws are implemented and
discharged using actual Base Bytes, without exposing representation helpers.
Post-write read witnesses are derived from preserved size
and the original local window proof, without an extra semantic premise or helper.
Public-only clients cover full model effects, actual empty-write identity,
empty-any-offset behavior, immutable snapshots and overlap/disjoint reads. Thirty-three
complete native frames agree with frozen literals, and thirty-one mapped frames
agree with the authenticated retained source baseline under strict normal/`-O` parsing,
without source replay. Caller derivations and compiled ownership/cost validation
remain open on their existing domains. No invalid-window completion, runtime error
or global frame invariant is
introduced. BufferRead remains independent; memory pricing’s policy-threading
contract is owned by Q63 and EthVmCore §5/§7; its local implementation/proofs are supplied below, while actual
callers/coherence/resource obligations remain open. This supplies no implementation closure, R1/C1–C4,
L-MEM-BOUND, G1–G7 or guest/EEST gate.

Q63's local pricing slice is supplied by [EthVmCore §3/§5/§7](modules/EthVmCore.md#3-eels-source-map):
two pure VmConfig-first functions, the existing two-Nat result and exactly ten ordinary
public laws. Private source-fold/rounded-maximum refinement proves the seed-aware closed
forms and subtraction validity for every raw coefficient/seed. Public-only clients derive
same-size/permutation/duplicate/subsumed invariance, seed-aware composition using actual
Memory.expand, post-expansion admission, read preservation and admitted write/read witnesses through provider laws.
Forty-two complete literal controls agree with actual interpreted/native observations;
twenty-four pinned-policy rows agree with unchanged authenticated original helpers, actual
source classes, full arguments and unchanged pre/post bytes/bindings. Strict normal/`-O`
comparison and actual CLI LF/CRLF controls check entire frames, not hashes or summary sizes.
Generic-policy controls are target-only; three raw unaligned predictions remain unrun
source-only controls. No returned huge extent is allocated. These local facts do not prove
actual caller/window/payload/config/target coherence, charge/allocation/check ordering,
L-MEM-BOUND, R1/C1–C4, G1–G7, general source-host/resources or VM/guest/EEST readiness.

The supplied Jumpdest slice is owned by [EthVmCore §3/§5/§7](modules/EthVmCore.md#3-eels-source-map):
abstract immutable packed map, existing factory/contains operations and exactly
three ordinary lookup equations. Private all-code/all-Nat packed/reference,
shape/update/padding/finite-support proofs use actual Base.Bytes public bridges;
public-only clients derive PUSH/head/tail, true-hit byte identity/bounds and huge
absence. The unchanged 32 handwritten controls and strict complete-frame/parser
checks are committed. The canonical 940-input catalog, preflight digest and source
packet are external inputs; the reader does not produce or authenticate them.
EthVmCore §3/§4 identifies the dated interpreted/native/retained-source evidence
and its exact scope. Logical bitmap observations remain distinct from private
physical shape proofs. Code/map/cache provenance, actual
JUMP/JUMPI ordering, source-host generalization, compiled costs/ownership/resources,
C1–C4, G1–G7 and whole VM/guest/EEST gates remain open.

The supplied chronological Log/LogRope slice is owned by
[EthVmCore §3/§5/§7](modules/EthVmCore.md#3-eels-source-map). Its exact existing
raw fields/public constructors/two operations and six ordinary laws have private
all-tree reference/workstack refinement and public-only consumer proofs. Source
rows distinguish the tuple model from unsupplied real LOG/transfer/child/output
operations; no Python rope helper or source replay is claimed. Full 16+6 controls
agree interpreted/native on every payload and saved observation. The dated native C3 record in §4
retains 102 successful process receipts with complete correctness outside clocks,
generated-C measure-erasure/lifetime inspection, deep skew and expanded shared
occurrences, explicit output/root/child cleanup and retained parents. The empty
family shares one dynamic empty subtree across its deep concat spine, and the
shared family repeats one A/B subtree; cleanup/allocations reflect this sharing.
Fixed payload globals and fresh mixed payloads are distinguished. Raw ns,
small-allocation heartbeats and whole-process RSS are scoped diagnostics; combined
construction includes attempted failed-child release and IO holders. General host
stack/exact heap bounds, C1/C4, actual producer/frame/receipt composition, whole
VM/guest gates and dated §6 readiness remain open.

Use these three independent acceptance checks:

- **Reference:** ordered successful and failing behaviour matches the pinned source/dependencies, including the phase that catches each failure.
- **Component:** representation invariant and public model equations hold on the stated domain; no caller unfolds a replaceable container.
- **Composition:** every consumed premise is produced by a provider or established by a caller, and every returned effect/error fits the shared adapters. Cyclic proofs cannot discharge each other's premises.

At module completion record which obligations are actually discharged and how. Tests may demonstrate counterexamples or confidence; they cannot be relabelled as a universal proof. Keep the Mathlib and security packages' dependencies directed outward from the core. Use the memory, trie and gas replacement exercises to check that clients depend on public equations; include order/caches/failure observations in the trie exercise.

For each implemented EELS operation, keep a reviewable source-to-Lean row in the owning module's §3 or in the implementation change: exact EELS `file:line` and dependency version if relevant; Lean declaration and public type; accepted-input/precondition domain; success value and state effects; ordered failure conditions and their first consuming handler/O-row; model equation or theorem; and at least one deterministic case or named fixture area. Grouped inventory claims in §3 establish ownership only. Mark an item **unimplemented**, **implemented but unproved**, or **discharged**, and name any caller that must establish a precondition. A passing fixture is evidence for the specific path it executes, not for every branch of the claimed operation.

The exact SC1 four-field equation and ordinary complete-wire reference are owned
by EthStateCommit §3. Its account-encoding driver compares both unchanged original
functions under explicit typed-field, complete-domain and runtime premises. Existing
account binding and conditional SC10 remain separate supplied laws; these controls
add no callback, secured-root or whole-backend result.

The exact SC2 integer equation and adjacent ordinary complete-wire reference are
owned by EthStateCommit §3. Its storage-encoding driver checks complete original
U256/RLP dispatch under the stated local source/runtime premises, with strict
normal/optimized parser controls. These local checks add no root or guest gate.

Local SC6/nonzero storage SC10 support is owned by EthStateCommit §3/§7.
The decoder laws and private strict admission/value clients use public provider
models. The nominal witness-error carrier is owned by
[EthState §3/§5](modules/EthState.md#3-eels-source-map).
Complete parser and typed-provider diagnostics preserve failure order separately
from the coarse leaf mapping; native/interpreted full-row controls are owned by §3.
These storage gates establish no global error/granularity,
secure roots/callbacks, authentication/progress, generic Q55 coupling, C1–C4
or guest/EEST readiness result.

Local SC5/conditional account SC10 support is owned by EthStateCommit §3/§7.
The definition and public contracts retain arbitrary supplied defaults,
unbounded nonce and numerical U256 balance acceptance. Private ordinary bounded
packed/reference equality, generalized prefix and absorbing/retained-state proofs
consume public provider models. Contract clients use whole assembled Q47 premises;
complete parser/value/default/constructor regressions check full local results.
A private empty-account client discharges its whole domain through public RLP sizes
before consuming the roundtrip contract.
Complete RLP-first order is observed upstream; local field order is statically
sequential and is not exposed by the coarse error. Contextual callbacks/secure
roots, witness authentication, backend progress, collisions/source history,
generic coupling, global errors/O12/resources, C1–C4 and guest/EEST readiness
remain open.

The mathematical block view and exactly its ordinary application equation are
supplied by EthState §3/§7.2. Private facade clients derive the full result, all
raw-field and observer consequences and independence from arbitrary
metadata/provider/constants/read sets/offset. Complete numerical/list interpreted
`#guard` controls cover raw non-WF states; no original Python view function is
claimed. Only the mathematical diff equation is discharged; full diff WF/history,
actual tracker/lifetimes, S1/S2/W1/F7 and cost/readiness gates remain open.

Q85 raw extraction is specified in EthState §3/§7: the seven ordinary all-raw
projection laws, public-only private clients and complete numerical/list controls
cover effects and supplied metadata, including malformed indexes and missing versus
present-empty slot maps. Four-effect EELS binding is static; no original malformed
separate-index runtime exists. Source alias/history, full WF, F7, S1/S2/W1 and
C1–C4 remain separate.

Internal first-write order support is specified in
[EthState §3/§7.5](modules/EthState.md#3-eels-source-map).

Q57's [EthState §3/§5](modules/EthState.md#3-eels-source-map) supplies the success-only
Id lookup predicate. Private whole-predicate positive/error-only and wrong-success
proofs cover arbitrary raw states, supplied constants and root functions; this adds
no production provider or progress theorem. Q58's [EthState §3/§7.4](modules/EthState.md#3-eels-source-map)
supplies StructuralPremises and its ordinary structural laws. Private arbitrary
public-law clients cover the selected-clause iff, both eliminations, initial-WF
conditional preservation and equal-four-effects congruence. Private omission proofs
and complete finite guards cover empty/zero patches, malformed initial states,
delete/clear/reintroduction, account replacement and arbitrary metadata/code/account
fields. Root, backend, full-WF/history and whole-State gates remain separate.

Q53's [EthCommit](modules/EthCommit.md#3-eels-source-map) and
[EthBlock](modules/EthBlock.md#3-eels-source-map) rows describe scoped seams.
Generic C11 storage/safety, the Q53 byte-key contract and pure unsecured preparation
and typed root composition, plus the conditional existing-Bytes key instance below,
are supplied by EthCommit §3; concrete consumer encoding and Python key/equality/alias
bridges remain **unimplemented**. Before any implementation claim, validate arbitrary
supplied defaults, unsafe
nondefault insertion versus safe default deletion, exact safety iff, direct valid stored
defaults, empty Bytes versus RLP zero/empty collections, lawful byte-key alias exclusion,
encoding exactly once, whole prepared maps and zero preparation queries. Root validation
must use a supplied nonliteral empty root, preserve original C8 errors/prior state and
whole queries/answers, and explicitly require `LawfulMonad` for sequential-reference
equality. Public proof-only clients establish the owner/consumer boundary. Authenticated
source comparisons must retain concrete supported non-`None` equality/dispatch,
source-schema/assembled `Encodable` (Q47), coherent F20 and pinned host premises.

Q54's [EthBase §3/§5/§7](modules/EthBase.md#3-eels-source-map) functional providers
are discharged there. Their gates validate every finite input through ordinary
`compare_eq_reference`, `compare_toList`, actual-equality `compare_eq_eq_iff`,
`Std.TransOrd`/`Std.LawfulEqOrd` and `toByteArray_toList` proofs; keep scanner/helper
private and give every new public law a symbolic proof-only client using public
Base/Std seams. Deterministic and unchanged authenticated source cases cover
empty/equal/proper-prefix, leading zeros, unsigned high bytes, early/late mismatch,
long shared prefixes and actual RLP ordinal ordering (`80` after `01`). Native
checks compare complete results with the List model. Run declaration/boundary gates;
retain existing equality and reject unapproved container/instance scope. Any local
comparator cost evidence has a correctness gate, no checksum in timed loops, and
explicit conversions/allocation/provenance. Actual map construction, preparation,
root composition, retained versions, replacement and C1–C4 remain separate gates;
reassess material limitations under D18/D25. The existing-Bytes adapter mechanism
and exact-export law are owned by
[EthCommit §3/§7.0.3](modules/EthCommit.md#pure-unsecured-typed-preparation-q53).
Its complete public-import preparation/root clients retain caller value/safety,
unsecured, empty-root and query premises; the sequenced reference additionally
requires `LawfulMonad`. Consumer schema/source/F20/host/secure-policy and guest
readiness obligations remain separate.

Q55's [EthCommit](modules/EthCommit.md#5-interface) complete generic decoder
operations, three public plain-Monad equations and private totality/acquisition/
inline/ordered-error laws are supplied with source-to-Lean rows in EthCommit §3.
Private public-import clients and complete Id/state/failure/structural controls
cover local bypass/missing/stub paths, raw thresholds and verbatim answers, strict
RLP/HP/first-error ordering, retained effects and underlying query failure, exact
inline parsed-subterm Encodable, alias-keyed short/long entries, repeated siblings,
diamonds and root-seeded cycles. Finite authenticated acyclic source comparisons
are conformance evidence; sequencing simplification explicitly uses LawfulMonad.
This supplies the local decoder portion of W1. The concrete Id-run consumer/error
adapter, generic interpretation/action/result-cache lifetime, Node.WF/cache bundle
and whole witness agreement remain open. The no-completed-memo baseline supplies
no production cost exception, host/O12 resolution, whole W1/S2/R2/C1–C4 gate or
guest readiness change.

The pure completed-cache child-reference contract and conditional differential
evidence are owned by [EthCommit §3/§7.0.7](modules/EthCommit.md#3-eels-source-map).
Public-law callers, complete nested-item and strict parser controls are supplied there.
Pure all-input List/HP equality is distinct from source-value evidence; dirty-cache,
query/write boundaries and whole B3/DISC-003/cache/mutation/resource gates remain open.

The supplied incremental-root contract and conditional source evidence are owned by
[EthCommit §3/§7.0.9](modules/EthCommit.md#3-eels-source-map): two operations, six literal
plain-Monad equations and ordinary private whole-action model equality. Committed
full-field/generic/failure/source controls retain the relevant accessed-cache/embedding
premises; clean cached roots bypass descendants. Wider root/map/mutation/action/cache,
B3/DISC-003, resource and guest-readiness gates remain open.

The completed immediate-extension contract and source-value evidence are owned by
[EthCommit §3/§7.0.8](modules/EthCommit.md#3-eels-source-map). Committed operational
recording-state guards exercise fresh extension widths 31/32/33 for branch and immediate
extension inputs; Id source comparisons record source stages/queries separately. Keep
child embedding/cache premises, one-splice scope and whole integration obligations.

The bounded completed fresh-leaf contract is owned by
[EthCommit §3/§6/§7.0.6](modules/EthCommit.md#3-eels-source-map). Public-import clients
and complete-field/query/failure controls are supplied there. The committed source
driver compares fresh successful Id results; seeded recording-state and transformer
controls are separate. Preserve the full assembled Encodable/class/Id/hash/host domain
and every open whole-cache/update/root/effect/lifetime/resource/guest obligation.

Q59's [EthCommit C20/§§4/5/7](modules/EthCommit.md#5-interface) lookup seam is
**supplied locally**: constructor, operation and seven public equations, private
structural descent and all-bare offset/reference equality are implemented.
Public-import clients and scoped controls observe complete optional bytes and exact
errors on arbitrary Enc,
all sixteen selected digits, arities 0/1/15/16/17, terminal-before-bounds, valid short/oversized
slots, ignored off-path stubs, present empty leaves, clipped/mismatched prefixes and
finite empty-extension/ext-to-ext/leaf descent. Fresh actual pinned source comparisons observe
values/stubs only under valid selected accesses and explicit actual Hash32/source-class/
host premises; the adopted typed out-of-range selected-slot adaptation is tested
separately. Odd generalized
Nibbles are covered by ordinary Lean equations, not original byte-entry observations.
The implementation uses public provider laws and private reference/cursor/child-size
support with ordinary all-bare-input equality (D25). Its offset execution avoids repeated
complete suffix copies and off-path scans (D18). No whole source agreement theorem,
benchmark or guest fault/output follows; Node.WF,
decoder/cache/update/root/security, generic coupling/lifetime, whole W1/S2/C1–C4/O12 and
guest readiness obligations remain open under their current owners.

Local ToVCVio `PatriciaReference` support is not an EELS inventory operation: `Trie/PatriciaReference.lean` owns exactly two mutually structural Prop relations, five necessary constructors and three conditional public laws; `Test/PatriciaReference.lean` owns the arbitrary-h/full-field/all-finite, every-slot/terminal, zero-digest, complete-threshold and omission clients. Erased symbolic 2^65-path/top-Fits and 2^64−1-value/joined-shell omission proofs separate canonicality and item-wise bounds from complete certificates without huge allocation. Pinned MPT assembly/C7/root source qualifies the boundary, not a source-refinement claim. Later actual C7/effect/C8 equality, executable certificate construction, empty-root coherence, generic D5/witness/security/budget/cost/readiness gates stay open; fresh strict complete mutual/private closure and actual current source/native/full-byte provenance gates apply to this bounded slice.

Local ToVCVio `PatriciaRlpDomain` (Q56; owning guidance §§3/4/5/7) supplies
exactly five total noncomputable logical width/domain definitions and six ordinary
conditional-width/inhabitation laws. The main directly imports only PatriciaReference;
all support stays private. Logical test clients cover both iff directions,
arbitrary h/finite paths/full bytes/all16 occurrences, symbolic huge and joined/extent
omissions, noncanonical shapes, complete byte/tag boundaries and modest provider
observations. Fresh fatal ordinary builds, strict zero-sorry every generated ToVCVio
declaration, complete private Expr/projection/inductive/every matching ALL-recursor/
rule closure with baseline axioms only, missing/default-warning controls, actual
current source/C/ordinary-OLean/header/O3/sole-link/runtime/full-output checks and
final exact source/pin authentication apply. Native checks cover executable provider
initializers/observations only, never logical width extraction or a Prop selector.
Two independent exact reviews and root evaluation remain required. General HP
flag-width simplification, executable extraction/construction, actual map/C7/C6/
effect/C8/empty-root/F20/D5/witness/security/budget/nonvacuity/cost/readiness stay open.

An implementation gate does not prohibit useful spikes or an incomplete development branch. It prohibits presenting unvalidated behaviour as the normative finished spec. Debt handling follows D18 (accepted): record performance exceptions in `STFSpec/informal/DEBT.md`, and keep missing premises explicit rather than silently weakening them. A patch affecting an observer, failure priority, gas policy, schema, ordering or state lifetime must update all affected contracts and the composition proof before a conformance claim is restored.

The actual ExecutionPayload SSZ dictionary and exactly its three Q81 certificates
are supplied by [EthStateless §3/§5/§7](modules/EthStateless.md#3-eels-source-map).
It consumes the actual Block Withdrawal dictionary and certificates. Callers retain
the extra-data-valid forward premise and the single WT-and-success reverse premise.
Private complete clients/count recovery and 129 independent whole-wire controls are
owned by §4; operation support and source parser/backing/host domains stay separate.
NewPayloadRequest/input decoding, roots/O2, validation, guest and resource/
security/readiness obligations remain open. This handoff adds no public helper,
decoder policy, guest outcome or completed integration gate.

## 5. Blocking obligations and proposed ownership

X1 is coordinated by EthConformance tooling; each module owns its explicit and implicit exception sites, and EthStateless owns phase projection. X6 belongs to Core/Instructions/Runner with the fuel-adequacy investigation ([§7](REVIEW.md#7-acceptance-criteria-proof-gates-composition-cases-replacement-and-cost-checks) G2–G7) as its integration gate. X10 is jointly discharged by State's reachable trace and Witness/Commit's ordered update laws. X7 belongs to Security/StateCommit, with full-state progress and oracle coupling supplied explicitly. Exact schemas belong to their record owner and Codec instances. These are assignments of review work, not assertions that the work is finished.

The highest-risk uncompleted items are closing the failure ledger's unresolved sites (X1), the complete CALL/CREATE gas proof (the fuel-adequacy investigation, §7 G2–G7), code-authenticity/oracle coupling, lenient witness root agreement (the witness/full-state agreement prototype, §7 S2), and the open interface items (X15). Until these are resolved, the repository is suitable for targeted validation and scaffolding, not an unconditional claim of end-to-end soundness.

## 6. Implementation-readiness assessment (2026-11-04)

**Implemented scope.** Each library's §3 owns its implemented declarations, source correspondence, public laws and evidence, and its §10 owns what is missing. Lean definitions exist in EthBase, EthHash, EthField, EthCodec, EthCommit, EthState, EthStateCommit, EthVmCore, EthVmInstructions, EthVmRunner, EthPrecompiles, EthBlock, EthFork and EthStateless, and in the local ToVCVio library of the security package. Above EthVmCore they are carriers, fork values and isolated operations: no opcode effect, step function, runner execution, block execution or guest entry point exists. EthCurve, EthPairing, EthStateFull, EthStateWitness, EthSecurity and the three Mathlib bridges remain scaffolding. [EthConformance §3](modules/EthConformance.md#3-eels-source-map) owns fixture extraction and authentication, including the guest records in both `blocks[]` and `engineNewPayloads[]`. [COMPOSITION](COMPOSITION.md) records supplied component premises; no end-to-end theorem is proved.

**Evaluation.** CI builds every library, runs the declaration check and replays the modules of each package's libraries through the kernel (CONTRIBUTING §4). Guards and caller proofs compile through `EthConformance`. Some CI steps compare native and interpreted outputs with frozen catalogues taken from EELS. No CI job executes EELS. The frozen catalogues remain evidence at `e1a316a0`, and some drivers still require that commit (GAPS-CROSSCUTTING X16). Each module's §3 states its evidence and its limits. Guest, full-state and engine runners are absent, and no EEST guest record executes in Lean. The exact pin is in `reference.toml`.

**Completion gates.** Lower-layer work can proceed against each module's contracts and §3 gates, together with its re-pin items (X16). Runner, block and guest completion still require fuel adequacy (G2–G7), witness/full-state agreement (S2), and X1, X6, X7 and X15. Unresolved domains, error priority, schemas and caller premises must stay explicit. X5 records fixture coverage limits. Passing document checks or a prototype does not close these gates.

**Performance and proof limits.** The C1–C4 workload and measurement gates and the R4 representation exercise remain open. No whole-guest native-baseline comparison or target-zkVM cost result supports a speed claim. The specification arguments and literature references do not supply concrete MPT, pairing, imported-crypto or whole-guest resource proofs (X7, X9, X12). DECISIONS owns decision statuses, and DEBT owns implementation debt.

## 7. Acceptance criteria: proof gates, composition cases, replacement and cost checks

*Live. These are the criteria an implementation must meet before it claims the corresponding results; they make the component contracts in [ARCHITECTURE](ARCHITECTURE.md) checkable. Cite them by ID: proof gates G1–G7, S1–S2, W1; replacement gates R1–R4; cost checks C1–C4.*

### 7.1 Scope and evidence

Use the EELS commit and dependency versions in [`reference.toml`](../../reference.toml). Start with public word, memory, storage and gas contracts; implement enough arithmetic, storage and CALL/CREATE behaviour to test their composition. A toy trie tests the backend seam, not Ethereum MPT correctness. A small executable relation derived from the same step function supplies the proof view; do not maintain a second opcode semantics.

Each obligation below has a stable identifier. The report records its status as **planned**, **source-checked**, **proved for the slice**, or **proved for the supported fork**. A source read, passing test or toy proof must not be reported as a whole-fork theorem. Include theorem names, hypotheses, declaration check output, source mapping and commands. If a gate fails, amend the affected contract/decision before implementing the full spec around it.

### 7.2 Proof gates

| ID | Obligation | Completion evidence |
|---|---|---|
| G1 | Meter accounting for Φ = execution gas + pending spill + committed spill | Public laws for every meter operation, with preconditions and exceptional paths |
| G2 | Whole-iteration progress | A continuing parent iteration decreases Φ by at least 1, including CALL/CREATE grant, child execution and resume. Prove returned child potential bounds and paid-stipend accounting; enumerate every continuing Amsterdam opcode before claiming whole-fork coverage |
| G3 | Structural termination | Lexicographic remaining depth/stage/frame-fuel measure; handlers cannot change context depth. Prove the depth bound and check before recursive descent; do not rely on saturating subtraction. Bound each helper separately. Account for frame-end and zero-cost terminal instructions |
| G4 | Checked-run soundness | Every completed checked run satisfies the semantic execution relation, including exception precedence |
| G5 | Completeness and fuel stability | Define the fuel-indexed frame loop or budget policy precisely; every semantic run appears at all sufficiently large fuel, and increasing fuel preserves a completed result with semantic gas held fixed |
| G6 | Computable sufficiency | An executable frame-budget policy eliminates fuel exhaustion for success, revert and EVM out-of-gas. Φ + 1 is a candidate, not an accepted bound |
| G7 | Internal-error freedom | `∀ input, ∃ out, runStatelessGuestChecked input = .ok out` at the guest integration stage. Slice proofs identify the remaining obligations; never infer this theorem merely from fuel sufficiency if other internal errors exist |
| S1 | State lifetimes | Current/original storage laws, write/clear precedence, snapshots, persistent observations, created-account handling, transient storage and child resume laws |
| S2 | Backend agreement and progress | `ModelsLookups consts ps σ` at the caller's BlockState record (Q57), with concrete full-model projection requiring F20 coherence; Models and ModelsRoot remain binary and ModelsCode remains unary at EthStateCommit's concrete Id interpretation. Code-hash/root agreement remain separate from progress under full well-formedness/data availability. Include an always-error provider for the success-only lookup predicate to show why agreement alone is insufficient |
| W1 | Witness traversal totality and acceptance | Empty-path leaf accepted; empty extension rejected; on-path cycle detection; diamond sharing accepted; off-path malformed descendants rejected eagerly; missing root versus unresolved child handled at the correct phase; Q55 pre-RLP occurrence queries/actual answers, raw/inline provenance, typed versus underlying first failures and no later query, Id-run consumer bridge and generic action/result-cache lifetime |

G4–G6 are separate results: existence of sufficient fuel does not give a computable bound, and a bound alone does not prove agreement with the semantic relation. No general gas-monotonicity theorem is required or expected: GAS and call forwarding can change behaviour when semantic gas changes.

### 7.3 Cases that must survive composition

- Charge exactly the remaining execution gas; fail one unit below a charge; spill from state gas, commit, restore, refund and repay. Exercise both spill pools, zero execution gas and signed per-frame refund-counter subtraction/merge without `Nat` saturation.
- CALL-family operations with and without value; EIP-150 rounding boundaries; stipend; zero requested gas; insufficient balance; maximum depth; child success, revert and exceptional halt. Cover CREATE/CREATE2 collision, init-code execution and code-deposit failure, including source-specific nonce effects and empty parent return data on successful creation.
- Storage clear after writes; write after clear; revert after clear; block-level clear with transaction override; original-value lookup for newly created accounts; persistent reads after child failure; transient storage reset between transactions.
- Memory expansion and overlapping copy, zero padding, and word endianness. Trace on/off must preserve outputs and buffer reuse.
- Guest phase precedence: malformed SSZ with header-limit excess (O1), empty headers (O3a), witness failure (O4), and multiple simultaneous failures. A checked internal error fails the test as a spec bug.

Use exact serialized regression inputs, not only random seeds. External oracles must support the tested fork and gas rules; clients with older semantics can compare only compatible behaviour.

### 7.4 Replacement gates

Capture baseline caller proof files before each exercise. Rebuild the same proof scripts after changing the component; retain the diff showing where definitions, contracts and proof scripts changed.

| Exercise | Permitted changes | Evidence |
|---|---|---|
| R1: memory | Memory implementation and proofs of its public laws | Memory-opcode caller proof scripts unchanged; composed execution agrees; expansion/copy benchmarks |
| R2: witness trie | Trie/backend implementation and proofs of the unchanged seam | Arithmetic/storage caller proof scripts unchanged; backend agreement and progress re-established; eager accept/reject cases unchanged |
| R3: gas-rule patch | Gas policy, affected instruction semantics/contracts and their proofs | Unrelated component/caller files unchanged; generic progress hypotheses either still discharged or explicitly revised. The patched schedule is an experiment, not a change to the pinned fork |
| R4: U256 representation | Word implementation and proofs of observer/operation laws | Opcode caller proof scripts unchanged; no stored-field or BitVec-instance dependency; opcode-loop benchmarks include conversions and allocation |

Each exercise uses small complete alternative implementations and ordinary equivalence proofs. `@[csimp]` is banned (D21); a faster implementation is adopted as a representation replacement proved against the same contract.

### 7.5 Composed cost checks

These are measurement gates, separate from the semantic proof gates. Include them in the slice report and label toy versus production coverage. They do not require implementing every candidate collection before the checks can be completed.

| ID | Workload | Completion evidence |
|---|---|---|
| C1 | Ownership, retained versions and cleanup | Repeated siblings from one parent; nested snapshots at depths 1, 32, 256 and the supported maximum; mixed success/revert, repeated slot writes and account-level clears. Report overlay sizes, key/payload costs, copied paths, allocated volume, peak live space and releases inside the timed lifetime. Any journal candidate includes inner success followed by outer revert and resize/undo boundaries |
| C2 | Hash-table assumptions | Benchmark concrete key hashing/bucket distributions and a lawful constant-hash stress case. Include DB/set construction and duplicate handling. Compare an ordered baseline; state expected versus worst-case costs. A synthetic stress case demonstrates a bound limitation, not a practical attack on Keccak |
| C3 | Log concatenation and final traversal | Left/right-skewed ropes, many sibling children, empty merges and mixed child success/revert. Check exact order/duplicates against a list model; demonstrate O(nodes + logs) flatten scaling without recursive list append or dependence on host call depth; include discard cleanup |
| C4 | Bulk operations and canonical output | Small-to-large and similarly sized overlay commits; repeated/duplicate keys and writes around clear markers; BAL sorted/distinct output from differing insertion orders. Record second-argument conflict bias for `union`, merge-function cost for `mergeWith`, and build/finalization scaling. Custom bulk algorithms are needed only if profiles justify them |

C3's supplied local LogRope component evidence is scoped by EthVmCore §4: 102
retained native process receipts, all 22 complete controls and measured full input-recipe equality,
explicit final-owner cleanup, actual generated-C loops and metric distributions.
Expanded occurrence counts include repeated shared empty/A-B subtrees; physical
cleanup follows actual ownership. This supplies bounded component evidence, not
universal host-stack/heap bounds or actual frame-incorporation cost coverage.

The component records distinguish source checks, analytical bounds and runtime measurements. A saved-root selection is O(1), while reclamation may traverse released objects. Benchmark methodology: no checksum inside the timed loop; include allocation, conversions and composition, and retain cleanup inside the measured workload. Report timings in the unit the workload was divided by (per frame versus per write), so that end-to-end workload averages are not mistaken for isolated operation costs.

### 7.6 Report and implementation handoff

Raw TxRevertible carrier evidence is scoped by EthState §3/§4/§5/§7; its §10 owns
all remaining tracker, lifetime, coupled-order and provider obligations. Complete
record retention and finite sibling controls discharge no S1/S2/W1 or C1–C4 gate.
The raw TxState/StateM handoff is likewise scoped there: exact three-field
assembly and transformer wiring do not repair X16(b) or discharge those gates.
EthVmCore §3/§4/§5/§7 separately scopes raw VmWorld/VmM wiring and its private
complete clients; initialization, liftState, actual error routing, tracker and
lifetime/fuel/guest/cost obligations remain open there.

Record the workload, hardware, toolchain, source commits, correctness gate, timing method, distributions, allocation/boxing evidence and tracing configuration. No earlier benchmark number settles D1 or D11.

For every implemented operation, record the source-to-Lean row that §4 above specifies: EELS source, Lean declaration, domain, effects, ordered failures, law or theorem, and a regression input or fixture area.

The handoff lists failed gates, uncovered instructions/input classes, conditional proof hypotheses and the corresponding decisions. Adopt only contracts validated by the evidence. Full EEST execution, whole-guest adequacy and cryptographic theorems remain separate deliverables; meeting the criteria above proves none of them.
