# Informal specification review and implementation gates

*Status: live implementation gates; dated findings retained. Date: 2026-10-06.*

**Structure.** §1–§2 are a dated record of the review of 2026-09-28; do not update them except to mark supersession. §3–§5 are **live**: the per-module gates and the implementation contract, kept current. §6 is a dated readiness assessment (2026-10-02); replace it, rather than patching it, when readiness changes. §7 (acceptance criteria) is **live**.

Review of 2026-09-28; exact reference commit `e1a316a06fc3d3e0a5da36fdc78580811e9d8a36` (`tests-zkevm@v21.0.0`). All 23 module documents now contain conditional correctness arguments in §7. [COMPOSITION](COMPOSITION.md) connects their premises, common types, error adapters and the complete byte-level guest. **The design remains a draft requiring the gates below.** Owning every reference declaration does not mean specifying every operation completely or proving it correct.

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
python3 scripts/gen_eels_inventory.py /path/to/eels --check
python3 scripts/gen_reference_records.py /path/to/eels --check
```

The fresh inventory comparison covers 717 nonexternal declarations and 304 external-use entries across 74 files. The field catalogue records source order/annotations and inherited bases. It is not a generated Lean implementation or a complete type-mapping proof. The five examples are regression evidence, not a complete conformance run. The fixture archive was not re-executed during this review; its existing verified counts remain in `reference.toml`.

The local validation completed successfully: `check_spec.py` (23 libraries, 717/717 ownership coverage), 16 mutation regression tests in `test_spec_checks.py`, generated-gap freshness, source inventory/record comparison, all five counterexamples, core dependency boundaries, protocol consistency, architecture diagram freshness and `git diff --check`. CI is configured to run the document guards/regressions; this review does not claim a remote CI run or a Lean semantic implementation test.

## 3. Per-module gates

Every row is required before claiming that module's corresponding refinement, in addition to its existing §10 gaps. A gate may be completed incrementally for a precisely bounded public API, with uncompleted operations labelled explicitly.

| Module | Remaining design/proof work |
|---|---|
| EthBase | Q54’s functional Bytes order/export provider, public-only clients and source/compiled ordering cases are supplied by EthBase §3; actual consumer/replacement/C1–C4 costs remain open. Q51 table-support functional seam is supplied by EthBase §3; concrete NodeDB/adversarial-distribution cost evidence and fixed-byte representation gates remain open. Enumerate checked integer operations and failure sites; specify Envelope's role; formalise Taylor descent and resolve DISC-002 practical feasibility. |
| EthHash | Prove padding/round/byte correspondence; fix RIPEMD capability policy (DISC-005); monad-parametric interfaces with `Id` specialisation and lift instances (D5; DECISIONS F1, F15). |
| EthField | Certify primality/tower irreducibility; qualify sqrt choices and encoding widths; finish public equations; complete the Montgomery backend's `sub`/`neg` and `W12` laws, observers and inversion (D6). |
| EthCurve | Fix general-a versus a=0 formulas; prove exact SSWU/sign/once-clearing adapters; specify recovery-compatible domain and dependency rejection behaviour. |
| EthPairing | Pin literal default Miller algorithms; establish concrete bilinearity/nondegeneracy before convention replacement; separate KZG completeness from binding. |
| EthCodec | Instantiate every schema; prove both inverse directions and strict acceptance; establish rootable/encodable domains, progressive lengths and host-depth policy. |
| EthState | Supplied component contracts are owned by EthState §3/§7: Account/emptyAccount, internal WriteOrder, raw MathState observers/structural WF, raw BlockDiff, raw mathematical application and the raw PreState carrier. Arbitrary supplied functions have ordinary record laws without a Monad premise; public-only generic clients and complete guard/native callbacks preserve every input/result/error tag and payload. Coarse WitnessItem/WitnessError values add no diagnostic adapter or EELS Protocol-body execution; carrier equality adds no action-effect interpretation. Source correspondence retains typed finite nonaliasing dictionaries, None/zero defaults, pinned fixed-width/Uint/U256 interpretation and coherent F20 constants, without local hashing. MathState raw equality retains whole optional inner maps and every code hash; structural WF supplies no code authenticity/completeness, and fixed-constants observer equality need not imply raw equality. Raw diff fields and application supply no reachable WF, hash authenticity, history or clear-order guarantee. Define Reachable; discharge account-read/write and balance preconditions at callers; implement/prove model mutation, actual providers/ModelsLookups/constants context, StateError/witness diagnostic refinement, tracker effects/errors, coupled ordered-write/clear/restore/incorporation/extraction and state lifetimes. The EELS default-empty BlockDiff convenience constructor remains deferred. S1/S2 and composed C1/C4 remain open; these contracts supply no whole-State readiness result. |
| EthCommit | Complete whole-source C7–C8 constructor/root refinement and C14 ordered diagnostic dispatch, WitnessError/O4 adapters and W1; compose Q53's supplied generic storage/safety, lawful byte-key, pure unsecured preparation and typed-root laws (EthCommit §3); implement/prove concrete encoding/key bridges and consumer instances with caller F20 coherence, exact source equality/dispatch and schema/assembled Encodable/host premises. Distinguish canonicality from lookup equivalence; implement/prove Q55's generic pre-RLP occurrence acquisition, raw/inline cache provenance, explicit Id-run agreement and failure forwarding; any B15 memo refinement additionally covers effects/path/first error; specify secure-key collision folding, source history and order-sensitive collapse; validate table and composed resource bounds. |
| EthStateCommit | Implement Q53 U256 validity/nonempty laws independently of zero deletion and contextual Account integration, without a bare Account instance or secured-policy claim. Finish code-authenticity/root clauses, lenient leaf cases and computable collision extraction including full-state code. |
| EthStateFull | Require CodeComplete for progress; prove applyChanges preservation and raw-helper WF premises; finish full-root folding model. |
| EthStateWitness | Prove reachable cache history, ordered update phases and storage-root-only rewrite commutation; establish eager availability requirements and Q55 action/result-cache ownership, lifetime, first failures and Id thunk adaptation; settle the storage-trie memo (F6) and clear order (F7). |
| EthVmCore | Complete GasCosts/error/record fields; prove gas preconditions and refund sign; align memory allocation with charging and compiled container costs. |
| EthVmInstructions | Expand all grouped handler claims into guard/effect/error equations; typecheck requests/resume and prove per-opcode source refinement. |
| EthPrecompiles | Prove every adapter and returned-meter law; thread pricing config consistently; verify multi-error priority and all accepted infinity/subgroup cases. |
| EthVmRunner | Define Exec/measure and TerminationReady; prove complete call/create progress and all four fuel guarantees; verify every InternalError path; choose how `ChildSettled` is produced (F11). |
| EthBlock | Implement/prove Q53's actual Bytes/legacy/typed/withdrawal encoding bridges and dense safe root-input composition using lawful byte keys and context empty root. Implement and prove F20 acquisition/threading and context coherence; expand every record/codec and admission arithmetic failure; prove BAL/index/receipt ordering, unchecked-system fault propagation and backend simulation. |
| EthFork | Compare complete parameter tables with source; construct coherent config/table; specialise behavioural termination proof; verify previous-header compatibility. |
| EthStateless | Implement and prove F20 acquisition/threading and context coherence; complete phase-to-outcome projection and input-to-context WF/rootability; typecheck subtype/header/request adapters; prove exact 43-byte encoding; prove O2 unreachable on decoded values. |
| EthConformance | Co-ordinate closing X1 in the failure ledger (maintained outside this repository); implement exact guest-record/label/replay handling, locked environment and dependent-transition policy. |
| EthFieldMathlib | Build public-operation bridges without circular typeclass premises; certify all primes/extensions and sqrt lemmas. |
| EthCurveMathlib | Prove valid-point operation bridges, group/subgroup orders, exact map/decompression and qualified ECDSA laws. |
| EthPairingMathlib | Supply concrete pairing laws/group/setup premises; complete convention-independence and honest-opening proofs. |
| EthSecurity | Consume bounded local ToVCVio RLP/reference laws without inferring whole-map binding; establish nonvacuous directional simulation, whole-trie extractors, oracle closure and budgets; keep chain anchoring and cryptographic security assumptions explicit. |
| ToVCVio | Certified RLP facade, child-reference threshold/effect laws, explicit query-morphism transport, local same-h raw-pair extraction and same-query InternalNode adapter are supplied (own guidance §7). Faithful Patricia shell/assembly/preimage injection, separate finite resolved canonical shape facts and a pure nonempty safe prepared-image bridge are supplied (own guidance §§5/7); total finite resolved lookup, packed/List join equality and one-step prefix lookup/canonical preservation and complete-key support for actual canonical trees/two distinct keys for canonical branches are also supplied, together with canonical resolved-tree observational extensionality under both actual canonicality premises and all-finite full-value/byte observations; ordinary Prop finite resolved-map existence for actual maps satisfying `NonemptyValues`, including the empty map, with complete optional bytes at every finite key is also supplied (own guidance §§5/7); conditional structural node/reference Prop derivations also supply admissibility, exact presence occupancy and canonical-to-local-shell laws under the complete present-shell certificate and fixed pure-h premises (own guidance §§5/7); top Fits remains separate from bare node derivation, while logical C/D width and exact inhabitation support is supplied by PatriciaRlpDomain (Q56; own guidance §§5/7). All complete domain/action premises remain explicit. Installed VCV-io pin/QueryHom adapter/import audit, a public resolved-map uniqueness corollary, executable C7/C6 reference/effect realization, C8 hashing/source agreement, recursive binding, witness agreement, whole-kernel coupling and consumer/cost gates remain open. |

## 4. Agent implementation contract

Read CONTRACT and `reference.toml`, the current decision statuses and DECISIONS dispositions, COMPOSITION, this review, the module's §2/§5/§7/§8/§10 and its providers' laws, the interface findings listed on the module's navigation line (DECISIONS §3), and the module's failure-ledger entries (X1) before implementing. Grouped inventory claims assign responsibility; expand them into a local declaration checklist, recording inputs, result/error types, ordered guards, observations, state effects and source/test references. Resolve `…`, bare structures, inferred/dead branches and undefined error types *in the Lean code* before treating an interface as frozen. The markdown specs are informal (`CONTRIBUTING.md` §5.4) and are not expected to reach that level themselves; where the spec is ambiguous rather than merely informal, raise it as a spec question instead of guessing.

Use these three independent acceptance checks:

- **Reference:** ordered successful and failing behaviour matches the pinned source/dependencies, including the phase that catches each failure.
- **Component:** representation invariant and public model equations hold on the stated domain; no caller unfolds a replaceable container.
- **Composition:** every consumed premise is produced by a provider or established by a caller, and every returned effect/error fits the shared adapters. Cyclic proofs cannot discharge each other's premises.

At module completion record which obligations are actually discharged and how. Tests may demonstrate counterexamples or confidence; they cannot be relabelled as a universal proof. Keep the Mathlib and security packages' dependencies directed outward from the core. Use the memory, trie and gas replacement exercises to check that clients depend on public equations; include order/caches/failure observations in the trie exercise.

For each implemented EELS operation, keep a reviewable source-to-Lean row in the owning module's §3 or in the implementation change: exact EELS `file:line` and dependency version if relevant; Lean declaration and public type; accepted-input/precondition domain; success value and state effects; ordered failure conditions and their first consuming handler/O-row; model equation or theorem; and at least one deterministic case or named fixture area. Grouped inventory claims in §3 establish ownership only. Mark an item **unimplemented**, **implemented but unproved**, or **discharged**, and name any caller that must establish a precondition. A passing fixture is evidence for the specific path it executes, not for every branch of the claimed operation.

Internal first-write order support is specified in
[EthState §3/§7.5](modules/EthState.md#3-eels-source-map).

Q53's [EthCommit](modules/EthCommit.md#3-eels-source-map) and
[EthBlock](modules/EthBlock.md#3-eels-source-map) rows describe scoped seams.
Generic C11 storage/safety, the Q53 byte-key contract and pure unsecured preparation
and typed root composition are supplied by EthCommit §3; concrete encoding/key adapters and consumer
seams remain **unimplemented**. Before any implementation claim, validate arbitrary supplied defaults, unsafe
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
reassess material limitations under D18/D25. A conditional future `KeyBytes Bytes`
adapter uses the public inverse/order/core-list export laws; it supplies no encoder,
schema, source equality, F20, host, secure-policy or guest-readiness result.

Q55's [EthCommit](modules/EthCommit.md#5-interface) complete decoder signatures
are clarified **unimplemented** targets. Future ordinary laws/public clients must
cover local empty/missing/stub paths with zero queries, complete-preimage threshold
queries before whole RLP, verbatim arbitrary answers, prior-state retention,
underlying query failures without later parsing/query, typed first-error ordering,
raw HP and exact inline parsed-subterm provenance/`Encodable`, long alias-keyed
entries, short authentic entries, repeated siblings and current-path cycles.
Use recording/stateful/failing instances and explicit `LawfulMonad` premises for
sequencing transformations; concrete source comparisons require coherent F20,
RLP and finite acyclic pinned-host compatibility. Prove the concrete Id-run
consumer/error-adapter bridge and generic action/result-cache lifetime separately.
The no-completed-memo baseline supplies no production cost exception or whole
W1/S2/R2/C1–C4 gate; no implemented source-to-Lean row is added by this guidance.

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

## 5. Blocking obligations and proposed ownership

X1 is coordinated by EthConformance tooling; each module owns its explicit and implicit exception sites, and EthStateless owns phase projection. X6 belongs to Core/Instructions/Runner with the fuel-adequacy investigation ([§7](REVIEW.md#7-acceptance-criteria-proof-gates-composition-cases-replacement-and-cost-checks) G2–G7) as its integration gate. X10 is jointly discharged by State's reachable trace and Witness/Commit's ordered update laws. X7 belongs to Security/StateCommit, with full-state progress and oracle coupling supplied explicitly. Exact schemas belong to their record owner and Codec instances. These are assignments of review work, not assertions that the work is finished.

The highest-risk uncompleted items are closing the failure ledger's unresolved sites (X1), the complete CALL/CREATE gas proof (the fuel-adequacy investigation, §7 G2–G7), code-authenticity/oracle coupling, lenient witness root agreement (the witness/full-state agreement prototype, §7 S2), and the open interface items (X15). Until these are resolved, the repository is suitable for targeted validation and scaffolding, not an unconditional claim of end-to-end soundness.

## 6. Implementation-readiness assessment (2026-10-02)

**Implemented scope.** [EthBase §3](modules/EthBase.md#3-eels-source-map) owns the
implemented declarations, source correspondence, public proofs and operation-value
regressions. Its §10 owns missing APIs and derived laws.
[EthHash §3](modules/EthHash.md#3-eels-source-map) owns the reference Keccak-f[1600]
hash providers, their public model/byte laws, primary KATs and finite differential
evidence; its §10 owns remaining hash APIs and correspondence.
[EthCodec §3](modules/EthCodec.md#3-eels-source-map) owns its implemented
operations, source correspondence and conformance evidence; §7 owns public-law
domains, and §10 owns remaining APIs and laws.
[EthCommit §3/§7](modules/EthCommit.md#3-eels-source-map) owns implemented path,
Q49 provider, internal-node, C12 raw database and Q53 generic storage/preparation/root APIs, public-law domains and
source/conformance evidence.
Q50 supplies actual finite-map domain/ending-key laws and private extension/child
strict sum-descent support and private longest shared-prefix selection with
ordinary domain/maximality/representative laws. Private bounded branch support
adds full-key partition/ending and ordered supplied-callback/C6 sequencing laws
with their explicit lawful-monad premises (EthCommit §3). Recursive C7 adds actual
full-map construction, public dispatch/extensionality and private every-node selector
independence. C8 adds the total local root, supplied-empty bypass and ordinary
whole-action reference/fused equality with explicit lawful sequencing. Its §10 owns
remaining witness/trie APIs and trie/resource obligations. Other semantic components
remain scaffolding.
[COMPOSITION](COMPOSITION.md) records supplied component premises; no end-to-end
theorem is proved.
[EthConformance §3](modules/EthConformance.md#3-eels-source-map) owns the fixture
extraction and authentication tooling.

**Evaluation.** Primitive guards and caller proofs compile through `EthConformance`.
Path/node guards and authenticated differential drivers are owned by [EthCommit
§3](modules/EthCommit.md#3-eels-source-map). Typed-Bytes/Python sequence support
checks supply provider evidence; finite full-output native correctness observations
supply no throughput or C1–C4 claim. Q49 supplies provider support; Q50 discharges
domain/strict-descent support over actual finite maps, including all sixteen
empty/nonempty child cases. Private callback-based branch formation adds bounded
ordered C6 encoding support. Recursive C7 supplies complete node/query observations
and private every-node selector independence, without a parent query at the return
(EthCommit §3). C8 supplies the total local wrapper and full-byte/effect reference
equality, with complete final-query and original-error observations. Canonicality,
whole-source refinement and aggregate copy/comparison costs remain open.
Base differential drivers compare public operation values with the pinned source.
Q51 table-support vectors compare complete UInt64/native/source values with independent
nonprotocol Python arithmetic and actual Std map observations (EthBase §3); this
provides no EELS cryptographic, root or C1–C4 claim.
The C12 source/complete-map/native slice is owned by EthCommit §3: authentication
at Id and input-order query/overwrite laws are supplied for future consumers.
Eager decoding, cache/root agreement, generic oracle coupling and table resource
gates remain open; functional large/sibling runs are not cost evidence.
[EthHash §3](modules/EthHash.md#3-eels-source-map) owns the bounded permutation,
compression and digest drivers, provider correspondence and evidence limits.
Production F20 entry seams, consumer coherence and D5 generic coupling remain open.
The packed candidate retains state across blocks and proves endpoint equality;
D4/resource/DEBT evaluation remains open.
Extraction guards, host regressions and authenticated content comparison validate
fixture tooling as specified by EthConformance §3–§4.
They establish local evidence, without implementing Lean opcode effects. Guest,
full-state and engine runners remain absent; no EEST guest records execute in Lean.
The exact pin and dependencies are in `reference.toml`; the generated inventory,
record catalogue and failure ledger support further implementation.

**Completion gates.** Lower-layer work can proceed against each module's contracts
and §3 gates. Runner, block and guest completion still require fuel adequacy (G2–G7),
witness/full-state agreement (S2), and X1, X6, X7 and X15. Unresolved domains, error
priority, schemas and caller premises must remain explicit. X5 records fixture
coverage limits; passing document checks or a prototype does not close these gates.

**Performance and proof limits.** The C1–C4 workload and measurement gates and R4
representation exercise remain open. No whole-guest native-baseline comparison or
target-zkVM cost result supports a speed claim. The specification arguments and
literature references do not supply concrete MPT, pairing, imported-crypto or
whole-guest resource proofs (X7, X9, X12). Decision statuses are owned by DECISIONS;
implementation debt is owned by DEBT.

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
| S2 | Backend agreement and progress | `ModelsLookups`, code-hash agreement and root agreement separately from successful operations under well-formedness/data availability. Include an always-error provider to show why agreement alone is insufficient |
| W1 | Witness traversal totality and acceptance | Empty-path leaf accepted; empty extension rejected; on-path cycle detection; diamond sharing accepted; off-path malformed descendants rejected eagerly; missing root versus unresolved child handled at the correct phase; Q55 pre-RLP occurrence queries/actual answers, raw/inline provenance, typed versus underlying first failures and no later query, Id-run consumer bridge and generic action/result-cache lifetime |

G4–G6 are separate results: existence of sufficient fuel does not give a computable bound, and a bound alone does not prove agreement with the semantic relation. No general gas-monotonicity theorem is required or expected: GAS and call forwarding can change behaviour when semantic gas changes.

### 7.3 Cases that must survive composition

- Charge exactly the remaining execution gas; fail one unit below a charge; spill from state gas, commit, restore, refund and repay. Exercise both spill pools, zero execution gas and signed per-frame refund-counter subtraction/merge without `Nat` saturation.
- CALL-family operations with and without value; EIP-150 rounding boundaries; stipend; zero requested gas; insufficient balance; maximum depth; child success, revert and exceptional halt. Cover CREATE/CREATE2 collision, init-code execution and code-deposit failure, including source-specific nonce effects and empty parent return data on successful creation.
- Storage clear after writes; write after clear; revert after clear; block-level clear with transaction override; original-value lookup for newly created accounts; persistent reads after child failure; transient storage reset between transactions.
- Memory expansion and overlapping copy, zero padding, and word endianness. Trace on/off must preserve outputs and buffer reuse.
- Guest phase precedence: malformed SSZ with header-limit excess (O1), empty headers (O3a), invalid hint (O5), witness failure (O4), and multiple simultaneous failures. A checked internal error fails the test as a spec bug.

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

The component records distinguish source checks, analytical bounds and runtime measurements. A saved-root selection is O(1), while reclamation may traverse released objects. Benchmark methodology: no checksum inside the timed loop; include allocation, conversions and composition, and retain cleanup inside the measured workload. Report timings in the unit the workload was divided by (per frame versus per write), so that end-to-end workload averages are not mistaken for isolated operation costs.

### 7.6 Report and implementation handoff

Record the workload, hardware, toolchain, source commits, correctness gate, timing method, distributions, allocation/boxing evidence and tracing configuration. No earlier benchmark number settles D1 or D11.

For every implemented operation, record the source-to-Lean row that §4 above specifies: EELS source, Lean declaration, domain, effects, ordered failures, law or theorem, and a regression input or fixture area.

The handoff lists failed gates, uncovered instructions/input classes, conditional proof hypotheses and the corresponding decisions. Adopt only contracts validated by the evidence. Full EEST execution, whole-guest adequacy and cryptographic theorems remain separate deliverables; meeting the criteria above proves none of them.
