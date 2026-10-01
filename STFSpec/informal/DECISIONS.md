# Decisions

*Status: current. Date: 2026-09-30. This is the single register of design decisions and question dispositions: statuses are recorded only here. Other documents cite entries by ID (P1, D5, B8, F7, Q20) and never restate them.*

| Status | Meaning |
|---|---|
| **accepted** | settled; revisit only with the named evidence |
| **provisional** | a working choice, awaiting the named evidence |
| **adopted** | a working resolution that the spec guidance follows (§2, §3) |
| **open** | an owned obligation; it blocks only the work it affects |
| **deferred** | deliberately not decided yet; it does not block current work |

A documented proposal or an implemented guard does not by itself make a decision accepted. [ARCHITECTURE](ARCHITECTURE.md) §11 lists the options that were considered for each D decision.

## 1. Decisions (P: project, D: design)

| # | Decision | Status | Current position | Evidence required to settle or revisit |
|---|---|---|---|---|
| P1 | Protocol pin | **accepted** | `tests-zkevm@v21.0.0` @e1a316a0, fixture sha256 verified (`reference.toml`) | a new canonical release; bump spec and fixtures together |
| P2 | Authority order | **accepted** | fixtures, then pinned EELS source, then the discrepancy policy ([CONTRACT](CONTRACT.md) §6) | — |
| P3 | Toolchain | **accepted** | Lean v4.34.0 | downstream bump needs |
| P4 | Package layout and checks | **accepted** (2026-09-28) | the core package (the repository root; `require`s nothing), `STFSpecMathlib/` (Mathlib bridges) and `STFSpecSecurity/` (security; VCV-io is added here only), which shares the bridge package's dependency checkouts. CI (`.github/workflows/ci.yml`): **core job**: `lake build --wfail`, `check_boundaries.py`, `check_decls.sh core`, the checkers' regression tests, the pinned-reference check and its regressions (`check_reference.py`, `test_reference_checks.py`), the diagram check, the spec checks (`check_spec.py`, `test_spec_checks.py`), gap-register freshness and `lake build EthConformance --wfail`; **bridge and security job**: `lake build --wfail` and `check_decls.sh mathlib`/`security` (sorry reported); **weekly job**: download the fixture archive and verify its sha256 and record counts (the full-corpus conformance run is added with the fixture runner). Benchmark packages are added, with correctness gates, when there is something to measure | — |
| P5 | Licence | **accepted** (2026-09-28) | Apache-2.0 OR MIT (dual); the consumers are MIT, the Lean dependencies Apache-2.0 | — |
| P6 | Relation to SpecRef | **accepted** (2026-09-28) | written from scratch; SpecRef is replaced, not moved. Equivalence with SpecRef is not a goal. Consumers (evm-asm, stateless-pancaketh) retarget in their own repositories | — |
| D1 | U256 stored representation | provisional | a `structure U256` wrapping `BitVec 256`, behind stable `toBitVec`/`toNat` (and `toInt`) observers and operation laws; a limb representation preserves those laws | a benchmark through the proof interface inside an opcode loop; proof cost; replacement exercise R4 preserves downstream proof scripts |
| D2 | Address/hash representation | provisional | distinct fixed-width `structure`s (`Address`, `Hash32`, `FixedBytes n`; `Bytes32 := FixedBytes 32`), each wrapping `BitVec (8n)` behind byte observers; `compare` is hand-written, lawful, and equals big-endian lexicographic byte order (EthBase §5–§6) | map-key `compare` cost and byte-conversion cost at codec boundaries |
| D3 | Forks | **accepted** | parameter records near their semantics, named fork modules for changed behaviour, an explicit composition module (`EthFork`); Amsterdam only | executing pre-Amsterdam (BPO2) blocks, for example the transition fixtures (Q8) |
| D4 | Hash implementations | provisional | a legible reference plus a proved unrolled fast path | re-measurement under the corrected benchmark methodology (no checksum inside the timed loop; include allocation, conversions and composition); a proof that fast ≡ reference; local reference allocation exception: [DEBT-HASH-REFERENCE](DEBT.md#debt-hash-reference--boxed-reference-rounds) |
| D5 | Keccak abstraction scope | **provisional** (B10) | **every** keccak goes through `KeccakQuery`, including: the trie and witness DB, the code DB, the header chain, the block-hash check, the transaction/withdrawal roots, `validate_header`'s parent hash, code preimages and newly installed code hashes, the KECCAK256 opcode, CREATE/CREATE2 addresses, ECRECOVER, the EIP-7708 transfer topic, and the keccak-derived constants. **Interfaces:** everything that hashes is parametric in `{m} [Monad m] [KeccakQuery m]`. Types that only carry a hashing pre-state or precompile (`PreState m`, `StateM m`, `VmWorld m`/`VmM m`, `PrecompileFn m := Bytes → GasMeter → m PrecompileResult`) take `{m} [Monad m]` and never mention the class; `BlockM m := CheckedT BlockError m` (EthBlock). Public entry points specialise to `m := Id`, where the `KeccakQuery Id` instance is concrete keccak256. The keccak-derived constants are a `HashConsts` record (`EthBase`), queried by `HashConsts.query` (`EthHash`) at the caller-owned boundary specified by F20 (§3). `NodeDB.Authentic`/`CodeDB.Authentic` are separate predicates; `KeccakQuery` has `ExceptT`/`StateT` lift instances. `KeccakQuery` itself stays in `EthHash`. `Models` is stated at `PreState Id`. Evidence: F1–F4, F15, F18 (§3) | a narrower scope only if the witness/full-state agreement prototype shows it is closed; the oracle coupling for `Models` at generic `m` is open; request-root binding separately uses SSZ/SHA-256 |
| D6 | Field arithmetic source | provisional | our own carry-preserving CIOS Montgomery backend, derived from CompPoly's zero-import `…Defs` and vendored with attribution (needs only `p < R`; `Wide8` for every pinned modulus below 2^256, `W12` for BLS12-381 q), or the same fix upstreamed to CompPoly. Width is settled by measurement (the `Nat` reference is 3–6.5× slower than `Wide8`; `Wide8` is 20–35× slower than native ecrecover); the source is not | **tracked upstream (2026-09-29):** CompPoly PR [#389](https://github.com/Verified-zkEVM/CompPoly/pull/389) (draft) makes the same carry fix for the eight-limb stack, covering `add`, CIOS `condSubWide`, the divstep inverse and the `modulus_lt` class field, and adds secp256k1 instances. Still to upstream after #389: P-256 instances and the 12-limb `W12` variant for BLS12-381 q. Also open: whether the core vendors the Defs or uses a Mathlib-free CompPoly runtime package (D26); the `sub`/`neg` and `W12` laws, observers and inversion |
| D7 | Curve coordinates | provisional | homogeneous projective initially (as `py_ecc`); Jacobian only as a later representation replacement (D25) | pairing and MSM benchmarks |
| D8 | Missing witness data | **accepted** | `Except WitnessError (Option α)`, kept separate from authenticated absence | — |
| D9 | `PreState` shape | **accepted** (revised by B2 and D5) | explicit operations; `ModelsLookups` in `EthState`, with code-hash and root clauses in `EthStateCommit`. `getCode : Hash32 → m (Except WitnessError ByteArray)`: missing code is an error (B2). The record is `PreState m` (D5). Backend progress/data availability is proved separately from agreement | revisit only if later work shows proof-ergonomics problems |
| D10 | Full-state instance | **accepted** | included (`blockchain_tests`, fuzzing) | — |
| D11 | Memory type | provisional | `ByteArray` | memory-expansion measurements under the corrected benchmark methodology |
| D12 | Precompile deliverables | **accepted** (2026-09-28) | all three in scope: (i) executable behaviour, (ii) mathematical correctness, (iii) cryptographic security; tracked and scheduled separately | — |
| D13 | Call-frame structure | provisional | recursion, EELS-shaped; remaining depth/stage/per-frame fuel, with a candidate gas potential | the fuel-adequacy investigation ([REVIEW §7](REVIEW.md#7-acceptance-criteria-proof-gates-composition-cases-replacement-and-cost-checks) G2–G7): whole CALL/CREATE progress, four fuel guarantees, stack depth and speed |
| D14 | Failure semantics | **accepted: structure and guidelines** (2026-09-28) | three channels (frame exits; protocol rejection; internal failure); behaviour of the first consuming reference handler preserved; each property checked at its reference-defined phase, with evidence carried downstream; internal errors always exposed by the checked runner, and the public fallback allowed only as a branch proved unreachable (CONTRACT O11). Further guidelines: make illegal states unrepresentable where cheap; loud failures are still total values (`InternalError`), never `panic!`/`get!`; diagnostic context in error constructors never influences the output bytes; no catch-all: the reference's catch-all handlers become an explicit mapping of named constructors, and anything unclassified is a gap (after Duffy, *The Error Model*, 2016; King, *Parse, don't validate*, 2019). Accepting approves **no** deviation from the reference. **O12's host-resource interpretation remains explicitly unresolved** (DISC-001) | O12 resolution (DISC-001, DISC-006). X1 is tracked by the failure ledger (maintained outside this repository; counts provisional); error types freeze per module once its failure sites close (B14). O13 is recorded in §3 |
| D15 | BLS12-381/KZG reference | provisional | ethereum/cryptography-specs as the legible reference | packaging (cryptography-specs requires Mathlib at the package level, the same core-dependency question as D6/D26); a toolchain bump from v4.29.1; the Q45 blockers (`partial def`, `get!`, `native_decide`) |
| D16 | State semantics separate from commitments | **accepted** | `EthState` independent of `EthCommit`; full and witness backends | replacement exercise 2 |
| D17 | Opcode stepping separate from call execution | **accepted** | `StepResult` with child requests; only the runner is recursive; import rule enforced | replacement exercise 1 and the fuel-adequacy investigation (REVIEW §7 G2–G7) |
| D18 | Implementation policy | **accepted** (2026-09-28) | implementations are **final**: each satisfies a finite, named set of required properties in its contract (semantics, totality, failure precedence, representation invariants, composition laws, applicable resource requirements), with unproved ones listed as open obligations. Data structures are **performance-appropriate** for the relevant operation costs and persistence requirements. Justified exceptions (legibility, or drastic proof-friendliness) are recorded in [`DEBT.md`](DEBT.md) with the expected workload, complexity, measured limitation, reason and replacement criterion. Debt never adds rejection limits or semantic shortcuts. Modularity (D25) keeps later performance work a contained representation replacement | revisit per debt entry |
| D19 | Witness decoding strategy | **accepted** | eager, as the reference (a lazy walk would accept witnesses it rejects); internal laziness only with a proof of the same accept/reject result | — |
| D20 | State/commitment integration | **accepted** | `EthStateCommit` owns the encodings, `mathStateRoot`, the root clause of `Models` and code-hash agreement; `EthCommit` is generic over bytes | replacement exercise 2 |
| D21 | `@[csimp]` policy | **accepted** (2026-09-28) | **no additional trust assumptions**: judged on the resulting proof dependencies whatever the tactic, so `native_decide`, `bv_decide` and `decide +native` are rejected (each verified to add a native axiom). Separately, as design rules for executable correspondence and transparency (not because they are logically unsound): no `@[csimp]`, `implemented_by`, `extern`, `unsafe`, `partial` or `opaque`. Bit-vector reasoning uses Std lemmas, extensionality, `simp`/`omega`, and plain `decide` for small concrete checks. Enforced by `check-decls`, with fixtures | — |
| D22 | Revertible-state representation | **accepted** | persistent worst-case trees (`Std.TreeMap`/`ExtTreeMap`); a HashMap + undo journal only as a later, measured representation replacement under the semi-persistence discipline (Conchon & Filliâtre 2008), never a `@[csimp]` | measurement against geth/revm journaling ([REVIEW §7](REVIEW.md#7-acceptance-criteria-proof-gates-composition-cases-replacement-and-cost-checks) C1) |
| D23 | Observation sets and `created_accounts` | **accepted** | threaded linearly *outside* the snapshotted component (never reverted within a transaction) | — |
| D24 | Logs | **accepted** | strict rope with O(1) append | — |
| D25 | Contract style | **accepted** | model-based: invariant plus commuting equations per operation; laws derived once on the model; an abstraction relation for partial structures (the trie) | replacement exercises 1, 2 and 4 |
| D26 | secp256k1 recovery for transaction senders and EIP-7702 authorities | **accepted** (2026-09-28) | direct `EthCurve` dependency of `EthVmRunner`, keeping the instruction/runner boundary. **Governing constraint: pure Lean**, with the trusted baseline documented in CONTRIBUTING §4 (Lean kernel and standard axioms, compiler, Lean-core runtime primitives). **Before adopting any third-party dependency,** `check-decls` must be extended to inspect the reachable third-party implementations (`extern`, `implemented_by`, `partial`, `opaque`) and relevant compiler replacements, not just our own module roots; axioms are already followed transitively. Executable (core) dependencies and those of the Mathlib and security packages are chosen separately. Known: cryptography-specs (at `09deaff`) uses `native_decide`, so it is reference-only as it stands. CompPoly at `96e4b3d` has no `native_decide`/`bv_decide` tactic use in its sources (text scan, 2026-09-29). Confirm with `#print axioms` at whichever commit is reused | — |
| D27 | `Log` and `BlockOutput` placement | **accepted** (2026-09-28) | `Log` in `EthVmCore`, `BlockOutput` in `EthBlock`. **Guideline:** one owner for each public type, semantic operation and protocol constant, and consumers reuse it (enforced by `contracts.toml` + `check_spec.py`). A component may deliberately hold **both** a mathematical model or legible reference **and** an executable representation, connected by refinement: "no duplicates" forbids competing sources of truth, not these distinct roles | — |

## 2. Working resolutions of interface questions (B)

Adopted provisionally on 2026-09-28; they are the working resolutions for implementation, re-evaluated whenever later work gives reason to. Each **condition** is part of the resolution: an implementation that satisfies the headline but not the condition does not satisfy it. The Q column gives the original question numbers; the NEW-… names are those used in the spec guidance documents' §9.

| B | Q | Question | Resolution |
|---|---|---|---|
| B1 | Q29, Q36 | NEW-STATE-1, NEW-WIT-1: write order | **Preserve** account, storage-address and slot first-write orders in `BlockDiff`. Erase an ordering only after proving that the relevant operations commute, *including failures*. **Condition:** preserve the orders together with the witness provenance they depend on; equal successful roots alone do not make two orderings interchangeable, because failure behaviour and observations must match too. The clear order is F7 (open, §3). |
| B2 | Q30 | NEW-STATE-2: `getCode` type | `Except WitnessError Bytes`: missing code is a failure, and empty code is a successful value. A small, explicit revision to **D9**. **Condition:** propagate through every provider and consumer: `EthState`, both backends, `EthStateCommit`, ARCHITECTURE and COMPOSITION. |
| B3 | Q32, Q34 | NEW-COMMIT-1 `Ref`; NEW-COMMIT-3 non-canonical encodings | Hide `Ref` behind the trie API. `Option Node` is viable only if it keeps enough encoding and reference provenance to reproduce the reference on non-canonical witnesses (DISC-003); demonstrate that before adopting it. **Condition:** equal successful roots do not make two node representations interchangeable; failure behaviour and observations on non-canonical witnesses must match too. |
| B4 | Q37 | NEW-WIT-2: decode triggers | Do **not** require construction-time decoding of every storage trie; pure functions can decode on demand. Precomputation is acceptable only after proving that errors match the reference's triggers, and measuring the extra work. **Condition:** Decode a root **when the reference triggers it, then eagerly decode its reachable nodes** (D19). "On demand" must never become lazy, path-only validation. |
| B5 | Q21, Q22 | SSZ decoder; SSZ value representation | A strict canonical decoder (`decode b = ok v → encode v = b`); `SszValue` plus `WellTyped`, with typed schema adapters and **both** inverse laws, behind the `EthCodec` boundary. **Reference:** [ethereum/ssz-specs `lean/`](https://github.com/ethereum/ssz-specs/tree/main/lean) (@d4a0d75, MIT, Lean v4.33.1, no dependencies). Its types-as-data design (`Desc` plus separate values) matches this resolution, and it proves codec canonicality ('every accepted byte string is canonical'), whole-value binding in collision form, progressive trees (EIP-7916/7495) and a merkleization cost bound. Its `Ssz/` tree is free of `partial`/`native_decide`/`extern` (text scan; `partial` appears only in its conformance reader). Use it as inspiration and reference, and as a dependency only if it passes our declaration check and matches our design decisions (D26). **Condition:** State schema well-formedness, value validity and the serialization-domain premises (for example the offset bound) explicitly. The adapter inverses hold on their stated valid domains only. |
| B6 | Q17 | `Envelope` contents and owner | Hypotheses of particular consumer or resource theorems, **never an implicit guest acceptance limit**. Add fields only when a named theorem needs them. |
| B7 | Q24 | NEW-VM-2: halts as values | Accept, preserving the frame and observations needed for settlement. **Condition:** keep global faults, internal failures and diagnostics separate from frame exits and outputs. |
| B8 | Q1, Q26, Q43 | NEW-VM-4, NEW-CRYPTO-6: parameter values; gas-record granularity; precompile gas constants | `GasCosts` and `StateGasCosts` inside one coherent `VmConfig`, including **every** pricing dependency: tables and derived constants too (for example the EIP-2537 pairing and MSM tables). The Amsterdam values live in `EthFork`. Group fields for readability without fragmenting the API. |
| B9 | Q11 | `PreState` as a query interface | Keep the accepted executable record stable. Add a *proof-level* query trace or adapter; change the executable interface only if later work shows a material benefit. |
| B10 | Q12 | D5 scope | A **single explicit keccak dependency**: every keccak goes through `KeccakQuery`, covering at least the parent-header hash, code preimages, **newly installed code hashes** and the keccak-derived constants; concrete execution instantiates it with keccak256 (D5). **Condition:** keep the broad scope until the witness/full-state agreement prototype justifies a narrower one. |
| B11 | Q28 | NEW-VM-6: fuel budget Φ + 1 | Provisional: Φ + 1 remains an **unproved candidate** until the fuel-adequacy investigation ([REVIEW §7](REVIEW.md#7-acceptance-criteria-proof-gates-composition-cases-replacement-and-cost-checks) G2–G7, in particular G6) settles it. Also open: whether the fuel-indexed family for guarantees 2–3 is `constBudget n` or all policies pointwise above some policy (EthVmRunner §10). |
| B12 | Q4 | Public diagnostic outcome (`classify`) | Exposed: `classify` is public (EthStateless §5); it is the checked runner's result type, which the O11 split already requires. **Condition:** diagnostics never influence the output bytes. |
| B13 | Q40, Q41, Q42 + cofactor boundaries | NEW-CRYPTO-3 pairing as a predicate; NEW-CRYPTO-4 recovery/verification basis; NEW-CRYPTO-5 setup representation; where cofactor clearing happens | **These crypto items affect interfaces** (result and recovery types, setup constants, the cofactor boundary), so they cannot be deferred with the other crypto plans. Decide them before the curve and pairing interfaces are fixed; the pairing contract as a predicate is recommended. **Working position on the cofactor boundary:** `mapToCurve*` is uncleared and the `mapFp*` wrappers clear exactly once (EthCurve R8, COMPOSITION §2). **Condition:** this row schedules Q40–Q42; it does not settle the pairing result type, the recovery/verification basis or the setup representation. |
| B14 | Q2, Q15, Q23, Q31 | NEW-VM-1, NEW-STATE-3: named constructors for Python runtime failures (block, base, VM, state tracker) | Fed by the **failure ledger** (maintained outside this repository; GAPS X1). Error types are frozen per module or phase once that module's ledger entries are closed; primitive data structures need not wait for the global ledger. Each fault gets a named constructor; there is no catch-all (O13, §3). |
| B15 | Q33, Q35 | NEW-COMMIT-2 strict or lazy cached encodings; NEW-COMMIT-4 memoised decoding | Internal to `EthCommit`, and interface-neutral behind its API. Decide with the `EthCommit` implementation; memoisation needs a proof that the accept/reject result is the same. **Condition:** Memoisation must preserve error **precedence** and observations, not only acceptance and rejection. The per-root storage-trie memo is F6 (open, §3). |

## 3. Interface outcomes (F, O2, O13)

A compiled prototype of the interfaces tested how the spec guidance composes. Its findings (F1–F19), plus the repository review finding F20, together with O2 and O13, have the dispositions below. **Adopted** means the spec guidance follows it.

| ID | Finding | Disposition |
|---|---|---|
| F1, F2, F3, F4, F15, F18 | The broad keccak scope needs monad-parametric interfaces; keccak-derived constants; ECRECOVER; authentication predicates; lift instances; the block-hash check and the tx/withdrawal roots | **Adopted** as D5. Precompiles are monadic (`PrecompileFn m`), including ECRECOVER; F3's pure-precompile form is not adopted. `HashConsts` = {`emptyCodeHash`, `emptyTrieRoot`, `emptyOmmerHash`, `transferTopic`} lives in `EthBase`; its acquisition/threading is F20. `KeccakQuery` stays in `EthHash`. |
| F5 | `Vector (Option Node) 16` in a nested inductive is rejected by the kernel | **Adopted:** `Array (Option Node)` with a separately stated size-16 invariant. |
| F6 | Storage-trie decoding memo | **Open** (owner: EthStateWitness). Specify memo ownership, lifetime and decode triggers; cache mechanics stay outside semantic state; preserve B4 triggers and B15 precedence. It is a [DEBT](DEBT.md) candidate until then. |
| F7 | Iteration order of storage clears in the witness root replay | **Open** (owners: EthState, EthStateWitness). The prototype's traversal is not adopted until agreement covers failures and observations as well as roots. A first-clear order alone does not reproduce Python set iteration. |
| F8 | Where the Amsterdam values live | **Adopted** (B8): `abbrev STACK_DEPTH_LIMIT : Nat := 1024` in `EthVmCore`. Every Amsterdam value lives in `EthFork`, with `vmLimits_depth : … = STACK_DEPTH_LIMIT := rfl`. |
| F9 | Precompile pricing constants | **Adopted** (B8): the EIP-2537 pairing constants, discount tables, maximum discounts and multiplier are `GasCosts` fields. |
| F10 | Resume preconditions | **Adopted:** `StepResult.call/.create` carry `hs : parent.stack.size < STACK_DEPTH_LIMIT`, and resume takes the config. |
| F11 | How `ChildSettled` is produced | **Open** (owner: EthVmRunner). Choose one: a decidable check raising `InternalError.invariant` (then proved dead with the fuel guarantees), or a settled subtype returned by the runner. |
| F12 | `createEvm` failure path | **Adopted:** the entry-meter law in EthVmRunner R-TOP-2; `setDelegation` (R-AUTH-3) returns a meter subtype. |
| F13 | Field names in SSZ schema metadata | **Adopted:** `SszSchema.fieldNames`. |
| F14 | Checked results in the monad | **Adopted:** `CheckedT ε m := ExceptT ε (ExceptT InternalError m)`, owned by `EthVmRunner`; `runVmChecked` returns `m (CheckedResult …)`. |
| F16, F17 | `sorry` leaves block evaluation; `deriving` on nested inductives generates `partial` constants | **Adopted as guidance** (EthConformance §4, EthCodec §6, [CONTRIBUTING](../../CONTRIBUTING.md) §4). |
| F19 | `Nibbles` range field; orderings for `(Address × Bytes32)` keys | **Adopted:** the orderings are in `EthBase`; the range field is optional. |
| F20 | HashConsts lifetime across guest, witness and standalone block execution | **Adopted** (2026-09-30; owners: EthBlock, EthStateless, EthConformance). Caller-owned acquisition and supplied-record kernels follow EthStateless R5, EthBlock §2.7 and EthConformance R4; consumers read existing context fields. Notation: CONTRIBUTING §7.2. Rationale, scope and open obligations: §6. |
| O2 | Request-root failure | **Open** (owner: EthStateless): prove it unreachable on decoded values (EthStateless L-root), and add a constructor only if that proof fails. |
| O13 | Unrowed deterministic reference faults | **Adopted** (2026-09-29): CONTRACT O13 is a documentation category for explicitly enumerated deterministic reference faults. The output is unchanged, `(root, false, …)`, and each fault has a named constructor, enumerated by its owner (EthBlock §2.12, EthVmCore R-EXC-2, EthState R29); there is no generic catch-all. O12 remains unresolved. |

## 4. Other questions (Q)

Questions that do not affect interfaces, or that are resolved or tracked elsewhere.

| Q | Question | Disposition |
|---|---|---|
| Q3 | Taylor loop on adversarial `excessBlobGas` | Tracked as **DISC-002** (measured). Liveness only; no interface change. |
| Q5 | Fork-activation check | Follow the reference, and keep the explicit exclusion (CONTRACT §5). |
| Q6, Q20 | Deep witness chains; deep RLP nesting | Tracked under **DISC-001** (O12 host resources) and **DISC-006** (why the error surfaces as O6). **Unresolved by design:** D14 does not decide it. The guest-process recursion limit is 100,000 (py_ecc raises it). RLP nesting of 20,000 levels decodes and 40,000 raises, and the resulting `RecursionError` becomes O6 on the guest path (observed by running the pinned EELS on deterministic probe inputs, 2026-09-29). The witness-chain depth has not been re-measured under that limit. |
| Q7 | Lean-native witness generator | Use the EELS host out of process for now; revisit when fuzzing throughput is measured. |
| Q8 | Transition fixtures | Skip and count them in the stateful runner until a BPO2 instantiation exists. |
| Q9 | EEST exception-name mapping | Warning-only; validity itself is decisive. |
| Q13 | Completeness (liveness) theorem | Later, and it needs a specified witness generator. |
| Q14 | VCV-io pin and API | Pin a full commit when `EthSecurity` work starts; use the `Measure`-based API. |
| Q16 | Placement of `fork_types.py` items | **Done** in the specs: `encode_account` is in `EthStateCommit` (both copies claimed); `Authorization` and `StateGasPerByte` are in `EthBase`. |
| Q18 | Unreachable utilities | The failure ledger's static call-graph pass places `is_prime`, `le_*uint32*` and `has_field` (EthBase §9) and `keccak512`, `_hashlib_has_keccak` and `_USE_HASHLIB` (EthHash §10) outside the guest call graph. **Pending:** exclude them in EXCLUDED.md with that reason; the owning modules claim them until then. |
| Q19 | RIPEMD-160 host dependency | Tracked as **DISC-005**. |
| Q25 | NEW-VM-3 `Log`/`BlockOutput` placement | **Resolved by D27** (accepted 2026-09-28). |
| Q27, Q38 | NEW-VM-5, NEW-CRYPTO-1: secp256k1 recovery | **Resolved by D26** (accepted 2026-09-28). |
| Q39 | NEW-CRYPTO-2: fast field plan | Width settled by measurement: a carry-preserving CIOS backend needs only `p < R`, so `Wide8` (8×32-bit limbs) covers every pinned modulus below 2^256 and `W12` covers BLS12-381 q. Measured: the `Nat` reference is 3–6.5× slower than `Wide8`, and `Wide8` is 20–35× slower than native ecrecover. The source (vendor or upstream) remains with D6, which tracks CompPoly PR #389. |
| Q44 | NEW-CRYPTO-7: owner of D12 (iii) security statements | `EthSecurity`, when it starts. |
| Q45 | NEW-CRYPTO-8: conditions for reusing cryptography-specs | With D15. At `09deaff` it is not reusable as-is (Lean v4.29.1, `partial def`, `get!`, `native_decide`). |
| Q46 | SHA-256 total input domain | **Accepted by the maintainer (2026-09-30), recorded in [issue #9](https://github.com/alexanderlhicks/leanerSTFSpec/issues/9).** Preserve `sha256 : ByteArray → Bytes32` and totality. Its trailer encodes `(8 * msg.size) mod 2^64` as eight big-endian bytes. FIPS 180-4 correspondence requires `8 * msg.size < 2^64`; beyond that domain this selects a total extension, without FIPS or pinned-host equivalence. No rejection, error-result or gas change. Fixed-word compression has no length premise. |
| Q47 | RLP total encoder outside the encodable domain | **Accepted by the maintainer (2026-09-30), recorded in [issue #12](https://github.com/alexanderlhicks/leanerSTFSpec/issues/12).** Preserve the total `Rlp.encode`, `encodeBytes` and length-prefix helper signatures. Compute prefix tags in UInt8 modulo 256 and retain exact, unbounded minimal big-endian length digits. The packed encoder must equal its total byte-list model for every item. Standard RLP and pinned-dependency correspondence require `Encodable` (every item payload length has an at-most-eight-byte prefix). Outside that domain, this selects a total extension without claiming protocol acceptance/rejection, injectivity, decoder canonicality or pinned-host/resource equivalence. No rejection API or gas change. Revisit if a consumer needs behavior beyond this domain. |

## 5. Adding or changing a decision

- **A new question** starts in a spec guidance document's §9, then gets a `Q` number here (§4), or a `B`/`F` entry if it affects interfaces.
- **A decision or status change** edits the row here, the options in ARCHITECTURE §11, and the affected spec guidance documents, in the same change. `scripts/check_spec.py` checks that every P, D, B, F and Q ID cited in a spec guidance document exists here.
- **A decision that needs more than a row** gets a record appended below this section (or, if long, a separate file next to this one), covering:
  - status and authorization (date, evidence; implementation alone is not acceptance);
  - problem and scope (trigger, owning component, consumers, governing principles);
  - sources (EELS and dependency commits, affected functions, fixture release);
  - options and evidence (alternatives, measurements, proof feasibility, reasons for the choice);
  - contract (public API and laws preserved or changed; hypotheses and exception precedence);
  - validation (theorem and axiom checks, regression inputs, conformance coverage, unverified claims);
  - change procedure (affected modules, consumer migration, compatibility and removal, rollback);
  - revisit criterion (the evidence that would change it; links to debt or discrepancy entries).
- **A performance exception** goes in [`DEBT.md`](DEBT.md), naming the expected workload, complexity, measured limitation, reason and replacement criterion (D18).
- **A protocol deviation** needs a [`DISCREPANCIES.md`](DISCREPANCIES.md) entry (reproducer, upstream issue and response) and an accepted decision here naming it.

## 6. F20: caller-owned hash constants

**Status and authorization.** The disposition is owned by §3. F20's caller-owned
acquisition was approved on 2026-09-30; the requester's confirmation is recorded
publicly in [PR #2's review](https://github.com/alexanderlhicks/leanerSTFSpec/pull/2#pullrequestreview-5365528147).
Approval of the interface leaves the compiled-case, oracle-trace and proof
obligations below open. D5 retains its status in §2.

**Problem and scope.** Witness construction and payload/header checks need keccak-derived
constants before `BlockState` exists. The guest, standalone block wrapper and engine
driver must provide one coherent record to their backends and kernels. EthStateless,
EthBlock and EthConformance own their respective acquisition boundaries; EthHash provides acquisition, EthBase the value record, and state, commitment,
VM and conformance consumers use it. D5 governs hashing; D14 governs failure channels.

**Sources.** The release and dependency commits are pinned in `reference.toml`:
`tests-zkevm@v21.0.0`, execution-specs `e1a316a06fc3d3e0a5da36fdc78580811e9d8a36`.
Relevant EELS sites are `src/ethereum/forks/amsterdam/stateless.py:250,281–294`,
`execution_engine/new_payload.py:112–136,147–157`,
`execution_engine/validation_helpers.py:61,108`, and `fork.py:265,309–325,498`
(the latter paths are under the same Amsterdam directory). EELS uses module-level
constants; F20 specifies their Lean acquisition boundary rather than an EELS operation.

**Options and rationale.** Acquiring inside the block kernel is too late for witness and
payload construction. Using literals there would bypass the generic oracle. Caller-owned
acquisition makes the same record available to each consumer without reacquisition.
Existing contexts hold the record once constructed; helpers called before those contexts
exist take it explicitly. The notation convention belongs to CONTRIBUTING §7.2.

**Contract.** Acquisition and effect order are owned by EthStateless R5, EthBlock §2.7
and EthConformance R4, with required equations in their §7 laws. The supplied-record kernels are
`executeNewPayloadRequest` and `executeBlock`; `executeBlockStandalone` accepts a
`mkPre : HashConsts → m (PreState m)` provider factory. EthConformance R4 specifies
acquisition for the engine driver. Consumer/provider coherence is a proof premise,
not a consequence of the factory's type. Exception precedence and the checked error
channels retain their owning contracts.

**Validation and limits.** This is an informal interface contract, with no production
implementation or theorem. The prior closure criterion, a compiled interface case
and an oracle trace, is retained as the required synthetic-oracle, failure-order and
repeated-run cases in EthStateless, EthBlock and EthConformance §4, together with
their §7 laws.
Implementation must compile and execute those cases and prove those laws; documentation
checks cannot establish those results. Backend coherence, D5's generic interpretation
coupling (X7), REVIEW §7 S2, EthStateWitness W1, fuel gates G2–G7, guest conformance and
security remain open; F20 establishes no performance or specialisation result.

**Change procedure.** Update the two kernel contracts, provider factories and their
consumers together; migrate direct payload callers as specified by EthConformance R4.
Keep the supplied record in existing state/backend contexts and use their fields.
Review any incompatible change through §5 and update ARCHITECTURE §11 and affected
guidance in the same work item. A rollback must preserve D5's oracle scope and the
reference's failure precedence.

**Revisit criterion.** Reconsider the acquisition boundary if production composition
shows it cannot preserve reference failure order or support a coherent generic oracle
interpretation. Such evidence belongs with X7 and the affected component laws; a
performance claim requires its own measurement and decision under CONTRIBUTING §3.
