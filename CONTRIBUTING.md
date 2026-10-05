# Contributing to STFspec

*Status: current contributor guidance. Date: 2026-10-05.*

Contributions are welcome: implementing a library, proving a law, fixing a discrepancy with the reference, improving a spec guidance document, or improving the checkers.

**Start with [`AGENTS.md`](AGENTS.md).** It maps each kind of task to the documents to read and update and the checks to run, and gives the authority order used when documents disagree. This file covers the principles every contribution follows (§1–§5), then the workflow, review gate and roles for agent-driven work (§6), the Lean style (§7) and documentation (§8). Sections §1–§5 are cited by number throughout the repository; keep their numbering stable.

## 1. The golden rule: EEST zkevm conformance

The spec must pass the EEST zkevm fixtures for the guest (`statelessInputBytes → statelessOutputBytes`) at the release pinned in [`reference.toml`](reference.toml). **Passing them is mandatory, and they are decisive wherever they speak.** Neither this spec, nor evm-sail, nor SpecRef, nor any client is more authoritative than the fixtures.

A finite corpus cannot determine behaviour on every uncovered input. Outside fixture coverage, the **pinned EELS source** at the same release commit governs, read as a specification together with the pinned dependency behaviour. Disagreements, accidental Python behaviour and unclear cases follow the discrepancy policy in [`STFSpec/informal/CONTRACT.md`](STFSpec/informal/CONTRACT.md) §6.

- Differential testing and fuzzing against other implementations are **bug-finding tools, not sources of truth**. A disagreement is investigated. It is settled by the fixtures, or, where they are silent, by reading EELS and reporting the gap upstream. It is never settled by deferring to another implementation.
- Proofs about the spec (for example witness soundness) add confidence in *properties*. They do not replace conformance.

## 2. Legibility is a first-class requirement

The spec is not a black box to be optimised. Like EELS, whose choice of Python reflects this, it must support human discussion of the semantics. The aim is **formality, legibility and performance together, balanced deliberately**:

- Design decisions are explicit and inspectable: each is recorded in [`STFSpec/informal/DECISIONS.md`](STFSpec/informal/DECISIONS.md) with its rationale, so that the qualitative properties expected of the spec can be checked by reading, not only by testing.
- Structure and names follow EELS wherever that does not conflict with totality or performance (§7.2). Where it does conflict, the deviation is documented.
- A reader should be able to find, for any EELS function, the spec definition that corresponds to it, and read that definition without first understanding an optimisation.

## 3. Performance policy

- **Appropriate costs.** Choose appropriate operation *and aggregate* costs for the stated workloads and persistence requirements: persistent maps for revertible state, in-place linear buffers for memory, incremental trie hashing. Avoid unnecessary copying, repeated traversal and avoidable asymptotic degradation. O(n log n) for sorting or for building persistent maps is ordinary, not a departure. Record justified departures from a component's expected bounds (D18). An algorithm's name alone does not establish suitability: measurements include allocation, conversions and composition.
- **Target:** within **10×** of native clients (evmone/revm-class) on the same workloads, **aiming for about 2×** where algorithmic improvements achieve it while *keeping the spec simple*.
- **Order of preference:**
  1. A better algorithm or data structure that remains legible.
  2. Only later, and only if needed, a faster **representation** of a component, proved against the same model-based contract (D25) so that callers and their proofs are unchanged. Never compiler substitution: `@[csimp]` is banned (D21).
  3. Never micro-optimisations that sacrifice purity or legibility of the spec text.
- The target is not a hard number fixed in advance. Measurements (the composed cost checks C1–C4 in [`STFSpec/informal/REVIEW.md`](STFSpec/informal/REVIEW.md#7-acceptance-criteria-proof-gates-composition-cases-replacement-and-cost-checks) §7) show where legibility and speed actually conflict, and each conflict is resolved explicitly in a decision record.
- **Benchmarks** have a correctness gate, keep checksums out of the timed loop, and report the unit the workload was divided by.

## 4. Structure and hygiene

The structure follows the [hex-dev](https://github.com/kim-em/hex-dev) pattern.

- **Packages.** The core (`STFSpec/`, the repository root package) is Mathlib-free and Batteries-free. Mathlib appears only in the bridge package `STFSpecMathlib/` (paired `…Mathlib` libraries) and the security package `STFSpecSecurity/`; VCV-io only in the latter. The boundary is enforced at the **package** level: Lake lets a library import any module in its package's dependency closure (verified 2026-09-28), so separate `lean_lib`s in one package would isolate nothing. Imports *between* core libraries follow [`scripts/boundaries.toml`](scripts/boundaries.toml), checked by `scripts/check_boundaries.py`.
- **Implementations are final (D18).** Each satisfies **all required properties**: a finite, named set in its component contract, covering semantics, totality, failure precedence, representation invariants, composition laws and the applicable resource requirements. Unproved obligations stay listed as open obligations.
  - Data structures must be **performance-appropriate**, judged against the relevant operation costs *and* the persistence requirements. A map with good lookups but a snapshot copy per frame is not appropriate.
  - A deviation must be justified on grounds of legibility or drastic proof-friendliness, and recorded in [`STFSpec/informal/DEBT.md`](STFSpec/informal/DEBT.md) with the expected workload, the complexity, the measured limitation, the reason and the replacement criterion.
  - The fastest possible implementation is not required now. Later improvements are contained representation replacements (D25).
- **`sorry`** is allowed only in the Mathlib and security packages during development; the core declaration check rejects it, including in proofs. `axiom` is never used.
- **No additional trust assumptions (D21).**
  - **What is checked:** the *resulting proof dependencies*, whatever tactic produced them. No axiom beyond `propext`, `Quot.sound` and `Classical.choice` may appear, directly or transitively. So `native_decide`, `bv_decide` and `decide +native` are rejected (each adds a `…._native…` axiom), and renaming or wrapping a tactic cannot bypass the check.
  - **Design rules:** `@[csimp]`, `implemented_by`, `extern`, `unsafe`, `partial` and `opaque` are banned too. `@[csimp]` and `opaque` are not *logically* unsound; the prohibition is about executable correspondence (compiled code must run the definition we reason about) and transparency (every definition must unfold).
  - **Enforcement:** `check-decls` (`scripts/check_decls.sh`), with regression fixtures. There is no exemption mechanism.
  - **Bit-vectors:** use Std's operation lemmas, bit extensionality, `simp`, `omega` and arithmetic reasoning, plus plain `decide` for small concrete checks; `check-decls` checks the resulting proofs.
- **Derived instances can introduce banned constructs.** `deriving BEq`/`Repr`/`DecidableEq` on a *nested* inductive (an RLP item or SSZ value containing a `List` of itself) generates `partial` constants. Write structural instances by hand for such types (F17, [DECISIONS §3](STFSpec/informal/DECISIONS.md)).
- **Fast definitions without compiler substitution.** Where the performance-appropriate executable definition is not the most legible form (an unrolled keccak permutation, limb arithmetic), the component keeps a **legible reference definition beside it**, with the equality proved as an ordinary theorem. Callers use the executable definition; readers and proofs can go through the reference. Both live in the owning module, and the model-based contract (D25) states which one the laws are proved against.
- **Compiler replacements, including dependencies'.** `check-decls` enumerates every current and superseded `@[csimp]` theorem, because a dependency might register one affecting our code. Any in-scope one is a finding.
- **Release theorems.** Consumer-facing theorems must be free of `sorry`, including through their dependencies. Conditional theorems list their hypotheses explicitly and name the bridge that discharges each; passing the development check is not a claim that a conditional theorem has been instantiated.
- **Toolchain.** Lean **v4.34.0**, pinned in `lean-toolchain` and `reference.toml`.
- **Trusted baseline ("pure Lean", D26).** The pinned Lean kernel and its standard axioms; the Lean compiler; and Lean core's runtime primitives (GMP-backed `Nat`, `ByteArray`/`Array` operations and the other `@[extern]` implementations in Lean core). It does **not** promise independence from the compiler or runtime. Everything else, including every third-party dependency, must be Lean source that passes `check-decls` on what we import. Core dependencies and those of the Mathlib and security packages are chosen separately: a mathematical library useful for proofs need not become a core dependency.

## 5. Tests, review and automation

1. **Tests are necessary, not the definition.** Passing the pinned fixtures is mandatory (§1). But the spec is not a test-passing artefact: it must carry meaning in its own right, as a legible, faithful statement of the protocol's semantics.
   - No fixture-specific special cases.
   - No definition shaped by what the corpus happens to exercise rather than by what the reference means.
   - A change that keeps the tests green but makes a definition less faithful or less legible is a regression.
2. **Review is continuous and proportionate.** Reviews produce findings, recorded as gaps, discrepancies or decision questions. They are not an ever-growing set of preconditions that nothing could satisfy. The bar for proceeding is that known issues are *recorded, owned and not hidden*, not that every conceivable issue is closed first.
3. **Automate only what is strictly deterministic.** CI and other automated checks enforce properties with an exact, mechanical definition:
   - builds and warnings;
   - import boundaries, and their agreement with the architecture's dependency table;
   - compiled-declaration checks (axioms, `sorry`, `partial`/`opaque`, extern, `@[csimp]`);
   - EELS coverage and ownership;
   - pins and checksums;
   - fixture conformance (once the conformance runner exists);
   - generated-document freshness;
   - the regression tests of the checkers themselves.

   Qualities without such a definition, such as legibility, argument quality, faithfulness of intent, or "enough" test coverage, are review matters. They are never approximated by heuristic CI checks. For example, the spec checker verifies that an informal argument *has* its Claim/Premises/Argument/Open-obligations parts, never whether it is convincing.
4. **The spec guidance documents are informal by design.** They are Markdown written for the implementer, human or agent, and must be precise enough to determine exactly what to build: behaviour, ordering, failures, ownership, and how the module fits the end-to-end spec. They do **not** need to typecheck, and they must not try to carry Lean proofs.
   - Lean-like signatures convey names, inputs, outputs, error channels and ownership. Fixing exact Lean types, resolving placeholders and compiling the interfaces is implementation work.
   - The informal correctness arguments are *sketches*: the claim, the premises, why it should hold, and what remains open. They tell the implementer what to prove and suggest how; the proofs themselves are the implementer's.
   - Precision is judged by one question: can an implementer act on it without guessing?
5. **Blocking findings require a material reason.** Review the stated work item and
   the contracts and evidence it relies on. A blocker identifies the governing
   requirement, the affected behavior or claim, and supporting evidence: a
   counterexample, a failed required check, a source discrepancy, or a missing
   required proof or test case. Passing Lean proofs alone does not establish
   reference fidelity or compiled behavior, but a request for more testing alone
   does not establish a defect either.
   - **Blockers:** incorrect semantics or failure order; a violated public contract,
     trust boundary or applicable resource requirement; missing required validation;
     or documentation/evidence that materially misstates what was implemented or
     verified. A Python or shell defect qualifies when it changes required behavior
     or makes evidence used by the work item unreliable—for example, executing the
     wrong oracle code, authenticating different bytes, or losing CLI reply framing.
   - **Non-blocking improvements:** formatting, naming preferences, unused imports,
     equivalent helper organization, cosmetic documentation edits and speculative
     harness hardening, absent an identified material consequence. These remain
     recommendations even when a style convention supports them. They may be fixed
     now or in a separate polishing change; no waiver, new issue or proof that the
     observation is wrong is required to defer them.
   - **Scope:** unrelated or pre-existing tooling cleanup belongs in a tooling work
     item. If a tooling defect prevents required validation, fix that prerequisite
     separately or as a focused dependency; do not expand the Lean contribution into
     a general harness rewrite. A failed required check still needs resolution.
     Propose additional general checks separately, with regression evidence; do not
     make an unrelated new gate a condition of the current contribution. Open
     repository obligations block only the work or readiness claim they affect.
     Cosmetic script lint may be advisory; it is not a required merge gate.

## 6. Workflow and pull requests

### 6.1 Before you start

- **Implementing a library:** read its spec guidance document in [`STFSpec/informal/modules/`](STFSpec/informal/modules) and the per-module gate and implementation contract in [`STFSpec/informal/REVIEW.md`](STFSpec/informal/REVIEW.md) §§3–4. Implement lower layers first; the dependency order is in [`STFSpec/informal/ARCHITECTURE.md`](STFSpec/informal/ARCHITECTURE.md) §3.
- **Changing behaviour, an interface or a decision:** open an issue first. The spec guidance documents play the role a blueprint plays elsewhere. Update the affected guidance document(s) and, where a design choice is involved, record the question or decision in [`STFSpec/informal/DECISIONS.md`](STFSpec/informal/DECISIONS.md) (its §5 says how), in the same change as the code.
- **Found a disagreement with EELS or the fixtures?** Record it in [`STFSpec/informal/DISCREPANCIES.md`](STFSpec/informal/DISCREPANCIES.md) with a reproducer (CONTRACT §6). An entry records; it never authorizes a deviation.

### 6.2 Pull request title and description

Titles follow the Lean community convention:

```
<type>(<optional-scope>): <subject>
```

- **Types:** `feat`, `fix`, `doc`, `style`, `refactor`, `test`, `chore`, `perf`, `ci`.
- **Scope:** the library (`EthVmCore`), package (`mathlib`, `security`) or area (`informal`, `decisions`, `scripts`).
- **Subject:** imperative, present tense ("add", not "added"); lower-case first letter; no final full stop.

The description gives the motivation, the change in behaviour or contract, the EELS sources it follows, the decisions or questions it touches (by ID), and references to issues (`Closes #123`). A change that implements EELS operations includes their source-to-Lean rows (REVIEW §4).

### 6.3 Checks

Run before opening a pull request (CI runs the same):

```sh
lake build --wfail
lake build bytes-native-tests --wfail
lake exe check-decls BytesNativeTests && lake exe bytes-native-tests
lake build write-order-native-tests --wfail
lake exe check-decls WriteOrderNativeTests && lake exe write-order-native-tests
lake build math-state-native-tests --wfail
lake exe check-decls MathStateNativeTests && lake exe math-state-native-tests
lake build block-diff-native-tests --wfail
lake exe check-decls BlockDiffNativeTests
lake exe block-diff-native-tests
lake build apply-native-tests --wfail
lake exe check-decls ApplyNativeTests
lake exe apply-native-tests
lake build fixed-endian-bench --wfail
lake exe check-decls FixedEndianBench
python3 scripts/check_boundaries.py
scripts/check_decls.sh core
lake build CheckDeclsTest check-decls && scripts/test_checks.sh
python3 scripts/test_differential.py
python3 -B scripts/test_hash32_output_parser.py
python3 -B -O scripts/test_hash32_output_parser.py
python3 -B scripts/test_node_db_output_parser.py
python3 -B -O scripts/test_node_db_output_parser.py
python3 scripts/check_reference.py && python3 scripts/test_reference_checks.py
python3 scripts/gen_arch_diagram.py --check
python3 scripts/check_spec.py && python3 scripts/test_spec_checks.py
python3 scripts/gen_gaps.py --check
lake build EthConformance fixture-records --wfail
python3 scripts/test_fixture_archive.py
```

The fixed-endian benchmark is built and audited here; timing measurements remain manual.

Changes to `STFSpecMathlib/` or `STFSpecSecurity/` also run `lake build --wfail` there and `scripts/check_decls.sh mathlib` or `security`. Regenerate, never hand-edit, generated files: `STFSpec/informal/GAPS.md`, `REFERENCE-RECORDS.md`, `eels-inventory.json`, and the README diagram.

### 6.4 Review and commit gate

Every change is a **work item**: a self-contained change that one reviewer can hold in full (for example one type with its operations and laws). A work item is committed only when all of these hold for the exact tree being committed:

- every check in §6.3 passes, together with the item's own tests: the deterministic and failure-order cases its spec guidance lists (§4 of each guidance document), and differential comparison against EELS where the guidance calls for it;
- an **independent adversarial review** of that exact diff (§6.6, *adversarial reviewer*)
  found it **clean**: required checks were run and no blocking finding under §5.5
  remains unresolved. Non-blocking recommendations may remain. A blocker must be
  fixed or rebutted with written evidence in the pull request; deferring a nit does
  not require a rebuttal. Any change made after review is reviewed again;
- the documentation is current (§6.5);
- the commit message follows §6.2's conventions and summarises the change, the evidence and the review verdicts.

Commits never contain `sorry` in the core, a banned construct (§4), a failing or skipped check, or unreviewed code.

### 6.5 Pull requests, stacking and documentation

- **Granularity:** one pull request per larger component (typically a library, or a coherent slice of one), made of several work-item commits.
- **Stacking:** a pull request's branch starts from the branch of the pull request it depends on, or from `main` if it depends on nothing unmerged; its base is set to that branch, and its description says "Depends on #N". Work continues on top of open pull requests: they may be reviewed and merged later, possibly in batches. After a parent changes, rebase its descendants (`git rebase --update-refs`) and push them with `--force-with-lease`; after a parent is merged, retarget the child to `main` and rebase it. Never push to or force-push `main`.
- **Description:** the §6.2 contents, plus the source-to-Lean rows, the check and test results, a summary of the review verdicts, the documentation updated, and the pull request's position in the stack.
- **Documentation in the same pull request:**
  - the implemented library's spec guidance: source-to-Lean rows and statuses (REVIEW §4), §10 gaps, and anything the implementation showed to be wrong or imprecise;
  - `STFSpec/informal/DECISIONS.md` for any new open question, or a disposition the maintainers approved;
  - regenerated generated files (`scripts/gen_gaps.py` and the others in §6.3);
  - REVIEW §6 and the README status line when a layer's readiness changes;
  - CONTRACT, DISCREPANCIES, ARCHITECTURE and COMPOSITION whenever the change touches what they own.
- **Maintainers decide:** accepting decisions or changing their status, protocol deviations, new dependencies (D26), changes to interfaces consumers rely on, and merges.

### 6.6 Roles for agent-driven work

Work may be carried out by agents in any harness. An **orchestrator** plans work items, briefs one agent per role, evaluates the results itself (re-running the checks, reading the diff, spot-checking fidelity against EELS), and alone commits and opens pull requests under §6.4–§6.5. Every agent reads [`AGENTS.md`](AGENTS.md), this file and the documents its brief names, and gets a self-contained brief: the work item, its scope and allowed files, the governing guidance and decisions, the checks to run and the report format. Agents other than the orchestrator never commit, push or open pull requests. Work items that run in parallel use separate worktrees.

- **Researcher** (read-only on tracked files). Answers one question about the pinned EELS source, its dependencies, the fixtures, literature or prior art. Marks each claim verified (code read at the pin, command run, measurement taken) or inferred; cites EELS as `file:line` at the pin; proposes, but never makes, changes to decisions or guidance.
- **Prototyper.** Settles a design question or measurement before the core depends on it, in isolated throwaway code outside the core (a separate package that requires nothing from it). Separates what runs from what is assumed; gives exact reproduction commands and a §3-compliant measurement method; proposes a disposition with evidence.
- **Implementer.** Implements exactly one work item on its branch: definitions, laws, proofs and tests, as the spec guidance and REVIEW §3/§4/§7 specify, under §4 and §7. If the guidance is wrong, ambiguous or incomplete, stops and reports it rather than filling the gap by convention. Updates the documentation (§6.5); reports the exact check output, the source-to-Lean rows, the laws proved and the open obligations.
- **Conformance engineer.** Builds the `EthConformance` runners, the `core` profile, replay records and differential harnesses against EELS, as its spec guidance specifies. Fixtures are decisive (§1): a mismatch is a failure of the spec, never special-cased; the archive is authenticated before use; CI jobs are deterministic and bounded.
- **Adversarial reviewer** (never edits). Judges only the diff, the brief and the governing documents, without the implementer's context, and tries to break the change:
  - fidelity to the pinned EELS, including every failure condition and its order;
  - the stated laws, and the one-owner rule;
  - totality and the hard rules (running `scripts/check_decls.sh` and `scripts/check_boundaries.py`);
  - test adequacy (an input that passes the tests but is wrong);
  - the data structures against the guidance or DEBT;
  - documentation drift.

  It re-runs the checks itself. It returns **clean** or **not clean** as defined in
  §6.4, with findings classified under §5.5: **blocking**, **should fix**
  (non-blocking recommendation), or **nit** (non-blocking polish). A blocker names
  its governing requirement, affected behavior or claim, file:line and evidence.
  The report lists what could not be verified and keeps tooling findings distinct
  from Lean semantic findings. A correctly classified script nit cannot turn a
  clean Lean work item into a **not clean** verdict. It never reports clean on
  unrun required checks. Load-bearing items (shared types, seams, laws other modules
  rely on) get two independent reviewers.
- **Polisher.** Improves accepted work for legibility and style (§2, §7) without changing behaviour, public signatures or stated laws: naming, structure, moving duplicated helpers to their owner, proof clarity, docstrings, stale documentation. One theme per pass; the result goes back through review.

Harness-specific configuration (for example agent definition files) is local to each contributor, is not committed, and only points to this section.

## 7. Lean style and naming

We follow the [Lean community's style and naming conventions](https://leanprover-community.github.io/contribute/index.html) (as mathlib does), with the project-specific rules below. Where this file and the community guide differ, this file wins; when in doubt, match the adjacent code.

### 7.1 Files and modules

- One Lake library per component, rooted as in [`scripts/boundaries.toml`](scripts/boundaries.toml) (library `EthVmCore` is the module tree `STFSpec.Vm.Core`). File names are `UpperCamelCase.lean`.
- Every file starts with the header

  ```lean
  /-
  Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
  -/
  ```

  then imports, then a module docstring (§8.1).
- Import only what the file uses, and only within the library's allowed dependencies.

### 7.2 Naming

- **EELS names first (§2).** A Lean definition corresponding to an EELS function keeps its name, converted to Lean case: `process_message_call` → `processMessageCall`, `get_storage_original` → `getStorageOriginal`. EELS classes keep their names (`Account`, `GasMeter`). Module-level protocol constants keep their EELS spelling (`STACK_DEPTH_LIMIT`) so they can be found by searching the reference; fields of parameter records use the lowerCamelCase form of the EELS name (`GasCosts.CALL_VALUE` → `GasCosts.callValue`, `COST_PER_STATE_BYTE` → `costPerStateByte`). A name that departs from EELS is documented in the spec guidance document.
- **Otherwise the community rules:** types, structures and classes `UpperCamelCase`; functions and terms `lowerCamelCase`; theorems and proofs `snake_case`; acronyms treated as words (`RlpItem`, not `RLPItem`); Prop-valued adjective classes with `Is` (`IsCanonical`).
- **Theorem names describe the statement**, using the community conventions (`_of_` for hypotheses, `ext`, `iff`, `inj`, `mono`, `left`/`right`; `le`/`lt` rather than `ge`/`gt`). Law names follow the operation they describe: `getStorage_setStorage_same`, `toBitVec_add`.
- **No provenance in names.** Name a declaration for what it says, never for where it came from: no EELS line numbers, paper or section numbers, or decision, question or gate IDs (`d5_...`, `g2_progress`). Cite those in docstrings instead (§8).
- **Variable conventions** (in addition to the community's `α`, `h`, `n`…): `m` is the hash-query monad (`{m} [Monad m] [KeccakQuery m]`); `σ` a mathematical state; `ps` a `PreState m`; `d` a `BlockDiff`; `cfg` a configuration record; `consts` the `HashConsts` record; `f` a frame; `w` a world. Use descriptive names where a single letter would be ambiguous.
- **Constants notation (F20).** At constants-consuming seams use `variable (consts : HashConsts)` and local notation with EELS names:

  ```lean
  variable (consts : HashConsts)
  local notation "EMPTY_CODE_HASH" => consts.emptyCodeHash
  local notation "EMPTY_TRIE_ROOT" => consts.emptyTrieRoot
  local notation "EMPTY_OMMER_HASH" => consts.emptyOmmerHash
  local notation "TRANSFER_TOPIC" => consts.transferTopic
  ```

  Where the record already lives in a state or backend, read its constants field. Functions called before that context exists, such as `validateHeader`, take `consts` explicitly; the notation names its fields. Bind context notation in its own section so it projects the stored record rather than capturing an outer `consts`.

### 7.3 Formatting

- Lines under 100 characters; two-space indentation; no tabs; no trailing whitespace.
- Spaces around `:`, `:=` and infix operators; an operator that breaks a line ends the line rather than starting the next.
- `fun x ↦ …`; `where` syntax for instances and structures; a space after binders (`∀ x,`).
- Hypotheses to the left of the colon (`(h : P) : Q`) when the proof introduces them.
- `by` at the end of the preceding line, with the tactic block indented. No blank lines inside definitions or proofs. Avoid `;` between tactics except in short single-line sequences.
- Prefer `<|` and `|>` to deep parentheses.

### 7.4 Definitions, contracts and proofs

- **Totality.** Every definition is total. Recursion is structural or well-founded with an explicit measure (`termination_by`, and `decreasing_by` where needed); fuel appears only where [ARCHITECTURE](STFSpec/informal/ARCHITECTURE.md) §5.5 puts it. No `get!`, `panic!` or `unreachable!`: represent impossible states in the types, or return a typed error (D14).
- **Contracts, not internals.** A component's callers use its public model laws and equations (ARCHITECTURE §4). Do not unfold another component's container internals or compiler-generated equations in a proof. Keep representation types behind a `structure` (for example `U256`) rather than an `abbrev`, so their instances cannot leak.
- **`simp` sets are small and opt-in**, one per component (`simp [Memory.laws]`). Do not add broad `@[simp]` lemmas that expand whole state structures.
- **Automation on well-scoped goals.** `simp`, `omega`, `decide` (small, concrete) and similar are fine as terminal steps or after an explicit transformation. Profile a slow proof before rewriting it; do not squeeze stable terminal `simp` calls without a measured reason.
- **Monads and errors.** Follow the three failure channels (D14): frame exits as values, protocol rejections as typed errors, internal failures as `InternalError`. Every hashing interface stays generic in `m` (D5); only public entry points specialise to `Id`.

### 7.5 Renaming and deprecation

Until the first tagged release, rename freely but update every caller and the spec guidance in the same change. After a release, keep a deprecated alias for renamed public declarations:

```lean
@[deprecated (since := "YYYY-MM-DD")] alias oldName := newName
```

## 8. Documentation and citations

### 8.1 Docstrings

- **Module docstring.** Each file opens with a `/-! … -/` block giving a title and summary, the library it belongs to, and a `Spec guidance:` line naming its document in `STFSpec/informal/modules/`.
- **Declarations.** Every public definition and every law or theorem callers rely on has a `/-- … -/` docstring. A definition that implements an EELS operation cites it as `src/ethereum/…/file.py:line` at the pinned commit (the source-to-Lean row, REVIEW §4).
- Use backticks for Lean names and `/-! ### Title -/` comments to section long files.

### 8.2 Citations

- **The reference:** cite EELS by path and line at the commit in `reference.toml`, and EIPs by number (`EIP-7702`).
- **Papers and books:** cite them in a `## References` section of the module docstring, as `* Author(s), *Title*, venue year`, and refer to them in text by author and year. Link a public version where one exists; never add copies of copyrighted papers or books to the repository.
- **Other implementations and specifications** (evm-sail, clients, cryptography-specs) may be linked directly, with a commit where the claim depends on one.

## 9. Code of conduct

Please treat fellow contributors with respect. STFspec follows the principles of the [mathlib Code of Conduct](https://github.com/leanprover-community/mathlib4/blob/master/CODE_OF_CONDUCT.md); participating in the project (code, issues, discussions) means agreeing to abide by them. Report unacceptable behaviour to the maintainers.

## 10. Licence

STFspec is licensed under either of the [Apache License, Version 2.0](LICENSE-APACHE) or the [MIT licence](LICENSE-MIT), at your option. Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in this work is dual licensed as above, without any additional terms or conditions. Vendored third-party code keeps its own licence, stated in its files.
