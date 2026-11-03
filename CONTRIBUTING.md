# Contribution guidance for STFspec

*Status: current contributor guidance. Date: 2026-11-03.*

Contributions of these kinds are welcome:

- The implementation of a library
- The proof of a law
- A fix for a discrepancy with the reference
- An improvement to a spec guidance document or to the checkers

**Start with [`AGENTS.md`](AGENTS.md).** It maps each kind of task to the documents to read and update, and to the checks to run. It also gives the authority order for documents that disagree. This file covers the principles that every contribution follows (§1–§5). Then it covers the workflow, review gate and roles for work by agents (§6), the Lean style (§7) and documentation (§8). The repository cites §1–§5 by number, so keep their numbers stable.

## 1. The golden rule: EEST zkevm conformance

The spec must pass the EEST zkevm fixtures for the guest (`statelessInputBytes → statelessOutputBytes`) at the release pinned in [`reference.toml`](reference.toml). **A pass of these fixtures is mandatory, and they are decisive wherever they speak.** Neither this spec, nor evm-sail, nor SpecRef, nor any client is more authoritative than the fixtures.

A finite corpus cannot determine behaviour on every uncovered input. Outside fixture coverage, the **pinned EELS source** at the same release commit governs. We read it as a specification, together with the pinned behaviour of its dependencies. Disagreements, accidental Python behaviour and unclear cases follow the discrepancy policy in [`STFSpec/informal/CONTRACT.md`](STFSpec/informal/CONTRACT.md) §6.

- Differential testing and fuzzing against other implementations are **bug-finding tools, not sources of truth**. We investigate each disagreement. The fixtures settle it. Where they are silent, the pinned EELS source settles it, and we report the gap upstream. Deference to another implementation never settles it.
- Proofs about the spec (for example witness soundness) add confidence in *properties*. They do not replace conformance.

## 2. Legibility is a first-class requirement

The spec is not a black box for optimization. Like EELS, whose choice of Python reflects this aim, it must support human discussion of the semantics. The aim is **formality, legibility and performance together, balanced deliberately**:

- Design decisions are explicit and open to inspection. Each one has a record in [`STFSpec/informal/DECISIONS.md`](STFSpec/informal/DECISIONS.md) with its rationale. As a result, a reader can assess the expected qualitative properties from the text, as well as from tests.
- Structure and names follow EELS wherever that does not conflict with totality or performance (§7.2). Where they conflict, document the deviation.
- A reader should be able to find the spec definition that corresponds to any EELS function. The reader should not need to understand an optimization before they read that definition.

## 3. Performance policy

Apply these performance rules:

- **Appropriate costs.** Choose appropriate operation *and aggregate* costs for the stated workloads and persistence requirements. Examples are persistent maps for revertible state, in-place linear buffers for memory and incremental trie hashing. Avoid unnecessary copies, repeated traversals and avoidable asymptotic degradation. O(n log n) for a sort or for the construction of a persistent map is ordinary, not a departure. Record justified departures from the expected bounds of a component (D18). The name of an algorithm alone does not establish suitability: measurements include allocation, conversions and composition.
- **Target:** within **10×** of native clients (evmone/revm-class) on the same workloads. **Aim for about 2×** where algorithmic improvements achieve it *while the spec stays simple*.
- **Order of preference:**
  1. A better algorithm or data structure that remains legible.
  2. Only later, and only if needed, a faster **representation** of a component. Prove it against the same model-based contract (D25), so that callers and their proofs stay unchanged. Never use compiler substitution: `@[csimp]` is banned (D21).
  3. Never micro-optimizations that sacrifice the purity or legibility of the spec text.
- The target is not a hard number fixed in advance. Measurements (the composed cost checks C1–C4 in [`STFSpec/informal/REVIEW.md`](STFSpec/informal/REVIEW.md#7-acceptance-criteria-proof-gates-composition-cases-replacement-and-cost-checks) §7) show where legibility and speed actually conflict. A decision record resolves each conflict explicitly.
- **Benchmarks** have a correctness gate, keep checksums out of the timed loop, and report the unit by which they divide the workload.

## 4. Structure and hygiene

The structure follows the [hex-dev](https://github.com/kim-em/hex-dev) pattern. Apply these structure and hygiene rules:

- **Packages.** The core (`STFSpec/`, the repository root package) is free of Mathlib and Batteries. Mathlib appears only in the bridge package `STFSpecMathlib/` (paired `…Mathlib` libraries) and the security package `STFSpecSecurity/`. VCV-io appears only in the security package. We enforce the boundary at the **package** level, because Lake lets a library import any module in the dependency closure of its package (verified 2026-09-28). Thus separate `lean_lib`s in one package would isolate nothing. Imports *between* core libraries follow [`scripts/boundaries.toml`](scripts/boundaries.toml), and `scripts/check_boundaries.py` checks them.
- **Implementations are final (D18).** Each implementation satisfies **all required properties**. These properties are a finite, named set in its component contract: semantics, totality, failure precedence, representation invariants, composition laws and the applicable resource requirements. Unproved obligations stay listed as open obligations.
  - Data structures must be **performance-appropriate**. Judge them against the relevant operation costs *and* the persistence requirements. A map with good lookups but a snapshot copy per frame is not appropriate.
  - A deviation must have a justification on grounds of legibility or drastic proof-friendliness. Record it in [`STFSpec/informal/DEBT.md`](STFSpec/informal/DEBT.md) with the expected workload, the complexity, the measured limitation, the reason and the replacement criterion.
  - The fastest possible implementation is not required now. Later improvements are contained representation replacements (D25).
- **`sorry`** is allowed only in the Mathlib and security packages during development. The core declaration check rejects it, also in proofs. Never use `axiom`.
- **No additional trust assumptions (D21).**
  - **What is checked:** the *proof dependencies that result*, whatever tactic produced them. No axiom beyond `propext`, `Quot.sound` and `Classical.choice` may appear, directly or transitively. Thus the check rejects `native_decide`, `bv_decide` and `decide +native`, because each adds a `…._native…` axiom. A renamed or wrapped tactic cannot bypass the check.
  - **Design rules:** `@[csimp]`, `implemented_by`, `extern`, `unsafe`, `partial` and `opaque` are banned too. `@[csimp]` and `opaque` are not *logically* unsound. The prohibition is about executable correspondence and transparency. Compiled code must run the definition that we reason about, and every definition must unfold.
  - **Enforcement:** `check-decls` (`scripts/check_decls.sh`), with regression fixtures. There is no exemption mechanism.
  - **Kernel replay:** `check-decls` and `#print axioms` trust the compiled environment. Thus a declaration that the kernel never checked passes both. An example is a declaration that an elaboration-time metaprogram adds through `addDecl` under `debug.skipKernelTC`, or through `addDeclWithoutChecking`. Logical soundness rests on kernel replay. CI checks every constant of every module of the libraries of each package again with `scripts/replay_kernel.sh`. The libraries are `STFSpec`, `STFSpecMathlib`, and `STFSpecSecurity` with `ToVCVio`. The script runs `lake env leanchecker`, and it fails unless the number of replayed modules equals the number of source modules. The replay omits the `scripts/` executables of the core package (native tests, benchmarks, checkers), because no library imports them and no result depends on them. `check-decls` audits them. Replay checks constants only: environment extensions, compiled IR and build-time IO are outside it. The regression fixture is `scripts/CheckDeclsTest/KernelBypass.lean`.
  - **Source-level controls in the core** (`scripts/check_boundaries.py`): from `Lean`, a core module may import only `Lean.Data.Json` and its submodules. These modules do not bring `addDecl`, the elaborator monads or the kernel environment into scope. The check reads imports with the fast import parser of Lake (`Lean.parseImports'`, run as `lean --deps-json` with the pinned toolchain), not with a pattern. Lake also uses that parser for build dependencies. It can over-report relative to the frontend, but it never under-reports without an error. If it cannot run or cannot read a header, the check fails. Check 4b is a tripwire against accidental or obvious metaprograms (`#eval`, `run_cmd`, `run_elab`, `run_meta`, `elab`, `initialize` and the others that it lists). The check also rejects the literal token `skipKernelTC`. These token checks are evadable, for example by a `macro` whose expansion builds a `#eval` command, or by an option name built from strings. They are not a soundness argument.
  - **Bit-vectors:** use the operation lemmas of Std, bit extensionality, `simp`, `omega` and arithmetic reasoning, plus plain `decide` for small concrete checks. `check-decls` checks the proofs that result.
- **Derived instances can introduce banned constructs.** `deriving BEq`/`Repr`/`DecidableEq` on a *nested* inductive (an RLP item or SSZ value that contains a `List` of itself) generates `partial` constants. Write structural instances by hand for such types (F17, [DECISIONS §3](STFSpec/informal/DECISIONS.md)).
- **Fast definitions without compiler substitution.** The performance-appropriate executable definition is sometimes not the most legible form, for example an unrolled keccak permutation or limb arithmetic. Then the component keeps a **legible reference definition beside it**, with the equality proved as an ordinary theorem. Callers use the executable definition, and readers and proofs can use the reference. Both definitions live in the module that owns them. The model-based contract (D25) states the definition against which we prove the laws.
- **Compiler replacements, also from dependencies.** `check-decls` enumerates every current and superseded `@[csimp]` theorem, because a dependency might register one that affects our code. Any such theorem in scope is a finding.
- **Release theorems.** Theorems for consumers must be free of `sorry`, also through their dependencies. Conditional theorems list their hypotheses explicitly and name the bridge that discharges each one. A pass of the development check does not claim that anyone instantiated a conditional theorem.
- **Toolchain.** Lean **v4.34.0**, pinned in `lean-toolchain` and `reference.toml`.
- **Trusted baseline ("pure Lean", D26).** The baseline has three parts: the pinned Lean kernel and its standard axioms, the Lean compiler, and the runtime primitives of Lean core. These primitives are GMP-backed `Nat`, `ByteArray`/`Array` operations and the other `@[extern]` implementations in Lean core. The baseline does **not** promise independence from the compiler or the runtime. All other code must be Lean source that passes `check-decls` on what we import, and that rule covers every third-party dependency. We choose the core dependencies separately from those of the Mathlib and security packages. A mathematical library that is useful for proofs need not become a core dependency.

## 5. Tests, review and automation

Apply these test, review and automation rules:

1. **Tests are necessary, not the definition.** A pass of the pinned fixtures is mandatory (§1). But the spec is not an artefact whose only purpose is to pass tests. It must state the protocol semantics faithfully and legibly in its own right.
   - No fixture-specific special cases.
   - No definition that follows what the corpus happens to exercise instead of what the reference means.
   - A change that keeps the tests green but makes a definition less faithful or less legible is a regression.
2. **Review is continuous and proportionate.** Reviews produce findings, recorded as gaps, discrepancies or decision questions. They are not a set of preconditions that always grows and that nothing could satisfy. The bar for progress is that known issues are *recorded, owned and not hidden*. The bar is not that every conceivable issue is closed first.
3. **Automate only what is strictly deterministic.** CI and other automated checks enforce properties with an exact, mechanical definition:
   - Builds and warnings
   - Import boundaries, and their agreement with the dependency table of the architecture
   - Compiled-declaration checks (axioms, `sorry`, `partial`/`opaque`, extern, `@[csimp]`) and kernel replay of every module of the libraries of each package
   - EELS coverage and ownership
   - Pins and checksums
   - Fixture conformance (once the conformance runner exists)
   - Freshness of generated documents
   - The regression tests of the checkers themselves

   Qualities without such a definition, such as legibility, argument quality, faithfulness of intent, or "enough" test coverage, are review matters. Heuristic CI checks never approximate them. For example, the spec checker verifies that an informal argument *has* its Claim/Premises/Argument/Open-obligations parts. It never judges whether the argument convinces a reader.
4. **The spec guidance documents are informal by design.** They are Markdown, written for the implementer, human or agent. They must be precise enough to determine exactly what to build. That precision covers behaviour, order, failures, ownership and the place of the module in the end-to-end spec. They do **not** need to typecheck, and they must not try to carry Lean proofs.
   - Lean-like signatures convey names, inputs, outputs, error channels and ownership. Implementation work fixes the exact Lean types, resolves placeholders and compiles the interfaces.
   - The informal correctness arguments are *sketches*: the claim, the premises, why it should hold, and what remains open. They tell the implementer what to prove and suggest how. The proofs themselves are the work of the implementer.
   - One question judges precision: can an implementer act on it without a guess?
5. **A finding that blocks requires a material reason.** Review the stated work item and the contracts and evidence that it relies on. A blocker identifies the requirement that governs, the affected behaviour or claim, and the evidence. That evidence is a counterexample, a failed required check, a source discrepancy, or a missing required proof or test case. Lean proofs that pass do not by themselves establish reference fidelity or compiled behaviour. But a request for more testing alone does not establish a defect either.
   - **Blockers:** these findings block:
     - Incorrect semantics or failure order
     - A violated public contract, trust boundary or applicable resource requirement
     - Missing required validation
     - Documentation or evidence that materially misstates what was implemented or verified

     A Python or shell defect qualifies when it changes required behaviour or makes evidence that the work item uses unreliable. Examples are the execution of the wrong oracle code, the authentication of different bytes and the loss of CLI reply framing.
   - **Improvements that do not block:** format, name preferences, unused imports, equivalent helper organization and cosmetic documentation edits. They also include speculative changes to strengthen the harness, absent an identified material consequence. These findings remain recommendations even when a style convention supports them. An author may fix them in this change or in a separate change for polish. A deferral needs no waiver, new issue or proof that the observation is wrong.
   - **Scope:** unrelated cleanup of tools belongs in a separate work item. Cleanup that predates this work item also belongs there. If a defect in a tool prevents required validation, fix that prerequisite separately or as a focused dependency. Do not expand the Lean contribution into a general rewrite of the harness. A failed required check still needs resolution. Propose additional general checks separately, with regression evidence. Do not make an unrelated new gate a condition of the current contribution. Open repository obligations block only the work or readiness claim that they affect. Cosmetic script lint may be advisory, but it is not a required merge gate.

## 6. Workflow and pull requests

### 6.1 Before you start

Read the documents for your task:

- **To implement a library:** read its spec guidance document in [`STFSpec/informal/modules/`](STFSpec/informal/modules). Read its gate and implementation contract in [`STFSpec/informal/REVIEW.md`](STFSpec/informal/REVIEW.md) §§3–4. Implement lower layers first. The dependency order is in [`STFSpec/informal/ARCHITECTURE.md`](STFSpec/informal/ARCHITECTURE.md) §3.
- **To change behaviour, an interface or a decision:** open an issue first. The spec guidance documents play the role that a blueprint plays elsewhere. Update the affected guidance documents in the same change as the code. If the change involves a design choice, record the question or decision in [`STFSpec/informal/DECISIONS.md`](STFSpec/informal/DECISIONS.md) in the same change. Its §5 tells you how.
- **If you find a disagreement with EELS or the fixtures:** record it in [`STFSpec/informal/DISCREPANCIES.md`](STFSpec/informal/DISCREPANCIES.md) with a reproducer (CONTRACT §6). An entry records the disagreement, but it never authorizes a deviation.

### 6.2 Pull request title and description

Titles use the format of the Lean community convention, with a wider subject rule:

```
<type>(<optional-scope>): <subject>
```

- **Types:** `feat`, `fix`, `doc`, `style`, `refactor`, `test`, `chore`, `perf`, `ci`.
- **Scope:** the library (`EthVmCore`), package (`mathlib`, `security`) or area (`informal`, `decisions`, `scripts`).
- **Subject:** an imperative phrase ("add strict RLP decoding") or a noun phrase for the result ("strict RLP decoding for headers"). A title is a label for the change, not a work step. The Lean convention permits only the imperative, but STFspec also permits the noun phrase. Do not use a past or third-person form such as "added" or "adds". Start the subject with a lowercase letter, and do not end it with a period.

The description gives the motivation and the change in behaviour or contract. It names the EELS sources that the change follows, the decisions or questions that it touches (by ID) and the related issues (`Closes #123`). A change that implements EELS operations includes their source-to-Lean rows (REVIEW §4). Use the [pull request template](.github/pull_request_template.md). It gives these contents and those of §6.5 as sections.

### 6.3 Checks

Run these commands before you open a pull request. CI runs the same commands:

```sh
lake build --wfail
lake build bytes-native-tests --wfail
lake exe check-decls BytesNativeTests && lake exe bytes-native-tests
lake build kzg-versioned-hash-native-tests --wfail
lake exe check-decls KzgVersionedHashNativeTests
lake exe kzg-versioned-hash-native-tests > .lake/kzg-versioned-hash-native.jsonl
python3 -B STFSpec/Conformance/Precompiles/kzg_versioned_hash_differential.py --check-target .lake/kzg-versioned-hash-native.jsonl
lake env lean --run scripts/KzgVersionedHashNativeTests.lean > .lake/kzg-versioned-hash-interpreted.jsonl
python3 -B STFSpec/Conformance/Precompiles/kzg_versioned_hash_differential.py --check-target .lake/kzg-versioned-hash-interpreted.jsonl
python3 -B scripts/test_kzg_versioned_hash_output_parser.py
python3 -B -O scripts/test_kzg_versioned_hash_output_parser.py
python3 -B scripts/gen_kzg_versioned_hash_guards.py --check
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
lake build pre-state-native-tests --wfail
lake exe check-decls PreStateNativeTests
lake exe pre-state-native-tests
lake build state-error-native-tests --wfail
lake exe check-decls StateErrorNativeTests
lake exe state-error-native-tests
lake build taylor-exponential-native-tests --wfail
lake exe check-decls TaylorExponentialNativeTests
lake exe taylor-exponential-native-tests > .lake/taylor.jsonl
python3 -B STFSpec/Conformance/Base/taylor_exponential_differential.py --check-target .lake/taylor.jsonl
lake build transaction-gas-allocation-native-tests --wfail
lake exe check-decls TransactionGasAllocationNativeTests
lake exe transaction-gas-allocation-native-tests > .lake/transaction-gas-allocation.jsonl
python3 -B STFSpec/Conformance/Vm/Core/transaction_gas_allocation_differential.py --check-target .lake/transaction-gas-allocation.jsonl
python3 -B scripts/test_transaction_gas_allocation_output_parser.py
python3 -B -O scripts/test_transaction_gas_allocation_output_parser.py
lake build transaction-gas-settlement-native-tests --wfail
lake exe check-decls TransactionGasSettlementNativeTests
lake exe transaction-gas-settlement-native-tests > .lake/transaction-gas-settlement.jsonl
python3 -B STFSpec/Conformance/Vm/Core/transaction_gas_settlement_differential.py --check-target .lake/transaction-gas-settlement.jsonl
python3 -B scripts/test_transaction_gas_settlement_output_parser.py
python3 -B -O scripts/test_transaction_gas_settlement_output_parser.py
lake build ssz-encode-native-tests --wfail
lake exe check-decls SszEncodeNativeTests
lake exe ssz-encode-native-tests > .lake/ssz-encode.txt
python3 -B STFSpec/Conformance/Codec/ssz_encode_differential.py --check-target .lake/ssz-encode.txt
python3 -B scripts/test_ssz_encode_output_parser.py
python3 -B -O scripts/test_ssz_encode_output_parser.py
lake build budget-policy-native-tests --wfail
lake exe check-decls BudgetPolicyNativeTests
python3 -B STFSpec/Conformance/Vm/Runner/budget_policy_model.py --write-input .lake/budget-policy-input.tsv
lake exe budget-policy-native-tests .lake/budget-policy-input.tsv > .lake/budget-policy.jsonl
python3 -B STFSpec/Conformance/Vm/Runner/budget_policy_model.py --check-target .lake/budget-policy.jsonl
python3 -B scripts/test_budget_policy_output_parser.py
python3 -B -O scripts/test_budget_policy_output_parser.py
lake build calldata-tokens-native-tests --wfail
lake exe check-decls CalldataTokensNativeTests
lake exe calldata-tokens-native-tests > .lake/calldata-tokens.jsonl
python3 -B STFSpec/Conformance/Block/count_tokens_differential.py --check-target .lake/calldata-tokens.jsonl
python3 -B scripts/test_count_tokens_output_parser.py
python3 -B -O scripts/test_count_tokens_output_parser.py
lake build witness-ancestors-native-tests --wfail
lake exe check-decls WitnessAncestorsNativeTests
lake exe witness-ancestors-native-tests > .lake/witness-ancestors.jsonl
python3 -B STFSpec/Conformance/State/witness_ancestors_differential.py --check-target .lake/witness-ancestors.jsonl
python3 -B scripts/test_witness_ancestors_output_parser.py
python3 -B -O scripts/test_witness_ancestors_output_parser.py
lake build stateless-output-native-tests --wfail
lake exe check-decls StatelessOutputNativeTests
lake exe stateless-output-native-tests > .lake/stateless-output.txt
python3 -B STFSpec/Conformance/Stateless/output_differential.py --check-target .lake/stateless-output.txt
python3 -B scripts/test_stateless_output_output_parser.py
python3 -B -O scripts/test_stateless_output_output_parser.py
lake build amsterdam-vm-native-tests --wfail
lake exe check-decls AmsterdamVmNativeTests
lake exe amsterdam-vm-native-tests > .lake/amsterdam-vm.json
python3 -B STFSpec/Conformance/Fork/amsterdam_vm_values.py --check-target .lake/amsterdam-vm.json
python3 -B scripts/test_amsterdam_vm_output_parser.py
python3 -B -O scripts/test_amsterdam_vm_output_parser.py
lake build deposit-data-native-tests --wfail
lake exe check-decls DepositDataNativeTests
lake exe deposit-data-native-tests > .lake/deposit-data.jsonl
python3 -B STFSpec/Conformance/Block/deposit_data_differential.py --check-target .lake/deposit-data.jsonl
python3 -B scripts/test_deposit_data_output_parser.py
python3 -B -O scripts/test_deposit_data_output_parser.py
lake build requests-hash-native-tests --wfail
lake exe check-decls RequestsHashNativeTests
lake exe requests-hash-native-tests > .lake/requests-hash.jsonl
python3 -B STFSpec/Conformance/Block/requests_hash_differential.py --check-target .lake/requests-hash.jsonl
python3 -B scripts/test_requests_hash_output_parser.py
python3 -B -O scripts/test_requests_hash_output_parser.py
lake build logs-bloom-native-tests --wfail
lake exe check-decls LogsBloomNativeTests
lake exe logs-bloom-native-tests > .lake/logs-bloom.jsonl
python3 -B STFSpec/Conformance/Block/logs_bloom_differential.py --check-target .lake/logs-bloom.jsonl
python3 -B scripts/test_logs_bloom_output_parser.py
python3 -B -O scripts/test_logs_bloom_output_parser.py
lake build reference-division-native-tests --wfail
lake exe check-decls ReferenceDivisionNativeTests
lake exe reference-division-native-tests > .lake/reference-division.jsonl
python3 -B STFSpec/Conformance/Field/reference_division_differential.py --check-target .lake/reference-division.jsonl
lake env lean --run scripts/ReferenceDivisionNativeTests.lean > .lake/reference-division-interpreted.jsonl
python3 -B STFSpec/Conformance/Field/reference_division_differential.py --check-target .lake/reference-division-interpreted.jsonl
python3 -B scripts/test_reference_division_output_parser.py
python3 -B -O scripts/test_reference_division_output_parser.py
lake build fixed-endian-bench --wfail
lake exe check-decls FixedEndianBench
lake build log-rope-bench --wfail
lake exe check-decls LogRopeBench
lake build packed-keccak-bench --wfail
lake exe check-decls PackedKeccakBench
python3 scripts/gen_packed_keccak.py --check
python3 scripts/test_packed_keccak_generator.py
python3 scripts/check_boundaries.py
scripts/check_decls.sh core
scripts/replay_kernel.sh core
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
python3 scripts/remap_citations.py --check && python3 scripts/test_remap_citations.py
lake build EthConformance fixture-records --wfail
python3 scripts/test_fixture_archive.py
```

These commands build and audit the fixed-endian, log-rope and packed-keccak benchmarks. They check that the output of the packed-keccak generator is fresh, and they run its regression test. Elapsed-time measurements remain manual. The commands build, audit and execute the Taylor producer, and then they check its complete captured stdout against the handwritten literals. The source-coupling check is separate.

For a change to `STFSpecMathlib/` or `STFSpecSecurity/`, also run `lake build --wfail` in that directory. Then run `scripts/check_decls.sh mathlib` and `scripts/replay_kernel.sh mathlib`, or the same commands with `security`.

Regenerate these files, and never edit them by hand:

- `STFSpec/informal/GAPS.md`, `REFERENCE-RECORDS.md` and `eels-inventory.json`
- `citation-remap.json` and `citation-remap-manual.txt`, with `scripts/remap_citations.py --apply` (no clone needed)
- The README diagram

`remap_citations.py --check` fails in either case:

- A recorded pre-remap EELS citation reappears in its recorded context.
- A listed citation changed or is absent.

Resolve each entry explicitly:

- If the citation is fixed or removed, use `--apply --drop-resolved DOC:LINE`.
- If the citation still refers to the old commit but moved within its document, use `--apply --relist DOC:LINE DOC:NEWLINE`. Use the same route if its context or format changed.
- For a move to another document, use `--drop-resolved` and read the new line with `--since`.
- If the citation is already correct at the pin, use `--apply --confirm DOC:LINE` with `--eels`.

The check cannot recognize old line numbers in new or edited prose. A branch that predates the remap (GAPS-CROSSCUTTING X16) must merge main and resolve conflicted lines to its own pre-remap numbers. After that merge, you must run `python3 -I scripts/remap_citations.py --apply --since <merged main commit> --eels <execution-specs clone>` and commit the result. The script's docstring states its rules.

### 6.4 Review and commit gate

Every change is a **work item**: a self-contained change that one reviewer can hold in full, for example one type with its operations and laws. Commit a work item only when all of these conditions hold for the exact tree that you commit:

- Every check in §6.3 passes, together with the tests of the item. These tests are the deterministic and failure-order cases that its spec guidance lists (§4 of each guidance document). They include a differential comparison against EELS where the guidance requires one.
- An **independent adversarial review** of that exact diff (§6.6, *adversarial reviewer*) found it **clean**. That verdict means that the required checks ran and that no unresolved finding under §5.5 blocks the change. Other recommendations may remain. Fix a blocker, or rebut it with written evidence in the pull request. A deferred nit needs no rebuttal. Any change after the review needs another review.
- The documentation is current (§6.5).
- The commit message follows the conventions of §6.2 and summarizes the change, the evidence and the review verdicts.

A commit never contains `sorry` in the core, a banned construct (§4), a failed or skipped check, or unreviewed code.

### 6.5 Pull requests, stacks and documentation

Follow these contribution rules:

- **Granularity:** one pull request for each larger component (typically a library, or a coherent slice of one), made of several work-item commits.
- **Stacks:** the branch of a pull request starts from the branch of the pull request that it depends on. It starts from `main` if it depends on nothing unmerged. Set the base of the pull request to that branch, and write "Depends on #N" in its description. Work continues on top of open pull requests, which may be reviewed and merged later, possibly in batches. After a parent changes, rebase its descendants (`git rebase --update-refs`), and push them with `--force-with-lease`. After a maintainer merges a parent, retarget the child to `main` and rebase it. Never push to `main`, and never force-push it.
- **Description:** these contents:
  - The contents of §6.2
  - The source-to-Lean rows
  - The check and test results
  - A summary of the review verdicts
  - The documentation that the change updates
  - The position of the pull request in its stack
- **Documentation in the same pull request:**
  - The spec guidance of the implemented library: source-to-Lean rows and statuses (REVIEW §4), §10 gaps, and anything that the implementation showed to be wrong or imprecise
  - `STFSpec/informal/DECISIONS.md` for any new open question, or for a disposition that the maintainers approved
  - Regenerated generated files (`scripts/gen_gaps.py` and the others in §6.3)
  - REVIEW §6 and the README status line when the readiness of a layer changes
  - CONTRACT, DISCREPANCIES, ARCHITECTURE and COMPOSITION whenever the change touches what they own
- **Maintainers decide:** the acceptance of decisions and changes to their status, protocol deviations, new dependencies (D26), changes to interfaces that consumers rely on, and merges.

### 6.6 Roles for agent-driven work

Agents in any harness can do the work. An **orchestrator** plans work items and briefs one agent for each role. It evaluates the results itself: it runs the checks again, reads the diff and spot-checks fidelity against EELS. Only the orchestrator commits and opens pull requests under §6.4–§6.5.

Every agent reads [`AGENTS.md`](AGENTS.md), this file and the documents that its brief names. Each agent gets a self-contained brief. The brief gives the work item, its scope and allowed files, the guidance and decisions that govern it, the checks and the report format. Agents other than the orchestrator never commit, push or open pull requests. Work items that run in parallel use separate worktrees.

Use these roles:

- **Researcher** (read-only on tracked files). It answers one question about the pinned EELS source, its dependencies, the fixtures, literature or prior art. It marks each claim verified (code read at the pin, command run, measurement taken) or inferred. It cites EELS as `file:line` at the pin. It proposes changes to decisions or guidance, but it never makes them.
- **Prototyper.** It settles a design question or measurement before the core depends on it. It works in isolated throwaway code outside the core, in a separate package that requires nothing from the core. It separates what runs from what it assumes. It gives exact reproduction commands and a measurement method that complies with §3. It proposes a disposition with evidence.
- **Implementer.** It implements exactly one work item on its branch: definitions, laws, proofs and tests. It follows the spec guidance and REVIEW §3, §4 and §7, under §4 and §7 of this file. If the guidance is wrong, ambiguous or incomplete, it stops and reports the problem. It does not fill the gap by convention. It updates the documentation (§6.5). It reports the exact check output, the source-to-Lean rows, the laws proved and the open obligations.
- **Conformance engineer.** It builds the `EthConformance` runners, the `core` profile, replay records and differential harnesses against EELS, as its spec guidance specifies. Fixtures are decisive (§1): a mismatch is a failure of the spec, and it never gets a special case. Use the tools to authenticate the archive before use. CI jobs are deterministic and bounded.
- **Adversarial reviewer** (never edits). It judges only the diff, the brief and the documents that govern the change, without the context of the implementer. It tries to break the change in these areas:
  - Fidelity to the pinned EELS, with every failure condition and its order
  - The stated laws, and the one-owner rule
  - Totality and the hard rules (it runs `scripts/check_decls.sh` and `scripts/check_boundaries.py`)
  - Test adequacy (an input that passes the tests but is wrong)
  - The data structures against the guidance or DEBT
  - Documentation drift

  It runs the checks again itself. It returns **clean** or **not clean** as §6.4 defines, with findings classified under §5.5: **"blocking"**, **"should fix"** (a recommendation), or **"nit"** (polish). A blocker names the requirement that governs it, the affected behaviour or claim, file:line and evidence.

  The report lists what the reviewer could not verify, and it keeps findings about tools distinct from Lean semantic findings. A correctly classified script nit cannot turn a clean Lean work item into a **not clean** verdict. The reviewer never reports clean on unrun required checks. Items that other modules depend on (shared types, seams, laws that other modules use) get two independent reviewers.
- **Polisher.** It improves accepted work for legibility and style (§2, §7) without changes to behaviour, public signatures or stated laws. Its work covers names, structure, helper ownership, proof clarity, docstrings and stale documentation. It works on one theme per pass, and its result needs another review.

Harness-specific configuration (for example agent definition files) is local to each contributor. Contributors do not commit it, and it only points to this section.

An author who uses an agent or another tool stays responsible for the result. These tasks remain with the author:

- Read the main theorem or law statements and the full description before you request review.
- Keep session notes, plans and handoff notes out of the contribution.
- Replace a temporary plan identifier that readers cannot access with an explanation or a maintained identifier.
- Coordinate concurrent tool runs, so that they do not open two pull requests for the same target.

## 7. Lean style and names

We follow the [Lean community conventions for style and names](https://leanprover-community.github.io/contribute/index.html) (as mathlib does), with the project-specific rules below. Where this file and the community guide differ, this file wins. When in doubt, match the adjacent code.

### 7.1 Files and modules

Use these file and module conventions:

- One Lake library for each component, rooted as in [`scripts/boundaries.toml`](scripts/boundaries.toml). For example, library `EthVmCore` is the module tree `STFSpec.Vm.Core`. File names are `UpperCamelCase.lean`.
- Every file starts with the header

  ```lean
  /-
  Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
  -/
  ```

  then imports, then a module docstring (§8.1). Do not add a separate line that attributes the file to an AI tool. The header credits the STFspec contributors, and it has no other author line.
- Import only what the file uses, and only within the allowed dependencies of the library.

### 7.2 Names

Use these name conventions:

- **EELS names first (§2).** A Lean definition that corresponds to an EELS function keeps its name, converted to Lean case: `process_message_call` → `processMessageCall`, `get_storage_original` → `getStorageOriginal`. EELS classes keep their names (`Account`, `GasMeter`). Module-level protocol constants keep their EELS spelling (`STACK_DEPTH_LIMIT`), so that a search of the reference finds them. Fields of parameter records use the lowerCamelCase form of the EELS name (`GasCosts.CALL_VALUE` → `GasCosts.callValue`, `COST_PER_STATE_BYTE` → `costPerStateByte`). The spec guidance document records each name that departs from EELS.
- **Otherwise the community rules apply:** `UpperCamelCase` for types, structures and classes, `lowerCamelCase` for functions and terms, and `snake_case` for theorems and proofs. Treat acronyms as words (`RlpItem`, not `RLPItem`). Name Prop-valued adjective classes with `Is` (`IsCanonical`).
- **Theorem names describe the statement** with the community conventions: `_of_` for hypotheses, `ext`, `iff`, `inj`, `mono`, `left`/`right`, and `le`/`lt` rather than `ge`/`gt`. Law names follow the operation that they describe: `getStorage_setStorage_same`, `toBitVec_add`.
- **No provenance in names.** Name a declaration for what it says, never for where it came from. Do not use EELS line numbers, paper or section numbers, or decision, question or gate IDs (`d5_...`, `g2_progress`). Cite those in docstrings instead (§8).
- **Variable conventions.** These names add to the community names such as `α`, `h` and `n`:
  - `m`: the hash-query monad (`{m} [Monad m] [KeccakQuery m]`)
  - `σ`: a mathematical state
  - `ps`: a `PreState m`
  - `d`: a `BlockDiff`
  - `cfg`: a configuration record
  - `consts`: the `HashConsts` record
  - `f`: a frame
  - `w`: a world

  Use descriptive names where a single letter would be ambiguous.
- **Constants notation (F20).** At seams that consume constants, use `variable (consts : HashConsts)` and local notation with EELS names:

  ```lean
  variable (consts : HashConsts)
  local notation "EMPTY_CODE_HASH" => consts.emptyCodeHash
  local notation "EMPTY_TRIE_ROOT" => consts.emptyTrieRoot
  local notation "EMPTY_OMMER_HASH" => consts.emptyOmmerHash
  local notation "TRANSFER_TOPIC" => consts.transferTopic
  ```

  Where the record already lives in a state or backend, read its constants field. A function that runs before that context exists, such as `validateHeader`, takes `consts` explicitly, and the notation names its fields. Bind context notation in its own section, so that it projects the stored record and does not capture an outer `consts`.

### 7.3 Format

Use this source format:

- Keep lines under 100 characters. Use two-space indentation, no tabs and no end-of-line whitespace.
- Put spaces around `:`, `:=` and infix operators. An operator that breaks a line ends the line and does not start the next one.
- Write `fun x ↦ …`, `where` syntax for instances and structures, and a space after binders (`∀ x,`).
- Put hypotheses to the left of the colon (`(h : P) : Q`) when the proof introduces them.
- Put `by` at the end of the previous line, with the tactic block indented. Do not put blank lines inside definitions or proofs. Avoid `;` between tactics except in short single-line sequences.
- Prefer `<|` and `|>` to deep parentheses.

### 7.4 Definitions, contracts and proofs

Apply these implementation rules:

- **Totality.** Every definition is total. Recursion is structural or well-founded with an explicit measure (`termination_by`, and `decreasing_by` where needed). Fuel appears only where [ARCHITECTURE](STFSpec/informal/ARCHITECTURE.md) §5.5 puts it. Do not use `get!`, `panic!` or `unreachable!`. Represent impossible states in the types, or return a typed error (D14).
- **Contracts, not internals.** The callers of a component use its public model laws and equations (ARCHITECTURE §4). In a proof, do not unfold the container internals or the compiler-generated equations of another component. Keep representation types behind a `structure` (for example `U256`) instead of an `abbrev`, so that their instances cannot leak.
- **`simp` sets are small and opt-in**, one for each component (`simp [Memory.laws]`). Do not add broad `@[simp]` lemmas that expand whole state structures.
- **Automation on well-scoped goals.** `simp`, `omega`, `decide` (small, concrete) and similar tactics are fine as terminal steps or after an explicit transformation. Profile a slow proof before you rewrite it. Do not squeeze stable terminal `simp` calls without a measured reason.
- **Monads and errors.** Follow the three failure channels (D14): frame exits as values, protocol rejections as typed errors and internal failures as `InternalError`. Every hashing interface stays generic in `m` (D5), and only public entry points specialize to `Id`.

### 7.5 Names and deprecation

Until the first tagged release, rename freely, but update every caller and the spec guidance in the same change. After a release, keep a deprecated alias for renamed public declarations:

```lean
@[deprecated (since := "YYYY-MM-DD")] alias oldName := newName
```

## 8. Documentation and citations

### 8.1 Docstrings

Use these docstring conventions:

- **Module docstring.** Each file opens with a `/-! … -/` block. The block gives a title and summary, the library of the file, and a `Spec guidance:` line that names its document in `STFSpec/informal/modules/`.
- **Declarations.** Every public definition, and every law or theorem that callers rely on, has a `/-- … -/` docstring. A definition that implements an EELS operation cites it as `src/ethereum/…/file.py:line` at the pinned commit (the source-to-Lean row, REVIEW §4).
- Use backticks for Lean names. Use `/-! ### Title -/` comments to divide long files into sections.

### 8.2 Citations

Use these citation conventions:

- **The reference:** cite EELS by path and line at the commit in `reference.toml`, and cite EIPs by number (`EIP-7702`).
- **Papers and books:** cite them in a `## References` section of the module docstring, as `* Author(s), *Title*, venue year`, and refer to them in text by author and year. Link a public version where one exists. Never add copies of copyrighted papers or books to the repository.
- **Other implementations and specifications** (evm-sail, clients, cryptography-specs): you may link them directly, with a commit where the claim depends on one.

### 8.3 Prose

[`WRITING.md`](WRITING.md) sets the standard for repository prose: documents, docstrings, comments, commit messages, pull request descriptions, issue text and review reports. It applies to every author, human or agent. It uses ASD-STE100 Simplified Technical English to correct defects in the current prose, and it marks each adaptation for technical text.

Draft or revise that prose with the [prose workflow](WRITING-WORKFLOW.md), and use the terms of the [vocabulary](WRITING-VOCABULARY.md). A style edit keeps claims, hypotheses, uncertainty and requirement strength unchanged.

Legibility is a review matter (§5.3), so no CI check applies the standard. Under §5.5, a prose finding is a recommendation that does not block, unless the text materially misstates what was implemented or verified. The advisory script `scripts/writing_hints.py` reports some patterns for authors, but its output is neither required nor sufficient.

## 9. Code of conduct

Treat other contributors with respect. STFspec follows the principles of the [mathlib Code of Conduct](https://github.com/leanprover-community/mathlib4/blob/master/CODE_OF_CONDUCT.md). Participation in the project (code, issues, discussions) means that you agree to follow them. Report unacceptable behaviour to the maintainers.

## 10. Licence

STFspec is licensed under either of the [Apache License, Version 2.0](LICENSE-APACHE) or the [MIT licence](LICENSE-MIT), at your option. Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in this work is dual licensed as above, without any additional terms or conditions. Vendored third-party code keeps its own licence, stated in its files.
