# Contributing to STFspec

*Status: current contributor guidance. Date: 2026-11-06.*

Contributions of these kinds are welcome:

- The implementation of a library
- The proof of a law
- A fix for a discrepancy with the reference
- An improvement to a spec guidance document or to the checkers

**Start with [`AGENTS.md`](AGENTS.md).** It maps each kind of task to the documents to read and update, and to the checks to run. It also gives the authority order for documents that disagree. This file covers the principles that every contribution follows (§1–§5). Then it covers the workflow, review gate and roles for work by agents (§6), the Lean style (§7) and documentation (§8). The repository cites §1–§5 by number, so keep their numbering stable.

## 1. The golden rule: EEST zkevm conformance

The spec must pass the EEST zkevm fixtures for the guest (`statelessInputBytes → statelessOutputBytes`) at the release pinned in [`reference.toml`](reference.toml). **A pass of these fixtures is mandatory, and they are decisive wherever they speak.** Neither this spec, nor evm-sail, nor SpecRef, nor any client is more authoritative than the fixtures.

A finite corpus cannot determine behaviour on every uncovered input. Outside fixture coverage, the **pinned EELS source** at the same release commit governs. We read it as a specification, together with the pinned behaviour of its dependencies. Disagreements, accidental Python behaviour and unclear cases follow the discrepancy policy in [`STFSpec/informal/CONTRACT.md`](STFSpec/informal/CONTRACT.md) §6.

- Differential testing and fuzzing against other implementations are **bug-finding tools, not sources of truth**. We investigate each disagreement. The fixtures settle it. Where they are silent, a reading of EELS settles it, and we report the gap upstream. Deference to another implementation never settles it.
- Proofs about the spec (for example witness soundness) add confidence in *properties*. They do not replace conformance.

## 2. Legibility is a first-class requirement

The spec is not a black box for optimization. Like EELS, whose choice of Python reflects this aim, it must support human discussion of the semantics. The aim is **formality, legibility and performance together, balanced deliberately**:

- Design decisions are explicit and open to inspection. Each one has a record in [`STFSpec/informal/DECISIONS.md`](STFSpec/informal/DECISIONS.md) with its rationale. As a result, a reader can check the qualitative properties that we expect of the spec by reading, not only by testing.
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
  - **Kernel replay:** `check-decls` and `#print axioms` trust the compiled environment. Thus a declaration that the kernel never checked passes both. An example is a declaration that an elaboration-time metaprogram adds through `addDecl` under `debug.skipKernelTC`, or through `addDeclWithoutChecking`. Logical soundness rests on kernel replay. CI re-checks every constant of every module of the libraries of each package with `scripts/replay_kernel.sh`. The libraries are `STFSpec`, `STFSpecMathlib`, and `STFSpecSecurity` with `ToVCVio`. The script runs `lake env leanchecker`, and it fails unless the number of replayed modules equals the number of source modules. The replay omits the `scripts/` executables of the core package (native tests, benchmarks, checkers), because no library imports them and no result depends on them. `check-decls` audits them. Replay checks constants only: environment extensions, compiled IR and build-time IO are outside it. The regression fixture is `scripts/CheckDeclsTest/KernelBypass.lean`.
  - **Source-level controls in the core** (`scripts/check_boundaries.py`): from `Lean`, a core module may import only `Lean.Data.Json` and its submodules. These modules do not bring `addDecl`, the elaborator monads or the kernel environment into scope. The check reads imports with the fast import parser of Lake (`Lean.parseImports'`, run as `lean --deps-json` with the pinned toolchain), not with a pattern. Lake also uses that parser for build dependencies. The parser can over-report relative to the frontend, but it never under-reports without an error. If it cannot run or cannot read a header, the check fails. Check 4b is a tripwire against accidental or obvious metaprograms (`#eval`, `run_cmd`, `run_elab`, `run_meta`, `elab`, `initialize` and the others that it lists). The check also rejects the literal token `skipKernelTC`. These token checks are evadable, for example by a `macro` whose expansion builds a `#eval` command, or by an option name built from strings. They are not a soundness argument.
  - **Bit-vectors:** use the operation lemmas of Std, bit extensionality, `simp`, `omega` and arithmetic reasoning, plus plain `decide` for small concrete checks. `check-decls` checks the proofs that result.
- **Derived instances can introduce banned constructs.** `deriving BEq`/`Repr`/`DecidableEq` on a *nested* inductive (an RLP item or SSZ value that contains a `List` of itself) generates `partial` constants. Write structural instances by hand for such types (F17, [DECISIONS §3](STFSpec/informal/DECISIONS.md)).
- **Fast definitions without compiler substitution.** The performance-appropriate executable definition is sometimes not the most legible form, for example an unrolled keccak permutation or limb arithmetic. Then the component keeps a **legible reference definition beside it**, with the equality proved as an ordinary theorem. Callers use the executable definition, and readers and proofs can use the reference. Both definitions live in the module that owns them. The model-based contract (D25) states the definition against which we prove the laws.
- **Compiler replacements, also from dependencies.** `check-decls` enumerates every current and superseded `@[csimp]` theorem, because a dependency might register one that affects our code. Any such theorem in scope is a finding.
- **Release theorems.** Theorems for consumers must be free of `sorry`, also through their dependencies. Conditional theorems list their hypotheses explicitly and name the bridge that discharges each one. A pass of the development check does not claim that anyone instantiated a conditional theorem.
- **Toolchain.** Lean **v4.35.0**, pinned in the three `lean-toolchain` files and in `reference.toml` `[lean]` (DECISIONS P3).
- **Trusted baseline ("pure Lean", D26).** The baseline has three parts: the pinned Lean kernel and its standard axioms, the Lean compiler, and the runtime primitives of Lean core. These primitives are GMP-backed `Nat`, `ByteArray`/`Array` operations and the other `@[extern]` implementations in Lean core. The baseline does **not** promise independence from the compiler or the runtime. All other code must be Lean source that passes `check-decls` on what we import, and that rule covers every third-party dependency. We choose the core dependencies separately from those of the Mathlib and security packages. A mathematical library that is useful for proofs need not become a core dependency.

## 5. Tests, review and automation

1. **Tests are necessary, not the definition.** Passing the pinned fixtures is mandatory (§1). But the spec is not a test-passing artefact: it must carry meaning in its own right, as a legible, faithful statement of the protocol's semantics.
   - No fixture-specific special cases.
   - No definition shaped by what the corpus happens to exercise rather than by what the reference means.
   - A change that keeps the tests green but makes a definition less faithful or less legible is a regression.
2. **Review is continuous and proportionate.** Reviews produce findings, recorded as gaps, discrepancies or decision questions. They are not an ever-growing set of preconditions that nothing could satisfy. The bar for proceeding is that known issues are *recorded, owned and not hidden*, not that every conceivable issue is closed first.
3. **Automate only what is strictly deterministic.** CI and other automated checks enforce properties with an exact, mechanical definition:
   - builds and warnings;
   - import boundaries, and their agreement with the architecture's dependency table;
   - compiled-declaration checks (axioms, `sorry`, `partial`/`opaque`, extern, `@[csimp]`) and kernel replay of every module of each package's libraries;
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

Install [uv](https://docs.astral.sh/uv/getting-started/installation/) for repository Python tooling. Run checks from the root with `uv run --no-project --python 3.12 python`. These standard-library checks need no project environment. CI pins uv 0.13.6 and uses Python 3.12, including for scripts that require `tomllib`.

Create the frozen EELS environment with `uv sync --frozen --no-dev` in its reference checkout. Reference acquisition calls that interpreter directly, as `EELS/.venv/bin/python -I -B`, with the flags required by `scripts/differential.py` or its conformance harness.

Run these commands before you open a pull request. CI runs the same commands:

```sh
lake build --wfail
lake build bytes-native-tests --wfail
lake exe check-decls BytesNativeTests && lake exe bytes-native-tests
lake build kzg-versioned-hash-native-tests --wfail
lake exe check-decls KzgVersionedHashNativeTests
lake exe kzg-versioned-hash-native-tests > .lake/kzg-versioned-hash-native.jsonl
uv run --no-project --python 3.12 python -B STFSpec/Conformance/Precompiles/kzg_versioned_hash_differential.py --check-target .lake/kzg-versioned-hash-native.jsonl
lake env lean --run scripts/KzgVersionedHashNativeTests.lean > .lake/kzg-versioned-hash-interpreted.jsonl
uv run --no-project --python 3.12 python -B STFSpec/Conformance/Precompiles/kzg_versioned_hash_differential.py --check-target .lake/kzg-versioned-hash-interpreted.jsonl
uv run --no-project --python 3.12 python -B scripts/test_kzg_versioned_hash_output_parser.py
uv run --no-project --python 3.12 python -B -O scripts/test_kzg_versioned_hash_output_parser.py
uv run --no-project --python 3.12 python -B scripts/gen_kzg_versioned_hash_guards.py --check
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
uv run --no-project --python 3.12 python -B STFSpec/Conformance/Base/taylor_exponential_differential.py --check-target .lake/taylor.jsonl
lake build transaction-gas-allocation-native-tests --wfail
lake exe check-decls TransactionGasAllocationNativeTests
lake exe transaction-gas-allocation-native-tests > .lake/transaction-gas-allocation.jsonl
uv run --no-project --python 3.12 python -B STFSpec/Conformance/Vm/Core/transaction_gas_allocation_differential.py --check-target .lake/transaction-gas-allocation.jsonl
uv run --no-project --python 3.12 python -B scripts/test_transaction_gas_allocation_output_parser.py
uv run --no-project --python 3.12 python -B -O scripts/test_transaction_gas_allocation_output_parser.py
lake build transaction-gas-settlement-native-tests --wfail
lake exe check-decls TransactionGasSettlementNativeTests
lake exe transaction-gas-settlement-native-tests > .lake/transaction-gas-settlement.jsonl
uv run --no-project --python 3.12 python -B STFSpec/Conformance/Vm/Core/transaction_gas_settlement_differential.py --check-target .lake/transaction-gas-settlement.jsonl
uv run --no-project --python 3.12 python -B scripts/test_transaction_gas_settlement_output_parser.py
uv run --no-project --python 3.12 python -B -O scripts/test_transaction_gas_settlement_output_parser.py
lake build ssz-encode-native-tests --wfail
lake exe check-decls SszEncodeNativeTests
lake exe ssz-encode-native-tests > .lake/ssz-encode.txt
uv run --no-project --python 3.12 python -B STFSpec/Conformance/Codec/ssz_encode_differential.py --check-target .lake/ssz-encode.txt
uv run --no-project --python 3.12 python -B scripts/test_ssz_encode_output_parser.py
uv run --no-project --python 3.12 python -B -O scripts/test_ssz_encode_output_parser.py
lake build budget-policy-native-tests --wfail
lake exe check-decls BudgetPolicyNativeTests
uv run --no-project --python 3.12 python -B STFSpec/Conformance/Vm/Runner/budget_policy_model.py --write-input .lake/budget-policy-input.tsv
lake exe budget-policy-native-tests .lake/budget-policy-input.tsv > .lake/budget-policy.jsonl
uv run --no-project --python 3.12 python -B STFSpec/Conformance/Vm/Runner/budget_policy_model.py --check-target .lake/budget-policy.jsonl
uv run --no-project --python 3.12 python -B scripts/test_budget_policy_output_parser.py
uv run --no-project --python 3.12 python -B -O scripts/test_budget_policy_output_parser.py
lake build calldata-tokens-native-tests --wfail
lake exe check-decls CalldataTokensNativeTests
lake exe calldata-tokens-native-tests > .lake/calldata-tokens.jsonl
uv run --no-project --python 3.12 python -B STFSpec/Conformance/Block/count_tokens_differential.py --check-target .lake/calldata-tokens.jsonl
uv run --no-project --python 3.12 python -B scripts/test_count_tokens_output_parser.py
uv run --no-project --python 3.12 python -B -O scripts/test_count_tokens_output_parser.py
lake build pre-state-account-native-tests --wfail
lake exe check-decls scripts.PreStateAccountNativeTests
lake exe pre-state-account-native-tests > .lake/pre-state-account-native.jsonl
lake env lean --run scripts/PreStateAccountNativeTests.lean > .lake/pre-state-account-interpreted.jsonl
uv run --no-project --python 3.12 python -B STFSpec/Conformance/State/pre_state_account_differential.py --check-target .lake/pre-state-account-native.jsonl
uv run --no-project --python 3.12 python -B STFSpec/Conformance/State/pre_state_account_differential.py --check-target .lake/pre-state-account-interpreted.jsonl
uv run --no-project --python 3.12 python -B scripts/test_pre_state_account_output_parser.py
uv run --no-project --python 3.12 python -B -O scripts/test_pre_state_account_output_parser.py
uv run --no-project --python 3.12 python -B scripts/test_pre_state_account_source.py
uv run --no-project --python 3.12 python -B -O scripts/test_pre_state_account_source.py
lake build pre-state-account-default-native-tests --wfail
lake exe check-decls scripts.PreStateAccountDefaultNativeTests
lake exe pre-state-account-default-native-tests > .lake/pre-state-account-default-native.jsonl
lake env lean --run scripts/PreStateAccountDefaultNativeTests.lean > .lake/pre-state-account-default-interpreted.jsonl
uv run --no-project --python 3.12 python -B STFSpec/Conformance/State/pre_state_account_default_differential.py --check-target .lake/pre-state-account-default-native.jsonl
uv run --no-project --python 3.12 python -B STFSpec/Conformance/State/pre_state_account_default_differential.py --check-target .lake/pre-state-account-default-interpreted.jsonl
uv run --no-project --python 3.12 python -B scripts/test_pre_state_account_default_output_parser.py
uv run --no-project --python 3.12 python -B -O scripts/test_pre_state_account_default_output_parser.py
uv run --no-project --python 3.12 python -B scripts/test_pre_state_account_default_source.py
uv run --no-project --python 3.12 python -B -O scripts/test_pre_state_account_default_source.py
lake build witness-ancestors-native-tests --wfail
lake exe check-decls WitnessAncestorsNativeTests
lake exe witness-ancestors-native-tests > .lake/witness-ancestors.jsonl
uv run --no-project --python 3.12 python -B STFSpec/Conformance/State/witness_ancestors_differential.py --check-target .lake/witness-ancestors.jsonl
uv run --no-project --python 3.12 python -B scripts/test_witness_ancestors_output_parser.py
uv run --no-project --python 3.12 python -B -O scripts/test_witness_ancestors_output_parser.py
lake build stateless-output-native-tests --wfail
lake exe check-decls StatelessOutputNativeTests
lake exe stateless-output-native-tests > .lake/stateless-output.txt
uv run --no-project --python 3.12 python -B STFSpec/Conformance/Stateless/output_differential.py --check-target .lake/stateless-output.txt
uv run --no-project --python 3.12 python -B scripts/test_stateless_output_output_parser.py
uv run --no-project --python 3.12 python -B -O scripts/test_stateless_output_output_parser.py
lake build amsterdam-vm-native-tests --wfail
lake exe check-decls AmsterdamVmNativeTests
lake exe amsterdam-vm-native-tests > .lake/amsterdam-vm.json
uv run --no-project --python 3.12 python -B STFSpec/Conformance/Fork/amsterdam_vm_values.py --check-target .lake/amsterdam-vm.json
uv run --no-project --python 3.12 python -B scripts/test_amsterdam_vm_output_parser.py
uv run --no-project --python 3.12 python -B -O scripts/test_amsterdam_vm_output_parser.py
lake build deposit-data-native-tests --wfail
lake exe check-decls DepositDataNativeTests
lake exe deposit-data-native-tests > .lake/deposit-data.jsonl
uv run --no-project --python 3.12 python -B STFSpec/Conformance/Block/deposit_data_differential.py --check-target .lake/deposit-data.jsonl
uv run --no-project --python 3.12 python -B scripts/test_deposit_data_output_parser.py
uv run --no-project --python 3.12 python -B -O scripts/test_deposit_data_output_parser.py
lake build requests-hash-native-tests --wfail
lake exe check-decls RequestsHashNativeTests
lake exe requests-hash-native-tests > .lake/requests-hash.jsonl
uv run --no-project --python 3.12 python -B STFSpec/Conformance/Block/requests_hash_differential.py --check-target .lake/requests-hash.jsonl
uv run --no-project --python 3.12 python -B scripts/test_requests_hash_output_parser.py
uv run --no-project --python 3.12 python -B -O scripts/test_requests_hash_output_parser.py
lake build logs-bloom-native-tests --wfail
lake exe check-decls LogsBloomNativeTests
lake exe logs-bloom-native-tests > .lake/logs-bloom.jsonl
uv run --no-project --python 3.12 python -B STFSpec/Conformance/Block/logs_bloom_differential.py --check-target .lake/logs-bloom.jsonl
uv run --no-project --python 3.12 python -B scripts/test_logs_bloom_output_parser.py
uv run --no-project --python 3.12 python -B -O scripts/test_logs_bloom_output_parser.py
lake build reference-division-native-tests --wfail
lake exe check-decls ReferenceDivisionNativeTests
lake exe reference-division-native-tests > .lake/reference-division.jsonl
uv run --no-project --python 3.12 python -B STFSpec/Conformance/Field/reference_division_differential.py --check-target .lake/reference-division.jsonl
lake env lean --run scripts/ReferenceDivisionNativeTests.lean > .lake/reference-division-interpreted.jsonl
uv run --no-project --python 3.12 python -B STFSpec/Conformance/Field/reference_division_differential.py --check-target .lake/reference-division-interpreted.jsonl
uv run --no-project --python 3.12 python -B scripts/test_reference_division_output_parser.py
uv run --no-project --python 3.12 python -B -O scripts/test_reference_division_output_parser.py
lake build header-carriers-native-tests --wfail
lake exe check-decls HeaderCarriersNativeTests
uv run --no-project --python 3.12 python -B STFSpec/Conformance/Block/header_carrier_cases.py --write-input .lake/header-carriers-input.tsv
lake exe header-carriers-native-tests .lake/header-carriers-input.tsv > .lake/header-carriers-native.jsonl
uv run --no-project --python 3.12 python -B STFSpec/Conformance/Block/header_carriers_differential.py --check-target .lake/header-carriers-native.jsonl
lake env lean --run scripts/HeaderCarriersNativeTests.lean .lake/header-carriers-input.tsv > .lake/header-carriers-interpreted.jsonl
uv run --no-project --python 3.12 python -B STFSpec/Conformance/Block/header_carriers_differential.py --check-target .lake/header-carriers-interpreted.jsonl
uv run --no-project --python 3.12 python -B scripts/test_header_carriers_output_parser.py
uv run --no-project --python 3.12 python -B -O scripts/test_header_carriers_output_parser.py
lake build storage-decode-native-tests --wfail
lake exe check-decls StorageDecodeNativeTests
lake exe storage-decode-native-tests > .lake/storage-decode-native.jsonl
uv run --no-project --python 3.12 python -B STFSpec/Conformance/StateCommit/storage_decode_differential.py --check-target .lake/storage-decode-native.jsonl
lake env lean --run scripts/StorageDecodeNativeTests.lean > .lake/storage-decode-interpreted.jsonl
uv run --no-project --python 3.12 python -B STFSpec/Conformance/StateCommit/storage_decode_differential.py --check-target .lake/storage-decode-interpreted.jsonl
uv run --no-project --python 3.12 python -B scripts/test_storage_decode_output_parser.py
uv run --no-project --python 3.12 python -B -O scripts/test_storage_decode_output_parser.py
lake build fixed-endian-bench --wfail
lake exe check-decls FixedEndianBench
lake build log-rope-bench --wfail
lake exe check-decls LogRopeBench
lake build packed-keccak-bench --wfail
lake exe check-decls PackedKeccakBench
uv run --no-project --python 3.12 python scripts/gen_packed_keccak.py --check
uv run --no-project --python 3.12 python scripts/test_packed_keccak_generator.py
uv run --no-project --python 3.12 python scripts/check_boundaries.py
scripts/check_decls.sh core
scripts/replay_kernel.sh core
lake build CheckDeclsTest check-decls && scripts/test_checks.sh
uv run --no-project --python 3.12 python scripts/test_differential.py
uv run --no-project --python 3.12 python -B scripts/test_hash32_output_parser.py
uv run --no-project --python 3.12 python -B -O scripts/test_hash32_output_parser.py
uv run --no-project --python 3.12 python -B scripts/test_node_db_output_parser.py
uv run --no-project --python 3.12 python -B -O scripts/test_node_db_output_parser.py
uv run --no-project --python 3.12 python scripts/check_reference.py && uv run --no-project --python 3.12 python scripts/test_reference_checks.py
uv run --no-project --python 3.12 python scripts/gen_arch_diagram.py --check
uv run --no-project --python 3.12 python scripts/check_spec.py && uv run --no-project --python 3.12 python scripts/test_spec_checks.py
uv run --no-project --python 3.12 python scripts/gen_gaps.py --check
uv run --no-project --python 3.12 python scripts/remap_citations.py --check && uv run --no-project --python 3.12 python scripts/test_remap_citations.py
lake build EthConformance fixture-records --wfail
uv run --no-project --python 3.12 python scripts/test_fixture_archive.py
```

These commands build and audit the fixed-endian, log-rope and packed-keccak benchmarks. They check that the output of the packed-keccak generator is fresh, and they run its regression test. Timing measurements remain manual. The commands build, audit and execute the Taylor producer, and then they check its complete captured stdout against the handwritten literals. Source coupling is separate.

The two pre-transaction account items' source comparisons additionally need
an authenticated pinned EELS clone with its frozen installed `.venv`. From the
repository root, reproduce that item test with:

```sh
uv run --no-project --python 3.12 python -B STFSpec/Conformance/State/pre_state_account_source.py --eels EELS --check-target .lake/pre-state-account-native.jsonl --report .lake/pre-state-account-source.json
uv run --no-project --python 3.12 python -B STFSpec/Conformance/State/pre_state_account_default_source.py --eels EELS --check-target .lake/pre-state-account-default-native.jsonl --report .lake/pre-state-account-default-source.json
```

The driver uses `EELS/.venv/bin/python -I -B` directly, normally and with `-O`,
and never installs packages or writes to EELS. Its report retains the original
child streams, actual waits, pin/import/runtime identities and installed RECORD
integrity. It compares complete bounded answers/calls/successful reads and source
field retention, with failed source reads separate from Lean's absent failed state.
No downloaded-wheel provenance, backend adapter, full-state projection or guest
claim follows. CI runs the source-reader/authentication regressions without EELS;
those tests do not replace the item's actual authenticated source comparison.

Changes to `STFSpecMathlib/` or `STFSpecSecurity/` also run `lake build --wfail` there, then `scripts/check_decls.sh mathlib` and `scripts/replay_kernel.sh mathlib`, or the same with `security`. Regenerate, never hand-edit, generated files: `STFSpec/informal/GAPS.md`, `REFERENCE-RECORDS.md`, `eels-inventory.json`, `citation-remap.json` and `citation-remap-manual.txt` (`scripts/remap_citations.py --apply`, no clone needed), `STFSpec/informal/eest-fixture-index.txt` (`scripts/gen_fixture_index.py`), `STFSpec/Hash/PackedKeccakPermutation.lean` (`scripts/gen_packed_keccak.py`), `STFSpec/Conformance/Precompiles/KzgVersionedHashGuards.lean` (`scripts/gen_kzg_versioned_hash_guards.py`), and the README diagram. `remap_citations.py --check` fails when a recorded pre-remap EELS citation reappears in its recorded context, or a listed one changed or no longer occurs; resolve each such entry explicitly, with `--apply --drop-resolved DOC:LINE` once it is fixed or removed, `--apply --relist DOC:LINE DOC:NEWLINE` if it is still at the old commit but was moved within its document, edited around or reformatted (for a move to another document, `--drop-resolved` it and read the new line with `--since`), or `--apply --confirm DOC:LINE` (with `--eels`) if it is already correct at the pin. The check cannot recognise old line numbers in new or edited prose. So a branch cut before the remap (GAPS-CROSSCUTTING X16) must, after merging main and resolving conflicted lines to its own pre-remap numbers, run `uv run --no-project --python 3.12 python -I scripts/remap_citations.py --apply --since <merged main commit> --eels <execution-specs clone>` and commit the result. The script's docstring states its rules.

### 6.4 Review and commit gate

Every change is a **work item**: a self-contained change that one reviewer can hold in full, for example one type with its operations and laws. Commit a work item only when all of these conditions hold for the exact tree that you commit:

- Every check in §6.3 passes, together with the tests of the item. These tests are the deterministic and failure-order cases that its spec guidance lists (§4 of each guidance document). They include a differential comparison against EELS where the guidance requires one.
- An **independent adversarial review** of that exact diff (§6.6, *adversarial reviewer*) found it **clean**. That verdict means that the required checks ran and that no blocking finding under §5.5 remains unresolved. Non-blocking recommendations may remain. Fix a blocker, or rebut it with written evidence in the pull request. A deferred nit needs no rebuttal. Any change after the review needs another review.
- The documentation is current (§6.5).
- The commit message follows the conventions of §6.2 and summarizes the change, the evidence and the review verdicts.

A commit never contains `sorry` in the core, a banned construct (§4), a failed or skipped check, or unreviewed code.

### 6.5 Pull requests, stacking and documentation

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
- **Conformance engineer.** Builds the `EthConformance` runners, the `core` profile, replay records and differential harnesses against EELS, as its spec guidance specifies. Fixtures are decisive (§1): a mismatch is a failure of the spec, never special-cased; the archive is authenticated before use; CI jobs are deterministic and bounded.
- **Adversarial reviewer** (never edits). It judges only the diff, the brief and the documents that govern the change, without the context of the implementer. It tries to break the change in these areas:
  - Fidelity to the pinned EELS, with every failure condition and its order
  - The stated laws, and the one-owner rule
  - Totality and the hard rules (it runs `scripts/check_decls.sh`, `scripts/replay_kernel.sh` and `scripts/check_boundaries.py`)
  - Test adequacy (an input that passes the tests but is wrong)
  - The data structures against the guidance or DEBT
  - Documentation drift

  It runs the checks again itself. It returns **clean** or **not clean** as §6.4 defines, with findings classified under §5.5: **blocking**, **should fix** (non-blocking recommendation), or **nit** (non-blocking polish). A blocker names the requirement that governs it, the affected behaviour or claim, file:line and evidence.

  The report lists what the reviewer could not verify, and it keeps tooling findings distinct from Lean semantic findings. A correctly classified script nit cannot turn a clean Lean work item into a **not clean** verdict. The reviewer never reports clean on unrun required checks. Items that other modules depend on (shared types, seams, laws that other modules use) get two independent reviewers.
- **Polisher.** Improves accepted work for legibility and style (§2, §7) without changing behaviour, public signatures or stated laws: naming, structure, moving duplicated helpers to their owner, proof clarity, docstrings, stale documentation. One theme per pass; the result goes back through review.

Harness-specific configuration (for example agent definition files) is local to each contributor. Contributors do not commit it, and it only points to this section.

An author who uses an agent or another tool stays responsible for the result. These tasks remain with the author:

- Read the statements of the main theorems or laws that the change proves, and the full description, before you request a review.
- Keep session notes, plans and handoff notes out of the contribution.
- Replace a temporary plan identifier that readers cannot access with an explanation or a maintained identifier.
- Coordinate concurrent tool runs, so that they do not open two pull requests for the same target.

## 7. Lean style and naming

We follow the [Lean community's style and naming conventions](https://leanprover-community.github.io/contribute/index.html) (as mathlib does), with the project-specific rules below. Where this file and the community guide differ, this file wins. When in doubt, match the adjacent code.

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

### 7.2 Naming

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

### 7.3 Formatting

Use this source format:

- Keep lines under 100 characters. Use two-space indentation, no tabs and no trailing whitespace.
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

### 7.5 Renaming and deprecation

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

### 8.3 Writing

[`WRITING.md`](WRITING.md) gives advice for repository prose: documents, docstrings, comments, commit messages, pull request descriptions, issue text and review reports. It applies to every author, human or agent. Use it where it improves clarity and accuracy; leave clear, correct text alone. This section does not add a separate writing-conformance requirement.

Draft or revise that prose with the [writing workflow](WRITING-WORKFLOW.md), and use the terms of the [vocabulary](WRITING-VOCABULARY.md). A style edit keeps claims, hypotheses, uncertainty and requirement strength unchanged.

Legibility is a review matter (§5.3), so no CI check applies the standard. Under §5.5, a writing finding is a non-blocking recommendation, unless the text materially misstates what was implemented or verified. The advisory script `scripts/writing_hints.py` reports some patterns for authors, but its output is neither required nor sufficient.

## 9. Code of conduct

Treat other contributors with respect. STFspec follows the principles of the [mathlib Code of Conduct](https://github.com/leanprover-community/mathlib4/blob/master/CODE_OF_CONDUCT.md). Participation in the project (code, issues, discussions) means that you agree to follow them. Report unacceptable behaviour to the maintainers.

## 10. Licence

STFspec is licensed under either of the [Apache License, Version 2.0](LICENSE-APACHE) or the [MIT licence](LICENSE-MIT), at your option. Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in this work is dual licensed as above, without any additional terms or conditions. Vendored third-party code keeps its own licence, stated in its files.
