# Working in STFspec

*Status: current repository entry point. Date: 2026-11-05.*

This file is the entry point for anyone, human or agent, who works in this repository. It tells you where things are and which document wins. It restates no facts, so follow the links.

## What this is

STFspec is a pure, total, executable Lean 4 specification of the Ethereum execution-layer zkVM guest (stateless block validation). It is fast enough for differential testing and fuzzing. The evm-asm and stateless-pancaketh projects are to be verified against it. These entries point to the main facts:

- **Pin:** [`reference.toml`](reference.toml).
- **Lean version:** `lean-toolchain`.
- **Golden rule:** pass the pinned EEST zkevm fixtures. Outside fixture coverage, the pinned EELS source governs ([`CONTRIBUTING.md`](CONTRIBUTING.md) §1).
- **Phase:** read the status line in [`README.md`](README.md) and the readiness assessment in [`STFSpec/informal/REVIEW.md`](STFSpec/informal/REVIEW.md) §6.

## Authority order

When documents disagree, the higher one wins, and the lower one is a bug to fix:

1. The pin, [`reference.toml`](reference.toml), and the guest contract, [`STFSpec/informal/CONTRACT.md`](STFSpec/informal/CONTRACT.md) (outcomes O1–O13, authority and discrepancy policy).
2. [`STFSpec/informal/DECISIONS.md`](STFSpec/informal/DECISIONS.md): decision **statuses** and question **dispositions** (Q1–Q90, B1–B15, and the interface items F1–F20 in §3).
3. [`CONTRIBUTING.md`](CONTRIBUTING.md), and [`WRITING.md`](WRITING.md) with its [vocabulary](WRITING-VOCABULARY.md), which extend its §8.
4. [`STFSpec/informal/ARCHITECTURE.md`](STFSpec/informal/ARCHITECTURE.md): component contracts. The checks enforce its dependency rules from [`scripts/boundaries.toml`](scripts/boundaries.toml). [`STFSpec/informal/REVIEW.md` §7](STFSpec/informal/REVIEW.md#7-acceptance-criteria-proof-gates-composition-cases-replacement-and-cost-checks): the proof gates (G, S, W), replacement gates and cost checks (C) that an implementation must meet.
5. [`STFSpec/informal/modules/Eth*.md`](STFSpec/informal/README.md): the behaviour of each library. Ownership is in [`STFSpec/informal/contracts.toml`](STFSpec/informal/contracts.toml).
6. Other material (experiments, prototypes, notes): evidence at most, which the repository adopts only through (2).

## Hard rules

Where possible, `check-decls` and `scripts/check_boundaries.py` enforce these rules (CONTRIBUTING §4, decisions D21 and D26):

- **Banned constructs:** `sorry` outside the Mathlib and security packages, `axiom`, `native_decide`, `bv_decide`, `decide +native`, `@[csimp]`, `implemented_by`, `extern`, `unsafe`, `partial`, `opaque`. There is no exemption mechanism. `deriving` on nested inductives can generate `partial` constants (CONTRIBUTING §4).
- **Fast code:** a fast definition sits *beside* a legible reference with an ordinary equality theorem, or it replaces a representation behind a model-based contract (D25).
- **Mathlib:** none in the core package. Mathlib appears only in `STFSpecMathlib/` and `STFSpecSecurity/`, and VCV-io appears only in `STFSpecSecurity/`.
- **Kernel replay:** every library module must pass `scripts/replay_kernel.sh`. From `Lean`, core modules import only `Lean.Data.Json` and its submodules (CONTRIBUTING §4).
- **Dependencies:** a third-party dependency must be pure Lean and must pass the declaration check on everything that we import (D26).
- **Hashing:** every keccak uses `KeccakQuery`, with monad-parametric interfaces specialized to `Id` (D5).
- **Data structures:** performance-appropriate, or recorded in [`STFSpec/informal/DEBT.md`](STFSpec/informal/DEBT.md) (D18).
- **Copyrighted references** (books, papers): cite them, and never commit or publish copies.
- **Other repositories:** never modify local checkouts of other repositories (EELS, VCV-io, CompPoly, evm-asm and others). Use fresh clones in a scratch directory.

## Working as an agent

This file and [`CONTRIBUTING.md`](CONTRIBUTING.md) apply in any harness. Work by agents follows CONTRIBUTING §6.4 to §6.6:

- Each change is a work item. The orchestrator commits a work item only after its checks pass and an independent adversarial review finds it clean.
- Larger components become stacked pull requests.
- Defined roles divide the work: orchestrator, researcher, prototyper, implementer, conformance engineer, adversarial reviewer and polisher.

Harness-specific configuration stays local and only points to those sections.

[`CONTRIBUTING.md` §5.5](CONTRIBUTING.md#5-tests-review-and-automation) owns the severity of findings and the treatment of tooling issues, and §6.4 defines a clean review verdict. Apply those rules before you treat a review recommendation as a merge blocker.

Before you draft or revise any prose, use [`WRITING-WORKFLOW.md`](WRITING-WORKFLOW.md). Prose includes documents, docstrings, comments, commit messages, pull request and issue text, and review reports. The advice in [`WRITING.md`](WRITING.md) can help; leave clear, correct text alone. CONTRIBUTING §5.5 governs the severity of a finding.

## Task map

| Task | Read | Update | Check |
|---|---|---|---|
| **Implement or change library `EthX`** | `STFSpec/informal/modules/EthX.md`, whose navigation line lists the relevant decisions and questions. Also §5 and §7 of the providers, `STFSpec/informal/COMPOSITION.md` §2, and the `EthX` gate and handoff contract in `STFSpec/informal/REVIEW.md` §§3–4. | The spec guidance document (its §10 gaps, then `scripts/gen_gaps.py`). A source-to-Lean and test row for each implemented operation (REVIEW §4). DEBT.md for a performance exception. | `lake build --wfail`, `scripts/check_boundaries.py`, `scripts/check_decls.sh core`, `scripts/replay_kernel.sh core`, `scripts/check_spec.py`, `scripts/gen_gaps.py --check`, `scripts/remap_citations.py --check`. Before a commit, every check in CONTRIBUTING §6.3 (§6.4). |
| Add or change a decision | `STFSpec/informal/DECISIONS.md` (§5 tells you how to add one) | Its row (the only status owner), the ARCHITECTURE §11 options and the affected spec guidance documents, in the same change | `scripts/check_spec.py` (decision IDs) |
| Error, failure or outcome question | `STFSpec/informal/CONTRACT.md` §4, D14 and `STFSpec/informal/modules/EthStateless.md` §7 | CONTRACT (the outcome owner) and the error constructors of the module | None |
| Protocol discrepancy | CONTRACT §6 | `STFSpec/informal/DISCREPANCIES.md`, which only records. A deviation needs a decision. | None |
| Change the pin | `reference.toml` (its header comment) | `reference.toml` and CONTRACT together, in one commit, recorded in DECISIONS P1. Regenerate the files that the `reference.toml` header lists, and remap the EELS citations (GAPS-CROSSCUTTING X16 records the last move). | `scripts/check_reference.py`, `scripts/gen_fixture_index.py <ARCHIVE> --check`, `scripts/remap_citations.py --check` |
| Record the outcome of an investigation | `STFSpec/informal/DECISIONS.md` | The dispositions (or a decision) in DECISIONS and the affected specs, in the same change | `scripts/check_spec.py` |
| Performance work | CONTRIBUTING §3 and `STFSpec/informal/REVIEW.md` §7 (cost checks C1–C4) | DEBT.md and the decision record | A benchmark with a correctness gate, with no checksum in the timed loop |
| Change the declaration check or checkers | `scripts/CheckDecls.lean`, `scripts/replay_kernel.sh`, `scripts/test_checks.sh`, `scripts/test_spec_checks.py` | Add a regression fixture first. | `lake build CheckDeclsTest check-decls && scripts/test_checks.sh`, then `uv run --no-project --python 3.12 python scripts/test_spec_checks.py` and the regression tests of any other changed checker (`scripts/test_*.py`) |
| Write or revise prose: documents, docstrings, comments, commit messages, pull request and issue text, review reports | `WRITING.md`, `WRITING-VOCABULARY.md` and the owner of the text (`WRITING-WORKFLOW.md` §1) | The text only, with unrelated rewrites in a separate change | The reading pass of `WRITING-WORKFLOW.md` §4, and optionally the advisory `scripts/writing_hints.py`, which is not a check |
| Mathlib bridge or security package | `STFSpecMathlib/` or `STFSpecSecurity/`, and `STFSpec/informal/modules/*Mathlib.md` or `EthSecurity.md` | None | `(cd STFSpecMathlib && lake exe cache get && lake build --wfail) && scripts/check_decls.sh mathlib && scripts/replay_kernel.sh mathlib`, then `(cd STFSpecSecurity && lake build --wfail) && scripts/check_decls.sh security && scripts/replay_kernel.sh security`, which uses the same Mathlib checkout |

## Open items

Each of these items has an owner, so do not restate it elsewhere:

- The blockers of the informal specification: [`STFSpec/informal/GAPS.md`](STFSpec/informal/GAPS.md) (generated), with the cross-cutting items X1–X16 in `STFSpec/informal/GAPS-CROSSCUTTING.md`.
- Pending investigations: fuel adequacy (`STFSpec/informal/REVIEW.md` §7 G2–G7) and agreement of the witness with the full state (S2). REVIEW §6 covers both.
- Open interface items F6, F7, F11 and O2: `STFSpec/informal/DECISIONS.md` §3.
- O12, host resources: `STFSpec/informal/DISCREPANCIES.md` DISC-001 and DISC-006.

## Documentation conventions

Follow these conventions:

- **One owner per fact** (the authority list above). Everything else cites by ID: `D5`, `B8`, `Q20`, `F7`, `O13`, `DISC-001`, `X6`, `G2`.
- **Status and date.** Every document opens with a status and date line. A snapshot also names the external commit that it describes.
- **Generated files** say what generates them. Edit the source and regenerate: `STFSpec/informal/GAPS.md`, `STFSpec/informal/REFERENCE-RECORDS.md`, `STFSpec/informal/eels-inventory.json`, `STFSpec/informal/citation-remap.json`, `STFSpec/informal/citation-remap-manual.txt`, `STFSpec/informal/eest-fixture-index.txt` (`scripts/gen_fixture_index.py`), `STFSpec/Hash/PackedKeccakPermutation.lean` (`scripts/gen_packed_keccak.py`), `STFSpec/Conformance/Precompiles/KzgVersionedHashGuards.lean` (`scripts/gen_kzg_versioned_hash_guards.py`), and the README diagram.
- **Superseded material.** Do not rewrite it in place. Give it a supersession note that maps its sections to their current owners. Remove it when all of it is superseded, and git history keeps it.
- **Paths.** Use repository-relative paths only. Cite the reference as EELS `file:line` at the pin.
- **Prose** follows [`WRITING.md`](WRITING.md).
- **Spec guidance documents are informal** (CONTRIBUTING §5.4): precise signatures and argument sketches, with no Lean proofs. Keep their ten numbered sections, which `scripts/check_spec.py` enforces.