# Working in STFspec

*Status: current repository entry point. Date: 2026-09-30.*

This is the entry point for anyone, human or agent, working in this repository. It says where things are and which document wins. It restates no facts: follow the links.

## What this is

A pure, total, executable Lean 4 specification of the Ethereum execution-layer zkVM guest (stateless block validation), fast enough for differential testing and fuzzing. It is what evm-asm and stateless-pancaketh are to be verified against.
- **Pin:** [`reference.toml`](reference.toml).
- **Lean version:** `lean-toolchain`.
- **Golden rule:** pass the pinned EEST zkevm fixtures. Outside fixture coverage, the pinned EELS source governs ([`CONTRIBUTING.md`](CONTRIBUTING.md) §1).
- **Phase:** see the status line in [`README.md`](README.md) and the readiness assessment in [`STFSpec/informal/REVIEW.md`](STFSpec/informal/REVIEW.md) §6.

## Authority order

When documents disagree, the higher one wins, and the lower one is a bug to fix:

1. The pin, [`reference.toml`](reference.toml), and the guest contract, [`STFSpec/informal/CONTRACT.md`](STFSpec/informal/CONTRACT.md) (outcomes O1–O13, authority and discrepancy policy).
2. [`STFSpec/informal/DECISIONS.md`](STFSpec/informal/DECISIONS.md): decision **statuses** and question **dispositions** (Q1–Q45, B1–B15, and the interface items F1–F20 in §3).
3. [`CONTRIBUTING.md`](CONTRIBUTING.md).
4. [`STFSpec/informal/ARCHITECTURE.md`](STFSpec/informal/ARCHITECTURE.md): component contracts; the dependency rules are enforced from [`scripts/boundaries.toml`](scripts/boundaries.toml). [`STFSpec/informal/REVIEW.md` §7](STFSpec/informal/REVIEW.md#7-acceptance-criteria-proof-gates-composition-cases-replacement-and-cost-checks): the proof gates (G, S, W), replacement gates and cost checks (C) an implementation must meet.
5. [`STFSpec/informal/modules/Eth*.md`](STFSpec/informal/README.md): per-library behaviour; ownership is in [`STFSpec/informal/contracts.toml`](STFSpec/informal/contracts.toml).
6. Anything else (experiments, prototypes, notes): evidence at most, adopted only through (2).

## Hard rules

These are enforced by `check-decls` and `scripts/check_boundaries.py` where possible (CONTRIBUTING §4; decisions D21 and D26).
- **Banned constructs:** `sorry` outside the Mathlib and security packages, `axiom`, `native_decide`, `bv_decide`, `decide +native`, `@[csimp]`, `implemented_by`, `extern`, `unsafe`, `partial`, `opaque`. There is no exemption mechanism. `deriving` on nested inductives can generate `partial` constants (CONTRIBUTING §4).
- **Fast code:** a fast definition sits *beside* a legible reference with an ordinary equality theorem, or replaces a representation behind a model-based contract (D25).
- **Mathlib:** none in the core package. Mathlib appears only in `STFSpecMathlib/` and `STFSpecSecurity/`; VCV-io only in `STFSpecSecurity/`.
- **Dependencies:** a third-party dependency must be pure Lean and must pass the declaration check on everything imported (D26).
- **Hashing:** every keccak goes through `KeccakQuery`, with monad-parametric interfaces specialised to `Id` (D5).
- **Data structures:** performance-appropriate, or recorded in [`STFSpec/informal/DEBT.md`](STFSpec/informal/DEBT.md) (D18).
- **Copyrighted references** (books, papers): cite them; never commit or publish copies.
- **Other repositories:** never modify local checkouts of other repositories (EELS, VCV-io, CompPoly, evm-asm, …). Use fresh clones in a scratch directory.

## Working as an agent

This file and [`CONTRIBUTING.md`](CONTRIBUTING.md) apply in any harness. Agent-driven work follows CONTRIBUTING §6.4–§6.6: each change is a work item that is committed only after its checks pass and an independent adversarial review finds it clean; larger components become stacked pull requests; and work is divided among defined roles (orchestrator, researcher, prototyper, implementer, conformance engineer, adversarial reviewer, polisher). Harness-specific configuration stays local and only points to those sections.

Finding severity and the treatment of tooling issues are owned by
[`CONTRIBUTING.md` §5.5](CONTRIBUTING.md#5-tests-review-and-automation);
§6.4 defines a clean review verdict. Apply those rules before treating a review
recommendation as a merge blocker.

## Task map

| Task | Read | Update | Check |
|---|---|---|---|
| **Implement or change library `EthX`** | `STFSpec/informal/modules/EthX.md` (its navigation line lists the relevant decisions and questions); the providers' §5 and §7; `STFSpec/informal/COMPOSITION.md` §2; the `EthX` gate and handoff contract in `STFSpec/informal/REVIEW.md` §§3–4 | the spec guidance document (its §10 gaps, then `scripts/gen_gaps.py`); a source-to-Lean/test row per implemented operation (REVIEW §4); DEBT.md for a performance exception | `lake build --wfail`, `scripts/check_boundaries.py`, `scripts/check_decls.sh core`, `scripts/check_spec.py`, `scripts/gen_gaps.py --check` |
| Add or change a decision | `STFSpec/informal/DECISIONS.md` (§5: how to add one) | its row (the only status owner), the ARCHITECTURE §11 options, and the affected spec guidance documents in the same change | `scripts/check_spec.py` (decision IDs) |
| Error, failure or outcome question | `STFSpec/informal/CONTRACT.md` §4; D14; `STFSpec/informal/modules/EthStateless.md` §7 | CONTRACT (the outcome owner); the module's error constructors | — |
| Protocol discrepancy | CONTRACT §6 | `STFSpec/informal/DISCREPANCIES.md` (records only; a deviation needs a decision) | — |
| Change the pin | `reference.toml` (its header comment) | `reference.toml` and CONTRACT together, in one commit, recorded in DECISIONS P1; regenerate the inventory and reference records | `scripts/check_reference.py` |
| Record the outcome of an investigation | `STFSpec/informal/DECISIONS.md` | the dispositions (or a decision) in DECISIONS and the affected specs, in the same change | `scripts/check_spec.py` |
| Performance work | CONTRIBUTING §3; `STFSpec/informal/REVIEW.md` §7 (cost checks C1–C4) | DEBT.md; the decision record | a benchmark with a correctness gate, no checksum in the timed loop |
| Change the declaration check or checkers | `scripts/CheckDecls.lean`, `scripts/test_checks.sh`, `scripts/test_spec_checks.py` | add a regression fixture first | `lake build CheckDeclsTest check-decls && scripts/test_checks.sh`; `python3 scripts/test_spec_checks.py` |
| Mathlib bridge or security package | `STFSpecMathlib/` or `STFSpecSecurity/`; `STFSpec/informal/modules/*Mathlib.md` or `EthSecurity.md` | — | `(cd STFSpecMathlib && lake build) && scripts/check_decls.sh mathlib`; likewise `STFSpecSecurity` with `security` |

## Open items

Do not restate these elsewhere; each has an owner.
- The informal-spec blockers: [`STFSpec/informal/GAPS.md`](STFSpec/informal/GAPS.md) (generated), with the cross-cutting items X1–X15 in `STFSpec/informal/GAPS-CROSSCUTTING.md`.
- Pending investigations: fuel adequacy (`STFSpec/informal/REVIEW.md` §7 G2–G7) and witness/full-state agreement (S2); REVIEW §6.
- Open interface items F6, F7, F11, F20 and O2: `STFSpec/informal/DECISIONS.md` §3.
- O12, host resources: `STFSpec/informal/DISCREPANCIES.md` DISC-001 and DISC-006.

## Documentation conventions

- **One owner per fact** (the authority list above). Everything else cites by ID: `D5`, `B8`, `Q20`, `F7`, `O13`, `DISC-001`, `X6`, `G2`.
- **Status and date.** Every document opens with a status and date line. Snapshots also name the external commit they describe.
- **Generated files** say what generates them. Edit the source and regenerate: `STFSpec/informal/GAPS.md`, `STFSpec/informal/REFERENCE-RECORDS.md`, `STFSpec/informal/eels-inventory.json`, and the README diagram.
- **Superseded material** is not rewritten in place. It gets a supersession note mapping sections to their current owners, and is removed when fully superseded; git history keeps it.
- **Paths.** Repo-relative only. Cite the reference as EELS `file:line` at the pin.
- **Spec guidance documents are informal** (CONTRIBUTING §5.4): precise signatures and argument sketches, no Lean proofs. Keep their ten numbered sections; `scripts/check_spec.py` enforces them.
