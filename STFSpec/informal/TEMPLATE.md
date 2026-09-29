# `<Library>`: <one-line title>

*Status: informal specification, draft. Date: YYYY-MM-DD. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F<n>, … (DECISIONS §3) · gate: [REVIEW §3](REVIEW.md) · decisions: D<n>, … · questions: B<n>/Q<n>/F<n>, ….*

The navigation line lists what an implementer of this library must also read. These links are relative to this template; when copying it into `STFSpec/informal/modules/`, add one `../` to each target. Omit the parts that do not apply.

Every section below is required; `scripts/check_spec.py` enforces the headings, the EELS
coverage claims, the dependency/ownership registry, argument structure and decision IDs. These
checks do not establish Lean typing or mathematical truth. Write "none" rather than leaving a
section empty.

## 1. Purpose

What this library is for, in 2–5 sentences, and which layer (ARCHITECTURE §2) it belongs to.

## 2. Requirements

The expected behaviour, stated normatively ("must"), with references to the pinned EELS source
(`file:line`) and to `STFSpec/informal/CONTRACT.md` outcomes (O1–O13) where relevant. Include envelope
limits, failure behaviour, and any behaviour that differs from a naive reading of EELS.

## 3. EELS source map

Every EELS item this library specifies, claimed with a backquoted token `` `file::name` ``
(paths relative to `src/ethereum/`, names as in `STFSpec/informal/eels-inventory.json`) or a whole-file
claim `` `file::*` ``. Each inventory item must be claimed by exactly one module, or excluded
in `STFSpec/informal/EXCLUDED.md`.

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|

**External semantics** (library functions whose behaviour is part of the reference, from
the `external` entries of the inventory): which ones this library must specify, and how.

## 4. Tests

- EEST fixture areas exercising this library (from `STFSpec/informal/eest-fixture-index.txt`);
- EELS unit tests, if any (`tests/` at the pinned commit);
- `core` `#guard` cases to write (typical, edge, adversarial);
- property tests or differential checks.

## 5. Interface

The public API, in Lean-like signatures: types, structures, inductives, functions and
instances. Names follow EELS in lowerCamelCase. Mark each item public or internal. Use the
common declarations registered in `STFSpec/informal/contracts.toml` rather than redeclaring lookalikes.

The signatures are **informal** (`CONTRIBUTING.md` §5.4). They must make the names,
inputs, outputs, error channels, effects and ownership unambiguous, but they need not typecheck.
Placeholders are fine where their meaning is clear. Fixing exact Lean types, compiling the
interfaces, and proving schema-adapter inverses (source layouts in `REFERENCE-RECORDS.md`) are
implementation tasks: name them here if they matter, but don't do them in markdown.

## 6. Data structures

For each type: the representation, the public mathematical model, the abstraction
(function or relation), the invariant, the persistence class (ARCHITECTURE §5.0: snapshot-
reachable, and so worst-case persistent; or linear-only), and the expected complexity of each
operation.

## 7. Contract and laws

Per operation: invariant preservation and the commuting equation with the model (ARCHITECTURE
§4). Then the derived laws callers use. Tag each proof obligation [T] totality, [R] consumer
refinement, [C] component correctness, [F] fast path, or [S] security.

### Informal correctness argument

A *sketch* for the implementer, not a proof. Its job is to say what must be proved and why it
should hold.

**Claim.** What the module guarantees: the refinement, the observations, the input domain.

**Premises.** The provider laws and caller invariants it relies on, and who establishes each.

**Argument.** The proof strategy in prose: the case split or induction, the invariant and
measure, how errors, effect order and composition are handled. Enough that an implementer
knows how to start, without writing the proof.

**Open obligations.** What is not yet known to hold, what domain is unresolved, and what is
missing. Tests are evidence, not proof. Link COMPOSITION and REVIEW where relevant.

## 8. Composition

- **Depends on:** the exact list of direct dependencies from `scripts/boundaries.toml`
  for core, or `STFSpec/informal/contracts.toml` for proof libraries (checked), as `` `LibName` `` tokens
  on this line. External dependencies are recorded separately.
- **Used by:** the libraries that depend on this one.
- **Seams provided or consumed**, and the cross-module invariants this library relies on and
  guarantees (for example "every `PreState` passed in satisfies `Models`").

## 9. Open decisions

Decision IDs (`D1`…) from `STFSpec/informal/DECISIONS.md` affecting this library, with the local impact.
New questions are listed as `NEW:` and added to the index.

## 10. Gaps

**Everything missing**, stated plainly. Cover:
- EELS behaviour not yet understood or specified;
- missing or thin EEST coverage;
- missing upstream pieces (Lean libraries, CompPoly fields, and so on);
- unverified claims;
- design questions without an owner;
- proofs with no known strategy.
