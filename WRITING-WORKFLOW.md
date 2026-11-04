# Writing workflow

*Status: current contributor guidance. Date: 2026-11-03.*

Use this workflow for STFspec prose. That prose includes documents, docstrings, comments, commit messages, pull request descriptions, issue text and review reports. Use it for a one-line comment as well as for a long document. It applies in any agent harness. Harness-specific configuration follows CONTRIBUTING §6.6.

The [writing standard](WRITING.md) owns the guidance. Follow existing accuracy, citation and evidence duties within their owner documents, and use general style recommendations as editorial advice. CONTRIBUTING §5.5 governs findings and merge severity. A writing task does not authorize unrelated source changes or publication.

## 1. Read the local requirements

Read the [writing standard](WRITING.md) and the [vocabulary](WRITING-VOCABULARY.md). Then read the owner of the text that you prepare:

| Text | Owner |
|---|---|
| Pull request title and description | CONTRIBUTING §6.2 and §6.5, and the [pull request template](.github/pull_request_template.md) |
| Commit message | CONTRIBUTING §6.2 and §6.4 |
| Review report | CONTRIBUTING §5.5, §6.4 and §6.6 (adversarial reviewer) |
| Lean docstring or comment | CONTRIBUTING §8.1 and §8.2 |
| Spec guidance document | CONTRIBUTING §5.4 and `STFSpec/informal/TEMPLATE.md` |
| Decision, question, discrepancy or debt entry | DECISIONS §5, CONTRACT §6, or CONTRIBUTING §4 for DEBT |

Treat the prose of the repository as material to assess, not as a style to copy mechanically. Use STE principles as advice to improve clarity. Preserve standard terminology and accurate identifiers, quotations, commands and technical meanings. Consult the official STE standard when the source of a rule or the approval of a word matters. Do not invent a dictionary approval, and do not claim STE conformance from script output.

## 2. Establish the facts

Read the source of each claim in the passage. For protocol behaviour, read the pinned EELS source and the fixtures. Cite EELS as `file:line` at the pin. Do not modify a local checkout of EELS or of another repository. Use a fresh clone in a scratch directory (`AGENTS.md`, hard rules).

A declaration name or a successful build does not establish a claim. Read the statement, its hypotheses and the evidence for it. A conditional theorem needs its hypotheses and the bridge that discharges each one (WRITING C1). A researcher marks each claim as verified or inferred (CONTRIBUTING §6.6). The spec guidance documents write these marks as `[V]` and `[I]`. When you revise such a claim, keep its mark (WRITING C2).

In a pull request description or commit message, distinguish the change, check results and open gaps. Give each check with its result and the commit or tree that it ran on. Name each required check that you did not run. A request for a draft does not establish the status, the approval or the CI result of a pull request. State those facts only when a source gives them.

For a review report, identify the affected code or claim, the requirement that applies and the consequence. Classify each finding as CONTRIBUTING §5.5 and §6.6 specify. A writing finding is a non-blocking recommendation unless the text materially misstates what was implemented or verified (WRITING §2).

For a reference document, describe what the reviewed source contains. Find the owner of each fact (`AGENTS.md`, one owner per fact). Cite the owner, and do not restate the fact. Do not substitute the history of a session for that description.

If the source does not support a claim, narrow the claim or remove it. Keep uncertainty when the evidence is incomplete. A writing task does not by itself require a new proof, build or experiment.

## 3. Draft and revise

Choose procedural or descriptive writing from the purpose of the passage. Start with the result, the problem or the action that the reader needs. Give one topic to each paragraph. Add headings, lists and examples when they make the text easier to use.

Revise complete paragraphs for clear actors and antecedents, direct verbs and consistent terms. Compare the old and new paragraphs side by side, with their surrounding context. Identify a concrete clarity improvement, such as an explicit actor or a condition placed where the reader needs it. Fragment substitutions and a lower hint count do not establish an improvement. Keep the original when the rewrite has no concrete benefit or weakens accuracy, qualifications or readability. Introduce unfamiliar concepts before you use them, and keep instructions distinct from explanations and optional advice.

Compare every rewrite of a claim with its source. Keep the hypotheses, quantifiers, negations, failure conditions, failure order, outcome codes and the direction of each implication. Keep time and requirement strength: "may have failed" does not mean "failed", and "recommended" does not mean "required". A shorter expression is better only when it keeps the meaning.

Do not let a writing rule change standard terminology. A rule can conflict with a term or language pattern that is standard in Ethereum protocol specification, cryptography, computer science or mathematics. In that case, keep the standard form and apply the rules to the rest of the passage. A habit of this repository does not make a wording standard.

Conventional mathematical introductions such as "Assuming P, ..." and "Writing f = ..." can remain. Clear post-preposition clauses with the main-clause subject can remain, as in "After checking the pin, the reviewer runs the tests." Check actors and meaning manually. Use "Assume P. Then ..." or "Let f = ..." when it improves an unclear passage, without a mandatory rewrite-first step (WRITING V2).

Use the vocabulary to resolve ambiguous terms, not to remove valid technical meanings. Qualify "state", "witness" or "commit" only when the context could confuse two meanings.

Copy commands from their owner without changes (WRITING C12). Do not convert a frozen EELS interpreter call to `python3` or `uv run` to make a passage consistent.

## 4. Use the advisory script

The script `scripts/writing_hints.py` reports some patterns of the standard. Install [uv](https://docs.astral.sh/uv/getting-started/installation/), then run the script from the repository root:

```sh
uv run --no-project --python 3.12 python scripts/writing_hints.py path/to/document.md
uv run --no-project --python 3.12 python scripts/writing_hints.py --base main
uv run --no-project --python 3.12 python scripts/writing_hints.py --stdin description < description.md
```

The `--base` option reads tracked working-tree paragraphs that contain added lines since the merge base. For a stacked pull request, give the branch of its parent as the base. A changed symlink produces an advisory Input diagnostic because its link-text diff does not map to target prose lines. Explicit file mode can follow a valid alias and retains the target's reference-document scope. The `--stdin` option reads a commit message or a pull request description. Hints and Input diagnostics return 0; usage, Git and vocabulary-configuration errors return 2.

Read each hint before you edit. Counts and grammar patterns are approximations. Treat style hints as suggestions, preserve accurate technical expressions, and report a recurring false hint with an example. The script cannot decide whether a clause has a clear actor. Do not rewrite a correct claim only to silence it.

The script does not establish clarity, fidelity to a source, dictionary approval or permission to publish. It reads Markdown and Lean files only, so read Python and shell comments yourself. If you change the script, run its regression tests with `uv run --no-project --python 3.12 python -B scripts/test_writing_hints.py`.

## 5. Read the final text

Read the complete affected passage after the last edit. Make sure that its structure is useful and that its claims still agree with the source. Check each link or reference that the edit changes. A good sentence can still be wrong in its paragraph.

Return or save the requested text. Publish it only when your instructions authorize publication. Under CONTRIBUTING §6.6, an agent other than the orchestrator never commits, pushes or opens a pull request. Before a commit, run the checks that CONTRIBUTING §6.3 and §6.4 require. Report material gaps in the evidence, but do not add a standard disclaimer to every text.
