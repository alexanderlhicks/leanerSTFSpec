# Writing workflow

*Status: current contributor guidance. Date: 2026-11-04.*

Use this workflow for STFspec documents, docstrings, comments, commit messages, pull request and issue text, and review reports. Work within the requested scope. A writing task does not authorize unrelated source changes or publication.

## 1. Read the source before stating a claim

Read the owner of the text and the relevant contribution requirements in CONTRIBUTING. Sections 6.2 and 6.5 own pull request descriptions; §8.1 and §8.2 own docstrings and citations; §5.5 and §6.6 own review findings and roles. The [writing guide](WRITING.md) and [vocabulary](WRITING-VOCABULARY.md) offer advice, not a conformance test.

For protocol behaviour, read the pinned EELS source and the fixtures, and cite EELS as `file:line` at the pin. EEST fixtures decide covered cases; pinned EELS governs uncovered cases (CONTRIBUTING §1). Do not modify another local checkout; use a fresh scratch clone. A declaration name or a successful build does not establish a claim: read the statement, hypotheses and evidence. Distinguish what changed, which checks actually ran and what remains uncertain.

## 2. Start with what the reader needs

State the problem, result or action first. Develop one topic per paragraph. Use headings, lists and examples where they help the reader. Copy commands from their owner without changing interpreters or flags. In particular, keep direct frozen EELS interpreter calls such as `EELS/.venv/bin/python` with the flags in the driver docstring (WRITING C12).

## 3. Revise real problems

Identify a clarity or accuracy problem before changing a passage. Keep established technical terms, hypotheses, quantifiers, failure conditions, failure order, uncertainty and requirement strength. Preserve verified/inferred markers and maintained identifiers. Repository habit alone does not justify unclear wording.

## 4. Compare complete passages

Read the old and new paragraphs side by side in context. Check that the revision keeps their meaning, conditions and scope, and explain why it is clearer. A lower suggestion count does not establish an improvement. Read the final passage and check any changed links or references.

## 5. Leave correct text alone

The optional script reports word-level suggestions and approximate sentence lengths. Read each suggestion in context; it establishes neither clarity nor technical accuracy. Do not change clear, correct text to silence it. Install [uv](https://docs.astral.sh/uv/getting-started/installation/), then run it from the repository root:

```sh
uv run --no-project --python 3.12 python scripts/writing_hints.py path/to/document.md
uv run --no-project --python 3.12 python scripts/writing_hints.py --base main
uv run --no-project --python 3.12 python scripts/writing_hints.py --stdin description < description.md
```

For a stacked pull request, give its actual parent branch to `--base`. The script reads tracked working-tree paragraphs containing added lines; a changed symlink gets an advisory Input diagnostic instead of target-line attribution. Explicit file mode can follow a valid alias. Suggestions and Input diagnostics return 0; usage, Git and vocabulary-configuration errors return 2. It reads Markdown and Lean only; review other prose manually. If you change the script, run `uv run --no-project --python 3.12 python -B scripts/test_writing_hints.py`.

Return or save the requested text. Publish only when the instructions authorize it. Before a commit, run the checks in CONTRIBUTING §6.3 and §6.4. Under §6.6, only the orchestrator commits, pushes or opens pull requests; this workflow does not change those roles.
