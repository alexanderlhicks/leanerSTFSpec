# Writing Guide

*Status: current contributor guidance. Date: 2026-11-03.*

This guide helps you write clear, precise, correct technical text. Its rules are advice. If a passage is clear and correct, leave it alone, even if it does not follow a rule or the checker reports it. Accuracy comes first, then clarity. A habit of the repository is not a reason to keep unclear writing.

The [vocabulary](WRITING-VOCABULARY.md) records the technical terms of the protocol, the reference, Lean and the repository. The [writing workflow](WRITING-WORKFLOW.md) tells authors and agents how to apply this standard.

## 1. Scope

The standard applies to prose that a person or an agent writes for the repository:

- Markdown documents, for example the root guides and the documents in `STFSpec/informal/`
- Lean module docstrings, declaration docstrings and comments
- Docstrings and comments in Python and shell scripts
- Commit messages, pull request descriptions, issue text and review reports

Apply the standard to the text that you add or change. Read the text around it for context. Correct related defects that affect the passage, but put unrelated rewrites in a separate change, for example a polisher pass (CONTRIBUTING §6.6).

Keep these elements accurate, and do not rewrite them to satisfy a prose rule:

- Lean code, the Lean-like signatures in spec guidance documents, commands and other code
- Formulas, identifiers, EELS citations and fixture names
- Quoted text, for example EELS source or an error message
- Titles of documents and other works, and licence text
- Generated files, which [`AGENTS.md`](AGENTS.md) lists, and superseded material, which is not rewritten in place

These exclusions do not cover an explanation that an author puts in quotation marks. Headings and table labels can be fragments, but they must use clear and consistent terms.

## 2. Status of the rules

All rules in this guide are advice. CONTRIBUTING owns the contribution requirements, and §5.5 governs the severity of findings. This guide does not add a second set of requirements. Legibility remains a review matter under §5.3, so no CI check applies this guide.

Outside this document, cite a rule with the prefix "WRITING", for example "WRITING S1". The bare labels collide with repository identifiers, for example the proof gate S2, the cost check C1 and the decision P1.

The advisory script `scripts/writing_hints.py` reports some patterns that a search can find. It is an editing aid, not a check in the sense of CONTRIBUTING §5.3. CI does not run it, and its output is neither required nor sufficient.

## 3. How to use STE

Use the [vocabulary](WRITING-VOCABULARY.md) to clarify technical meanings, not to decide which English words are permitted. The guide draws freely on STE; §10 gives its source.

Technical accuracy takes priority over the rules in this standard. A rule can conflict with a term or language pattern that is standard in Ethereum protocol specification, cryptography, computer science or mathematics. In that case, keep the standard form and apply the rules to the rest of the sentence. A wording that is only a habit of this repository is not a standard form.

## 4. Text types

Choose a text type from the purpose of a sentence, not from its Markdown marker:

| Type | Purpose | Examples in STFspec | Suggested sentence length |
|---|---|---|---|
| Procedural | Tell the reader how to do a task | The task map in `AGENTS.md`, CONTRIBUTING §6, role briefs, the writing workflow, numbered steps | 20 words |
| Descriptive | Give information | Docstrings, comments, spec guidance documents, entries in DECISIONS, DISCREPANCIES and DEBT, commit messages, pull request descriptions, review reports | 25 words |

A numbered list can describe results. A paragraph can contain an instruction. Use these lengths as prompts to review a sentence, not targets that require a rewrite. A title of a commit or a pull request is a label, not a work step, and CONTRIBUTING §6.2 gives its form.

## 5. Rules

The labels below are local identifiers. STE references identify source principles, not exact equivalence to source rules. All the rules below are advice. A checker suggestion alone does not require an edit.

### Words

Apply these rules:

- **W1.** Prefer a common, simple word with the intended meaning. Use an established technical term when the subject requires it. Rephrase if a replacement would change the meaning. (STE 1.1 to 1.4, 9.1, 9.2)
- **W2.** Use technical terms with the meanings and grammatical roles that the vocabulary gives. Qualify a term when the passage could support more than one meaning, for example "world state" and "Lean state". (STE 1.5 to 1.13)
- **W3.** Use one term for one concept in a passage. Do not change between synonyms for variety. Introduce a different technical meaning before you use it. (STE 1.11, 9.4)
- **W4.** Write a multi-word noun with no more than three words. Divide a longer group with words such as "of", "for" or "on". Keep established terms under W5. (STE 2.1, 2.2)
- **W5.** Write a longer technical noun in full the first time. Then use a clear shorter name, a defined abbreviation or a hyphenated form: "Ethereum Execution Layer Specification (EELS)". Do not invent an abbreviation only to shorten the text. (STE 2.2)
- **W6.** Prefer a direct verb when it preserves the meaning: write "install uv", not "set up uv". Keep a phrasal verb when it expresses the intended meaning more clearly. (STE 9.3)
- **W7.** Write English words instead of Latin abbreviations in prose. Write "for example", not "e.g.". Keep official titles and quotations unchanged. (STE GR-6)
- **W8.** Use Oxford spelling in prose: British spelling with "-ize" endings, such as "behaviour", "optimization" and "analyse". American spelling is also correct. Keep one spelling in a file. Keep official names, identifiers and quotations with a different spelling unchanged. Lean declaration names follow the American spelling of Mathlib. Do not convert the spelling of a file except to make the file consistent. (STE 1.14, 9.4)
- **W9.** Prefer gender-neutral language when gender is irrelevant. If a person's pronouns are unknown, use "they" or repeat the name. Respect known pronouns. (STE GR-7, adapted)

### Verbs

Apply these rules:

- **V1.** Prefer the simple tenses, the imperative and the infinitive. Avoid a complex verb form when a simpler construction gives the same information. Keep time and uncertainty: "the archive may have changed" does not mean "the archive changed". (STE 3.1 to 3.4, adapted)
- **V3.** Use the active voice. Name the actor: a definition, a check, the guest, EELS, a fixture, a reviewer or "we". Make clear who or what does each action. Do not invent an actor. (STE 3.6)
- **V4.** In descriptive text, write a passive construction only if you do not know who or what does the action. A past participle that gives a state is not a passive construction: "the account is empty". (STE 3.3, 3.6)
- **V5.** Use a verb, not an abstract noun phrase, to describe an action. Write "the guest rejects the block", not "the guest performs a rejection of the block". (STE 3.7)
- **V6.** Write "that" after "prove", "show", "assume" or "make sure" when it separates a claim from the verb. Do not add it before an object: "prove the law". (STE GR-1)

### Sentences

Apply these rules:

- **S1.** Review a sentence that is longer than the suggested length for its text type. Split it if that improves clarity, and keep its conditions and qualifications. Section 6 explains the word-count estimates. (STE 5.1, 6.3)
- **S2.** Give a sentence one topic. Give a work step one instruction, unless two actions must occur together. (STE 4.1, 5.2)
- **S3.** Put a condition before an instruction when the reader needs it before the action: "If `check-decls` fails, read its report." (STE 5.4)
- **S4.** Use the imperative for work steps. Keep an instruction distinct from a requirement and from a description. When you revise a requirement, keep the force of "must", "may" and "can". (STE 5.3, adapted)
- **S5.** Keep the articles, subjects and verbs that a sentence needs. Do not use contractions to shorten prose. (STE 4.2, 4.5)
- **S6.** Connect related sentences with words such as "and", "but", "then", "thus" or "as a result". Do not expect punctuation alone to show the connection. (STE 4.4)
- **S7.** Give each pronoun a clear antecedent. After "this" or "these", name the noun when the reference could be ambiguous: "this law", not "this". (STE GR-3, GR-4)
- **S8.** Put instructions in the procedure, not in a note. Readers can skip notes, so use notes only for additional information. (STE 5.5)

### Paragraphs and lists

Apply these rules:

- **P1.** Give each paragraph one topic. Introduce that topic before its details. (STE 6.4, 6.5)
- **P2.** Write no more than six sentences in a paragraph. Divide a paragraph where its subject or purpose changes. (STE 6.6)
- **P3.** Give information gradually. Define a term or a notation before you use it in an explanation. (STE 6.1)
- **L1.** Use a vertical list when it makes steps, cases or conditions easier to distinguish. A short series does not always need a list. (STE 4.3)
- **L2.** Introduce a list with a sentence or a clause that ends with a colon. Make sure that each item connects to that introduction. An item can complete the introduction or be a full sentence. (STE 4.3)
- **L3.** Keep the grammatical form and the end punctuation consistent in a list: end every item with a period, or end no item with one. Start each prose item with an uppercase letter, and keep the case of identifiers. Do not end an item with a comma or a semicolon. (STE 4.3, adapted)
- **L4.** Number the work steps when their order matters. Do not number independent facts. (STE 5.2)

### Punctuation and emphasis

Apply these rules:

- **U1.** Do not use semicolons in prose. Write two sentences or use a conjunction. Do not change punctuation in code. (STE 8.1)
- **U2.** Do not join two clauses with a dash. State the relation in words or write two sentences. A dash can separate a term from its description. This rule does not apply to ranges such as "O1–O13" or to mathematical notation. (*STFspec*)
- **U3.** Use a hyphen to join words that modify a noun as one unit: "fixture-specific special cases". Keep the conventional spelling of an established technical term. (STE 8.2)
- **U4.** Use parentheses for references, identifiers, abbreviations, explanations or alternatives. Place information that an instruction needs outside parentheses. (STE 8.3, with an STFspec instruction-placement rule)
- **U5.** Use emphasis for a term in its definition, a label, a warning or a specific requirement. Do not emphasize a whole paragraph. (*STFspec*)

## 6. Word count

STE 8.4 to 8.7 specify how to count words. Each of these elements counts as one word:

- A number, or a number with its unit
- An abbreviation, for example "EELS" or "RLP"
- An alphanumeric identifier, for example `D5`, `Q20`, `O13` or `DISC-001`
- Quoted text, which in STE includes formulas and can appear in a different font
- A title, a heading, or the text of a label
- A proper noun of a person, a group, an organization or a geopolitical entity
- A hyphenated word

A parenthesis adds one word to the count of the sentence that contains it. The words inside the parenthesis form a separate sentence for the limit. In a vertical list, the colon ends the introduction, and each item counts separately.

Thus a formula counts as one word. STFspec treats a code span as quoted text in code font, so a code span also counts as one word. The code spans include Lean expressions, commands and EELS citations such as `src/ethereum/utils/byte.py:18`. As an adaptation for technical text, STFspec also counts each of these elements as one word:

- A URL that is not in a code span
- A section reference such as "CONTRIBUTING §5.3"

Ordinary link text keeps its words. Do not add hyphens or quotation marks to hide a long sentence. The advisory script approximates these conventions, so read the sentence itself when its count is doubtful.

## 7. Claims, evidence and commands

This advice helps you write claims that agree with their sources and evidence. The contribution requirements remain in CONTRIBUTING and the other owner documents cited below. This section adds no separate conformance test; CONTRIBUTING §5.5 governs findings.

- **C1.** State only what the code or the recorded evidence establishes. Identify conditional results, open obligations and checks that you did not run. A conditional theorem lists its hypotheses and names the bridge that discharges each one. A pass of the development check does not claim that anyone instantiated a conditional theorem. (CONTRIBUTING §4, release theorems)
- **C2.** Keep the strength of each claim. Keep its hypotheses, quantifiers, negations, failure conditions, failure order and qualifications. Do not change "can" to "does", an inferred result to a verified one, or "recommended" to "required". Keep the `[V]` and `[I]` markers that show verified and inferred claims. (CONTRIBUTING §1, §6.6)
- **C3.** Name the evidence for a claim of conformance or fidelity. The EEST zkevm fixtures at the pinned release are the only conformance evidence, and they are decisive wherever they speak. Outside their coverage, the pinned EELS source governs, and the claim cites it as `file:line`. Neither this spec, nor evm-sail, nor SpecRef, nor any client is more authoritative than the fixtures. (CONTRIBUTING §1)
- **C4.** Do not present agreement with another implementation as evidence of correctness. A differential test or a fuzzing run finds a disagreement to investigate. The fixtures or the pinned EELS source settle it. Proofs about the spec add confidence in properties, but they do not replace conformance. (CONTRIBUTING §1)
- **C5.** Cite each decision, question, interface item, outcome, gap, gate, cost check or discrepancy by its identifier. Examples are `D5`, `Q20`, `F7`, `O13`, `X6`, `G2` and `DISC-001`. Make sure that the identifier exists in its owner document. Do not put an identifier in a Lean declaration name. (`AGENTS.md`, documentation conventions, and CONTRIBUTING §7.2)
- **C6.** Do not cite session notes, local files, prototypes or experiments by a path outside the repository. Replace a temporary plan identifier with an explanation or a maintained identifier. Such material is evidence at most, and the repository adopts it only through DECISIONS. (`AGENTS.md`, authority order, and CONTRIBUTING §6.6)
- **C7.** In the docstring of a definition that implements an EELS operation, cite that operation as `src/ethereum/…/file.py:line` at the pin. Cite EIPs by number, and cite papers and books in the `## References` section of the module docstring. Use repository-relative paths. (CONTRIBUTING §8.1, §8.2)
- **C8.** In Lean files, spec guidance documents and other reference documents, describe the present state. Do not narrate history with words such as "no longer", "previously" or "formerly". DECISIONS, DISCREPANCIES, DEBT, dated review records, supersession notes, commit messages and pull request descriptions record history by design. (*STFspec*)
- **C9.** Replace a quality claim that has no evidence with a fact, a measurement or a reason. Words such as "robust" or "comprehensive" do not supply evidence. A performance claim follows the measurement method of CONTRIBUTING §3. (*STFspec*)
- **C10.** Do not call a result "obvious" or "trivial". Give an argument or the name of a theorem. Lean names such as `trivial` are code, not claims. (*STFspec*)
- **C11.** State each fact in its owner document. In other documents, cite the owner, and do not restate the fact. Repeat a condition only when the reader needs it at the point of use. (`AGENTS.md`, one owner per fact)
- **C12.** Copy each command from its owner, and do not change its interpreter or flags in a prose edit. Repository checks run as CONTRIBUTING §6.3 gives them. A differential driver that executes the pinned EELS source uses the frozen EELS interpreter. Call it directly as `EELS/.venv/bin/python`, with the flags of the driver docstring, for example `-I -B`. Do not replace that interpreter with `python3` or `uv run`. Most of these drivers check isolated mode through `scripts/differential.py`, and some also check the interpreter path. (The driver docstrings and `scripts/differential.py`)

The history of a change belongs in its commit message and its pull request description. Rule C8 applies to the reference text of the repository, not to the description of a change.

## 8. Specification and mathematical conventions

"Let", "fix" and "suppose" can introduce notation. They do not give a work step. "We" can refer to the author and the reader in an argument, and to the project in a policy. A state such as "the trie is secured" is not an instruction or a passive action.

A technical word can have a noun use and a verb use, as in "a hash" and "hash the header", or "a commit" and "commit a change". STE permits both roles when each use meets the rules of its category (STE 1.7, 1.12, 1.13). The vocabulary records the noun and verb uses separately. Qualify a word such as "state", "witness", "proof" or "commit" when its meaning changes between the protocol, Lean and the repository.

Write EELS names and Lean names as code spans: `process_message_call` and `processMessageCall`. Keep the parts of an informal argument in a spec guidance document (claim, premises, argument and open obligations) under their labels, because `scripts/check_spec.py` reads them.

## 9. Examples

These examples show the rules on STFspec text. The text in the first column is a quotation, so it is exempt from the rules.

| Before | After | Rules |
|---|---|---|
| "Fixed padding (previously truncated); now matches geth byte-for-byte." | `Bytes.leftPadZero` prepends zero bytes up to the width and keeps an input that is longer than the width, as EELS `src/ethereum/utils/byte.py:18` does. | U1, C8, C4, C3 |
| "The stateless theorem is done (modulo the witness bridge)." | The theorem is conditional. It holds if the witness agrees with the full state (S2), and it names the bridge that discharges that hypothesis. | C1, C5 |
| "Make sure checks pass; e.g. run the boundary checker, decls, etc." | Run every command in CONTRIBUTING §6.3. If a command fails, read its output before you continue. | U1, W7, S3 |
| "Passes the differential against EELS, so the refund order is correct." | The refund differential found no disagreement with the pinned EELS on its catalogue. No fixture covers the order, so the source-to-Lean row cites the EELS line that decides it. | C3, C4 |
| "This PR has refactored the account API and leverages a cleaner abstraction." | This pull request moves the account operations into one module. | V1, W1, C9 |
| "The archive may have changed." | Keep as written. | V1: the modal keeps the uncertainty. |
| "Hash the RLP-encoded header." | Keep as written. | "Hash" has a technical noun use and a technical verb use (§8). |

Use the [writing workflow](WRITING-WORKFLOW.md) to compare a rewrite with its source. A shorter sentence is not an improvement if it changes the claim.

## 10. STE source

This guide draws on ASD-STE100 Simplified Technical English, Issue 9, and adapts it freely for STFspec. It claims no STE conformance and does not reproduce or check the official dictionary. Refer to [ASD's official Issue 9](https://www.asd-ste100.org/assets/files/ASD-STE100_ISSUE9.pdf) when a source rule or dictionary entry matters. ASD owns the standard.