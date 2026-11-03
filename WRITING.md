# Writing in STFspec

*Status: current contributor guidance. Date: 2026-11-03.*

This document is the writing standard for English prose in STFspec. It extends [`CONTRIBUTING.md`](CONTRIBUTING.md) §8 and has the same place in the authority order of [`AGENTS.md`](AGENTS.md). CONTRIBUTING §2 makes legibility a requirement, and this standard applies that requirement to prose.

The standard draws on ASD-STE100 Simplified Technical English (STE), Issue 9, January 2025. STE is the reference to correct prose. A habit of the repository is not a reason to keep unclear writing. §10 gives the relation to STE and marks each adaptation.

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

CONTRIBUTING §5.3 makes legibility a review matter, so no CI check applies this standard. Under CONTRIBUTING §5.5, a finding against a writing rule is a non-blocking recommendation. It can block only when the text materially misstates what was implemented or verified. Any rule can describe such a misstatement, for example a wrong EELS citation under C7. Rules C1 to C4 and C12 describe the most frequent cases.

Outside this document, cite a rule with the prefix "WRITING", for example "WRITING S1". The bare labels collide with repository identifiers, for example the proof gate S2, the cost check C1 and the decision P1.

The advisory script `scripts/writing_hints.py` reports some patterns that a search can find. It is an editing aid, not a check in the sense of CONTRIBUTING §5.3. CI does not run it, and its output is neither required nor sufficient.

## 3. How to use STE

STE combines writing rules with a general dictionary. The dictionary limits both word meanings and parts of speech. Technical nouns and technical verbs of a subject field supplement it under STE rules 1.5 to 1.13. The [vocabulary](WRITING-VOCABULARY.md) gives that subject field for STFspec.

Use the STE dictionary to confirm the approved meaning or part of speech of a general word. Use the vocabulary for technical terms. A term that the vocabulary does not list is not automatically a defect, and a familiar English word is not automatically approved. When a literal replacement changes the meaning, rewrite the sentence, or keep the necessary term and explain its technical use.

Technical accuracy takes priority over the rules in this standard. A rule can conflict with a term or language pattern that is standard in Ethereum protocol specification, cryptography, computer science or mathematics. In that case, keep the standard form and apply the rules to the rest of the sentence. A wording that is only a habit of this repository is not a standard form.

This standard is a repository adaptation of STE. It is not a complete copy of STE, and it does not claim full STE conformance. It does not distribute the official dictionary, and no tool checks text against that dictionary.

## 4. Text types

Choose a text type from the purpose of a sentence, not from its Markdown marker:

| Type | Purpose | Examples in STFspec | Sentence limit |
|---|---|---|---|
| Procedural | Tell the reader how to do a task | The task map in `AGENTS.md`, CONTRIBUTING §6, role briefs, the writing workflow, numbered steps | 20 words |
| Descriptive | Give information | Docstrings, comments, spec guidance documents, entries in DECISIONS, DISCREPANCIES and DEBT, commit messages, pull request descriptions, review reports | 25 words |

A numbered list can describe results. A paragraph can contain an instruction. Apply the limit for the purpose of each sentence. Do not mix procedural and descriptive items in one list. A title of a commit or a pull request is a label, not a work step, and CONTRIBUTING §6.2 gives its form.

## 5. Rules

Each rule names the STE rule that it adapts. The label *STFspec* marks a rule that has no STE source. STE's general recommendations (GR) are advice in STE. This standard makes the recommendations that it names into repository rules.

### Words

- **W1.** Prefer an STE-approved general word with the intended meaning and part of speech. Use an established technical term when the subject requires it. Rephrase before you make a replacement that changes the meaning. (STE 1.1 to 1.4, 9.1, 9.2)
- **W2.** Use technical terms with the meanings and grammatical roles that the vocabulary gives. Qualify a term when the passage could support more than one meaning, for example "world state" and "Lean state". (STE 1.5 to 1.13)
- **W3.** Use one term for one concept in a passage. Do not change between synonyms for variety. Introduce a different technical meaning before you use it. (STE 1.11, 9.4)
- **W4.** Write a multi-word noun with no more than three words. Divide a longer group with words such as "of", "for" or "on". Keep established terms under W5. (STE 2.1, 2.2)
- **W5.** Write a longer technical noun in full the first time. Then use a clear shorter name, a defined abbreviation or a hyphenated form: "Ethereum Execution Layer Specification (EELS)". Do not invent an abbreviation only to shorten the text. (STE 2.2)
- **W6.** Do not use phrasal verbs. Use a direct verb: write "install uv", not "set up uv". If no direct verb keeps the meaning, rewrite the sentence. (STE 9.1, 9.3)
- **W7.** Write English words instead of Latin abbreviations in prose. Write "for example", not "e.g.". Keep official titles and quotations unchanged. (STE GR-6)
- **W8.** Use Oxford spelling in prose: British spelling with "-ize" endings, such as "behaviour", "optimization" and "analyse". American spelling is also correct. Keep one spelling in a file. Keep official names, identifiers and quotations with a different spelling unchanged. Lean declaration names follow the American spelling of Mathlib. Do not convert the spelling of a file except to make the file consistent. (STE 1.14, 9.4)
- **W9.** Use gender-neutral language. Write "they" for a person, not "he" or "she". (STE GR-7)

### Verbs

- **V1.** Prefer the simple tenses, the imperative and the infinitive. Avoid a complex verb form when a simpler construction gives the same information. Keep time and uncertainty: "the archive may have changed" does not mean "the archive changed". (STE 3.1 to 3.4, adapted)
- **V2.** A word that ends in "-ing" can name a technical concept, as "padding", "gas metering" and "differential testing" do. It can also modify a technical noun, as in "hashing interface". Rewrite every other "-ing" form, unless the STE dictionary approves the word, as it approves "during" and "missing". (STE 3.5)
- **V3.** Use the active voice. Name the actor: a definition, a check, the guest, EELS, a fixture, a reviewer or "we". Do not invent an actor. (STE 3.6)
- **V4.** In descriptive text, write a passive construction only if you do not know who or what does the action. A past participle that gives a state is not a passive construction: "the account is empty". (STE 3.3, 3.6)
- **V5.** Use a verb, not an abstract noun phrase, to describe an action. Write "the guest rejects the block", not "the guest performs a rejection of the block". (STE 3.7)
- **V6.** Write "that" after "prove", "show", "assume" or "make sure" when it separates a claim from the verb. Do not add it before an object: "prove the law". (STE GR-1)

### Sentences

- **S1.** Keep to the sentence limit of the text type. Divide a long sentence at a logical boundary, and keep its conditions and qualifications. Count words as §6 specifies. (STE 5.1, 6.3)
- **S2.** Give a sentence one topic. Give a work step one instruction, unless two actions must occur together. (STE 4.1, 5.2)
- **S3.** Put a condition before an instruction when the reader needs it before the action: "If `check-decls` fails, read its report." (STE 5.4)
- **S4.** Use the imperative for work steps. Keep an instruction distinct from a requirement and from a description. When you revise a requirement, keep the force of "must", "may" and "can". (STE 5.3, adapted)
- **S5.** Keep the articles, subjects and verbs that a sentence needs. Do not use contractions to shorten prose. (STE 4.2, 4.5)
- **S6.** Connect related sentences with words such as "and", "but", "then", "thus" or "as a result". Do not expect punctuation alone to show the connection. (STE 4.4)
- **S7.** Give each pronoun a clear antecedent. After "this" or "these", name the noun when the reference could be ambiguous: "this law", not "this". (STE GR-3, GR-4)
- **S8.** Put instructions in the procedure, not in a note. Readers can skip notes, so use notes only for additional information. (STE 5.5)

### Paragraphs and lists

- **P1.** Give each paragraph one topic. Introduce that topic before its details. (STE 6.4, 6.5)
- **P2.** Write no more than six sentences in a paragraph. Divide a paragraph where its subject or purpose changes. (STE 6.6)
- **P3.** Give information gradually. Define a term or a notation before you use it in an explanation. (STE 6.1, 6.2)
- **L1.** Use a vertical list when it makes steps, cases or conditions easier to distinguish. A short series does not always need a list. (STE 4.3)
- **L2.** Introduce a list with a sentence or a clause that ends with a colon. Make sure that each item connects to that introduction. An item can complete the introduction or be a full sentence. (STE 4.3)
- **L3.** Keep the grammatical form and the end punctuation consistent in a list: end every item with a period, or end no item with one. Start each prose item with an uppercase letter, and keep the case of identifiers. Do not end an item with a comma or a semicolon. (STE 4.3, adapted)
- **L4.** Number the work steps when their order matters. Do not number independent facts. (STE 5.2)

### Punctuation and emphasis

- **U1.** Do not use semicolons in prose. Write two sentences or use a conjunction. Do not change punctuation in code. (STE 8.1)
- **U2.** Do not join two clauses with a dash. State the relation in words or write two sentences. A dash can separate a term from its description. This rule does not apply to ranges such as "O1–O13" or to mathematical notation. (*STFspec*)
- **U3.** Use a hyphen to join words that modify a noun as one unit: "fixture-specific special cases". Keep the conventional spelling of an established technical term. (STE 8.2)
- **U4.** Use parentheses for references, identifiers, abbreviations, explanations or alternatives. Keep information that an instruction needs in the instruction itself. (STE 8.3)
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

STE controls the form of a text. These rules control what a text claims, and they have no STE source. When a rule restates a requirement that another document owns, it names that owner.

- **C1.** State only what the code or the recorded evidence establishes. Identify conditional results, open obligations and checks that you did not run. A conditional theorem lists its hypotheses and names the bridge that discharges each one. A pass of the development check does not instantiate a conditional theorem. (CONTRIBUTING §4, release theorems)
- **C2.** Keep the strength of each claim. Keep its hypotheses, quantifiers, negations, failure conditions, failure order and qualifications. Do not change "can" to "does", an inferred result to a verified one, or "recommended" to "required". Keep the `[V]` and `[I]` markers that show verified and inferred claims. (CONTRIBUTING §1, §6.6)
- **C3.** Name the evidence for a claim of conformance or fidelity. The EEST zkevm fixtures at the pinned release are the only conformance evidence, and they are decisive wherever they speak. Outside their coverage, the pinned EELS source governs, and the claim cites it as `file:line`. Neither this spec, nor evm-sail, nor SpecRef, nor any client is more authoritative than the fixtures. (CONTRIBUTING §1)
- **C4.** Do not present agreement with another implementation as evidence of correctness. A differential test or a fuzzing run finds a disagreement to investigate. The fixtures or the pinned EELS source settle it. Proofs about the spec add confidence in properties, but they do not replace conformance. (CONTRIBUTING §1)
- **C5.** Cite each decision, question, interface item, outcome, gap, gate, cost check or discrepancy by its identifier. Examples are `D5`, `Q20`, `F7`, `O13`, `X6`, `G2` and `DISC-001`. Make sure that the identifier exists in its owner document. Do not put an identifier in a Lean declaration name. (`AGENTS.md`, documentation conventions, and CONTRIBUTING §7.2)
- **C6.** Do not cite session notes, local files, prototypes or experiments by a path outside the repository. Replace a temporary planning code with an explanation or a maintained identifier. Such material is evidence at most, and the repository adopts it only through DECISIONS. (`AGENTS.md`, authority order)
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

## 10. Relation to ASD-STE100

| STE part | Use in STFspec |
|---|---|
| Rules 1.1 to 1.4, the general dictionary | Kept as the reference for general meanings and parts of speech. This standard does not reproduce the dictionary, and no tool implements it. |
| Rules 1.5 to 1.13, technical nouns and verbs | Kept. The vocabulary gives them for the protocol, the reference, Lean and the repository. |
| Rules 1.7, 1.12 and 1.13, noun and verb roles | Kept. STE permits one word in both roles when each use meets the rules of its category, for example "hash". |
| Rule 1.14, spelling | Kept as a local directive, not a departure. STE 1.14 permits another official spelling directive. STFspec uses Oxford spelling and also accepts American spelling. Lean declaration names follow Mathlib (W8). |
| All STE rules | Adapted: technical accuracy takes priority. A standard term or language pattern of Ethereum protocol specification, cryptography, computer science or mathematics stays when a rule conflicts with it (§3). |
| Sections 2 to 6, 8 and 9 | Kept as the source principles of the rules in §5, with the adaptations in this table. |
| Rules 3.1 to 3.4, verb forms | Adapted: a modal or complex form stays when a simpler form would lose uncertainty or time (V1). |
| Rule 4.3, list punctuation | Adapted: every item or no item ends with a period (L3), because authors add items to Markdown lists and move them. |
| Rule 5.3, imperative | Adapted: S4 also keeps a requirement distinct from an instruction, and keeps the force of "must", "may" and "can". |
| Section 7, safety instructions | Adapted: the signal words of rule 7.1 are not used. Rules 7.2 and 7.3 apply to operations that can lose work or publish it. Examples are a force-push and a push to `main`. Put the condition or the command before the explanation of its result. |
| Rules 8.4 to 8.7, word count | Kept, with formulas and code spans counted as quoted text. Adapted: URLs and section references also count as one word (§6). |
| General recommendations | GR-1, GR-3, GR-4, GR-6 and GR-7 are repository rules here (V6, S7, W7, W9). They are not STE rules. |
| STFspec additions | The claims rules (§7), dashes between clauses (U2), emphasis (U5) and the "WRITING" prefix for citations (§2). |

ASD owns the copyright and the trademark of ASD-STE100. This standard gives the ideas of the STE rules in its own words and with its own examples. It does not reproduce the text, the examples or the dictionary of STE. STFspec text is not certified STE text. Refer to [ASD's official Issue 9](https://www.asd-ste100.org/assets/files/ASD-STE100_ISSUE9.pdf) for the full rules and dictionary.
