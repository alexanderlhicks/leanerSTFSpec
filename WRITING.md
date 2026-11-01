# Writing in STFspec

*Status: current contributor guidance. Date: 2026-10-31.*

This document sets the rules for English prose in STFspec. It extends [`CONTRIBUTING.md`](CONTRIBUTING.md) §8 and has the same authority. CONTRIBUTING §2 makes legibility a requirement, and these rules apply that requirement to prose.

The rules adapt the writing rules of ASD-STE100 Simplified Technical English (STE), Issue 9. STE makes technical text short, literal and difficult to misread. §9 says how this document relates to STE.

## 1. Scope

The rules apply to prose that a person or an agent writes for the repository:

- Markdown documents, which include the root guides and the documents in `STFSpec/informal/`
- Lean module docstrings, declaration docstrings and comments
- Commit messages, pull request descriptions, issue bodies and review reports.

The rules apply to all authors in the same way. Apply them to the text that you add or change. A change does not have to rewrite text that it does not touch.

The rules do not apply to:

- Lean code, the Lean-like signatures in spec guidance documents, commands and other code
- Quoted text, for example EELS source or an error message
- Titles of documents and other works
- Generated files, superseded material and licence text. [`AGENTS.md`](AGENTS.md) lists the generated files, and superseded material is not rewritten in place.

## 2. Enforcement

The rules are review matters, as CONTRIBUTING §5.3 requires. No CI check approximates them. A reviewer cites a rule by its identifier, for example "S1".

Under CONTRIBUTING §5.5, a finding against these rules is a non-blocking recommendation. The exception is a text that materially misstates what was implemented or verified. Rules C1 to C4 describe such misstatements, and a finding against them can block.

## 3. Text types

STE gives different limits to two types of text. Identify the type of your text before you apply the rules.

| Type | Function | Examples in STFspec | Sentence limit |
|---|---|---|---|
| Procedural | Tells the reader what to do | The task map in `AGENTS.md`, CONTRIBUTING §6, role briefs, numbered steps | 20 words |
| Descriptive | Gives information | Docstrings, comments, spec guidance documents, entries in DECISIONS, DISCREPANCIES and DEBT, commit messages, descriptions, review reports | 25 words |

Do not put procedural and descriptive items in the same list.

## 4. Rules

Each rule names the STE rule that it adapts. The label *STFspec* marks a rule that has no STE source.

### Words

- **W1.** Use the most common word that gives the correct meaning. (STE 1.1)
- **W2.** Use the terms in §7 only with their listed meanings. (STE 1.3, 1.5, 1.8, 1.12)
- **W3.** Use one term for one concept in a text. Do not change between synonyms to vary the text. (STE 1.11, 9.4)
- **W4.** Write a multi-word noun with no more than three words. Use "of", "for" or "on" to divide a longer group. (STE 2.1)
- **W5.** If an established term has more than three words, write it in full the first time. Then use its abbreviation: "Ethereum Execution Layer Specification (EELS)". (STE 2.2)
- **W6.** Do not use phrasal verbs, for example "set up", "carry out", "figure out" or "point out". Use a single verb. (STE 9.3)
- **W7.** Do not use Latin abbreviations, for example "e.g.", "i.e.", "etc.", "cf." or "resp.". Write the English words. (STE GR-6)
- **W8.** Keep the spelling convention of the document that you change. The repository uses both British and American spelling, so do not correct the spelling of text that you do not otherwise change. (STE 1.14, adapted)
- **W9.** Use gender-neutral language. For a person whose pronouns you do not know, use "they". (STE GR-7)

### Verbs

- **V1.** Use the simple present, simple past, simple future, imperative and infinitive forms. Do not use the perfect or the progressive forms. (STE 3.2, 3.4) Write "this pull request adds", not "this pull request has added". After a modal verb, keep the perfect form when it carries a hedge: "the archive may have changed".
- **V2.** Use the "-ing" form only in a technical noun, for example "padding", "hashing" or "gas metering". Do not start a clause with an "-ing" form. (STE 3.5)
- **V3.** Use the active voice. Make the agent the subject: a definition, a check, the guest, EELS, a reviewer or "we". (STE 3.6)
- **V4.** Use the passive voice only when the agent is unknown or not relevant. A past participle that gives a state is not passive voice: "the account is empty". (STE 3.3, 3.6)
- **V5.** Use a verb, not a noun, to describe an action. Write "the guest rejects the block", not "the guest performs a rejection of the block". (STE 3.7)
- **V6.** After "prove", "show", "assume" and "make sure", write "that". (STE GR-1)

### Sentences

- **S1.** Write procedural sentences of no more than 20 words. Write descriptive sentences of no more than 25 words. Count words as §5 specifies. (STE 5.1, 6.3)
- **S2.** Give each sentence one topic. Give each procedural sentence one instruction, unless two actions occur at the same time. (STE 4.1, 5.2, 6.1)
- **S3.** If an instruction has a condition, write the condition first: "If `check-decls` fails, read its report." (STE 5.4)
- **S4.** Write instructions in the imperative. Do not write "you must" before an instruction unless the instruction is important for correctness. (STE 5.3)
- **S5.** Do not omit articles, subjects or verbs to make a sentence shorter. Do not use contractions. (STE 4.2, 4.5)
- **S6.** Connect related sentences with words such as "and", "but", "then", "thus" and "as a result". (STE 4.4)
- **S7.** Make sure that each pronoun refers to one noun. After "this" or "these", write the noun: "this law", not "this". (STE GR-3, GR-4)
- **S8.** Use a note only to give information. Do not put an instruction in a note. (STE 5.5)

### Paragraphs

- **P1.** Give each paragraph one topic. Start the paragraph with a sentence that states that topic. (STE 6.4, 6.5)
- **P2.** Write no more than six sentences in a paragraph. (STE 6.6)
- **P3.** Give information gradually. Define a term or a notation before you use it. (STE 6.1)

### Lists

- **L1.** Use a vertical list for three or more items, steps or conditions. (STE 4.3)
- **L2.** Introduce a list with a sentence or a clause that ends with a colon. Make sure that each item completes that sentence or clause. (STE 4.3)
- **L3.** Start each item with an uppercase letter. Use the same punctuation at the end of all items in a list. Do not end an item with a semicolon. (STE 4.3)
- **L4.** Use a numbered list for steps that occur in a sequence. (STE 5.2)

### Punctuation

- **U1.** Do not use semicolons in prose. Write two sentences. (STE 8.1)
- **U2.** Do not join two clauses with a dash. Write two sentences. (*STFspec*)
- **U3.** Use a hyphen to join words that modify a noun as one unit: "fixture-specific special cases". (STE 8.2)
- **U4.** Use parentheses to give an abbreviation, an explanation, a reference or an alternative. (STE 8.3)
- **U5.** Use bold text only for the term in a definition, the label of a list item or the phrase that states a rule. (*STFspec*)

## 5. Word count

Count words as STE does, with extensions for technical text (STE 8.4 to 8.7). Each of these elements counts as one word:

- A number, or a number with its unit
- An abbreviation, for example "EELS" or "RLP"
- A code span, for example a Lean name, a command or an EELS citation such as `src/ethereum/utils/byte.py:18`
- An identifier of a decision, a question, a gap or a discrepancy, for example `D5`, `Q20` or `DISC-001`
- A section reference, for example "CONTRIBUTING §5.3"
- A hyphenated word
- A quotation, a title or a proper noun
- Text in parentheses.

The text in parentheses also counts as a separate sentence. In a vertical list, the colon ends the introductory sentence, and each item counts as a separate sentence.

## 6. Claims

STE controls the form of a text. These rules control what a text claims, and they have no STE source. Each rule restates a requirement that another document owns, and names that owner.

- **C1.** State only what the code establishes. A conditional theorem lists its hypotheses and names the bridge that discharges each one. A pass of the development check does not instantiate a conditional theorem. (CONTRIBUTING §4, release theorems)
- **C2.** Keep the strength of each claim. Do not remove a hypothesis or a qualifier, and do not change "can" to "does". Do not add a fact that the source does not give. (CONTRIBUTING §1)
- **C3.** Name the evidence for a claim of conformance or fidelity. The EEST fixtures at the pinned release decide each case that they cover. The pinned EELS source decides each other case, and the claim cites it as `file:line`. (CONTRIBUTING §1)
- **C4.** Do not present agreement with another implementation as evidence of correctness. A differential test finds a disagreement to investigate. It does not settle one. (CONTRIBUTING §1)
- **C5.** Cite each decision, question, interface item, outcome, gap or discrepancy by its identifier, for example `D5`, `Q20`, `F7`, `O13`, `X6` or `DISC-001`. Make sure that the identifier exists in its owner document. (`AGENTS.md`, documentation conventions)
- **C6.** Do not refer to session notes, local files, prototypes or experiments by a path outside the repository. Such material is evidence at most, and it enters the repository only through DECISIONS. (`AGENTS.md`, authority order)
- **C7.** In the declaration docstring of a definition that implements an EELS operation, cite that operation as `file:line` at the pin. Cite papers and books in the `## References` section of the module docstring. (CONTRIBUTING §8)
- **C8.** In Lean files and spec guidance documents, describe the present state. Do not narrate history with words such as "now", "no longer", "previously" or "new". DECISIONS, DISCREPANCIES, DEBT and supersession notes record history by design. (`AGENTS.md`, documentation conventions)
- **C9.** Do not use words that claim quality without evidence, for example "robust", "seamless" or "comprehensive". Give the measurement or the reason. A performance claim follows the measurement method of CONTRIBUTING §3. (*STFspec*)
- **C10.** Do not write "clearly", "obviously" or "trivially" in place of an argument. Give the reason or the name of the theorem. (*STFspec*)
- **C11.** State each fact in its owner document only. In other documents, cite the owner and do not restate the fact. (`AGENTS.md`, one owner per fact)

The history of a change belongs in its commit message and its pull request description. Rule C8 applies to the library and its guidance, not to the description of a change.

## 7. Vocabulary

The STE dictionary does not cover the Ethereum protocol or Lean. Thus STFspec uses the STE method for a subject field: a list of technical nouns and technical verbs. The lists are a starting set. Add a term in the change that first needs it. Select the term that EELS uses, and give it one meaning.

### Terms with one fixed meaning

Use each word below only with the meaning in the second column. For the other meaning, use the term in the third column.

| Term | Meaning in STFspec prose | For the other meaning, write |
|---|---|---|
| conformance | Agreement with the EEST fixtures at the pinned release | "agreement" for a match with another implementation |
| fidelity, faithful | Agreement with the pinned EELS source, read as a specification | "agreement" for a match with a client or another specification |
| fixture | An EEST zkevm test case at the pinned release | "test case" or "regression test" for other tests |
| pin | The reference versions in `reference.toml` | "version" for a dependency in `lake-manifest.json` |
| guest | The stateless validation program, from `statelessInputBytes` to `statelessOutputBytes` | Not applicable |
| law | A property that a component contract requires, proved as a theorem | "lemma" for a helper theorem |
| check | A deterministic test that a tool runs, as CONTRIBUTING §5.3 defines | "review" for a judgment by a person or an agent |
| review | An independent adversarial review, as CONTRIBUTING §6.4 defines | "read" or "examine" for an informal reading |
| work item | A change as CONTRIBUTING §6.4 defines it | "task" for other work |
| decision | An item of DECISIONS, cited by its identifier | "choice" in general prose |
| discrepancy | An entry of DISCREPANCIES | "difference" in general prose |
| gap | An item in §10 of a spec guidance document, or a cross-cutting item in `STFSpec/informal/GAPS-CROSSCUTTING.md` | "missing part" in general prose |
| contract | The guest contract in CONTRACT, a component contract in ARCHITECTURE, or a contract of the protocol, for example a smart contract or a contract creation. Qualify each use: "guest contract", "component contract", "smart contract". | "signature" or "interface" for a Lean declaration |

### Technical nouns

The nouns below are examples for each category. A noun that fits a category is permitted, also when this list does not include it.

| Category | Examples |
|---|---|
| Protocol | block, header, transaction, receipt, withdrawal, account, storage, state, state root, witness, fork, gas, opcode, precompile, RLP, SSZ, keccak |
| Reference | EELS, EEST, fixture, pin, inventory, source-to-Lean row |
| Specification | library, component, component contract, guest contract, outcome, law, obligation, spec guidance document, decision, question, discrepancy, gap |
| Lean | declaration, definition, theorem, docstring, axiom, `sorry`, package, module |
| Repository and tools | work item, review, verdict, finding, blocker, check, stack, branch, commit, pull request |

### Technical verbs

These verbs are permitted with the meaning that the field gives them.

| Category | Verbs |
|---|---|
| Protocol | execute, validate, reject, fail, charge, refund, hash, encode, decode, pad |
| Specification | implement, prove, cite, record, supersede, regenerate, discharge |
| Lean | unfold, compile, instantiate, specialize, elaborate |
| Repository and tools | build, review, rebase, merge, push |

"Valid" is a technical word of the protocol, for example a valid block. Use it with that meaning.

### Words to avoid

The words in the first column make text longer, less exact or less literal. Use the word in the second column.

| Avoid | Use |
|---|---|
| "utilize", "leverage", "make use of" | use |
| "ensure" | make sure that |
| "in order to" | to |
| "prior to", "subsequent to" | before, after |
| "in the event that" | if |
| "comprised of" | has, contains |
| "a number of", "various" | the number, or "some" |
| "e.g.", "i.e.", "etc." | for example, that is, the full list |
| "cf.", "resp.", "w.r.t." | compare, two separate clauses, with respect to |
| "respectively" | two separate clauses |
| "the following" | these, or "that follow" |
| "robust", "seamless", "comprehensive", "powerful", "elegant", "crucial" | the measurement or the reason (rule C9) |
| "clearly", "obviously", "trivially", "simply", "basically", "essentially" | the reason, or delete the word (rule C10) |
| "note that", "it is worth noting that", "it is important to" | delete the phrase |
| "now", "no longer", "previously", "formerly", "currently", "new" | in Lean files and spec guidance documents, the fact about the present state (rule C8) |

## 8. Examples

These examples show the rules on STFspec text. The text in the first column is quoted, so it is exempt from the rules.

| Before | After | Rules |
|---|---|---|
| "Fixed padding (previously truncated); now matches geth byte-for-byte." | The helper pads on the left with zero bytes and never truncates, as EELS `src/ethereum/utils/byte.py:18,37` does. | U1, C8, C4, C3 |
| "The stateless theorem is done (modulo the witness bridge)." | The theorem is conditional. It holds if the witness agrees with the full state (S2), and it names the bridge that discharges that hypothesis. | C1, C5 |
| "Make sure checks pass; e.g. run the boundary checker, decls, etc." | 1. Run `lake build --wfail`. 2. Run `scripts/check_boundaries.py`. 3. Run `scripts/check_decls.sh core`. | U1, W7, S2, L4 |
| "Passes the differential against geth, so the refund order is correct." | The differential corpus found no disagreement with geth. No fixture covers the case, so the source-to-Lean row cites the EELS line that decides it. | C3, C4 |
| "This PR has refactored the account API and leverages a cleaner abstraction." | This pull request moves the account operations into one module. | V1, W1, C9 |

## 9. Relation to ASD-STE100

This document keeps the STE rules in sections 2 to 6, 8 and 9, with these changes:

| STE part | Change in STFspec |
|---|---|
| Rules 1.1 to 1.4, the dictionary | Replaced. Rule W1 and the vocabulary in §7 replace the STE dictionary, which does not cover the protocol or Lean. |
| Rules 1.5 to 1.13, technical nouns and verbs | Kept. §7 lists them for this subject field. |
| Rule 1.14, spelling | Adapted. Rule W8 keeps the spelling convention of each document. |
| Rule 4.3, punctuation of list items | Adapted. Rule L3 requires the same punctuation for all items. |
| Rule 8.6, word count | Extended to code spans, citations and identifiers. STE counts a formula as one word. |
| Section 7, safety instructions | Not used. STFspec text has no safety instructions. |

ASD owns the copyright and the trademark of ASD-STE100. This document gives the ideas of the STE rules in its own words and with its own examples. It does not reproduce the text, the examples or the dictionary of the standard. STFspec text is not certified STE text, and this document does not claim compliance with STE. To read the full standard, request a free copy from [ASD](https://www.asd-europe.org/standards-specifications/simplified-technical-english/download-asd-ste-100).
