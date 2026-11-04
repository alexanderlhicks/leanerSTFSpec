# Writing vocabulary

*Status: current contributor guidance. Date: 2026-11-03.*

Use this vocabulary with the [writing standard](WRITING.md). The STE general dictionary stays the reference for general words, their meanings and their parts of speech. This page adds the technical terms of the Ethereum protocol, the reference, Lean and the repository. It is not a replacement for the dictionary or a list of every permitted English word.

## 1. How to add a term

1. Find the term in the pinned EELS source, an EIP, the Lean documentation or the owner document in this repository.
2. Select the established term instead of a local synonym. For a protocol term, select the term that EELS uses.
3. Record the meaning and the grammatical role when the word can cause ambiguity.
4. Give a qualifier when two technical meanings occur in the same passage.
5. Add a term or a meaning in the change that first needs it.

A noun use and a verb use need separate entries, also when they have the same spelling. An entry for "hash" as a noun does not approve every verb use of that word. A category example is not a reason to reject another established term of that field.

## 2. Terms with a fixed meaning

In STFspec prose, use each term below only with the meaning in the second column. For the other meaning, use the wording in the third column:

| Term | Meaning in STFspec prose | For another meaning, write |
|---|---|---|
| EELS | The Ethereum Execution Layer Specification, which is the Python reference in `ethereum/execution-specs`. "The pinned EELS source" is that source at the commit in `reference.toml`. | The name of the other specification |
| EEST | Ethereum Execution Spec Tests, the test fixtures that an execution-specs release publishes. | Not applicable |
| fixture | An EEST zkevm test case at the pinned release. | "regression fixture" for an input to a repository checker, "test case" for other tests |
| conformance | Agreement with the EEST zkevm fixtures at the pinned release (CONTRIBUTING §1). | "agreement" for a match with another implementation |
| fidelity, faithful | Agreement with the pinned EELS source, read as a specification. | "agreement" for a match with a client or another specification |
| pin, re-pin | The reference versions in `reference.toml`. To re-pin is to move them to another release (DECISIONS P1). | "version" for a dependency in `lake-manifest.json` |
| guest | The stateless validation program of the zkVM, from `statelessInputBytes` to `statelessOutputBytes`. | Not applicable |
| spec | This Lean specification. | "the reference" for the pinned EELS source, "spec guidance document" for a document in `STFSpec/informal/modules/` |
| law | A property that a component contract requires, proved as a theorem. | "lemma" for a helper theorem |
| check | A deterministic test that a tool runs (CONTRIBUTING §5.3). | "review" for a judgment by a person or an agent |
| review | A judgment of a change by a person or an agent. Write "independent adversarial review" for the commit gate of CONTRIBUTING §6.4. | "read" or "examine" for an informal reading |
| work item | A change as CONTRIBUTING §6.4 defines it. | "task" for other work |
| decision, question | An item of DECISIONS, cited by its identifier. | "choice" or "open point" in general prose |
| discrepancy | An entry of DISCREPANCIES, cited as `DISC-n`. | "difference" in general prose |
| gap | An item in §10 of a spec guidance document, or a cross-cutting item in `STFSpec/informal/GAPS-CROSSCUTTING.md`. | "open item" in general prose |
| outcome | A row of the outcome table in CONTRACT, cited as `O1` to `O13`. | "result" in general prose |
| debt | An entry of DEBT, a performance exception under D18. | Not applicable |
| differential testing | A comparison of the outputs of the spec and another implementation on the same inputs. It is a bug-finding tool (CONTRIBUTING §1). | "conformance" only for agreement with the fixtures |

## 3. Terms that need a qualifier

These terms have more than one technical meaning. Qualify a term when the passage could support another meaning:

| Term | Meanings | Clarify when necessary |
|---|---|---|
| state | (a) The world state of accounts, storage and code. (b) A Lean state record such as `BlockState` or `PreState m`. (c) A mathematical state `σ`. | Write "world state", "pre-state", "post-state" or the Lean type name. |
| witness | (a) The `ExecutionWitness` of the guest input, which holds trie-node preimages, codes and headers. (b) A witness of an existential statement in Lean or cryptography. | Write "execution witness" when another meaning is near. |
| proof | (a) A Lean proof. (b) A zkVM proof of guest execution. (c) A Merkle proof in a trie. | Name the kind of proof. |
| commit, commitment | (a) A git commit. (b) A state commitment, which is a trie root (`EthStateCommit`, `EthCommit`). | Write "state commitment" or "trie root" for the protocol meaning. |
| contract | (a) The guest contract in CONTRACT. (b) A component contract in ARCHITECTURE. (c) A model-based contract (D25). (d) A smart contract. | Always qualify: "guest contract", "component contract", "smart contract". Write "signature" or "interface" for a Lean declaration. |
| valid, invalid | Satisfaction of a validity rule of the pinned EELS source, for example a valid block. | Name the rule or the outcome. Write "malformed" for input that fails decoding. |
| reject, rejection | A protocol rejection, one of the three failure channels of D14. | Write "fail" or "refuse" for a tool. |
| error, failure, exception, fault | (a) A typed error (D14). (b) An exceptional halt of an EVM frame. (c) A Python exception in EELS. (d) A reference fault under O13. | Name the channel or the type: "frame exit", "protocol rejection", "internal failure", "Python `IndexError`". |
| revert | The rollback of the state changes of a call frame, for example after the `REVERT` opcode or an exceptional halt. | Write "git revert" for the git command. |
| fork | (a) A protocol fork such as Amsterdam. (b) A fork of a git repository. | Write "protocol fork" or "repository fork" when both occur. |
| frame | (a) An EVM call frame. (b) A framed output record of a native test. | Write "call frame" or "output frame" when both occur, and "stack frame" for a Lean or Python call stack. |
| module | (a) A Lean module, which is one file. (b) A Python module. (c) A spec guidance document. | Write "Lean module", "Python module" or "spec guidance document". |
| library, component | A Lake library, one per component (`EthVmCore`). | Write "dependency" for a third-party package. |
| bridge | (a) The Mathlib bridge package `STFSpecMathlib/`. (b) A theorem that discharges a hypothesis of a conditional theorem (CONTRIBUTING §4). | Write "bridge package" or "bridge theorem". |
| reference | (a) The pinned EELS source and fixtures. (b) A legible reference definition beside a fast definition (CONTRIBUTING §4). | Write "reference definition" for the Lean meaning. |
| native | (a) A Lean test compiled to native code (`lake exe …-native-tests`). (b) A native client such as evmone. (c) A native axiom from `native_decide`. | Write "native test", "native client" or "native axiom". |
| oracle | (a) The reference side of a differential test. (b) A random oracle in `STFSpecSecurity/`. | Write "test oracle" or "random oracle". |
| sound, soundness | (a) Logical soundness of the Lean development (kernel replay, axioms). (b) A security property such as witness soundness. | Name the property and its assumptions. |
| total, totality | A Lean definition that terminates and returns a value on every input (CONTRIBUTING §7.4). | Write "complete" or "whole" for the ordinary meaning. |
| catalogue | The frozen cases and expected values of a differential driver. | "test case" for a single input |

## 4. Technical nouns

These nouns are examples for each subject field. A noun that fits a field is permitted, also when this list does not include it. Introduce a longer or unfamiliar term before you use its abbreviation:

| Field | Examples |
|---|---|
| Protocol: blocks and state | state transition function, block, header, transaction, receipt, withdrawal, request, account, nonce, balance, storage, code, world state, state root, execution witness, protocol fork, signature |
| Protocol: execution and gas | gas, gas limit, gas used, intrinsic gas, refund, blob gas, opcode, precompile, call frame, Keccak-256 |
| Encodings and tries | RLP (Recursive Length Prefix), RLP item, SSZ (SimpleSerialize), Merkle Patricia trie, secured trie, trie node, branch, extension, leaf, trie root |
| Validation | stateless validation, block validation, outcome, protocol rejection, frame exit, internal failure |
| Reference | EELS, EEST, fixture, fixture archive, pin, inventory, source-to-Lean row, discrepancy |
| Testing | conformance, differential testing, differential driver, catalogue, fuzzing, native test, regression fixture, benchmark, correctness gate |
| Specification | library, component, component contract, guest contract, law, obligation, spec guidance document, decision, question, gap, debt, fuel |
| Lean | declaration, definition, theorem, lemma, docstring, axiom, `sorry`, package, Lean module, instance, tactic, elaboration, kernel replay, declaration check |
| Repository | work item, review, verdict, finding, blocker, check, stack, branch, commit, pull request, CI |

## Technical -ing nouns

These terms name technical concepts and supplement the broader technical vocabulary above. They are examples, not a closed approval list. Each table entry describes a whole technical term and its noun meaning; it does not approve every verb use or create a global exemption for a component word.

| Term | Technical meaning |
|---|---|
| `hashing` | The computation of a protocol hash from input bytes |
| `padding` | The byte sequence or rule that extends an encoding to a required width |
| `encoding` | A representation of a protocol value as bytes |
| `decoding` | The inverse operation that reconstructs a protocol value from bytes |
| `gas metering` | The protocol mechanism that accounts for gas costs and limits |
| `differential testing` | See the definition of "differential testing" in §2. |
| `fuzzing` | A test technique that generates varied protocol inputs to find defects |
| `binding` | A commitment property that constrains distinct openings to one committed value |
| `source coupling` | A conformance-driver check that links a fixed catalogue to its source |
| `finding` | A review item classified under CONTRIBUTING §5.5 |
| `cross-cutting gap` | An open specification item that affects several component contracts (GAPS-CROSSCUTTING) |
| `arithmetic reasoning` | A proof method that uses arithmetic laws |
| `spelling` | The conventional sequence of letters in a word, under the language directive of WRITING W8 |
| `warning` | A diagnostic message that identifies a potential problem |
| `framing` | The delimiters and schema boundaries of a structured test output |
| `commitment opening` | The value and evidence that a verifier checks against a commitment |

A technical noun can qualify another noun, as in "hashing interface". Technical modifiers such as "trailing" in "trailing whitespace" also remain permitted. A noun entry does not itself approve a verb use. Clear clauses after prepositions and conventional mathematical introductions follow the local adaptation in WRITING V2; review their actors and meaning manually.

## 5. Technical verbs

Use these verbs with the meaning that the field gives them. Keep the meaning of a verb consistent in a passage:

| Field | Examples of actions |
|---|---|
| Protocol | execute a transaction, validate a block, reject a block, revert a frame, charge gas, refund gas, hash a header, sign a transaction, recover a sender |
| Encodings and tries | encode a value, decode an RLP item, pad a byte sequence, insert a key, delete a key, find a key in a trie |
| Reference and testing | pin a release, re-pin the reference, authenticate an archive, regenerate a generated file, replay a record, fuzz an input |
| Specification | implement an operation, prove a law, discharge a hypothesis, cite a source, record a decision, supersede a document |
| Lean | unfold a definition, elaborate a term, compile a module, instantiate a variable, specialize an interface to `Id`, derive an instance |
| Repository | build a target, run a check, review a change, rebase a branch, merge a pull request, push a branch, retarget a pull request |

"Look up" is a phrasal verb (WRITING W6), so write "find a key in the trie". The noun "lookup" names an operation of the trie (`STFSpec/Commit/Lookup.lean`), and it stays.

## 6. Words to avoid

This table gives prompts for an editing pass over ordinary prose. It does not define STE approval. Use a replacement only when it keeps the meaning and the grammatical role. Rewrite the sentence when a direct replacement does not work:

| Avoid | Use |
|---|---|
| "utilize", "leverage", "make use of" | use |
| "ensure" | make sure that, or name the condition and the action |
| "in order to" | to |
| "prior to", "subsequent to" | before, after |
| "in the event that" | if |
| "comprised of" | has, contains |
| "a number of", "various" | the number, or "some" if the quantity is not specified |
| "e.g.", "i.e.", "etc." | for example, that is, the full list |
| "cf.", "resp.", "w.r.t.", "wlog" | compare, explicit pairs, with respect to, without loss of generality |
| "respectively" | explicit pairs when the reference would otherwise be unclear |
| "robust", "seamless", "comprehensive", "powerful", "elegant", "crucial" | the measurement or the reason (WRITING C9) |
| "clearly", "obviously", "trivially", "basically" | the reason, or delete the word (WRITING C10) |
| "it is worth noting that", "it is important to" | delete the phrase when it adds no information |
| "matches geth", "agrees with geth" | the evidence that decides the case (WRITING C3, C4) |
| "now", "no longer", "previously", "formerly", "currently", "new" | in reference text, the fact about the present state (WRITING C8) |

"The following are equivalent" is a permitted mathematical introduction. "Assuming P, ..." and "Writing f = ..." can also stay under WRITING V2. Words such as "simply" and "essentially" occur in technical terms, for example "simply typed". Read their meaning, and do not delete them as isolated words.