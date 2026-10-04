# `ToVCVio`: local RLP references and finite Patricia structure

*Status: informal specification; local support implemented, security composition open. Date: 2026-10-04. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: decisions P4, D5, D26; question Q14; security coupling X7; gates REVIEW §§3–4/7.*

`ToVCVio` is a separate library of `STFSpecSecurity/`. It uses existing dependencies only. Its local executable helpers and ordinary laws support future security proofs; they do not install VCV-io or prove whole-trie binding. `EthSecurity` owns agreement and security claims.

## 1. Purpose

Provide a proved canonical RLP facade, faithful child-reference wire/threshold kernel, explicit query-preserving interpretation contract, local same-h collision extractor, and adapter to the actual core `encodeInternalNode`. These helpers sit outside the core and Mathlib bridge under P4. The faithful nonrecursive Patricia shell and separate finite resolved grammar supply local injection/domain facts. `PatriciaStructure` adds exact finite lookup, packed path joining and one-step prefix compression preserving lookup and canonical shape. `PatriciaSupport` supplies complete supported keys for every actual canonical finite tree and two distinct complete keys for every canonical branch. `PatriciaRealization` supplies ordinary Prop existence of a canonical optional resolved root for every actual finite map satisfying `NonemptyValues`, explicitly including the empty map, with exact complete byte observation at every finite key. `PatriciaExtensionality` proves that all-finite full lookup, or complete optional byte observation, determines an already canonical resolved tree or root.

## 2. Requirements

Retain recursive `Rlp.Encodable`, including joined payload bounds. Thresholds count complete packed RLP, including all headers. Empty child absence, a present empty list, supplied empty leaf values and a 32-byte digest remain distinct. Every query passes through the chosen callback; the core adapter uses the actual installed `KeccakQuery`. Generic naturality requires explicit pure/bind/query laws. Arbitrary direct-style kernels have no naturality guarantee from a capability type alone. No decoder, secure-key, root, error or host policy is introduced. `PresentValue` excludes empty encoded bytes locally; total core finite maps and lenient witness acceptance retain their existing behavior. Generic paths permit every finite length, including empty leaf paths.

## 3. EELS source map

No EELS inventory operations are owned here. The adapter consumes `EthCommit` C6 (`src/ethereum/merkle_patricia_trie.py:213–249` at the pin); its complete assembly/threshold laws remain owned by `EthCommit`. Canonical RLP acceptance and representation laws remain owned by `EthCodec`. Structural lookup is a pure resolved-tree model; EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:349–379` has data/default behavior and witness acquisition effects, which these local equations do not refine.

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| none | — | — | local security support; no source-operation refinement claim |

## 4. Tests

`ToVCVio.Test.Reference` consumes public declarations. Complete 31/32/33-byte encodings include outer/inner headers. Guards distinguish empty bytes/list/hash, retain leading zeros, certify nested joined payloads and a supplied empty leaf value, preserve arbitrary answers and repeated full query order, and show inline/empty bypass versus exact state-changing hashed failure in both transformer orders. A concrete Id-to-state morphism and installed core adapter client expose their premises. Same-h extraction returns the complete distinct pair, while equal preimages return none. `observations` retains complete result wires, queries, counter and original errors for interpreted/native checks. Release checks include both security libraries, strict ordinary declaration closure and applicable native provenance gates (REVIEW §7).

`ToVCVio.Test.PatriciaNode` covers every shell constructor, HP empty/odd/even/extreme and 129-digit paths, retained lenient raw aliases, all sixteen numeric child positions and terminal-last, zero-hash occupancy, local and resolved branch counts, positive extensions with a resolved branch kind, full 31/32-byte preimages, nested inline lists and long joined headers. Complete certificates and public callback/installed capability adapters retain their premises. The actual C7 two-map test distinguishes stored terminal-empty from absence while observing identical complete preimages; this is a representation ambiguity, not a cryptographic collision. The local faithful domain excludes that map, and the pure safe preparation client requires no unsecured premise.

`ToVCVio.Test.PatriciaStructure` uses public equations for prefix inverse/composition, exact leaves, extension delegation, all sixteen distinguishable child values, complete join model/index/size laws, arbitrary-tree lookup preservation and canonical preservation. Concrete cases cover absent roots/children, short/long/first/last mismatches, empty and positive extensions, every empty-prefix constructor, positive branch prefixes, deliberately noncanonical extension chains, 129-digit asymmetric joins and canonical one-child-with-terminal/two-child/positive-extension boundaries. Interpreted/native clients retain full queries, optional tags, complete value bytes and joined path/index observers.

`ToVCVio.Test.PatriciaSupport` applies both existential laws to arbitrary canonical inputs and retains arbitrary-length leaves and full nonempty bytes containing zero/255. Concrete clients cover empty/odd/129/137 paths, terminal plus one child at 0/15 with equal values, repeated equal child trees at extremes/interior positions, all sixteen numeric slots with either terminal, nested branch/extension suffixes and complete positive prefixes. Empty/dead branches, one child without terminal and zero extensions are omitted-premise controls. Runtime clients execute specified complete keys and compare None/Some tags and complete bytes; Prop-valued laws provide no runtime witness selector.

`ToVCVio.Test.PatriciaExtensionality` applies all three laws to arbitrary actual trees/roots with both canonicality premises and all-finite full-value/full-byte hypotheses. Clients cover arbitrary Nat and packed paths, empty/odd/even/128/129/137+ complete paths and early/late mismatches, None/Some in both orientations, every numeric slot with both terminals, terminal-plus-one at 0/15, extreme/interior two-child counts, equal values and repeated identical child trees. Syntactically different constant/split and reversed-condition child functions are compared propositionally through public laws and extensionality. Canonical nested branches, positive shared segments, unequal residual lengths and arbitrarily long complete prefixes retain their full queries. Public-equation omission controls include zero extensions, extensions to leaves, dead roots/children and compressible one-child branches. Distinct full present values can have identical support at every key; for every bound n, distinct-value canonical leaves at an n+1-digit path agree below the bound but differ at the full path. Zero/255 and leading/trailing zeros remain in complete bytes. Native clients specify keys directly and preserve optional tags and full values; they neither extract Prop witnesses nor compare function-valued trees executably.

`ToVCVio.Test.PatriciaRealization` retains arbitrary actual maps, insertion and finite histories under explicit nonempty-value premises, and composes the public safe pure prepared-model bridge without an unsecured assumption. Empty/odd/even/129/137 and arbitrary Nat-length paths, empty/prefix-ending keys, repeated equal values, all sixteen numeric slots and terminal-inclusive occupancy boundaries remain covered. Controls exclude stored empty bytes from the domain and from every possible observer witness, separate conflicting full values at one lookup, and distinguish equal support from unequal complete bytes including leading/trailing zero and 255. Explicit canonical runtime fixtures compare full optional bytes against actual maps for complete positive/negative keys and long suffixes; no Prop witness is selected or executable normalizer introduced.

## 5. Interface

Names below are in `ToVCVio.Rlp`, except the explicit oracle record and core adapter. These are compiled APIs; `ValidItem.encode` and `RlpListNode.encode` use the existing core packed encoder.

```lean
abbrev ValidItem := {x : STFSpec.Codec.RlpItem // STFSpec.Codec.Rlp.Encodable x}
abbrev RlpListNode := {x : ValidItem // ∃ xs, x.val = .list xs}
inductive ChildRef where
  | empty | inline (node : RlpListNode) | hashed (digest : STFSpec.Base.Hash32)
def wireItem : ChildRef → STFSpec.Codec.RlpItem
def AdmissibleRef : ChildRef → Prop
def childRefM {m} [Monad m] (q : ByteArray → m STFSpec.Base.Hash32)
  (node : RlpListNode) : m ChildRef
def emptyRefM {m} [Monad m] : m ChildRef
structure ToVCVio.Oracle.QueryMorphism (Input Answer : Type) (m n : Type → Type)
  [Monad m] [Monad n] (qm : Input → m Answer) (qn : Input → n Answer) where
  map : {α : Type} → m α → n α
  map_pure : ∀ {α} (a : α), map (pure a) = pure a
  map_bind : ∀ {α β} (a : m α) (k : α → m β),
    map (a >>= k) = map a >>= fun x => map (k x)
  map_query : ∀ input, map (qm input) = qn input
def refWithHash (h : ByteArray → STFSpec.Base.Hash32) (node : RlpListNode) : ChildRef
def extractCollision (x y : RlpListNode) : Option (ByteArray × ByteArray)
```

`ToVCVio.EthCommit.asListNode node henc` embeds the actual complete `assembleInternalNode (some node)` with its `Encodable` certificate and list shape. `keccak_adapter` fixes the callback to the installed `KeccakQuery.keccak`. The more general `callback_adapter` additionally requires exact item shape and **full action equality** of the chosen callback with that capability at the complete encoded assembly; equal returned digests alone do not identify effects or failure. Both nonempty adapters require `LawfulMonad`; `empty_adapter` requires only `Monad` and `KeccakQuery`.

Names in `ToVCVio.Trie` supply `PresentValue := {b : ByteArray // b ≠ ByteArray.empty}`, `Terminal := Option PresentValue`, and `PatriciaNode` with leaf `(Nibbles, PresentValue)`, extension `(Nibbles, ChildRef)`, and branch `(Vector ChildRef 16, Terminal)`. `toInternalNode`, `assembled`, `preimage` and `FitsRlp` embed the complete actual core assembly and packed encoder. `asListNode` reuses the accepted facade; shell `callback_adapter`/`keccak_adapter` reuse the accepted full-action laws.

`LocallyAdmissible` accepts every leaf path, requires positive/occupied/admissible extension references, and requires all sixteen branch references admissible plus at least two occupied entries counting terminal presence. `FullTree` is a separate finite resolved leaf/extension/branch type, whose branch children are `Fin 16 → Option FullTree`. Its ordinary inductive `Canonical` accepts every leaf, positive extensions to canonical resolved branches, and canonical present children with at least two occupied entries. `CanonicalRoot none` holds; `some` requires `Canonical`. No hashes, stubs, sharing or caches occur in this type. `NonemptyValues` quantifies over every stored map lookup.

`PatriciaStructure` exports the following pure interfaces in `ToVCVio.Trie`:

```lean
def stripPrefix : List (Fin 16) → List (Fin 16) → Option (List (Fin 16))
def lookup (tree : FullTree) (key : List (Fin 16)) : Terminal
def lookupRoot (root : Option FullTree) (key : List (Fin 16)) : Terminal
def observe (root : Option FullTree) (key : Nibbles) : Option ByteArray
def joinPathReference (p q : Nibbles) : Nibbles
def joinPath (p q : Nibbles) : Nibbles
def prepend (p : Nibbles) (tree : FullTree) : FullTree
```

`lookupRoot` is the mutual optional arm for roots and branch children. Leaves require the exact complete remaining path; extensions consume the entire segment; empty branch queries observe the terminal and numeric queries select precisely that child. Lookup accepts every finite tree, including noncanonical trees, with no fuel, hash, default or canonicality premise. `observe` projects full nonempty encoded bytes from inherited `PresentValue`; it performs no runtime filter. `prepend` merges the outer leaf/extension path, retains an empty-prefix branch, and otherwise wraps that branch once. It traverses no descendants and performs no branch collapse.

`PatriciaSupport` exports exactly these ordinary laws over the same actual types:

```lean
theorem canonical_supported (tree : FullTree) (h : Canonical tree) :
    ∃ (key : List (Fin 16)) (value : PresentValue), lookup tree key = some value
theorem canonical_branch_two_keys (children : Fin 16 → Option FullTree) (terminal : Terminal)
    (h : Canonical (.branch children terminal)) :
    ∃ (key₁ key₂ : List (Fin 16)) (value₁ value₂ : PresentValue),
      key₁ ≠ key₂ ∧ lookup (.branch children terminal) key₁ = some value₁ ∧
      lookup (.branch children terminal) key₂ = some value₂
```

These are complete residual keys. Equal values and repeated identical children are allowed; numeric slots are counted separately. No selector or enumeration API is supplied.

`PatriciaExtensionality` exports only these three main-module laws in `ToVCVio.Trie`:

```lean
theorem canonical_lookup_ext (a b : FullTree) (ha : Canonical a) (hb : Canonical b)
    (he : ∀ key : List (Fin 16), lookup a key = lookup b key) : a = b
theorem canonicalRoot_lookup_ext (a b : Option FullTree)
    (ha : CanonicalRoot a) (hb : CanonicalRoot b)
    (he : ∀ key : List (Fin 16), lookupRoot a key = lookupRoot b key) : a = b
theorem canonicalRoot_observe_ext (a b : Option FullTree)
    (ha : CanonicalRoot a) (hb : CanonicalRoot b)
    (he : ∀ key : Nibbles, observe a key = observe b key) : a = b
```

Both inputs must satisfy the actual resolved grammar. Queries range over every finite length, with no value/child distinctness or frontend length premise. The byte observer retains Option tags and entire values. Branch function equality is ordinary propositional `funext`; no executable tree comparison, selector, enumeration or prefix/count API is supplied.

`PatriciaRealization` exports exactly one main-module law in `ToVCVio.Trie`:

```lean
theorem nonemptyValues_realized (obj : Std.ExtTreeMap Nibbles ByteArray)
    (values : NonemptyValues obj) :
    ∃ root : Option FullTree, CanonicalRoot root ∧
      ∀ key : Nibbles, observe root key = obj[key]?
```

This is Prop-only existence over the actual finite-map type, including the empty map. Every stored value must differ from `ByteArray.empty`; no key-length, distinct-value, frontend or unsecured premise is added. Complete None/Some tags and full bytes are retained. All entry, partition, descent, occupancy, choice and map-bridge support stays private. The law supplies no runtime root selector, constructor, normalization API or public uniqueness corollary.

## 6. Data structures

| Object | Representation | Model | Invariant | Persistence | Complexity |
|---|---|---|---|---|---|
| `ValidItem` / `RlpListNode` | certified subtypes | existing RLP item | recursive Encodable / list shape | value | certificate erased; encoder cost owned by EthCodec |
| `ChildRef` | empty/list/hash sum | exact RLP item | inline admissibility means complete encoded size <32 | value | one complete encode, zero or one query |
| `QueryMorphism` | map plus proof fields | selected monad interpretation | pure/bind/query preservation | value | no runtime adapter is adopted |
| `PatriciaNode` | nonrecursive typed shell | actual core assembly | nonempty encoded values; actual child wires | value | fixed sixteen-child assembly; encoder cost owned by EthCodec |
| `FullTree` / `Canonical` | finite nested inductive / ordinary predicate | resolved shape | positive extension to branch; terminal-inclusive occupancy | value | proof model only; no canonicalizer or cost claim |
| `joinPath` | public packed bounded generation | `Nibbles.ofList (p.toList ++ q.toList)` | ordinary all-input equality; total guarded callback | value | no input List materialization in packed runtime; no cost claim |
| `lookup` / `lookupRoot` | mutually structural finite tree/optional arm | exact resolved path observation | no canonicality premise | value | model support; no source resource bound |
| `prepend` | outer-constructor match | prefix removal followed by old lookup | canonical input preserves canonical shape | value | one-step operation only |
| `extractCollision` | raw optional byte pair | compared complete preimages | conditional same-h soundness | value | encode each node once and compare complete bytes |

The extractor performs no verification queries. Its soundness hypothesis fixes one chosen `h`; adding a generic effectful verifier would require explicit new effects and laws. No measured C1–C4 cost conclusion follows.

## 7. Contract and laws

`ValidItem.decode_encode`, `decode_eq_ok_iff`, `accepted_image`, `encode_inj`, `encode_prefix_free` and `encode_toList` consume `EthCodec` public canonical/packed laws. `RlpListNode.encode_inj` and `ne_bytes` preserve list shape. `wireItem_encodable`, `wireItem_inj` and `wire_encode_inj` cover all three reference forms, using exact 32-byte digest width and list/bytes disjointness.

`childRefM_eq`, `childRefM_inline` and `childRefM_hash` require only `Monad` and preserve the literal complete-preimage callback action. `childRefM_admissible`, pure-answer and transformer laws state their `LawfulMonad` premises explicitly. Recording, error and lift laws preserve full answers, entered queries and underlying state; no local error is added. `childRefM_natural` uses the supplied `QueryMorphism` fields for this defined kernel only.

`refWithHash_admissible` and `equal_or_collision` use one fixed deterministic `h`. `extractCollision_none_iff`, `extractCollision_of_ne` and `extractCollision_sound` identify the exact full raw pair, distinct wires and equal h answers conditional on equal references. The core adapter laws retain shape, complete-domain and same-query premises described in §5. This is child-reference threshold support; the nonempty top root's unconditional hash is a separate `EthCommit` C8 contract.

### Faithful node and finite shape laws

`terminalItem_inj`, `wireVector_inj`, `toInternalNode_inj` and `assembled_inj` bind all shell fields. Security-local `assembleInternalNode_inj` covers the broader `Option InternalNode` domain using the public assembly equations, HP path/flag injection, two-versus-seventeen arity and numeric vector laws. `branch_child`/`branch_terminal` preserve all positions. `assembled_list` and `asListNode_item` supply complete list shape; `preimage_inj` requires both complete `FitsRlp` certificates, never only field bounds.

Local extension/branch iff laws expose the actual reference/occupancy premises; a zero hash remains occupied. `canonical_extension_iff` and `canonical_branch_iff` expose resolved shape, positivity, children and counts. `not_canonical_zero_extension`, `canonical_one_child_terminal` and `not_canonical_one_child_absent` establish the compression boundary. No digest-only branch-kind claim is supplied. `prepareTrieModel_nonemptyValues` follows solely from public `prepareTrieModel_image_nonempty`, with lawful key order, `KeyBytes`, `TrieValue` and `PrepareSafe`; it requires no unsecured premise, concrete encoding injectivity or frontend policy.

### Finite lookup and one-step compression laws

`stripPrefix_nil`, `stripPrefix_short`, `stripPrefix_cons`, `stripPrefix_match` and `stripPrefix_mismatch` expose exact steps. `stripPrefix_some_iff` is the inverse equation `key = prefix ++ rest`; `stripPrefix_append`, `stripPrefix_concat` and `stripPrefix_self` fix finite composition and residuals. `lookup_leaf`, `lookup_leaf_some_iff`, `lookup_leaf_exact` and `lookup_leaf_empty` state exact leaf matching. `lookup_extension`/`lookup_extension_append`, `lookup_branch_nil`/`lookup_branch_cons`, `lookupRoot_none`/`lookupRoot_some` and `observe_none`/`observe_some` expose all constructors, numeric positions and optional cases.

`joinPath_eq_reference` is an ordinary equality to the adjacent List reference. `joinPath_toList`, `joinPath_size`, `joinPath_empty_left`/`joinPath_empty_right` and `joinPath_positive_right` follow public `Nibbles` model/generation laws, without access to private packed data. The total callback reads the left bounded index or the right offset bounded index; its fallback is unreachable at generated indices. `prepend_leaf`, `prepend_extension`, `prepend_branch` and `prepend_empty` fix the one-step behavior. `lookup_prepend` holds unconditionally and returns `(stripPrefix p.toList key).bind (lookup tree)`. `prepend_canonical` requires the actual `Canonical tree` and preserves its resolved-branch/positive-segment/occupancy premises. `observe_prepend_join` observes the original suffix bytes after joining the prefix.

The prefix inverse and constructor equations prove exact lookup. Complete indexed observer equality establishes the packed join model. Outer constructor cases, prefix composition and optional bind associativity prove lookup preservation; actual `Canonical` constructors and positive joined segments prove shape preservation. These are local finite-tree laws, with no map realization, source refinement or commitment theorem.

### Canonical finite support laws

**Claim.** Every actual canonical finite resolved tree has a complete supported key; every canonical branch has two distinct complete supported keys, whose values may agree.

**Premises.** The existing `Canonical` predicate and nonempty `PresentValue` type; branch child canonicality and terminal-inclusive occupancy. No map, hash, distinct-value or distinct-child premise is added.

**Argument.** Induction on canonicality uses the exact leaf path, prefixes an extension's child witness, or uses a present terminal at the empty key. A terminal-absent branch has a present canonical child and prefixes its witness by that numeric digit. The private count bridge uses the actual filtered `List.ofFn children`, maps/filter-counts numeric slots and preserves their Nodup; positive count gives one slot and count at least two gives two unequal slots. For two-key support, a present terminal and one child give empty versus cons keys; otherwise unequal child digits separate the complete keys, even when values and suffixes coincide.

**Open obligations.** The existential proofs introduce no runtime selector or operation cost claim. Finite resolved-map existence is supplied below. Executable construction, a public resolved-map uniqueness corollary, global prefix properties, reference realization/binding, source refinement and witness/security composition remain separate.

### Canonical resolved-tree observational extensionality

**Claim.** Exact full lookup at every finite key determines an already canonical resolved tree or optional root. Equal complete optional byte observations at every packed key determine an already canonical optional root.

**Premises.** Actual `Canonical` or `CanonicalRoot` on both inputs; equality of entire optional lookup values or ByteArrays at every finite query. Nonempty values are inherited from `PresentValue`. Equal stored values and repeated identical child trees remain allowed.

**Argument.** Private List.ofFn count/Nodup reasoning finds two unequal numeric positions when terminal is absent; child support then gives a branch key avoiding any selected leading digit. A present terminal supplies the empty key. Thus a canonical branch has no nonempty universally shared prefix. Exact extension support decomposition and finite-prefix antisymmetry identify competing positive extension segments. Induction on canonicality, generalized over the opposing tree, distinguishes leaf singleton support from canonical nonleaves, transports extension-child equality through all suffix queries, and compares branch terminals and every optional child through empty/cons queries and `funext`. Canonical support separates None from Some roots. Public packed/List roundtrips and Option/Subtype projection injection recover full lookup equality from all-finite byte observations.

**Open obligations.** This is observational uniqueness of an already canonical resolved representation. Finite resolved-map existence is supplied below; executable finite-map construction, a public resolved-map uniqueness corollary, normalization, actual reference realization, whole-map preimage/hash binding, witness agreement and generic oracle/security/cost/source correspondence remain separate. Private local shared-prefix reasoning does not discharge global prefix obligations or add a runtime selector.

### Canonical finite-map observational existence

**Claim.** Every actual finite map satisfying `NonemptyValues`, including the empty map, has an actual canonical optional resolved root with exact complete optional byte observations at every finite packed key.

**Premises.** The existing actual `ExtTreeMap Nibbles ByteArray` and `NonemptyValues`; the inherited `PresentValue`, `FullTree`, `CanonicalRoot` and public map/path/lookup/prepend contracts. No different-value, prefix-free-key, key-length, hash, frontend or unsecured assumption is added.

**Argument.** Public finite-map `toList` membership and key-distinctness laws convert the actual stored bindings to private distinct residual keys with certified nonempty values. Strong induction on the sum of residual key lengths plus one per binding realizes each numeric partition after stripping its leading digit; every group strictly decreases for a nonempty parent, including empty groups. Empty residual keys determine the terminal. Filtered `List.ofFn` counts actual numeric slots separately even for identical children. Zero children/no terminal yields None; zero children/present terminal yields an empty-path leaf; one child/no terminal uses public `prepend` lookup and canonicality preservation; terminal-plus-one or at least two children yields the actual canonical branch. Choice combines recursive witnesses inside Prop only. Public membership, packed/List roundtrips and full Option/Subtype projection transfer exact lookup to complete map bytes for every key.

**Open obligations.** The proof supplies no runtime witness selector, constructor, normalization or cost result. A public resolved-map uniqueness corollary, executable finite-map construction, actual C7/C6 reference/effect realization, C8 hashing/source agreement, secure-key folding, witness provenance, whole-map binding and oracle/security/consumer composition remain separate. Total core maps may still store empty bytes; their existing C7 domain and lenient witness behavior are unchanged.

### Informal correctness argument

**Claim.** The local reference faithfully represents certified canonical RLP and its explicit callback action; equal references under one chosen hash, together with unequal certified nodes (equivalently unequal complete preimages), expose a raw hash collision under the stated hypotheses.

**Premises.** Recursive/joined Encodable, list shape, exact digest width, the chosen monad laws, explicit query preservation for transport, and identical installed callback action for core comparison.

**Argument.** Core canonical decoding supplies an inverse and injection on the certified domain. List/bytes tags and digest width separate reference forms. Split on complete encoded size: inline returns the original item without a query; hashing forwards one full callback answer. Rewrite pure/bind/query preservation for transport. Equal references either identify their original nodes by injection or identify hash answers; unequal complete encodings then form the extractor's exact raw pair. Rewrite actual core assembly/threshold equations with the same callback to establish the adapter.

**Open obligations.** Executable finite-map construction, a public resolved-map uniqueness corollary and reference realization, witness decoding/authenticity, whole-map binding, generic backend/oracle coupling and a VCV-io QueryHom adapter remain separate work. No security probability or whole guest result follows.

## 8. Composition

- **Depends on:** `EthBase`, `EthCodec`, `EthCommit`; exact direct repository import owners are registered in `contracts.toml`. `Init` laws are standard Lean. No Mathlib or VCV-io module is imported by this slice.
- **Used by:** future `EthSecurity` agreement/ROM development, by citation; no core library imports this proof package.
- **Seams consumed:** recursive RLP domain/canonical/packed laws, `Hash32` exact byte observer, actual `InternalNode` assembly and `KeccakQuery` capability, plus public `Nibbles` finite model/index/generation laws and the finite resolved lookup/canonical support equations. Canonical resolved-tree observational extensionality and actual finite-map existence retain the premises in §7.
- **Guaranteed:** the bounded local contracts in §7, with their explicit law/shape/domain/coupling premises.

## 9. Open decisions

P4 fixes security-only placement. D5 retains the shared-oracle requirement; D26 and Q14 still gate any future external VCV-io pin, imported declaration audit and adapter. This local standard/core layer changes no decision status or question disposition. A future QueryHom adapter must supply this record's actual pure/bind/query laws; it is not installed here.

## 10. Gaps

- **Installed VCV-io adapter:** Q14/D26 pin/dependency adoption, complete imported declaration audit, Hash32/range adapter and exact QueryHom preservation remain open.
- **Whole trie support:** one-shell injection, finite resolved shape, total resolved lookup, one-step prefix preservation, canonical complete-key/branch two-key witnesses and canonical resolved-tree observational extensionality and finite resolved-map existence for maps satisfying `NonemptyValues`, including the empty map, are supplied above; executable finite-map construction, a public resolved-map uniqueness corollary, actual reference realization, whole-map binding, lenient witness provenance and secure-key folding remain open. Arbitrary certified RLP lists do not prove Patricia child kind.
- **Oracle/security composition:** X7 generic Models/Progress/provider coherence and whole direct-style kernel interpretation, complete preimage sets, budgets and S2/W1 remain owned by EthSecurity/REVIEW; local transport and raw extraction do not discharge them.
- **Cost and consumers:** actual security consumers and C1–C4 measurements remain open. Native helper checks validate execution/provenance for this scope only.
