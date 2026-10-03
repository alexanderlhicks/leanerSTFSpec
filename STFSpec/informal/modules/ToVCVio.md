# `ToVCVio`: local RLP references and faithful Patricia shells

*Status: informal specification; local support implemented, security composition open. Date: 2026-10-03. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: decisions P4, D5, D26; question Q14; security coupling X7; gates REVIEW §§3–4/7.*

`ToVCVio` is a separate library of `STFSpecSecurity/`. It uses existing dependencies only. Its local executable helpers and ordinary laws support future security proofs; they do not install VCV-io or prove whole-trie binding. `EthSecurity` owns agreement and security claims.

## 1. Purpose

Provide a proved canonical RLP facade, faithful child-reference wire/threshold kernel, explicit query-preserving interpretation contract, local same-h collision extractor, and adapter to the actual core `encodeInternalNode`. These helpers sit outside the core and Mathlib bridge under P4. The faithful nonrecursive Patricia shell and separate finite resolved grammar supply local injection/domain facts for later recursive work.

## 2. Requirements

Retain recursive `Rlp.Encodable`, including joined payload bounds. Thresholds count complete packed RLP, including all headers. Empty child absence, a present empty list, supplied empty leaf values and a 32-byte digest remain distinct. Every query passes through the chosen callback; the core adapter uses the actual installed `KeccakQuery`. Generic naturality requires explicit pure/bind/query laws. Arbitrary direct-style kernels have no naturality guarantee from a capability type alone. No decoder, secure-key, root, error or host policy is introduced. `PresentValue` excludes empty encoded bytes locally; total core finite maps and lenient witness acceptance retain their existing behavior. Generic paths permit every finite length, including empty leaf paths.

## 3. EELS source map

No EELS inventory operations are owned here. The adapter consumes `EthCommit` C6 (`src/ethereum/merkle_patricia_trie.py:213–249` at the pin); its complete assembly/threshold laws remain owned by `EthCommit`. Canonical RLP acceptance and representation laws remain owned by `EthCodec`.

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| none | — | — | local security support; no source-operation refinement claim |

## 4. Tests

`ToVCVio.Test.Reference` consumes public declarations. Complete 31/32/33-byte encodings include outer/inner headers. Guards distinguish empty bytes/list/hash, retain leading zeros, certify nested joined payloads and a supplied empty leaf value, preserve arbitrary answers and repeated full query order, and show inline/empty bypass versus exact state-changing hashed failure in both transformer orders. A concrete Id-to-state morphism and installed core adapter client expose their premises. Same-h extraction returns the complete distinct pair, while equal preimages return none. `observations` retains complete result wires, queries, counter and original errors for interpreted/native checks. Release checks include both security libraries, strict ordinary declaration closure and applicable native provenance gates (REVIEW §7).

`ToVCVio.Test.PatriciaNode` covers every shell constructor, HP empty/odd/even/extreme and 129-digit paths, retained lenient raw aliases, all sixteen numeric child positions and terminal-last, zero-hash occupancy, local and resolved branch counts, positive extensions with a resolved branch kind, full 31/32-byte preimages, nested inline lists and long joined headers. Complete certificates and public callback/installed capability adapters retain their premises. The actual C7 two-map test distinguishes stored terminal-empty from absence while observing identical complete preimages; this is a representation ambiguity, not a cryptographic collision. The local faithful domain excludes that map, and the pure safe preparation client requires no unsecured premise.

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

## 6. Data structures

| Object | Representation | Model | Invariant | Persistence | Complexity |
|---|---|---|---|---|---|
| `ValidItem` / `RlpListNode` | certified subtypes | existing RLP item | recursive Encodable / list shape | value | certificate erased; encoder cost owned by EthCodec |
| `ChildRef` | empty/list/hash sum | exact RLP item | inline admissibility means complete encoded size <32 | value | one complete encode, zero or one query |
| `QueryMorphism` | map plus proof fields | selected monad interpretation | pure/bind/query preservation | value | no runtime adapter is adopted |
| `PatriciaNode` | nonrecursive typed shell | actual core assembly | nonempty encoded values; actual child wires | value | fixed sixteen-child assembly; encoder cost owned by EthCodec |
| `FullTree` / `Canonical` | finite nested inductive / ordinary predicate | resolved shape | positive extension to branch; terminal-inclusive occupancy | value | proof model only; no canonicalizer or cost claim |
| `extractCollision` | raw optional byte pair | compared complete preimages | conditional same-h soundness | value | encode each node once and compare complete bytes |

The extractor performs no verification queries. Its soundness hypothesis fixes one chosen `h`; adding a generic effectful verifier would require explicit new effects and laws. No measured C1–C4 cost conclusion follows.

## 7. Contract and laws

`ValidItem.decode_encode`, `decode_eq_ok_iff`, `accepted_image`, `encode_inj`, `encode_prefix_free` and `encode_toList` consume `EthCodec` public canonical/packed laws. `RlpListNode.encode_inj` and `ne_bytes` preserve list shape. `wireItem_encodable`, `wireItem_inj` and `wire_encode_inj` cover all three reference forms, using exact 32-byte digest width and list/bytes disjointness.

`childRefM_eq`, `childRefM_inline` and `childRefM_hash` require only `Monad` and preserve the literal complete-preimage callback action. `childRefM_admissible`, pure-answer and transformer laws state their `LawfulMonad` premises explicitly. Recording, error and lift laws preserve full answers, entered queries and underlying state; no local error is added. `childRefM_natural` uses the supplied `QueryMorphism` fields for this defined kernel only.

`refWithHash_admissible` and `equal_or_collision` use one fixed deterministic `h`. `extractCollision_none_iff`, `extractCollision_of_ne` and `extractCollision_sound` identify the exact full raw pair, distinct wires and equal h answers conditional on equal references. The core adapter laws retain shape, complete-domain and same-query premises described in §5. This is child-reference threshold support; the nonempty top root's unconditional hash is a separate `EthCommit` C8 contract.

### Faithful node and finite shape laws

`terminalItem_inj`, `wireVector_inj`, `toInternalNode_inj` and `assembled_inj` bind all shell fields. Security-local `assembleInternalNode_inj` covers the broader `Option InternalNode` domain using the public assembly equations, HP path/flag injection, two-versus-seventeen arity and numeric vector laws. `branch_child`/`branch_terminal` preserve all positions. `assembled_list` and `asListNode_item` supply complete list shape; `preimage_inj` requires both complete `FitsRlp` certificates, never only field bounds.

Local extension/branch iff laws expose the actual reference/occupancy premises; a zero hash remains occupied. `canonical_extension_iff` and `canonical_branch_iff` expose resolved shape, positivity, children and counts. `not_canonical_zero_extension`, `canonical_one_child_terminal` and `not_canonical_one_child_absent` establish the compression boundary. No digest-only branch-kind claim is supplied. `prepareTrieModel_nonemptyValues` follows solely from public `prepareTrieModel_image_nonempty`, with lawful key order, `KeyBytes`, `TrieValue` and `PrepareSafe`; it requires no unsecured premise, concrete encoding injectivity or frontend policy.

### Informal correctness argument

**Claim.** The local reference faithfully represents certified canonical RLP and its explicit callback action; equal references under one chosen hash, together with unequal certified nodes (equivalently unequal complete preimages), expose a raw hash collision under the stated hypotheses.

**Premises.** Recursive/joined Encodable, list shape, exact digest width, the chosen monad laws, explicit query preservation for transport, and identical installed callback action for core comparison.

**Argument.** Core canonical decoding supplies an inverse and injection on the certified domain. List/bytes tags and digest width separate reference forms. Split on complete encoded size: inline returns the original item without a query; hashing forwards one full callback answer. Rewrite pure/bind/query preservation for transport. Equal references either identify their original nodes by injection or identify hash answers; unequal complete encodings then form the extractor's exact raw pair. Rewrite actual core assembly/threshold equations with the same callback to establish the adapter.

**Open obligations.** Recursive canonicalization/lookup/map uniqueness and reference realization, witness decoding/authenticity, whole-map binding, generic backend/oracle coupling and a VCV-io QueryHom adapter remain separate work. No security probability or whole guest result follows.

## 8. Composition

- **Depends on:** `EthBase`, `EthCodec`, `EthCommit`; exact direct repository import owners are registered in `contracts.toml`. `Init` laws are standard Lean. No Mathlib or VCV-io module is imported by this slice.
- **Used by:** future `EthSecurity` agreement/ROM development, by citation; no core library imports this proof package.
- **Seams consumed:** recursive RLP domain/canonical/packed laws, `Hash32` exact byte observer, actual `InternalNode` assembly and `KeccakQuery` capability.
- **Guaranteed:** the bounded local contracts in §7, with their explicit law/shape/domain/coupling premises.

## 9. Open decisions

P4 fixes security-only placement. D5 retains the shared-oracle requirement; D26 and Q14 still gate any future external VCV-io pin, imported declaration audit and adapter. This local standard/core layer changes no decision status or question disposition. A future QueryHom adapter must supply this record's actual pure/bind/query laws; it is not installed here.

## 10. Gaps

- **Installed VCV-io adapter:** Q14/D26 pin/dependency adoption, complete imported declaration audit, Hash32/range adapter and exact QueryHom preservation remain open.
- **Whole trie support:** one-shell injection and the separate finite resolved shape are supplied above; recursive canonicalization/lookup/uniqueness, actual reference realization, whole-map binding, lenient witness provenance and secure-key folding remain open. Arbitrary certified RLP lists do not prove Patricia child kind.
- **Oracle/security composition:** X7 generic Models/Progress/provider coherence and whole direct-style kernel interpretation, complete preimage sets, budgets and S2/W1 remain owned by EthSecurity/REVIEW; local transport and raw extraction do not discharge them.
- **Cost and consumers:** actual security consumers and C1–C4 measurements remain open. Native helper checks validate execution/provenance for this scope only.
