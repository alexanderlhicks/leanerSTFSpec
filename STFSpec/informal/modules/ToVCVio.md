# `ToVCVio`: local canonical RLP reference support

*Status: informal specification; local support implemented, security composition open. Date: 2026-10-02. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: decisions P4, D5, D26; question Q14; security coupling X7; gates REVIEW §§3–4/7.*

`ToVCVio` is a separate library of `STFSpecSecurity/`. It uses existing dependencies only. Its local executable helpers and ordinary laws support future security proofs; they do not install VCV-io or prove whole-trie binding. `EthSecurity` owns agreement and security claims.

## 1. Purpose

Provide a proved canonical RLP facade, faithful child-reference wire/threshold kernel, explicit query-preserving interpretation contract, local same-h collision extractor, and adapter to the actual core `encodeInternalNode`. These helpers sit outside the core and Mathlib bridge under P4.

## 2. Requirements

Retain recursive `Rlp.Encodable`, including joined payload bounds. Thresholds count complete packed RLP, including all headers. Empty child absence, a present empty list, supplied empty leaf values and a 32-byte digest remain distinct. Every query passes through the chosen callback; the core adapter uses the actual installed `KeccakQuery`. Generic naturality requires explicit pure/bind/query laws. Arbitrary direct-style kernels have no naturality guarantee from a capability type alone. No decoder, secure-key, root, error or host policy is introduced.

## 3. EELS source map

No EELS inventory operations are owned here. The adapter consumes `EthCommit` C6 (`src/ethereum/merkle_patricia_trie.py:213–249` at the pin); its complete assembly/threshold laws remain owned by `EthCommit`. Canonical RLP acceptance and representation laws remain owned by `EthCodec`.

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| none | — | — | local security support; no source-operation refinement claim |

## 4. Tests

`ToVCVio.Test.Reference` consumes public declarations. Complete 31/32/33-byte encodings include outer/inner headers. Guards distinguish empty bytes/list/hash, retain leading zeros, certify nested joined payloads and a supplied empty leaf value, preserve arbitrary answers and repeated full query order, and show inline/empty bypass versus exact state-changing hashed failure in both transformer orders. A concrete Id-to-state morphism and installed core adapter client expose their premises. Same-h extraction returns the complete distinct pair, while equal preimages return none. `observations` retains complete result wires, queries, counter and original errors for interpreted/native checks. Release checks include both security libraries, strict ordinary declaration closure and applicable native provenance gates (REVIEW §7).

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

## 6. Data structures

| Object | Representation | Model | Invariant | Persistence | Complexity |
|---|---|---|---|---|---|
| `ValidItem` / `RlpListNode` | certified subtypes | existing RLP item | recursive Encodable / list shape | value | certificate erased; encoder cost owned by EthCodec |
| `ChildRef` | empty/list/hash sum | exact RLP item | inline admissibility means complete encoded size <32 | value | one complete encode, zero or one query |
| `QueryMorphism` | map plus proof fields | selected monad interpretation | pure/bind/query preservation | value | no runtime adapter is adopted |
| `extractCollision` | raw optional byte pair | compared complete preimages | conditional same-h soundness | value | encode each node once and compare complete bytes |

The extractor performs no verification queries. Its soundness hypothesis fixes one chosen `h`; adding a generic effectful verifier would require explicit new effects and laws. No measured C1–C4 cost conclusion follows.

## 7. Contract and laws

`ValidItem.decode_encode`, `decode_eq_ok_iff`, `accepted_image`, `encode_inj`, `encode_prefix_free` and `encode_toList` consume `EthCodec` public canonical/packed laws. `RlpListNode.encode_inj` and `ne_bytes` preserve list shape. `wireItem_encodable`, `wireItem_inj` and `wire_encode_inj` cover all three reference forms, using exact 32-byte digest width and list/bytes disjointness.

`childRefM_eq`, `childRefM_inline` and `childRefM_hash` require only `Monad` and preserve the literal complete-preimage callback action. `childRefM_admissible`, pure-answer and transformer laws state their `LawfulMonad` premises explicitly. Recording, error and lift laws preserve full answers, entered queries and underlying state; no local error is added. `childRefM_natural` uses the supplied `QueryMorphism` fields for this defined kernel only.

`refWithHash_admissible` and `equal_or_collision` use one fixed deterministic `h`. `extractCollision_none_iff`, `extractCollision_of_ne` and `extractCollision_sound` identify the exact full raw pair, distinct wires and equal h answers conditional on equal references. The core adapter laws retain shape, complete-domain and same-query premises described in §5. This is child-reference threshold support; the nonempty top root's unconditional hash is a separate `EthCommit` C8 contract.

### Informal correctness argument

**Claim.** The local reference faithfully represents certified canonical RLP and its explicit callback action; equal references under one chosen hash, together with unequal certified nodes (equivalently unequal complete preimages), expose a raw hash collision under the stated hypotheses.

**Premises.** Recursive/joined Encodable, list shape, exact digest width, the chosen monad laws, explicit query preservation for transport, and identical installed callback action for core comparison.

**Argument.** Core canonical decoding supplies an inverse and injection on the certified domain. List/bytes tags and digest width separate reference forms. Split on complete encoded size: inline returns the original item without a query; hashing forwards one full callback answer. Rewrite pure/bind/query preservation for transport. Equal references either identify their original nodes by injection or identify hash answers; unequal complete encodings then form the extractor's exact raw pair. Rewrite actual core assembly/threshold equations with the same callback to establish the adapter.

**Open obligations.** Canonical Patricia grammar and map representation, witness decoding/authenticity, whole-map binding, generic backend/oracle coupling and a VCV-io QueryHom adapter remain separate work. No security probability or whole guest result follows.

## 8. Composition

- **Depends on:** `EthBase`, `EthCodec`, `EthCommit`; exact direct repository import owners are registered in `contracts.toml`. `Init` laws are standard Lean. No Mathlib or VCV-io module is imported by this slice.
- **Used by:** future `EthSecurity` agreement/ROM development, by citation; no core library imports this proof package.
- **Seams consumed:** recursive RLP domain/canonical/packed laws, `Hash32` exact byte observer, actual `InternalNode` assembly and `KeccakQuery` capability.
- **Guaranteed:** the bounded local contracts in §7, with their explicit law/shape/domain/coupling premises.

## 9. Open decisions

P4 fixes security-only placement. D5 retains the shared-oracle requirement; D26 and Q14 still gate any future external VCV-io pin, imported declaration audit and adapter. This local standard/core layer changes no decision status or question disposition. A future QueryHom adapter must supply this record's actual pure/bind/query laws; it is not installed here.

## 10. Gaps

- **Installed VCV-io adapter:** Q14/D26 pin/dependency adoption, complete imported declaration audit, Hash32/range adapter and exact QueryHom preservation remain open.
- **Whole trie support:** canonical Ethereum HP/keyed-Patricia grammar, map binding, lenient witness provenance and secure-key folding are not supplied by certified arbitrary RLP lists.
- **Oracle/security composition:** X7 generic Models/Progress/provider coherence and whole direct-style kernel interpretation, complete preimage sets, budgets and S2/W1 remain owned by EthSecurity/REVIEW; local transport and raw extraction do not discharge them.
- **Cost and consumers:** actual security consumers and C1–C4 measurements remain open. Native helper checks validate execution/provenance for this scope only.
