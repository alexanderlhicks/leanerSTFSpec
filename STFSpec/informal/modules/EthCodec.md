# `EthCodec`: RLP, SSZ, `hash_tree_root` and derived addresses

*Status: informal specification, draft. Date: 2026-10-27. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F1, F13, F17, F18 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D5, D14, D18, D21 · questions: B5/Q21/Q22, B10/Q12, Q20, Q67, Q68, Q69, Q70, Q71, Q72, Q73, Q74, Q75, Q76, Q77, Q78, Q79, Q80, F13, F17, O2.*

Unprefixed paths are relative to `src/ethereum/` at the pin. Two external libraries are part of the semantics:
- **`ethereum_rlp`**: `rlp.py` from `ethereum-rlp` 0.1.6, as locked in `uv.lock`. Historical D1r research used 0.1.7 after comparing the wheels: `rlp.py` and `exceptions.py` were byte-identical (only `__version__` differed). D2r nesting probes and the implemented typed-leaf differential use locked 0.1.6. The latter authenticates installed RECORD/current source and compiles those bytes without admitting cached code.
- **`remerkleable`**: `eth-remerkleable` 0.1.31.

## 1. Purpose

`EthCodec` (layer L0) owns the two wire formats:
- **RLP**: headers, transactions, receipts, trie nodes, account leaves, CREATE preimages and the BAL encoding.
- **SSZ**: the guest's input and output (`StatelessInput`, `StatelessValidationResult`), `NewPayloadRequest` and its `hash_tree_root` (the guest's committed output), and withdrawals and requests.

It also owns **contract-address derivation** (CREATE/CREATE2). That derivation needs RLP and Keccak, and it must be visible to both `EthVmInstructions` and `EthBlock` (`fork.py:638`). `EthCodec` is the lowest library both may import. Concrete schemas (which fields, which limits) belong to their owners (`EthBlock`, `EthStateless`). `EthCodec` supplies the generic machinery and its laws.

## 2. Requirements

### RLP encoding (`ethereum_rlp/rlp.py:66–135`)

- **E1. Byte strings.**
  - A single byte `< 0x80` encodes as itself.
  - A string of length `< 56` encodes as `0x80+len ‖ data`.
  - A longer string encodes as `0xB7+|L| ‖ L ‖ data`, where `L` is the minimal big-endian length.
- **E2. Lists.** The payload is the concatenation of item encodings. A payload of length `< 56` gets the header `0xC0+len`; a longer one gets `0xF7+|L| ‖ L`.

**Total-domain scope (Q47).** E1–E2 standard RLP and pinned-dependency correspondence are stated under `Encodable`: every item payload length has an at-most-eight-byte length prefix. The total encoder and prefix helper compute the tag in UInt8 (modulo 256) and retain exact, unbounded minimal big-endian length digits outside this domain; their packed implementation must equal the total byte-list model for every item. This completion supplies no outside-domain protocol acceptance/rejection, injectivity, decoder canonicality or pinned-host/resource claim. Locked `rlp.py:104–108,122–126` has no explicit eight-digit guard: byte construction rejects list tags at nine length digits and string tags at 73. Those conceptual constructor bounds are separate from physical allocation limits.

- **E3. Typed values.**
  - `Uint`/`FixedUnsigned` encode as the byte string `to_be_bytes()`, which is minimal. **Zero is the empty string (`0x80`), never `0x00`** (`:77–78`; `ethereum_types/numeric.py:477`).
  - `bool` encodes as `0x01` or the empty string (`:79–83`).
  - `str` encodes as its UTF-8 bytes.
  - Dataclasses encode as the list of their fields (`:84–85`).
  - A plain Python `int` raises `EncodingError`; this is unreachable in well-typed EELS.

### RLP decoding (`rlp.py:143–543`)

- **D1r. Untyped decode.** `decode(b)` succeeds **iff `b` is exactly the encoding of some item**. It rejects, all with `DecodingError`:
  - empty input (`:148`);
  - trailing bytes after any item (`:400,422,436,455`), including after a single byte `< 0x80`, which is reported as "negative length" (`:394–397`);
  - declared lengths exceeding the input (`:398,410,419,434,441,453,476,519,535`);
  - a one-byte string `< 0x80` in prefixed form (`:403–404`);
  - a long-form length with a leading zero byte (`:412,443,521,537`);
  - a long form used for a length `< 56` (`:417,448`).

  Items inside a list are decoded recursively from their exact extent (`:464–484`). *Verified empirically on ethereum-rlp 0.1.7 (`rlp.py` byte-identical to the locked 0.1.6):* 200k structured mutations of random encodings plus 300k random ≤5-byte strings produced no accepted non-canonical input, and no exception other than `DecodingError`. This is evidence, not a proof; the proof is the [C] canonicality obligation in §7.
**Header-helper scope (`rlp.py:488–543`).** `decodeItemLength b pos` reports
`decode_item_length(b[pos:])`'s declared encoded extent. Short forms require only
the tag. Long forms require all one-to-eight length digits and reject a leading
zero; header truncation precedes that rejection. They still accept lengths below
56, missing declared payloads and trailing bytes. Prefixed single bytes below
0x80 are also accepted by this helper. The full decoder and
`decode_joined_encodings` (`:465–484`) own payload availability, full consumption
and item canonicality. An empty or out-of-range cursor fails as empty. Extents
use Nat: an eight-byte length of 2^64−1 gives extent 2^64+8, with no wrap or
allocation proportional to that declaration.

- **D2r. Deep nesting is a host-limit case (O12).** Decoding recurses about 3 Python frames per nesting level. `ethereum/__init__.py:30` sets the recursion limit to `max(12288, current)`, but the guest also imports py_ecc, which raises it, so the **guest-process limit is 100,000**. Deterministic probe inputs (payload transactions with deep RLP nesting) showed that 20,000 nested lists in a payload transaction decode, while 40,000 and 120,000 raise **`RecursionError`**, not `DecodingError`. (With only `import ethereum`, the threshold is between 4,000 and 5,000 levels.)
  - Witness nodes and headers are at most 2^10 bytes (`stateless.py:35–36`), so they cannot reach this.
  - Transactions are `progressive_byte_list` with no size limit (`execution_engine/types.py:64–67`), so a deep-nesting transaction reaches it inside `decode_transaction` (`transactions.py:573–585`). **On the complete guest path** the first decode is in `is_valid_versioned_hashes` (`execution_engine/new_payload.py:60–68`), whose local catch-all consumes the `RecursionError`, so the output is O6 `(root, false, …)` (DISC-006). A standalone `execute_block` call would raise it from its own decode.

  The spec's total decoder returns a nested `RlpItem` there, and the **typed** decode then fails, because no transaction schema nests more than about 4 levels. On the guest path both sides then give O6, so the output agrees. The reference side is witnessed by probe `tx-deep-rlp-40000`, the DISC-001 reproducer; the typed-depth bound on the spec side is argued, not proved (§10). The case stays under CONTRACT O12 / DISC-001 (DECISIONS Q20), which is unresolved by design.
- **D3r. Typed decode (`decode_to` / `deserialize_to`, `:162–384`).**
  - Integers must be byte strings with **no leading zero** (`:270–271`), and for fixed widths **at most `width` bytes** (`FixedUnsigned.from_be_bytes` length check, `numeric.py:573`).
  - Fixed bytes require the exact length (`bytes.py:34`). `Bytes` requires a string, not a list.
  - `bool` accepts only the empty string or `0x01` (`:245–251`).
  - A dataclass requires a list with exactly as many items as it has fields (`:222–228`).
  - `Tuple[T, ...]` and `List[T]` accept any length.
  - The supplied generic list adapter preserves complete ordered child models
    (`:70–78,112–135`). List typing checks `toList` shape first, then core `mapM`
    preserves empty success and the complete first child error (`:191–205,311–318,370–384`).
    It introduces no default element, cap, normalization, sorting or deduplication.
  - A `Union` requires **exactly one** alternative to succeed (`:325–343`; used for `to: Bytes0 | Address`).
  - `decode_to` **wraps every exception raised during typed deserialization into `DecodingError`** (`:167–171`). The header fallback in `stateless.py:234–237` (Amsterdam `Header`, then `PreviousForkHeader`) depends on this. The raw `decode` step is *outside* that wrapper, so a `RecursionError` there is not converted (D2r).
- **D4r. Naive-reading trap.** A fixed-arity `Tuple[A, B]` target is decoded with `zip` (`:346–367`), which has **no length check**: extra items are dropped, and missing items give a shorter tuple. I found no fixed-arity RLP tuple target in the Amsterdam decode sites (`transactions.py:573–585`, `blocks.py:434`, `stateless.py:235–237`); all use dataclasses. The spec therefore does not model this laxity. Any future use must be flagged.

### Contract addresses (`forks/amsterdam/utils/address.py`)

- **A1.** `compute_contract_address(a, n) = keccak256(rlp([a, n]))[12:32]`, with `n : Uint` minimally encoded (`:42–63`). The final `left_pad_zero_bytes(…, 20)` is a no-op.
- **A2.** `compute_create2_contract_address(a, s, c) = keccak256(0xff ‖ a ‖ s ‖ keccak256(c))[12:32]` (`:66–93`).
- **A3.** Both keccaks of A1 and A2 go through `KeccakQuery` (D5): the derivations are generic in `{m} [Monad m] [KeccakQuery m]` (CREATE2 makes two queries), and the pure forms are their `Id` specialisations.

### SSZ (`utils/ssz.py` over `remerkleable`)

- **S1. Schema language.** EELS dataclasses map to SSZ types by `_infer` (`ssz.py:179–205`):
  - `FixedBytes` subclasses become `ByteVector[LENGTH]`;
  - `FixedUnsigned` subclasses become `uint(bitlen(MAX))`;
  - `bool` becomes `boolean`;
  - `SszContainer` subclasses become containers, and `ProgressiveSszContainer` subclasses become progressive containers with **all active fields = 1** (`:250–251`);
  - `Annotated` markers select `uint(bits)` for `bits ∈ {8,16,32,64,128,256}` (`:91–95`), `byte_vector(n)`, `byte_list(N)`, `ssz_list(N)`, `progressive_list()` or `progressive_byte_list()`.

  An unannotated `Uint` is a schema `TypeError`, not a runtime case. Annotated fields may be *wider* in Python than on the wire, e.g. `timestamp: Annotated[U256, uint(64)]` and `block_number: Annotated[Uint, uint(64)]` (`execution_engine/types.py:57–62`). Decoding converts with `base(int(v))` (`ssz.py:309–310`), which cannot fail for decoded values.
- **S2. Serialization** is standard SSZ:
  - fixed-size fields are written inline, and each variable-size field is a 4-byte little-endian offset followed later by its payload;
  - lists of fixed-size elements are concatenated, and lists of variable-size elements get an offset table;
  - `uintN` is little-endian and `boolean` is `0x00`/`0x01`.

  **Progressive lists serialize exactly like lists, and progressive containers exactly like containers.** `active_fields` is not serialized; I checked this on remerkleable.
- **S3. Decoding.** It must accept **exactly the canonical encodings.** EELS gets this by decoding with remerkleable and then requiring `view.encode_bytes() == data` (`ssz.py:137–146`). This matters because remerkleable alone is permissive:
  - `Container.deserialize` checks only `first_offset ≥ fixed_size` (`remerkleable/complex.py:948–950`), not equality;
  - it then reads variable fields *sequentially from the stream position*, not from their offsets.

  So an offset gap silently misaligns the fields. I checked this: `C{a: uint16, b: ByteList[10], c: ByteList[10]}` with a 1-byte gap decodes to `b = 0x0061, c = 0x6263`. The re-encode check then rejects it. The spec's decoder must be a **strict canonical decoder**; equality of its accept set with an encoder image needs a separately resolved inverse domain (§7). Q80 forward support alone is insufficient.

  The consequences cover all O1 SSZ cases (CONTRACT §4). A decoder must reject all of the following:
  - wrong total length for fixed-size types;
  - a first offset other than the fixed-part size;
  - decreasing offsets, or offsets beyond the scope;
  - a variable-element list whose first offset is not `4·count`, including a non-empty scope with first offset 0 (`tests/json_loader/test_ssz.py:126`);
  - an element or field size outside `[min, max]` (`complex.py:186–220`);
  - `ByteList`/`List` over its limit (`byte_arrays.py:173–178`; `complex.py` `is_valid_count`);
  - a `boolean` byte other than `0x00`/`0x01` (`basic.py:56–61`);
  - trailing bytes.
- **S4. `hash_tree_root`**, with `H(a, b) = sha256(a ‖ b)` (`remerkleable/settings.py:16–17`), `pack` = right-zero-padded 32-byte chunks, and `mix(r, n) = H(r, n as uint256 LE)`:
  - `uintN`/`boolean`: the value as little-endian bytes, padded to 32. Lists of basic values are packed.
  - `ByteVector[n]`: `merkleize(pack(b), ⌈n/32⌉)`.
  - `ByteList[N]`: `mix(merkleize(pack(b), ⌈N/32⌉), |b|)`.
  - `List[T, N]`: `mix(merkleize(roots or packed chunks, limit), count)`.
  - `Container`: `merkleize(field roots, #fields)`.
  - **Progressive list / byte list** (EIP-7916): `mix(prog(chunks), count)`. Here `prog([]) = 0^32` and `prog(c, k) = H(merkleize(c[:k], k), prog(c[k:], 4k))`, starting from `k = 1` (`remerkleable/progressive.py:25–32,118`).
  - **Progressive container** (EIP-7495): `H(prog(field roots, with 0^32 at inactive positions), active_fields as a 256-bit little-endian bitvector chunk)` (`progressive.py:500–530`).
  - `merkleize(c, L)` pads to the next power of two ≥ `L` using precomputed zero hashes.

  *Verified empirically*: I checked every formula above against remerkleable 0.1.31 on 200 random instances each of `ProgressiveByteList`, `ProgressiveList[ByteList[1024]]`, `List[ByteList[1024], 256]` and `ProgressiveList[uint64]`, plus a 3-field progressive container. The spec follows remerkleable, the pinned dependency. Agreement with the EIP texts was **not** checked (§10).
- **S5. Totality of the committed root.** `compute_new_payload_request_root` (`stateless.py:226`) is outside the inner handler, so a failure there would give the zero sentinel (O2). The spec must prove that `hashTreeRoot` is total on every decoded value, which would make O2 unreachable; a constructor is added only if that proof fails (CONTRACT O2; DECISIONS §3, O2, open). The `_to_view` conversion observation is evidence only: prove the actual decoded domain is Rootable, including progressive counts/mix-ins and schema adapters; resolve host-resource differences separately. No unrestricted O2-freedom theorem is established.
- **S6. Output encoding.** The only SSZ value the guest *encodes* is the fixed-size 43-byte `StatelessValidationResult` (CONTRACT §3). Encoding arbitrary values can fail in remerkleable when a written offset reaches 2^32 (`encode_offset` via `uint32`, `complex.py:23–24`). Q80 selects the proof-domain `encode` contract in §5/§7: actual recursive support and every emitted start `< 2^32`, without a final-payload bound. The generic forward encoder is supplied (§3); the guest output consumer theorem remains open.

## 3. EELS source map

### Implemented RLP encoder slice

`STFSpec/Codec/RlpEncode.lean` implements the pure total encoder on the public
`RlpItem` model. **Discharged:** its packed output equals the total readable
byte-list reference on every item, and the computed size equals actual output
width. Standard RLP/pinned-source correspondence retains `Encodable` (Q47).
Byte/list payloads and all length digits are preserved in order. Raw wire laws
are owned by §7; schema instances and guest outcomes remain unimplemented.

| Locked dependency source | Lean declaration and public type | Domain, value/effects | Ordered failures | Public law and deterministic regression |
|---|---|---|---|---|
| `ethereum_rlp/rlp.py:66–88` (0.1.6), raw byte/list dispatch | `Rlp.encode : RlpItem → ByteArray` | every model item; two-pass packed total byte-model completion, no effects; pinned/standard scope `Encodable` | none; Q47 defines completion outside the correspondence domain | `toList_encode`, `size_encode`; empty/ordered nested/asymmetric zero models |
| `ethereum_rlp/rlp.py:90–109` | `Rlp.encodeBytes : ByteArray → ByteArray` | every byte string; singleton<80 itself, otherwise header then original bytes | none; standard/pinned scope `Encodable (.bytes b)` | `encodeBytes_single`, `encodeBytes_short`, `encodeBytes_long`, `size_encodeBytes`; 00/7f/80, 55/56, 255/256 |
| `ethereum_rlp/rlp.py:100–108,119–126`; `ethereum_types/numeric.py:477–484` (0.4.1) | internal `Rlp.encodeLengthPrefix : UInt8 → UInt8 → Nat → ByteArray`; public `lengthPrefixModel` observation | every length/base tag; short tag or long tag plus exact minimal BE digits; tags modulo256 per Q47 | none; source correspondence only at standard tags with ≤8 digits | `toList_encodeLengthPrefix`, `size_encodeLengthPrefix`, `length_digits_value/width/head/order`, `short_tag_toNat`, `long_tag_toNat`; 255/256/65535/65536 and symbolic 8/9/72/73-digit helper cases |
| `ethereum_rlp/rlp.py:112–128` | list branch `Rlp.encode (.list xs)`; `Rlp.encodeModel : RlpItem → List UInt8` | header length counts encoded child bytes, never item count; ordered complete payload; total model completion | none; standard/pinned scope `Encodable (.list xs)` | `toList_encode_list`, `encode_list_short/long`, `size_encode_list`; payload55/56 from empty children and single prefixed strings |
| `ethereum_rlp/rlp.py:130–135` | reference `Rlp.encodePayloadModel : List RlpItem → List UInt8` | exact ordered concatenation of encoded child models; runtime uses cached packed writers | none | `encodePayloadModel_append`, `encodePayloadModel_eq_flatMap`, `length_encodePayloadModel`; empty/nested/mixed children |
| derived from the prefix cases above, no extra Python acceptance guard | `Rlp.encodedSize : RlpItem → Nat`; `Rlp.Encodable : RlpItem → Prop` | cached size pass; every recursive item payload has ≤8 minimal length digits; refinement hypothesis rather than protocol limit | none; no rejecting API | `encodedSize_eq_model_length`, `encodable_bytes_iff`, `encodable_list_iff`, `encodable_bytes_tag`, `encodable_list_tag` |

**Checks and provenance.** `RlpEncodeGuards.lean` supplies strict deterministic
byte/list/prefix/typed-leaf composition cases. `RlpEncodeCallerProofs.lean` uses only
public model/size/domain contracts. `rlp_encode_differential.py` reuses the typed
driver's authenticated current-source/RECORD loader, frozen `-I -B` interpreter and
pinned EELS byte checks. Its seed5023 bounded raw bytes/list trees reach depth32,
string lengths1024, sibling counts256 and mixed nested cases; the Nat handoff
is supplied below. It checks exact Python input/result classes before observations,
including11 negative shape controls. Whole returned bytes, byte helper dispatch,
sequence dispatch and joined payloads are compared, not checksums. Lengthy Lean
literals are chunked and constant-byte runs use `List.replicate`, without
changing limits or tested bytes. Interpreter/startup,
frozen installation and RECORD remain trust inputs. These are finite actual
encoder observations, not EEST guest execution or a Python equivalence proof.

### Implemented typed RLP encoding foundation

`STFSpec/Codec/RlpEncodeOf.lean` supplies the one-field `RlpEncode (α : Type)`
class, its direct reference wrapper and only the Nat encoding instance. The
class has no inverse, domain or proof field. All naturals remain valid inputs,
including values above 2^256; Q47 retains the standard wire/source domain.

| Locked dependency source | Lean declaration and public type | Domain, value/effects | Ordered failures | Public contract and deterministic regression |
|---|---|---|---|---|
| `ethereum_rlp/rlp.py:66–88` (0.1.6), typed dispatch | `RlpEncode (α : Type)` with exactly `toRlp : α → RlpItem` | complete supplied model adapter; instance schema laws remain separate | no local rejection or diagnostic mapping | private generic wrapper/complete byte-model/size clients use the supplied field and existing public encoder laws |
| `ethereum_rlp/rlp.py:66–135` | `Rlp.encodeOf : [RlpEncode α] → α → ByteArray` | exactly `Rlp.encode (RlpEncode.toRlp a)`; pure, total reference composition | none; no decoder or error-policy choice | private composition through `toList_encode` and `size_encode`; private nominal carrier with complete nontrivial bytes |
| `ethereum_rlp/rlp.py:77–78`; `ethereum_types/numeric.py:477–484` (0.4.1) | Nat's `RlpEncode` instance, with field exactly `Rlp.ofNat` | unbounded minimal unsigned payload; empty zero | none; source input is exact Uint, not Python int | private adapter identity and conditional raw-wire image via `decode_encode`; bounded caller discharges `Encodable (ofNat n)` for n<2^256 using public leaf/Base laws |

**Checks and provenance.** `RlpEncodeOfCallerProofs.lean` supplies eight private
consumer proofs through the Codec facade, without unfolding underlying providers.
`RlpEncodeOfGuards.lean` compares every output byte in sixteen handwritten cases:
zero/1/127/128/255/256/1024, asymmetric zero-containing digits, 2^64 and 2^256
boundaries and two private nominal carrier inputs. There is no exported helper-law
family. `rlp_encode_differential.py` retains seed5023 and its hundred random raw
trees, with 141 total raw-tree observations and complete byte/helper/payload checks.
Its exactly 22 Nat cases span 0/1/2, singleton transitions, asymmetric digits,
2^64/2^256 boundaries and payload widths55/56/255/256/257. Each actual
`rlp.encode(Uint(n))` produces both the existing raw `encode (ofNat n)` and new
`encodeOf (n : Nat)` complete-byte guard: 326 guards in total compiled successfully.
Before oracle encoding, exact nonnegative Python int and original authenticated
Uint identity are required; exact bytes are required before comparison/emission.
Fourteen bounded Nat/Uint admission controls reject bool, negative/plain wrong
numeric/string/bytes classes and another unsigned class, alongside the eleven
retained raw-shape controls. Source/executable/class identity and current
source/RECORD/runtime bodies are bound before/after the frozen `-I -B` profile.
Interpreter/native runtime, startup, installation and RECORD remain trust inputs.
This is bounded encoder evidence, without typed decoding/inverse, all-Nat Python
equivalence, host/resource, guest/EEST or throughput claims. `RlpDecode`,
`decodeTo` and Nat decoding are supplied by the typed decoding foundation below;
schema instances remain open. Q68 owns the diagnostic equation.

### Implemented typed RLP decoding foundation

`STFSpec/Codec/RlpDecodeOf.lean` supplies the independent one-field `RlpDecode`
class, literal raw-first `decodeTo`, Nat's exact `toNat` instance, and only the
ordinary conditional `decodeTo_encodeOf_nat` law. No class proof field, public
helper-law family, error or observation projection is added. The runtime accepts
all naturals; `Encodable (ofNat n)` remains explicit in the roundtrip theorem.

| Locked dependency source | Lean declaration and public type | Domain, value/effects | Ordered failures | Public contract and deterministic regression |
|---|---|---|---|---|
| `ethereum_rlp/rlp.py:162–171` (0.1.6), supplied typed dispatch | `RlpDecode (α : Type)` with exactly `ofRlp : RlpItem → Except RlpError α` | total supplied model callback, independent of encoding | every supplied error and complete success retained | private decode-only/encode-only carriers and arbitrary complete-result forwarding |
| `ethereum_rlp/rlp.py:167–171` | `Rlp.decodeTo : [RlpDecode α] → ByteArray → Except RlpError α` | direct reference composition, no effects | raw failure unchanged before typing; raw success returns whole typed result | literal equation;168 whole-result controls including90 raw-first controls and21 arbitrary typed errors |
| `ethereum_rlp/rlp.py:204–205,263–273`; `ethereum_types/numeric.py:517–540` (0.4.1) | Nat's `RlpDecode` instance with field exactly `Rlp.toNat` | intended source is exact Uint, unbounded; empty payload zero | list shape, then leading zero; no fixed-width bound | `decodeTo_encodeOf_nat` composes public `decode_encode`/`toNat_ofNat` with explicit `Encodable`; Nat wires include internal zeroes and above-U256 values |

**Proof clients and limits.** Eight private groups cover the whole equation and
class independence, raw failure, whole typed forwarding, generic inversion with
both caller-owned premises (and a noninverse counterexample), Nat adapter and
conditional theorem, a bounded local domain discharge, successful Nat exact
reencoding/domain recovery, and the existing single-channel observation. These
use public raw/leaf/Base laws and reduce only the new adapters. They prove no
arbitrary instance pair inverse or all-Nat `Encodable` assertion. Source causes,
class/reflection/callback/host admission and the first consuming handler remain
local premises (D14, Q20/O12); no schema, EEST/guest, cost or readiness gate closes.

**Wire evidence.** `rlp_decode_of_differential.py` provides the seed5029 narrow
profile:59 authenticated source encoder entry calls and283 actual original
`decode_to(Uint, bytes)` calls, with25 exact-type and eight exception-admission
negative fixtures. The schedule retains30 literal raw failures,22 Nat encodings,
ten typed failures,12 byte widths, seven depths, eight list widths,128 random
wires and66 mutations. Maximum wire length is1027, depth32 and sibling width256.
The controller checks exact original Uint before integer conversion and exact
bytes, authenticates source code/class bindings and current RECORD inventories,
and admits only original raw raise sites or typed outer171 with cause269/271.
It retains complete errors, causes, tracebacks and whole generated Except guards.
Interpreter/native runtime, startup, frozen installation/RECORD and Lean compiler
remain trust inputs. The fresh 2026-10-23 frozen `-I -B` execution completed all
283 wire calls (34 accepted,249 rejected),59 encoder entries and283 complete
emitted guards, which compiled successfully. Normal and `-O` helper runs each
passed25 type and eight exception negative fixtures. Complete original wire,
success/error/cause/traceback observations and source/runtime/controller/all483
candidate body/mode snapshots were retained and unchanged before/after execution.
These are finite source observations, with no generic Python or host equivalence
claim.

### Implemented ByteArray RLP instances

`STFSpec/Codec/RlpByteArray.lean` supplies exactly the byte-string encoding and
decoding instances and one ordinary conditional instance inverse. Every byte,
including zeros and leading zeros, remains data; no integer normalization applies.

| Locked dependency source | Lean declaration and public type | Domain, value/effects | Ordered failures | Public law and deterministic regression |
|---|---|---|---|---|
| `ethereum_rlp/rlp.py:70–72` (0.1.6); `ethereum_types/bytes.py:165` (0.4.1) | `RlpEncode ByteArray`, field exactly `RlpItem.bytes` | every mathematical ByteArray, complete payload; pure | none; standard/source domain retains Q47 | `decodeTo_encodeOf_byteArray` with explicit `Encodable (.bytes b)`; empty, singleton00/7f/80/ff, leading/internal zeros, payload55/56/255/256 |
| `ethereum_rlp/rlp.py:206–207,254–262`; `ethereum_types/bytes.py:165` | `RlpDecode ByteArray`, field exactly `Rlp.toBytes` | original source Bytes is builtin bytes; every model byte leaf preserved | existing `.shape "bytes"` on lists after complete raw success; every raw diagnostic wins unchanged (Q68) | public `toBytes_eq_ok_iff` and the conditional wire inverse; seven canonical list wires,33 ordered raw failures and direct model/Nat contrasts |

**Proof clients and controls.** `RlpByteArrayCallerProofs.lean` has eight private
facade client groups: arbitrary leaf success, exact adapter accept set, the
conditional inverse, recovery of the exact raw leaf, successful-domain and
size<2^64 recovery, exact original-wire reencoding, local size≤256 domain
discharge, and byte-preserving encoding/list non-success. They compose public
`decode_encode`, `toBytes_eq_ok_iff`, `decode_success_encodable`,
`encode_eq_of_decode_eq_ok` and `encodable_bytes_iff`, reducing only the new
adapters/wrappers. No arbitrary-ByteArray Encodable claim follows.

`RlpByteArrayGuards.lean` supplies102 complete outcomes across54 wire vectors:
14 payloads each check model constructor plus every byte, complete model success,
exact encoded wire and complete wire success; seven lists and33 raw failures;
three direct list rejections and three Nat contrasts. All support is manually
private, without nested deriving or exported conformance declarations.

**Bounded source profile.** `rlp_byte_array_differential.py` fixes seed29201:
14 catalog payloads (encode then decode), seven literal lists,33 literal raw
failures, then48 generated payloads at widths0/1/2/7/8/31/32/55/56/127/255/256,
four trials each, with encode/decode/drop-last/append00 in that order. The fresh
frozen Python3.13 `-I -B` run completed62 encode entries and198 decode calls:
62 decoder successes,129 raw
errors and seven typed-list errors;124 successful source calls include encoders.
All260 complete result guards compiled successfully through the existing Lean
driver. Normal and `-O` helper runs passed twelve exact-type negatives, eight
exception-admission negatives and one wrong-value negative; the same controls
also passed before the source profile.
Maximum supplied wire260, payload256, list depth3/width56 and declared length
2^64−1 are bounded controls, without proportional allocation for declared lengths.

The source controller uses original builtin Bytes and original encode/decode_to,
checks exact bytes before equality, verifies saved aliases/functions/code and
current source/origin/RECORD identity, and retains complete source events separately
from full Lean diagnostics and the existing `Except Unit ByteArray` observation.
Raw raises remain outside the typed catch; exact list provenance is checked at
outer `decode_to:171`, with cause `decode_to:169` → `deserialize_to:207` →
`_deserialize_to_bytes:258` and exact invalid-bytes cause arguments. Frozen interpreter/startup,
installation/RECORD, Lean compiler/core runtime and ambient host are trust inputs.
This finite profile supplies no generic Python refinement, schema-depth, practical
host/resource, C1–C4, EEST, guest or whole-layer readiness result. Complete
source events, all generated bytes/wires and guards, actual argv/cwd/environment,
and source/runtime/controller/compiled-Lean/all487 target body/mode snapshots
were retained and unchanged before/after the single run. The actual empty-input
raise is149; the typed-list cause is258, distinguished from condition/signature lines.

### Implemented Bool RLP instances

`STFSpec/Codec/RlpBool.lean` supplies exactly two Bool instances and one ordinary
unconditional wire inverse. False maps to empty bytes, true to singleton 01;
`ofRlp` is exactly the existing `Rlp.toBool`.

| Locked dependency source | Lean declaration and public type | Domain, value/effects | Ordered failures | Public law and deterministic regression |
|---|---|---|---|---|
| `ethereum_rlp/rlp.py:79–83` (0.1.6) | `RlpEncode Bool`, field `if b then .bytes ⟨#[1]⟩ else .bytes ByteArray.empty` | both mathematical Bool values; pure; both models lie in Q47 | none | `decodeTo_encodeOf_bool`; complete false/true models and exact wires 80/01 |
| `ethereum_rlp/rlp.py:208–209,245–251` | `RlpDecode Bool`, field exactly `Rlp.toBool` | original source native Bool target; empty bytes false, singleton 01 true | complete raw errors first (Q68); other bytes and lists both retain `.shape "boolean"` | `toBool_eq_ok_iff` and unconditional instance wire inverse; two successes, 16 typed and 30 raw rejections |

**Proof clients and controls.** `RlpBoolCallerProofs.lean` supplies eight private
facade client groups: exact encoder/decoder equations, finite-domain discharge,
typed model inverse, public unconditional wire inverse, exact raw-model recovery
and accepted-wire reencoding, complete raw-first forwarding, lists/invalid-byte
rejection, and diagnostic preservation with external common-channel erasure.
Only the new adapters and transparent wrappers and the intentionally public
normative `toBool` semantic equation (for private exact-error clients) are reduced;
the proofs compose public `encodable_bytes_iff`, `decode_encode`,
`toBool_eq_ok_iff` and `encode_eq_of_decode_eq_ok`, without private workers.
`RlpBoolGuards.lean` supplies 52 complete controls:
two full model observations, two exact encodings and 48 whole wire outcomes.
Support is private and introduces no nested equality or deriving instance.

**Bounded source profile.** `rlp_bool_differential.py` fixes seed 29301 with no
random draws: 18 encode calls interleaved with corresponding Bool decode calls,
then 30 malformed wires in the Nat profile's fixed order. The first two encode
inputs are exact native False/True; the other 16 deliberately encode raw models
(11 byte payloads and five lists), then test Bool rejection. Target comparisons
use `encodeOf` for the two Bool values and public raw `encode` for other models.
The fresh frozen Python 3.13 `-I -B` profile completed 48 decodes:
two successes, 16 typed and 30 raw failures,
20 successful source calls including encoders. All 66 complete generated guards
compiled through the existing Lean driver.
Maximum wire 259, byte payload 256, list depth 2 and width 56 bound this profile.

Exact Bool admission precedes equality/JSON/emission, rejecting Python 0/1;
all wires and encoder results require exact bytes. Original builtin Bool/Bytes,
source aliases, functions/code, current source and RECORD are bound pre/post.
Raw decode at 167 is outside the typed catch. Typed rejection retains outer
`decode_to:171`, cause `decode_to:169` → `deserialize_to:209` →
`_deserialize_to_bool:251` and exact arguments. Its original authenticated
frame's full native value/class distinguishes invalid bytes from lists; accepted
empty/01 values cannot be failures. Both retain the same Lean diagnostic.
Complete source events, complete Lean results and external `Except Unit Bool`
observations are separate. Thirty-nine local helper negatives cover 22 Bool,
eight byte, eight exception/provenance and one complete-value rejection.

Both normal and `-O` helper-only runs passed all 39 local negatives without source
entry calls; the same controls also passed before the single source profile.
Actual argv/cwd/UTC/empty stdin, selected nonsecret effective environment,
full stdout/stderr/exits, ordered per-call records and full source/Lean
observations were retained. All 491 target bodies/modes, source/runtime/install,
compiled Lean and controller inputs were frozen and unchanged pre/post.
Interpreter/startup,
installation/RECORD, outer orchestration, ambient host, Lean compiler/kernel and
native runtime remain trust inputs. This finite profile supplies no generic
Python refinement, practical host/resource, C1–C4, EEST, guest or whole-layer
readiness claim.

### Implemented U256 RLP instances

`STFSpec/Codec/RlpU256.lean` supplies exactly two U256 instances and one ordinary
unconditional wire inverse. Encoding is minimal, including empty zero; decoding
maps the existing 32-byte bounded Nat result through `Base.U256.ofNat`.

| Locked dependency source | Lean declaration and public type | Domain, value/effects | Ordered failures | Public law and deterministic regression |
|---|---|---|---|---|
| `ethereum_rlp/rlp.py:77–78` (0.1.6); `ethereum_types/numeric.py:477–484` (0.4.1) | `RlpEncode Base.U256`, `toRlp x := Rlp.ofNat x.toNat` | every word; minimal payload, zero empty; pure | none | `decodeTo_encodeOf_u256`;12 exact fixed wires including zero and maximum |
| `ethereum_rlp/rlp.py:204–205,263–275`; `ethereum_types/numeric.py:566–577` | `RlpDecode Base.U256`, `ofRlp item := (Rlp.toNatBounded 32 item).map Base.U256.ofNat` | exact original source U256; guarded construction cannot wrap admitted success | raw errors first (Q68), list shape, leading zero, excess width; existing diagnostics unchanged | bounded acceptance and word reconstruction; unconditional inverse;12 model/12 wire successes,10 model failures,12 raw failures and 6 Nat/ByteArray contrasts |

**Private callers and controls.** Eight facade groups cover complete encoder
model/size, arbitrary-item decoder and raw-error equation, model inverse,
unconditional wire inverse, success iff exact raw model, accepted-wire raw
recovery/domain/reencoding, leading-zero precedence and external common-channel
observation preserving whole successful words. They use only public laws and
reduce the new adapters/wrappers. `RlpU256Guards.lean` supplies exactly 64 complete
handwritten outcomes. All test support, including generated declarations, is
private; no public helper/domain theorem or other carrier instance is added.

**Bounded source profile.** `rlp_u256_differential.py` fixes seed 29401 without
random draws: A00–A23 interleave 24 original-U256 encodes and 24 corresponding
decodes; the 16 B-series cases supply success wires; C00–C31 supply eight list-shape,
12 leading-zero and 12 width failures; R00–R23 supply 24 raw malformed wires.
The portable invocation is:

```sh
EELS/.venv/bin/python -I -B STFSpec/Conformance/Codec/rlp_u256_differential.py \
  --eels EELS --output EXTERNAL.lean --wheel-dir WHEELS
```

WHEELS must contain the original locked `ethereum_rlp-0.1.6-py3-none-any.whl`
and `ethereum_types-0.4.1-py3-none-any.whl`. The driver checks their hashes
against pinned `uv.lock` and matches installed source members; it downloads
nothing and has no private fallback. `--help` lists the usage and filenames;
missing wheel input fails clearly before original RLP entries.
The corrected candidate's fresh frozen Python 3.13 `-I -B` profile completed
exactly 120 entries:24 encodes and 96 decodes (40 exact U256 successes,32 typed
failures,24 raw failures),64 successful source calls including encodes. All 120
complete generated guards compiled through unchanged `context.run`. Payload≤256, wire≤259,
success payload≤32/wire≤33, depth 32, width 64 and nine-byte declarations of
2^64−1 bound the supplied inputs. Fixed header recipes are a bounded fixture
catalog, not a replacement encoder/parser/oracle.

Inputs require exact Python int in [0,2^256) before original U256 construction;
success requires exact original U256 before conversion, equality or emission.
Wires/results require exact builtin bytes. Current source/RECORD, lock-hashed
wheel members, original RLP functions/classes, numeric inheritance/method code
and MAX_VALUE are authenticated. Raw failures remain outside the typed catch.
Shape 269 and leading-zero 271 retain original arguments and outer 171; width
retains original numeric ValueError 575, empty-argument inner 275 and outer 171,
with complete classes, arguments, cause/context identity and traceback frames.
Unrecognized host/reflection/native origins abort evidence. Twenty-eight helper
negatives (ten numeric, five wire, five success, eight provenance) exercise the
same real admission helpers on isolated primitive fixtures, without mutating
shared oracle code/classes or making extra source entries. Normal and optimized
helper-only runs each passed all 28 final-driver negatives before the one source
profile:56 fixture executions and zero RLP entries. The explicit supplied wheel
copies were lock-hashed and their complete bodies/modes bound before/after.
All 495 target bodies/modes and selected executable/Lean/comments/controllers,
source/runtime/install/compiled Lean inputs remained frozen across the profile. Actual
argv/cwd/UTC/empty stdin,
selected effective nonsecret environment, complete streams/exits, ordered
per-call observations and exact wheel-directory bindings are retained with
candidate/source/runtime/install/controller/compiled input bodies/modes.

Finite source observations, complete Lean diagnostics and the external
`Except Unit U256` observation remain separate. Interpreter/startup/installation,
native primitives, ambient host, outer orchestration and Lean compiler/kernel
remain trusted; body/mode binding is not compiler correspondence or whole-host
closure. No universal Python refinement, host resource, C1–C4, EEST or guest
result follows; other carriers/schemas and actual consuming handlers stay open.

### Implemented narrow unsigned RLP instances

`STFSpec/Codec/RlpNarrowUnsigned.lean` supplies six instances and three ordinary
unconditional inverses for the independent nominal `Base.U64`, `Base.U32` and
`Base.U8` carriers. Minimal unsigned encoding uses empty zero; bounded decoding
checks shape, leading zero and width before mapping the admitted natural through
`ofNat`. U16, U128, generic carrier APIs and schema instances are outside this slice.

| Locked dependency source | Lean declaration and public type | Domain, success/effects | Ordered failures | Law and deterministic regression |
|---|---|---|---|---|
| `ethereum_rlp/rlp.py:77–78` (0.1.6); `ethereum_types/numeric.py:477–484` (0.4.1) | `RlpEncode Base.U64`, `toRlp x := Rlp.ofNat x.toNat` | every U64; minimal bytes; pure | none | `decodeTo_encodeOf_u64`; six exact wires, zero and maximum |
| same encoding sources | `RlpEncode Base.U32`, same minimal model | every U32; pure | none | `decodeTo_encodeOf_u32`; six exact wires |
| same encoding sources | `RlpEncode Base.U8`, same minimal model | every U8; pure | none | `decodeTo_encodeOf_u8`; six exact wires |
| `ethereum_rlp/rlp.py:204–205,263–275`; `ethereum_types/numeric.py:566–577` | `RlpDecode Base.U64`, `(Rlp.toNatBounded 8 item).map Base.U64.ofNat` | original source U64; bounded success cannot wrap | raw first (Q68), list shape, leading zero, width | bounded acceptance; six model/wire successes, list/zero/width and cross-width controls |
| same decoding sources | `RlpDecode Base.U32`, bounded 4 map `Base.U32.ofNat` | original source U32; pure | same ordered diagnostics | six model/wire successes; cross-width controls |
| same decoding sources | `RlpDecode Base.U8`, bounded 1 map `Base.U8.ofNat` | original source U8; pure | same ordered diagnostics | six model/wire successes; `0100` rejects width |
| public leaf/range laws composed with raw wire inverse | `Rlp.decodeTo_encodeOf_u64 (x : Base.U64)` | unconditional complete `.ok x`; discharged | none | private encoder-domain proof; arbitrary-value facade caller |
| same public laws, width 4 | `Rlp.decodeTo_encodeOf_u32 (x : Base.U32)` | unconditional complete `.ok x`; discharged | none | same private proof composition |
| same public laws, width 1 | `Rlp.decodeTo_encodeOf_u8 (x : Base.U8)` | unconditional complete `.ok x`; discharged | none | same private proof composition |

**Private callers and controls.** `RlpNarrowUnsignedCallerProofs.lean` supplies
24 type-specialized groups, eight per type: full encoder byte/size model; private
Encodable discharge; model inverse; public wire inverse; success iff exact raw
item and accepted-wire recovery/domain/reencoding; entire bounded-map result and
raw-error forwarding; list nonsuccess, exact leading-zero precedence and exact
bounded construction; external common-channel observation. Public bounded
acceptance proves list nonsuccess; exact list diagnostics remain complete runtime
controls. No private integer/parser worker or Base representation is unfolded.
Only new adapters/wrappers, ordinary Except operations and intentionally exported
model equations are reduced. `RlpNarrowUnsignedGuards.lean` fixes 147 complete
outcomes: 54 encoder/model/wire successes, 21 typed rejects, 36 raw rejects,
18 cross-width results and 18 Nat/ByteArray contrasts. Every supporting and
generated conformance declaration is private; the provider has exactly nine
public declarations and no public helper/domain predicate.

**Bounded source profile.** `rlp_narrow_unsigned_differential.py` fixes seed 29501
without RNG calls, in U64→U32→U8 order and A→B→C→Z→W→R→D order per carrier.
A encodes and immediately decodes each exact returned wire. All indexed duplicate
fixtures stay separate. The released schedule has 229 entries: 36 encodes and 193
decodes (55 successes, 66 typed and 72 raw rejects), 91 successes including encodes.
The per-carrier encode/decode/success/typed/raw counts are 16/72/27/21/24,
12/64/18/22/24 and 8/57/10/23/24. It emits 229 whole compiled guards.

```sh
EELS/.venv/bin/python -I -B STFSpec/Conformance/Codec/rlp_narrow_unsigned_differential.py \
  --eels EELS --output EXTERNAL.lean --seed 29501 --wheel-dir WHEELS
```

WHEELS explicitly supplies `ethereum_rlp-0.1.6-py3-none-any.whl` and
`ethereum_types-0.4.1-py3-none-any.whl`, admitted by pinned lock hash and installed
source-member equality; there is no private fallback or download. The driver
requires exact bounded Python int before original construction, exact original
nominal carrier before int/equality/emission and exact bytes for wire/result
observation. Original classes, final MAX objects/classes/values, inherited method
code, RLP functions/dispatch/exception rendering, reflection callbacks and relevant
builtin resolutions are bound with installed current source/RECORD and original
wheel bytes. Shape 269 and zero 271 retain outer 171; width retains original
ValueError 575→empty-argument DecodingError 275→outer 171, original target/MAX/frame
bytes and width. Raw decode 167 stays outside the typed catch. Other host/native,
class, callback or reflection origins abort evidence, never become width rejects.

Before source, 75 negative and 14 positive fixture groups run once normally and
once with `-O`: 178 groups, zero RLP entries. Negatives cover 21 numeric, 6 wire,
30 encode-carrier/decode-result, 8 provenance, 6 primitive-origin and 4 reflection
fixtures. Positives cover six numeric boundaries, three original carriers through
both relevant helpers, exact empty bytes and four original-form event descriptors.
Synthetic event fixtures are explicitly primitive descriptors and mutate no
source code, class or builtin. No fixture group repeats inside the source branch.

The fresh frozen Python 3.13 `-I -B` author profile completed all 229 scheduled
entries and compiled all 229 complete generated guards through unchanged
`context.run`, with the exact partitions above. Normal and optimized helper-only
runs each passed 75 negative and 14 positive fixture groups before source: 178
groups total, zero RLP entries. A full facade build, both actual `--deps`,
full raw type/proof-body/privacy/axiom inventory and focused declaration audit
passed before source. Exactly nine provider declarations are public; all support
is private. All 499 target bodies/modes, executable/Lean/comments/controllers and
selected original source/runtime/install/compiled/wheel inputs were bound before
and unchanged after the run. Actual argv, explicit supplied/resolved wheel
directory, cwd/UTC/empty stdin, selected effective nonsecret environment, full
streams/exits, ordered calls and sidecar/generated guards are retained. Input
bounds were payload 256/wire 259, success payload 8/wire 9/max 2^64−1, depth 32, list
width 64 and nine actual bytes declaring 2^64−1. Complete source events, complete Lean results
and external `Except Unit C` observations remain separate. Interpreter/startup,
installation/RECORD, native primitives, ambient host, outer orchestration and Lean
compiler/kernel remain trusted. Selected input body/mode binding is no whole-host
snapshot, compiler correspondence, universal Python/host/resource, C1–C4, EEST or
guest theorem; actual consuming schema/first-handler obligations remain open.

### Implemented generic fixed-byte RLP instances

`STFSpec/Codec/RlpFixedBytes.lean` supplies exactly two generic instances and
one ordinary conditional inverse. Every mathematical Nat width, including zero,
is supported; existing FixedBytes aliases inherit these instances.
List/schema instances remain separate; nominal Hash32 and Address are supplied below.

| Locked dependency source | Lean declaration and public type | Domain, success/effects | Ordered failures | Law and deterministic regression |
|---|---|---|---|---|
| `ethereum_rlp/rlp.py:70–72,99–108` (0.1.6) | `RlpEncode (Base.FixedBytes n)`, `.bytes x.toBytes.toByteArray` | all n; complete exact-width bytes, including leading zeros; pure | none | conditional `decodeTo_encodeOf_fixedBytes`; complete model/wire controls at widths 0/1/20/32/55/56/255/256 |
| `ethereum_rlp/rlp.py:206–207,255–262`; `ethereum_types/bytes.py:29–37` (0.4.1) | `RlpDecode (Base.FixedBytes n)`, exactly `Rlp.toFixed n` | exact n-byte leaf; checked constructor; all bytes retained | raw failure first; list `.shape "bytes"`; byte-length mismatch `.shape "fixed bytes length"`; no integer normalization | public `toFixed_eq_ok_item_iff`/`toFixed_eq_ok_iff`; model inverse for arbitrary n; shape, length and raw-error controls |
| public raw inverse, typed acceptance and Base byte laws | `Rlp.decodeTo_encodeOf_fixedBytes (x : Base.FixedBytes n)` with explicit `Rlp.Encodable (.bytes x.toBytes.toByteArray)` | complete `.ok x`; ordinary proof discharged on stated domain | premise retained for arbitrary n (Q47) | eight private facade caller groups; finite domain discharge and symbolic above-bound negation without huge allocation |

**Private clients and controls.** `RlpFixedBytesCallerProofs.lean` has eight
private groups: adapter/complete wire model and size; all-n raw item inverse;
both directions of complete typed success; checked byte construction and exact
Base/packed adapters; conditional public wire inversion and independent-class
composition with an actual item-inverse premise; raw success/domain/full-wire
recovery and reencoding with exact size; raw/model errors and separate external
Unit success/error observations; private domain equivalence with n<2^64, finite
instantiations at 0/1/20/32/55/56/255/256, symbolic omission at n≥2^64 and width-zero
empty model/inverse. Supporting, caller and generated declarations are private.
Only the new adapters/wrappers, ordinary Except composition and intentionally
public encoder semantic model are reduced; Base storage, private parser/integer
workers and generated provider equations are not unfolded.

`RlpFixedBytesGuards.lean` fixes 256 complete handwritten outcomes: S64 (16 payloads,
four observations each), boundary 16 (55/56/255/256 header boundaries), C32 (four list
shapes at four widths, model and wire), length 88 (44 length mismatches, model and wire),
R48 (12 exact raw errors per source-profile width), X8 (Nat/ByteArray/fixed-byte
contrasts). Successes compare complete byte models, actual FixedBytes values and
whole wires; errors retain their complete constructors and contexts. Mathematical
widths 55/56/255 do not invent Python source classes.

**Bounded original source profile.** `rlp_fixed_bytes_differential.py` fixes
seed 29601 without RNG, with exact original Bytes0/1/20/32 class order. A00-E/A00-D
through A15-E/A15-D encode and immediately decode the actual returned native
object; B-group indices 00–07 are independent successes, C00–15 list rejects, D-group indices
00–43 length
rejects and R00–47 raw rejects. The one profile has 148 entries: 16 encode and 132
decode_to (24 successful, 60 typed and 48 raw rejects), 40 total successes and 148
whole compiled guards. All indexed duplicates remain. Maximum payload 256/wire 259,
raw literal 3 bytes, raw-valid list depth 2/arity 1. Exactly 16 direct constructor
setups plus 24 successful and 44 length-failing decode constructions give 84 original
FixedBytes constructor invocations. Source aliases and constructors are checked,
without arbitrary-width class factories or standalone constructor-error probes.

```sh
EELS/.venv/bin/python -I -B STFSpec/Conformance/Codec/rlp_fixed_bytes_differential.py \
  --eels EELS --wheel-dir WHEELS --output EXTERNAL.lean
```

Supply original locked `ethereum_rlp-0.1.6-py3-none-any.whl` and
`ethereum_types-0.4.1-py3-none-any.whl` explicitly; no private fallback or download.
The unchanged shared setup checks the pin and current installed source/RECORD;
the driver also checks locked wheel members, exact original classes, LENGTH int
objects/hierarchy/inherited constructor, native bytes observers/equality, RLP
functions/aliases/codes/globals, reflection, builtins and exception rendering.
Admit native class before conversion/equality. Low-singleton 00/01/7f encodes are
exact original Bytes1 objects identical to their constructor inputs; their actual
encode outputs pass unchanged to decode_to, whose raw singleton branch preserves
the same object. Ordinary outputs/literal wires are exact builtin bytes. Every
successful typed result is the exact original target before full byte projection.

Raw exceptions retain original class/args/full traceback/code identity before
mapping. Shape 258 wraps at 171; exact native ValueError 36 wraps through empty
DecodingError 262 then outer 171, retaining causes, contexts, suppression and actual
class_/cls/value/args/kwargs/result/LENGTH. Failure-frame result admission checks
the exact target class before projecting its wrong-length bytes, separately from
successful-length admission. Native bytes.__new__33/reflection/class/host events
fail evidence with full traces; they are never renamed length failures. Complete
Lean diagnostics and external `Except Unit` observations remain separate.

On 2026-10-24, the single released profile passed all 148 original calls and
all 148 generated compiled guards. The final normal and -O helper-only runs each
passed 49 negative and 15 positive
groups (128 total), zero RLP entries and five direct original success-constructor
setups per run, including a second Bytes1 for the identity-negative control.
They exercise exact payload/wire/result classes, provenance, primitive raw/shape/
length descriptors and native output identity. Good length descriptors are
synthetic primitive validation, not impossible wrong-length constructor setups.
The source branch does not repeat helper fixtures. Invocation streams, supplied/
resolved wheel paths, selected target/source/runtime/install/compiled/controller
bodies and modes were unchanged before/after the sole profile. The actual facade
build, both dependency reads and complete generated raw Expr type/full proof-value,
privacy and allowed-axiom inventory passed before source execution: exactly three
public declarations; all 40 supporting declarations private; focused audit 43
declarations with zero findings. These are finite
observations: interpreter/startup/installation, native primitives, ambient host,
outer orchestration and Lean compiler/kernel remain trusted. No universal Python,
arbitrary-n source, host/resource, C1–C4, EEST, guest or readiness result follows;
actual consuming handlers and other schemas remain open.

### Implemented nominal Hash32 RLP instances

`STFSpec/Codec/RlpHash32.lean` supplies exactly two instances and one ordinary
unconditional inverse for the existing nominal Base.Hash32. Root/VersionedHash
aliases inherit them. The provider imports RlpDecodeOf and does not depend on the
generic FixedBytes instance. No Base seam, other instance or public helper is added.

| Locked source | Lean declaration and public type | Domain, success/effects | Ordered failures | Law and deterministic regression |
|---|---|---|---|---|
| EELS `crypto/hash.py:19`; `ethereum_rlp/rlp.py:70–72,101` (0.1.6) | `RlpEncode Base.Hash32`, `.bytes x.toBytes.toByteArray` | all nominal hashes; every one of 32 bytes, including leading/internal zeros; pure | none | ordinary unconditional `decodeTo_encodeOf_hash32`; complete model/wire controls |
| EELS `crypto/hash.py:19`; `ethereum_rlp/rlp.py:206–207,255–262`; `ethereum_types/bytes.py:29–37` (0.4.1) | `RlpDecode Base.Hash32`, `(Rlp.toFixed 32 item).map Base.Hash32.ofBytes32` | exactly 32-byte leaves; complete nominal reconstruction | raw decode first; list `.shape "bytes"`; byte-length mismatch `.shape "fixed bytes length"` | complete acceptance both ways from public toFixed/conversion laws; C/D/E/R controls |
| public raw inverse, typed acceptance and Base conversion/byte laws | `Rlp.decodeTo_encodeOf_hash32 (x : Base.Hash32)` | every x, complete `.ok x`; finite Q47 premise discharged privately at 32<2^64 | no new error or domain family | eight private public-law caller groups; unconditional nominal inverse and full-wire recovery |

All three are **discharged for this slice**. The private caller groups cover exact
adapters/byte diagrams, item inverse, complete acceptance in both directions,
checked constructors/both conversion inverses/both byte laws/packed adapters,
unconditional wire inverse with independent-class composition retaining its own
item-inverse premise, raw success/domain/complete reencoding/size 32, exact raw/list/
length failures and separate external Unit observations, finite domain and nominal
separation including empty/31/33-byte rejection and distinct Nat/ByteArray acceptance.
All support, caller, guard and generated declarations remain private. Clients use
public laws; the new adapter/wrapper composition and intentionally exported normative
toFixed equations may reduce. Base storage/private conversion, parser/integer workers
and compiler-generated provider equations are not unfolded. The generic FixedBytes
wire inverse retains its separate explicit domain premise.

`RlpHash32Guards.lean` supplies 90 complete handwritten controls: S24 (six payloads,
model/typed/wire/roundtrip), B4 (two additional complete successes), C8 (four list
models/wires), D24 (twelve wrong lengths), E10 (five singleton/leading-zero length
failures), R12 (complete raw errors) and X8 (Hash32/Nat/ByteArray contrasts). Values
use public Bytes32 construction and Hash32.ofBytes32; every expected byte and entire
nominal result/wire/diagnostic is checked. There is no zero-width Hash32 value.

`rlp_hash32_differential.py` fixes seed 29701 without RNG and uses the exact original
locked Bytes32 class, the static EELS Hash32 alias. It imports no crypto/hash module
and executes no hash. Its single bounded schedule A00-E/A00-D through A05-E/A05-D,
B-group indices 00–01, C-group indices 00–03, D-group indices 00–11,
E-group indices 00–04, R-group indices 00–11 contains 47 original RLP entries: 6 encode,
41 decode_to (8 successes, 21 typed failures: 4 shape/17 length, 12 raw failures),
14 total successful calls and 47 whole compiled guards. Six successful direct setups,
eight successful decode constructions and 17 length-failing constructions give 31
original constructor invocations. Maxima are payload 256/wire 259/raw literal 3 bytes,
raw-valid list depth 2/arity 1. All duplicates remain; finite header fixtures are not
a parser/oracle. Actual native encode wires pass unchanged to paired decode.

```sh
EELS/.venv/bin/python -I -B STFSpec/Conformance/Codec/rlp_hash32_differential.py \
  --eels EELS --wheel-dir WHEELS --output EXTERNAL.lean
```

WHEELS supplies exactly named original locked ethereum_rlp-0.1.6-py3-none-any.whl
and ethereum_types-0.4.1-py3-none-any.whl; no fallback/download. Before source,
`--helpers-only` normally then with `-O` runs 50 negative/nine positive groups each:
118 executions total, one successful original Bytes32 setup per run, no RLP entries
or wrong-length constructor probes. Stable HP/HW/HS/HV/HE/HO fixtures test exact
payload/wire types and sizes, success native class before conversion/equality,
primitive provenance/length descriptors and builtin encode-output admission;
sentinels retain zero conversion/equality touches. The source branch records that
separate helper boundary and never repeats it.

The shared unchanged setup admits pin/current source/installed RECORD, while this
driver admits explicit lock-hashed wheel members, original Bytes32/FixedBytes,
exact int 32 LENGTH, bases/inherited constructor/current code/globals, native byte
observers/equality, RLP functions/aliases, reflection/builtins and exception renderer.
Successes require original native class before byte conversion; encode outputs and
literal payloads/wires require exact builtin bytes before comparison. Literal 00/01/7f
raw singleton wires retain actual identity through wrong-length rejection. Native
wrong-length frame results are exact Bytes32 before full projection, with K≠32;
they are not admitted as successful 32-byte values. Original construction at 33
precedes the source check 34, whereas Lean checks width before construction: the
byte accept sets coincide, without identical allocation timing.

Complete original exceptions retain class, args/message, cause/context/suppression,
code/full selected traceback and original target/raw/constructor args/kwargs/result/
LENGTH values. Raw 167 precedes typing; list 258 wraps at 171; native ValueError 36
wraps through empty DecodingError 262 to outer 171. Native 33/reflection/class/host
errors abort evidence and are never renamed length failures. Complete source
values, Lean diagnostics and external Except Unit remain distinct. Selected source,
runtime/install/compiled/controller/target full bodies/modes are retained unchanged
pre/post; interpreter/startup/install/RECORD/ambient host/outer orchestration/compiler/
kernel remain trusted. These bounded observations prove no universal Python, guest,
EEST, resource/host-exclusion, security or whole-Codec result; caller first-handler
and broader composition obligations remain open.

### Implemented nominal Address RLP instances

`STFSpec/Codec/RlpAddress.lean` supplies exactly two instances and one ordinary
unconditional inverse for the existing nominal Base.Address. The provider imports
RlpDecodeOf and does not depend on generic FixedBytes or Hash32 instances. No Base seam, other
instance or public helper is added.

| Locked source | Lean declaration and public type | Domain, success/effects | Ordered failures | Law and deterministic regression |
|---|---|---|---|---|
| EELS `state.py:33`; `ethereum_rlp/rlp.py:70–72,101` (0.1.6) | `RlpEncode Base.Address`, `.bytes x.toBytes.toByteArray` | all nominal addresses; every one of 20 bytes, including leading/internal zeros; pure | none | ordinary unconditional `decodeTo_encodeOf_address`; complete model/wire controls |
| EELS `state.py:33`; `ethereum_rlp/rlp.py:206–207,255–262`; `ethereum_types/bytes.py:29–37` (0.4.1) | `RlpDecode Base.Address`, `Rlp.toBytes item` then checked `Address.ofBytes? (Bytes.ofByteArray b)` via bind/Option.elim | exactly 20-byte leaves; complete nominal reconstruction | raw decode first; list `.shape "bytes"`; byte-length mismatch `.shape "fixed bytes length"` | complete acceptance both ways from public checked-constructor/packed-byte laws; C/D/E/R controls |
| public raw inverse, typed acceptance and Base conversion/byte laws | `Rlp.decodeTo_encodeOf_address (x : Base.Address)` | every x, complete `.ok x`; finite Q47 premise discharged privately at 20<2^64 | no new error or domain family | eight private public-law caller groups; unconditional nominal inverse and full-wire recovery |

All three are **discharged for this slice**. The private caller groups cover exact
adapters/byte diagrams, item inverse, complete acceptance in both directions,
checked construction/nominal byte injectivity/both packed inverses,
unconditional wire inverse with independent-class composition retaining its own
item-inverse premise, raw success/domain/complete reencoding/size 20, exact raw/list/
length failures and separate external Unit observations, finite domain and nominal
separation including empty/19/21-byte rejection and distinct Nat/ByteArray acceptance.
All support, caller, guard and generated declarations remain private. Clients use
public laws; the new adapter/wrapper composition and intentionally exported normative
toBytes and ordinary Except/Option composition may reduce. Base storage/private
conversion, parser/integer workers
and compiler-generated provider equations are not unfolded. The generic FixedBytes
wire inverse retains its separate explicit domain premise.

`RlpAddressGuards.lean` supplies 90 complete handwritten controls: S-group 24 (six payloads,
model/typed/wire/roundtrip), B-group 4 (two additional complete successes), C-group 8 (four list
models/wires), D-group 24 (twelve wrong lengths), E-group 10 (five singleton/leading-zero length
failures), R-group 12 (complete raw errors) and X-group 8 (Address/Nat/ByteArray contrasts). Values
use public scalar fixtures, with complete checked Address.ofBytes? construction in
each positive model control; every expected byte and entire
nominal result/wire/diagnostic is checked. There is no zero-width Address value.

`rlp_address_differential.py` fixes seed 29801 without RNG and uses the exact original
locked Bytes20 class, the static EELS Address alias. It imports no state/crypto/hash module
and executes no hash. Its single bounded schedule A00-E/A00-D through A05-E/A05-D,
B-group indices 00–01, C-group indices 00–03, D-group indices 00–11,
E-group indices 00–04, R-group indices 00–11 contains 47 original RLP entries: 6 encode,
41 decode_to (8 successes, 21 typed failures: 4 shape/17 length, 12 raw failures),
14 total successful calls and 47 whole compiled guards. Six successful direct setups,
eight successful decode constructions and 17 length-failing constructions give 31
original constructor invocations. Maxima are payload 256/wire 259/raw literal 3 bytes,
raw-valid list depth 2/arity 1. All duplicates remain; finite header fixtures are not
a parser/oracle. Actual native encode wires pass unchanged to paired decode.

```sh
EELS/.venv/bin/python -I -B STFSpec/Conformance/Codec/rlp_address_differential.py \
  --eels EELS --wheel-dir WHEELS --output EXTERNAL.lean
```

WHEELS supplies exactly named original locked ethereum_rlp-0.1.6-py3-none-any.whl
and ethereum_types-0.4.1-py3-none-any.whl; no fallback/download. Before source,
`--helpers-only` normally then with `-O` runs 50 negative/nine positive groups each:
118 executions total, one successful original Bytes20 setup per run, no RLP entries
or wrong-length constructor probes. Stable HP/HW/HS/HV/HE/HO fixtures test exact
payload/wire types and sizes, success native class before conversion/equality,
primitive provenance/length descriptors and builtin encode-output admission;
sentinels retain zero conversion/equality touches. The source branch records that
separate helper boundary and never repeats it.

The shared unchanged setup admits pin/current source/installed RECORD, while this
driver admits explicit lock-hashed wheel members, original Bytes20/FixedBytes,
exact int 20 LENGTH, bases/inherited constructor/current code/globals, native byte
observers/equality, RLP functions/aliases, reflection/builtins and exception renderer.
Successes require original native class before byte conversion; encode outputs and
literal payloads/wires require exact builtin bytes before comparison. Literal 00/01/7f
raw singleton wires retain actual identity through wrong-length rejection. Native
wrong-length frame results are exact Bytes20 before full projection, with K≠20;
they are not admitted as successful 20-byte values. Original construction at 33
precedes the source check 34, whereas Lean checks width before construction: the
byte accept sets coincide, without identical allocation timing.

Complete original exceptions retain class, args/message, cause/context/suppression,
code/full selected traceback and original target/raw/constructor args/kwargs/result/
LENGTH values. Raw 167 precedes typing; list 258 wraps at 171; native ValueError 36
wraps through empty DecodingError 262 to outer 171. Native 33/reflection/class/host
errors abort evidence and are never renamed length failures. Complete source
values, Lean diagnostics and external Except Unit remain distinct. Selected source,
runtime/install/compiled/controller/target full bodies/modes are retained unchanged
pre/post; interpreter/startup/install/RECORD/ambient host/outer orchestration/compiler/
kernel remain trusted. These bounded observations prove no universal Python, guest,
EEST, resource/host-exclusion, security or whole-Codec result; caller first-handler
and broader composition obligations remain open.

### Implemented generic typed RLP List composition

`STFSpec/Codec/RlpList.lean` supplies exactly four public declarations under Q69:
two generic independent instances and two ordinary laws. Every support/caller
and generated declaration is private. The accepted nominal Address slice above
is preserved. No schema, global lawful-codec class, public traversal/helper,
new diagnostic, runtime guard or global invariant is introduced.

| Locked dependency source | Lean declaration and public type | Domain, value/effects | Ordered failures | Public law and deterministic regression |
|---|---|---|---|---|
| `ethereum_rlp/rlp.py:70–78,112–135` (0.1.6) | `RlpEncode (List α)` with `[RlpEncode α]` | every finite list; `.list (xs.map toRlp)` with complete ordered children, pure/total | no adapter rejection; Q47 retains whole standard wire domain | complete byte model through `toList_encode/toList_encode_list`; S01-M–S08-E, K01/K03, CM01/CM06/CM10 |
| `ethereum_rlp/rlp.py:191–205,311–318,370–384` | `RlpDecode (List α)` with `[RlpDecode α]` | `toList.bind (fun children => children.mapM ofRlp)`; complete success list and empty success | list shape before callbacks; first complete error in child order, unchanged Q68 raw-first wrapper | S01-I–S08-D, T01-I–T06-D, R01-N–R06-F, A01-H–A06-B, CM/Z/K/X; CP02/CP07/CP08 |
| public model composition; no additional Python entry | `Rlp.ofRlp_toRlp_list` with membership-local `hElements` (§7) | complete model inverse for actual members, no Encodable premise | independent instances alone supply no nonempty inverse | ordinary induction through public core mapM equations; CP03/CP05/CP06/CP09, including recursive public nested-law reuse |
| public raw inverse plus wrapper/model composition | `Rlp.decodeTo_encodeOf_list` with same `hElements` and whole assembled Encodable (§7) | complete `.ok xs`; every child domain AND joined payload bound retained | no added rejecting API or accepted-wire generic right inverse | public `decode_encode` then public model law; CP04/CP06, S/K whole wires |

The fixed control catalogue has 104 separate whole outcomes in S,T,R,A,CM,Z,K,X
order (32/12/18/18/10/4/4/6), and ten private caller groups CP01–CP10.
Model observations preserve constructor delimiters, every byte and every child;
there is no nested deriving, checksum or count-only substitute. Independent
Fail/Const/Local carriers show nonempty failure, lost accepted-value recovery and
strict actual-member/global agreement differences. Public Nat/byte/list acceptance
contracts support symbolic contrasts; exact diagnostics are finite guard values.
No private integer/parser/Base representation or provider helper is unfolded.

The portable `rlp_list_differential.py` requires explicit `--wheel-dir` with the
original locked ethereum_rlp 0.1.6/types 0.4.1 wheels, authenticates whole wheels,
installed current Python members and RECORD inventories, and freshly compiles
authenticated bytes through the accepted loaders. `--help` exits 0; a missing
wheel directory exits 2. Native builtin bytes/list and exact original Uint with
plain-int nonnegative `_number` admission precede conversion or whole-value
comparison. The retained genuine `typing.List[Uint]` alias is parameterized once
per process, with original origin/args/class/name/rendering metadata; no equal
replacement, fake alias, With callback or crypto import is used.

The finite preflight closure binds 14 selected RLP functions (including joined
encoding generator code), Uint/Unsigned hierarchy and inherited numeric methods,
original code/globals/scoped builtins and exact None defaults for those selected
functions/methods plus direct get_origin/get_args/is_dataclass. Reached typing
helper/class and alias construction/rendering dependencies retain their actual
defaults, including `_should_unflatten_callable_args` and dataclasses `_FIELDS`;
there is no universal None-default claim. Uint.from_be_bytes is numeric.py:522–528;
dataclass reflection is rlp.py:215–217, byte shape :219–220 and arity :222–228.
No dataclass constructor or get_type_hints is exercised.

The closed author schedule is 40 negative/8 positive admission groups normally and
under `-O`, 96 group executions with zero RLP entries, then seed 30001/no RNG,
E01–E08, decode01–08, T01–T06, R01–R06: 28 original entries (8 encode/20 decode;
8 decode successes/6 typed/6 raw failures) and 28 separately compiled complete guards.
Helper setups are four original numeric constructions per run; source setup is
five reused Uint values, 13 explicit numeric constructions across the three
processes. The source-internal 125 Uint-construction prediction is static source
reasoning, not instrumentation. Maximum wire 58 bytes, list length 56, raw depth 2
and natural 256. No extra raw decode, hidden replay or success raw-tree capture.
Typed failure records retain complete outer/cause/context/suppression/args,
original frame/code/global identity, reached raw trees, exact original target,
first index and actual child. Sites are list 374, child 379, wrapper 382, outer 171;
raw 167 precedes typing. Complete raw paths/args are separately admitted. Native,
reflection/class or host faults abort evidence, including wrapped faults; they
are never mapped to a protocol error. The source exception record and Lean
complete diagnostic remain distinct from mathematical `Except Unit` observation.

**Validation status.** The 104 controls and ten caller groups compile through both
complete facades. The fresh V2 full raw type/proof-value/axiom/privacy audit finds
211 item declarations: exactly four public and 207 private, including generated
support. The two private CP09 concrete-wire proofs now compose public byte-model
laws and core byte extensionality; production types, definitions and laws are
unchanged. The authorized final author03 profile passes all 28 original entries
and 28 compiled whole guards after fresh normal/-O admission 96. All 515 target
bodies and selected source/controller/runtime/install/wheel/compiled bodies and
modes match pre/post successful execution. The final tree is frozen before its
fresh current 47 required checks; no cache result supplies passing credit.
Author01 reached 28 entries but failed metadata packaging before guard compilation
and remains uncredited. Its reviewed renderer-only repair preceded author02's
successful 28-entry/28-guard profile; those results are historical and superseded
for V2. Across all three attempts, historical execution totals 84 source entries,
288 helper groups and 39 explicit numeric setups. Credited final author03 evidence
is 28 source entries/28 compiled guards/96 helper groups, with 13 explicit numeric
setups in the final three processes. The reviewed CODE packet retains full
streams, body/mode receipts, original outcomes, failed attempts and fresh current
gates. These finite observations supply no cold-build, whole-host or generic
Python refinement, callback execution/cost trace, host resource, schema-depth,
first-consuming-handler, EEST, guest or readiness gate. Header fallback
stateless.py:234–237 and transaction execution_engine/new_payload.py:60–68 remain
separate premises. Compiler/kernel, native integer/bytes/arithmetic/allocation,
interpreter/startup, frozen install/RECORD, ambient host and orchestration remain
explicit trust inputs. No whole-host certification or cold-build claim follows.

### Implemented RLP header slice

`STFSpec/Codec/RlpHeader.lean` implements the total packed cursor helper, with
ordinary equality to `itemLengthModel` on the observed suffix. **Discharged for
this slice:** exact tag/header cases, ordered diagnostics, bounded-digit public
endian correspondence, suffix/window observations, positive extents and independence
from bytes beyond the nine-byte header window. No complete item decoder is implied.

| Locked dependency source | Lean declaration and public type | Domain, value/effects | Ordered failures and consuming handler | Public law and deterministic regression |
|---|---|---|---|---|
| `ethereum_rlp/rlp.py:488–543` (0.1.6) | `Rlp.decodeItemLength : ByteArray → Nat → Except RlpError Nat`; readable `itemLengthModel : List UInt8 → Except RlpError Nat` | all packed inputs/Nat cursors; declared first-item extent; pure, no effects; accepts missing bodies/small long forms/trailing bytes | empty cursor; long-header truncation; leading-zero length; all diagnostics erase to source DecodingError. Raw decode/callers (`:465–484`) remain separate; header fallback O3 and payload O6 handlers are unimplemented | `decodeItemLength_eq_model`, `decodeItemLength_single/short_bytes/short_list/long`, `length_digits_bound`, `decodeItemLength_empty_iff/pos/lt/success_bound/window/suffix/header_congr`, `itemLengthModel_take_nine`; tag boundaries, zero-versus-truncated, asymmetric digits, nonzero cursors, 2^64−1 declared length |

Header regressions are `RlpHeaderGuards.lean` (complete diagnostic results and an
all-256-tag sweep) and `RlpHeaderCallerProofs.lean` (public equations only).
`rlp_header_differential.py` calls the actual locked helper under the accepted
source-authenticated fresh loader and shared driver. The bounded seeded cases cover
all tags, one-to-eight digit fields, leading zeros, incomplete headers, small long
forms, absent payloads, trailing bytes, nonzero/random cursors and conceptual
out-of-range Nat offsets using small buffers. Observation/input negative controls
reject bool, float and untyped results before Lean emission. Success is an exact
plain int; the only admitted source failure is the exact DecodingError class.
Package source/origins/RECORD, EELS/lock and interpreter identity are checked as in
the typed driver; interpreter/startup/frozen installation/RECORD remain trust inputs.
This finite evidence establishes neither full raw-decode canonicality nor host limits.

### Implemented raw RLP decoder slice

`STFSpec/Codec/RlpDecode.lean` supplies pure total `Rlp.decode` on finite packed
inputs. **Discharged for this slice:** exact storage correspondence to the
proof-facing `decodeModel`, byte-window observations, singleton/short-string
case equations, short-list outer-failure priority and nonempty successful input.
Each recursive child consumes a nonempty prefix of its bounded parent window.
The packed and list frontends share parser classification and ordered-error
semantics: the refinement proves storage correspondence, while authenticated
source probes independently audit those semantics. The universal wire-law
contracts and their domains are owned by §7.

| Locked dependency source | Lean declaration and public type | Domain, value/effects | Ordered failures and consuming handler | Public law and deterministic regression |
|---|---|---|---|---|
| `ethereum_rlp/rlp.py:143–162` (0.1.6) | `Rlp.decode : ByteArray → Except RlpError RlpItem`; proof-facing `decodeModel : List UInt8 → Except RlpError RlpItem` | all finite bytes; exact nested byte/list tree, pure/no effects | empty before dispatch; all errors refine DecodingError; header fallback O3 and payload O6 handlers remain unimplemented | `decode_eq_model`, `decode_empty`, `decode_success_nonempty`; empty/00/7f/80/81/ff |
| `ethereum_rlp/rlp.py:387–424` | private byte branches of `decode` | accepted exact byte leaf; copy only validated available scope | low tag with extra bytes: negative length; short extent truncation, trailing, prefixed low singleton; long digit truncation, leading zero, length<56, payload truncation, trailing | `decode_single`, `decodeModel_single`, `decodeModel_short_bytes`; 55/56/255/256 bytes and simultaneous failures; long equations pending |
| `ethereum_rlp/rlp.py:427–484` | private list branches/ordered joined cursor of `decode` | exact ordered children in original-input windows; no copied list payload | outer header/canonicality/extent/trailing before children; child permissive header, declared-extent truncation, exact child decode; first failure wins | `decodeModel_short_list_truncated`, `decodeModel_short_list_trailing`; empty/nested/asymmetric trees, malformed first/later child and outer-extent priority; universal `decodeModel_success`, `decodeModel_encodeModel` |
| `ethereum_rlp/rlp.py:487–543` | private bounded window header descriptor in `decode` | at most eight original length digits; Nat extents; validated header endpoint | digit truncation before leading zero; header remains permissive about body and short/long form | advancing/bounded witnesses used by kernel-checked termination; all eight string/list long tags and tiny input declaring2^64−1 |
| derived storage observation | `decode_window_model` | clipped/empty/public Base extract, including conceptual huge offsets | same complete result and diagnostics as the exact list window | public Base window law; caller proof does not unfold the Base representation |
| derived from `ethereum_rlp/rlp.py:66–135,143–162,387–484` | `Rlp.decode_encode`, `decode_success_encodable`, `encode_eq_of_decode_eq_ok` | every `Encodable` item round trips; every successful finite input proves its result `Encodable` and reencodes exactly | no extra successful-domain premise or protocol guard | `decodeModel_encodeModel`, `decodeModel_success`; public-law callers in `RlpCanonicalCallerProofs.lean` |
| derived extent/image laws, `ethereum_rlp/rlp.py:387–484,487–543` | `Rlp.decode_eq_ok_iff`, `exists_decode_eq_ok_iff`, `eq_of_encode_eq`, `encode_inj`, `encode_prefix_free` | exact accepted image; injective and prefix-free encodings on `Encodable` with arbitrary tails | no claim of inverses or binding outside Q47 standard domain | public universal callers including accepted-tree round trip composition in `RlpCanonicalCallerProofs.lean` |

**Checks and provenance.** `RlpDecodeGuards.lean` compares complete constructor
trees with manual structural functions and exact diagnostics. Caller proofs use
only public equations. `rlp_decode_differential.py` uses the accepted current-source,
origin/RECORD loader and frozen `-I -B` interpreter, bypasses `.pyc`, and checks
sources before/after. It checks exact bytes inputs and recursively exact Python
bytes/list results before observations, including14 negative class controls.
Its seed5025 corpus covers all256 tags, strings through1024 bytes, width512,
depth32 and mutations. Success compares every byte/constructor/order; rejection
requires exact DecodingError, maps the first authenticated source raise site to
its diagnostic and checks the source message. Other exceptions, including
RecursionError, cannot count as protocol rejection. Interpreter/startup/frozen
installation/RECORD remain trust inputs. This is bounded actual raw-decoder
evidence, not a universal canonicality proof, Python host-depth agreement,
typed/schema composition or EEST guest execution.

### Implemented typed RLP slice

`STFSpec/Codec/RlpItem.lean` supplies the public raw model and diagnostic error.
`STFSpec/Codec/RlpTyped.lean` implements the following pure, total operations on
all model items. The exported accept-set laws are discharged for this slice;
typed decoding, other instances, schema and guest correspondence remain open (§10).
No instance is added on nested `RlpItem` (F17); only nonnested `RlpError` derives
`DecidableEq`. The model constructors preserve all supplied bytes/ordered children.

| Locked dependency source | Lean declaration and public type | Domain, value/effects | Ordered failures | Public law and deterministic regression |
|---|---|---|---|---|
| `ethereum_rlp/rlp.py:77–78` (0.1.6); `ethereum_types/numeric.py:477–484` (0.4.1) | `Rlp.ofNat : Nat → RlpItem` | every natural; `.bytes (Uint.toBeBytes n).toByteArray`; no effects | none | `toNat_ofNat`; zero/01/7f/80/0100 payloads |
| `ethereum_rlp/rlp.py:263–277` (0.1.6) | `Rlp.toNat : RlpItem → Except RlpError Nat` | all items; byte leaf gives complete BE value, zero from empty | list shape; nonempty leading zero | `toNat_canonical_iff`, `toNat_eq_ok_iff`; 00/0001/000001 reject |
| `ethereum_rlp/rlp.py:263–277`; `ethereum_types/numeric.py:566–577` | `Rlp.toNatBounded : Nat → RlpItem → Except RlpError Nat` | all widths/items; canonical integer of at most width bytes | list shape; leading zero; byte count exceeds width; guards precede numeric construction | `toNatBounded_canonical_iff`, `toNatBounded_eq_ok_item_iff`, `toNatBounded_leading_zero`; U64 max/overflow, 33-byte U256, model width zero |
| `ethereum_rlp/rlp.py:245–251` | `Rlp.toBool : RlpItem → Except RlpError Bool` | empty bytes false, singleton01 true | every other leaf or list, one Boolean shape diagnostic | `toBool_eq_ok_iff`; 00/02/0101/list reject |
| `ethereum_rlp/rlp.py:254–260` | `Rlp.toBytes : RlpItem → Except RlpError ByteArray` | every byte leaf, exact bytes; no effects | list shape | `toBytes_eq_ok_iff`; 0001ff preservation/list rejection |
| `ethereum_rlp/rlp.py:254–260`; `ethereum_types/bytes.py:27–36` | `Rlp.toFixed : (n : Nat) → RlpItem → Except RlpError (FixedBytes n)` | exact n-byte leaf, including n=0; all bytes preserved | list shape; wrong length | `toFixed_eq_ok_iff`, `toFixed_eq_ok_item_iff`; 0-byte and 19/20/21-byte address payloads, 31/32/33 bytes |
| `ethereum_rlp/rlp.py:374–379` | `Rlp.toList : RlpItem → Except RlpError (List RlpItem)` | raw list shape only; ordered children unchanged, no child typing | byte shape | `toList_eq_ok_iff`; nested raw child preserved; actual target `list[Bytes]` cases use valid Bytes children |
| `ethereum_rlp/rlp.py:217–229` | `Rlp.toFields : (n : Nat) → RlpItem → Except RlpError (Vector RlpItem n)` | raw dataclass shape/arity step only; exact n ordered fields, no child typing | byte shape; field count before children | `toFields_eq_ok_iff`, `toFields_wrong_arity`; too few/many and arity0; actual toy dataclasses have valid Bytes fields |
| `ethereum_rlp/rlp.py:325–343` | `Rlp.union2 : (RlpItem → Except RlpError α) → (RlpItem → Except RlpError α) → RlpItem → Except RlpError α` | all items, total callbacks; both alternatives contribute; returns sole success | zero successes (no variant); two successes (multiple variants), even equal values | `union2_eq_ok_iff`; actual Bytes0/Bytes20 union; model both-failure and same/different-value double-success |

**Error correspondence (Q68).** All typed rejection constructors here are
diagnostic refinements of one dependency `DecodingError`. The supplied wrapper
preserves each raw error and the entire typed result, including shape, Boolean,
width, field-count, no-variant, multiple-variant and integer-leading-zero
`nonCanonical` diagnostics. Single-channel erasure occurs only in the
mathematical source/consumer observation in §7. `empty`, `truncated` and `trailing`
are supplied raw-wire diagnostics, never produced by these leaf implementations;
a generic supplied callback can nevertheless return any `RlpError`.

Locked `ethereum_rlp/rlp.py:162–171` first calls raw `decode` outside the typed
catch, then wraps exceptions from `deserialize_to` in outer `DecodingError`.
`raise ... from e` retains causes (`ethereum_rlp/exceptions.py:19–30`); our
observation does not equate Python exception identity, messages or cause chains.
Intended source-target admission and successful reflection/class metadata
(`rlp.py:184–241,311–322`), local callback refinement and host premises remain
explicit. Nat corresponds to exact source Uint (`:204–205,265–275`), not plain
Python int or U256; its supplied decoder is exactly `Rlp.toNat`.

First consuming handlers remain the header fallback (`stateless.py:234–237`,
CONTRACT O3) and transaction check (`execution_engine/new_payload.py:60–68`, O6).
They must treat all projected rejections alike within their reference phase;
single-channel rejection is no universal O6 mapping. Raw `RecursionError` lies
outside the typed catch. A total raw decoder followed by typing proves no
generic host-depth agreement: a callback could accept every tree. D2r still
requires actual schema-depth and first-handler premises (D14, Q20, O12). These
leaves supply neither handler implementation nor full-guest correspondence.

**Checks and provenance.** `STFSpec/Conformance/Codec/RlpTypedGuards.lean` owns
strict deterministic model regressions; `RlpTypedCallerProofs.lean` uses only public
contracts, including both canonicality directions, complete bounded range and
exactly-one union. `rlp_typed_differential.py` authenticates the pinned source and
locked installed ethereum-rlp 0.1.6/ethereum-types 0.4.1 with trusted RECORD metadata,
verified resolved origins and current bytes pre/post. Its loader bypasses existing
`.pyc`; generated trusted-package probes check poisoned cache, wrong origin and
changed source. Run the frozen interpreter with `-I -B`, `--eels EELS` and
`--output SCRATCH/observations.lean` outside both repositories. The interpreter,
startup environment, frozen installation and RECORD remain trust inputs. The seed
5015 run has 422 guards: integers123, Boolean44, Bytes41, fixed123, list5,
field20, union41 and minimal payload25. Successful oracle results are checked for
exact Python classes/types, including bool versus integer classes. Width-zero
integers and arbitrary callbacks are model-only cases, not actual pin targets.
This is finite typed-value evidence, not EEST execution or a proof of Python code.

### Implemented derived addresses

`STFSpec/Codec/Address.lean` implements the four existing address APIs and proves
their exact one/two-query expansions, arbitrary-answer dependence, concrete Id
formulas and final twenty-byte suffix observations through public Base laws.
`encodable_computeContractAddress_preimage` proves the CREATE sender/nonce list is
`Encodable` for every sender and nonce below 2^256, supplying Q47's standard-domain
premise for protocol nonces. The Nat API remains total at every nonce; the bound
is a theorem hypothesis, not an input guard or outside-domain acceptance policy.
Creation/state/gas/collision handling, security assumptions and generic oracle
coupling remain separate.

| Pinned EELS source | Lean declaration and public type | Domain, value/effects | Ordered failures and consuming handler | Public law and deterministic regression |
|---|---|---|---|---|
| `forks/amsterdam/utils/address.py::compute_contract_address` (`:42–63`); locked `ethereum_rlp/rlp.py:66–88`, `ethereum_types/numeric.py:477–484` | `computeContractAddressQ : [Monad m] → [KeccakQuery m] → Address → Nat → m Address`; `computeContractAddress : Address → Nat → Address` | all Nat; one exact RLP sender/minimal-nonce query; complete final twenty bytes; `Encodable` proved for every nonce < 2^256 | no local guard/error mapping; lawful ExceptT queries preserve the original failure; VM/guest consuming handlers remain unimplemented | `encodable_computeContractAddress_preimage`, `computeContractAddressQ_eq`, `computeContractAddressQ_of_pure_answer`, `computeContractAddress_id/eq`, `toBytes_computeContractAddressQ`, `toBytes_computeContractAddress`, `run_computeContractAddressQ_error`; fixed sender at nonces 0–3, 127/128/255/256, 2^64−1 and larger Nat widths |
| `forks/amsterdam/utils/address.py::compute_create2_contract_address` (`:66–93`) | `computeCreate2ContractAddressQ : [Monad m] → [KeccakQuery m] → Address → Bytes32 → ByteArray → m Address`; `computeCreate2ContractAddress : Address → Bytes32 → ByteArray → Address` | every supplied fixed sender/salt and finite init code; exact code query, then ff/sender20/salt32/that answer32 query; final twenty-byte suffix | under the lawful ExceptT error contracts, first query failure suppresses second; outer failure retains its original error; no local handler or query after failure; VM/guest consuming handlers remain unimplemented | `computeCreate2ContractAddressQ_eq`, `computeCreate2ContractAddressQ_of_pure_answers`, `computeCreate2ContractAddress_id/eq`, `toBytes_computeCreate2ContractAddressQ`, `toBytes_computeCreate2ContractAddress`, `run_computeCreate2ContractAddressQ_error_code/hash`; EIP-1014 examples 0–3 and arbitrary recording answers/errors |
| D5 transformer composition | `run_computeContractAddressQ_stateT/exceptT`, `run_computeCreate2ContractAddressQ_stateT/exceptT` | added state unchanged; underlying ordered effects retained; exception lift wraps success without handling underlying failures | underlying effects remain unchanged; lawful ExceptT error contracts preserve failures | ordinary lawful-monad equations; extra StateT/ExceptT recording cases |

**Checks and provenance.** `AddressGuards.lean` compares complete values and exact
recorded preimages, distinct arbitrary inner/final answers, inner-answer changes,
zero-containing suffixes and first/second failures. `AddressCallerProofs.lean` uses
only public expansion/Id/suffix/Base equations, including the no-op padding proof
and the bounded CREATE preimage law. The suffix conversion uses
`Address.toBytes_ofNat_toNat`, owned by [EthBase §3](EthBase.md#3-eels-source-map).
The four CREATE2 facts are [EIP-1014 examples 0–3](https://eips.ethereum.org/EIPS/eip-1014#examples),
also observed against the actual pinned address functions. The committed driver
`STFSpec/Conformance/Codec/address_differential.py` authenticates current EELS,
ethereum-types and typed RLP source/RECORD files. Run it from the repository root:

```sh
EELS/.venv/bin/python -I -B STFSpec/Conformance/Codec/address_differential.py \
  --eels EELS --output EXTERNAL.lean
```

The driver owns its seed and case counts and records them in the result. It checks
exact Python input/output and hash classes, with negative class controls. It
instruments only ephemeral loaded hash bindings, forwards the original provider
and restores bindings in `finally`. Complete 20-byte results and one/two-query
preimages/digests are retained. Source/lock/RECORD files are authenticated before
and after execution; the imported recursion setup is left unchanged. Dependency
versions are checked against the pin. The concrete hash backend, isolated
interpreter, startup and installed dependencies/RECORD remain explicit trust
inputs. The emitted Lean guards and committed generic-effect guards provide
bounded reproducible evidence. They establish no universal Python equivalence,
EEST guest execution, native-client speed, C1–C4 or security result.

### Raw SSZ vocabulary and remaining source ownership

`STFSpec/Codec/SszModel.lean`, exported through `STFSpec.Codec`, supplies exactly
the nine `SszType`, five `SszValue` and six `SszError` constructors in §5. These
inductives are their own raw models: arbitrary natural parameters, complete byte
payloads, ordered finite recursive lists and independent boolean masks are
retained without a construction invariant. No authored instances or public laws
are added. Schema adapters, codecs, root operations and error producers remain
unimplemented. Structural sizing, nameless well-formedness and payload-only typing
are supplied separately below.

The descriptor graph in `utils/ssz.py:32–87,179–225,231–258` supplies the static
shape correspondence below. `_field_types` preserves reflected field order and
the wrapper's progressive container activates every field; the raw model also
admits other masks and independent field lists. Names, Python class admission,
inheritance and the at-capacity `more` rule are separate future schema premises.
`utils/ssz.py:263–325` supplies the natural/boolean/bytes/ordered-child abstraction
ingredients for values, without implementing Python coercions, runtime-class
reflection, backing nodes or defaults. Arbitrary raw trees imply no source-object
admission theorem. The six nominal `SszError` tags are guidance vocabulary, not
six Python exception classes; declaring them selects no producer, priority,
diagnostic correspondence or O1/O2/O12/O13 classification.

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `utils/ssz.py::_SszType` | 32 | `SszType` (inductive) | marker base class |
| `utils/ssz.py::_Uint` | 38 | `SszType.uint` | supported `uint(bits)` factory widths (`utils/ssz.py:91–95`): 1/2/4/8/16/32 bytes; raw Nat unrestricted |
| `utils/ssz.py::_ByteVector` | 44 | `SszType.byteVector` | |
| `utils/ssz.py::_ByteList` | 50 | `SszType.byteList` | |
| `utils/ssz.py::_List` | 56 | `SszType.list` | |
| `utils/ssz.py::_ProgressiveList` | 63 | `SszType.progressiveList` | |
| `utils/ssz.py::_Container` | 69 | `SszType.container` | |
| `utils/ssz.py::_Bool` | 73 | `SszType.bool` | |
| `utils/ssz.py::_ProgressiveByteList` | 77 | `SszType.progressiveByteList` | |
| `utils/ssz.py::_ListLimit` | 83 | `SszType.list` (limit argument) | annotation marker only |
| `utils/ssz.py::_ProgressiveListMarker` | 87 | `SszType.progressiveList` | annotation marker only |
| `utils/ssz.py::uint` | 91 | `SszType.uint` + width check | rejects unsupported widths at schema time |
| `utils/ssz.py::byte_vector` | 98 | `SszType.byteVector` | |
| `utils/ssz.py::byte_list` | 103 | `SszType.byteList` | |
| `utils/ssz.py::ssz_list` | 108 | `SszType.list` | |
| `utils/ssz.py::progressive_list` | 113 | `SszType.progressiveList` | |
| `utils/ssz.py::progressive_byte_list` | 118 | `SszType.progressiveByteList` | |
| `utils/ssz.py::_C` | 123 | none (type variable) | |
| `utils/ssz.py::SszContainer` | 126 | `class SszSchema` | |
| `utils/ssz.py::SszContainer.encode_bytes` | 129 | `SszSchema.encodeBytes` | |
| `utils/ssz.py::SszContainer.hash_tree_root` | 133 | `SszSchema.hashTreeRoot` | |
| `utils/ssz.py::SszContainer.decode_bytes` | 138 | `SszSchema.decodeBytes` (strict) | re-encode check becomes a theorem (S3) |
| `utils/ssz.py::ProgressiveSszContainer` | 149 | `SszType.progressiveContainer` (all fields active) | |
| `utils/ssz.py::_annotated` | 153 | none (schema construction) | Python reflection; schemas are written explicitly in Lean |
| `utils/ssz.py::_collection_element` | 169 | none (schema construction) | as above |
| `utils/ssz.py::_infer` | 179 | schema-authoring rule (S1) | followed by hand in each `SszSchema` instance; checked by `#guard` against EELS type roots |
| `utils/ssz.py::_rmk_type` | 208 | `SszType` semantics | |
| `utils/ssz.py::_FIELD_TYPES` | 228 | none (Python cache) | |
| `utils/ssz.py::_field_types` | 231 | none (reflection) | |
| `utils/ssz.py::_CONTAINER_TYPES` | 240 | none (Python cache) | |
| `utils/ssz.py::_container_type` | 243 | `SszSchema.type` | active fields `[1]*n` |
| `utils/ssz.py::_to_ssz_value` | 263 | `SszSchema.toValue` | byte-vector length check becomes a type invariant |
| `utils/ssz.py::_to_view` | 288 | `SszSchema.toValue` | |
| `utils/ssz.py::_from_ssz_value` | 299 | `SszSchema.ofValue?` | `base(int(v))` widening (S1) |
| `utils/ssz.py::_from_view` | 318 | `SszSchema.ofValue?` | |

`to_address_masked` from the same file is claimed by `EthBase` (a pure conversion). `encode_account` (in `fork_types.py`) is claimed by `EthStateCommit`; its state-dependent encoding remains outside EthCodec.

**External semantics.** This module must specify these libraries completely:
- `ethereum_rlp.rlp` (`encode`, `decode`, `decode_to`, `With`) and `ethereum_rlp.Extended`, as E1–E3 and D1r–D4r. `With` custom decoders are not used in Amsterdam decode sites; I checked with a grep.
- `remerkleable.basic`, `.byte_arrays.{ByteList, ByteVector}`, `.complex.{Container, List}`, `.progressive.{ProgressiveList, ProgressiveByteList, ProgressiveContainer}`, as S2–S6.
- `hashlib.sha256` via `EthHash`.

### Structural SSZ sizing (Q67)

`STFSpec/Codec/SszFixedSize.lean`, exported through `STFSpec.Codec`, supplies
`SszType.fixedSize? : SszType → Option Nat` and the single ordinary public law
`SszType.fixedSize?_eq` in §7, **discharged** on every raw descriptor. The readable
descriptor/private-field-list recursion is structurally terminating; a private
list induction relates the short-circuiting worker to the exact public fold.
The §4 complete-result controls and six private public-equation client groups
elaborate. These are target proofs/controls, without executed source comparison.

| Source at the pin / locked dependency | Lean operation | Domain, effects and failures | Law and controls |
|---|---|---|---|
| `utils/ssz.py:179–225,231–258`; `remerkleable/basic.py:52–53,252–309`, `core.py:200–213`, `byte_arrays.py:78–103` | `SszType.fixedSize?` primitive branches | every raw Nat width; pure, no error channel; source agreement only for actually mapped classes and matching byte widths | `fixedSize?_eq`; bool, zero/standard/unsupported/large uint and byte-vector widths |
| `utils/ssz.py:181–194,213–220`; `remerkleable/byte_arrays.py:262–271`, `complex.py:516–529`, `progressive.py:121–134,244–266`, `core.py:106–108` | same operation, variable branches | every raw child and limit; no recursive admission judgment; progressive protocol fallback is statically falsey `None`, not literal `False` or an observed execution result | same single law; zero limits, unsupported children, zero-width fixed children and nested progressive lists |
| `utils/ssz.py:231–258`; `remerkleable/complex.py:811–848`, `progressive.py:440–498,535–536` | same operation, container branches | every ordered raw field list and independent mask; optional sum over fields only; source class admission and reflection remain separate | same single law; empty/zero/mixed/nested fields, variable fields and independent malformed masks |

These source correspondences are static consequences of the retained source,
conditional on an actual successful intended mapping to the standard pinned
class, matching primitive byte widths and the actual ordered field classes,
with unchanged methods, reflection metadata and caches. The source marker's
integer width is in bits; the raw descriptor's width is in bytes. On this domain,
`some n` corresponds to a truthy `is_fixed_byte_length()` result and
`type_byte_length() = n`; `none` corresponds to a falsey classifier result,
without calling `type_byte_length`. This is neither an exact-`False` identity nor
a min/max characterization: zero-limit byte/lists and containers containing
variable zero-limit fields can have equal source min/max while remaining variable.
For progressive lists and progressive byte lists, inherited `View` protocol
fallback (`core.py:106–108`) has an implicit `None` result under ordinary Python
semantics; no source probe or formal Python-refinement theorem is supplied.

EELS creates progressive containers with all-one masks. Direct dependency
correspondence for other masks additionally needs actual successful class
construction and the same enumerated fields. Ordinary name filtering/inheritance,
progressive admission and the capacity-256 `more` rule are not represented by
nameless raw syntax. Unsupported uint widths, ordinary empty containers and
malformed progressive masks can therefore have chosen raw answers without a
corresponding source class. Class/annotation exceptions remain separate from
sizing, codec failures and guest outcomes. In particular, fixed-zero element
classification does not repair the decoder's division/modulo by element width
(`remerkleable/complex.py:186–195`); its serialization/inverse domain stays open.

### Structural SSZ well-formedness (Q70)

`STFSpec/Codec/SszWellFormed.lean`, exported through `STFSpec.Codec`, supplies
`SszType.WellFormed : SszType → Prop` and exactly one ordinary public
`SszType.wellFormed_iff` constructor law in §7, **discharged** on all raw syntax.
Private descriptor/field-list recursion and a list bridge implement the equation;
there is no executable validator, DecidablePred, instance or diagnostic producer.

| Source at the pin / locked dependency | Lean operation and domain | Effects and failures | Law and controls |
|---|---|---|---|
| `utils/ssz.py:91–120,179–225`; `remerkleable/basic.py:252–309`, `byte_arrays.py:79–103,174–194` | `SszType.WellFormed` primitive branches; byte widths 1/2/4/8/16/32; unconditional bool/vector/byte-list/progressive-byte schemas, unrestricted raw Nat lengths/limits | pure Prop; no effects or ordered errors | `wellFormed_iff`; W01–W22, C01–C04/C07 |
| `utils/ssz.py:181–184,215–218`; `remerkleable/complex.py:336–399`, `progressive.py:88–134` | same predicate; recursive element validity even at list limit 0 | pure Prop; limit never hides an invalid child | same law; W23–W30, C05–C06/C10 |
| `utils/ssz.py:231–260`; `remerkleable/complex.py:800–819`, `progressive.py:440–498,535–536` | same predicate; ordinary nonempty/all-member fields; progressive final true/length ≤ 256/true-population=field count/all-member fields | no source-class or error-order assertion | same law; W31–W64, C08–C09/C11–C12 |

These are static structural correspondences conditional on actual mapped primitive
classes and reflected ordered fields/names. EELS creates all-one progressive
masks; direct dependency sparse-mask correspondence needs its own successful
class mapping. The raw Bool mask rules out nonbinary entries. At length 256 the
actual `more` name and View/type checks remain local source-mapping premises;
nameless well-formedness alone asserts no successful source class.

Zero vectors and limits remain admissible. Ordinary empty fields and empty masks
fail; sparse masks and length 256 are structurally admitted. Payload-only value
typing is supplied separately under Q71; it deliberately does not entail WF. Q67 sizing is unchanged on every malformed
schema and fixed zero remains possible under WF. Count/backing, offset/scope,
cache, codec/root and zero-width-list inverse domains retain separate premises.
No global positivity condition repairs a later division or inverse.

### Structural SSZ payload typing (Q71)

`STFSpec/Codec/SszWellTyped.lean`, exported through `STFSpec.Codec`, supplies
exactly `SszValue.WellTyped` and the ordinary complete `wellTyped_iff` in §7,
**discharged** on every raw descriptor/value pair. This is payload-only typing:
raw unsupported/zero uint widths use the mathematical range, empty lists visit
no child values, empty ordinary fields have an empty typed payload, and masks
never select payload fields. Equal lengths and every zipped pair enforce exact
arity, order and independent repeated field occurrences. WF is a separate premise.

| Source at pin / locked dependency | Operation and domain | Effects / failures | Law and private controls/clients |
|---|---|---|---|
| `utils/ssz.py:91–95,186–188,209–210,271–272,309–310`; `remerkleable/basic.py:90–97,252–309` | `SszValue.WellTyped`, every uint descriptor/value pair, raw width in bytes; `n < 2^(8*width)` | Prop only; no effects/errors; unsupported widths are mathematical completions, not source-class success | ordinary `wellTyped_iff`; wtM01–wtM05, wtR01–wtR24, wtN08–wtN09; wtP01/wtP02/wtP10/wtP13/wtP14 |
| `utils/ssz.py:196–197,223–224,273–284,311–314`; `remerkleable/basic.py:24–27,52–61`, `byte_arrays.py:79–103,174–194`, `progressive.py:265–266` | same predicate, Bool/byte-vector/byte-list/progressive-byte branches and all raw tags | Bool stays distinct from uint/bytes; exact sizes/limits; no source coercion or uint256 backing premise is built in | same law; wtM06–wtM20/wtM31–wtM35, wtB01–wtB12, wtN07, wtZ01; wtP08/wtP09/wtP14 |
| `utils/ssz.py:169–184,215–218,266–270,303–308`; `remerkleable/complex.py:336–399,492–493`, `progressive.py:88–134,239–249` | same predicate, ordinary actual count≤limit and actual-member recursion; progressive actual-member recursion without cap | no declared-child WF or source uint256/backing check; empty recursion is vacuous | same law; wtM21–wtM30, wtL01–wtL16, wtN04–wtN06/wtN10, wtZ02–wtZ05; wtP01–wtP04/wtP13/wtP15/wtP16 |
| `utils/ssz.py:231–260,288–296,318–325`; `remerkleable/complex.py:768–819`, `progressive.py:460–536` | same predicate, both container families: length equality and every ordered zipped pair; independent mask | every actual field occurrence checked; no inactive placeholder or mask validity/name admission; all unmatched tags False | same law; wtM36–wtM45, wtF01–wtF18, wtN01–wtN05; wtP05–wtP07/wtP11/wtP12/wtP16 |
| all branches above; ordinary private structural/list induction | `SszValue.wellTyped_iff (t) (v)`, every raw pair | complete logical characterization; no diagnostics, source execution or admission equivalence | exact §7 type proved; 130 complete signed controls and 16 private client groups |

These five source rows are static interpretation inherited from the approved
source investigation, conditional on actual mapped classes and fields; no fresh
source call, runtime-class probe or differential execution belongs to this Prop
slice. There is no count cap in WT. Source uint256 actual counts remain local at
ordinary nonempty List construction, ProgressiveList construction, ByteList
`get_backing`, nested constructor/backing consumers and length mix-ins. Names,
reflection/coercion, class construction, cache availability, emitted uint32
offsets, decoder scope and positive-width element recovery remain operation
premises. WT plus WF does not repair zero-width list inverse/count ambiguity.
No error policy, codec/root domain or host/guest/resource/cost gate is selected.

### Raw SSZ byte packing (Q72)

`STFSpec/Codec/SszPack.lean`, exported through `STFSpec.Codec`, supplies exactly
`Ssz.pack : ByteArray → Array Base.Bytes32` and the ordinary complete
`Ssz.pack_toBytes` in §7, **discharged** on every finite existing ByteArray.
“Internal” here means an exported Codec component helper; all references,
construction support, derived properties, controls and clients are Lean-private.
It preserves every input byte and its order, emits `(n+31)/32` exact 32-byte
chunks, and pads only a nonempty final partial chunk on the right. Empty input
has no chunks; an exact multiple of 32 has no extra chunk. This raw helper has
no schema, WF/WT, class/count cap, offsets, root, hash, backend, error/completion
or host-size parameter.

| Source at pin / locked dependency | Operation and domain | Effects / failures / first handler | Law and controls |
|---|---|---|---|
| EELS `utils/ssz.py:133–135,263–296` caller/coercion context; eth-remerkleable 0.1.31 `remerkleable/core.py:344–349` raw helper | `Ssz.pack : ByteArray → Array Base.Bytes32`, all finite mathematical bytes | pure ordered exact 32-byte chunks; no model failure or diagnostic producer, so no local handler/O-row | ordinary complete `Ssz.pack_toBytes`; six private property/client groups and all 15 complete literal controls in §4 |
| same helper; ordinary private List/range/window induction | `Ssz.pack_toBytes (b)`, complete ordered byte observation on every finite input | logical equation only; no source/runtime or host-resource equivalence | exact §7 type; private observation injectivity determines complete output arrays |

Static source correspondence retains original immutable builtin bytes, slicing,
concatenation, len/range/shifts, original helper/RootNode/Root identities and
successful host allocations. `RootNode` at `tree.py:274–275,296–302` stores and
projects leaves without a call-time hash. Importing `settings.py:24–31` initializes
zero hashes separately; typed views, backing construction and length mix-ins may
hash or consume uint256 counts. Those consumers are not this raw helper.
No original source was executed, imported or probed for this finite mathematical
slice, and no raw-pack differential profile is released here. Ordinary full-byte
proofs and the 15 mathematical controls verify the stated model operation;
they imply no unrestricted Python/class/host or guest correspondence. The
broader well-typed round trips and strict-decoder mutation comparisons in §4
remain obligations of the unimplemented typed codecs and their consumers.

### SSZ zero-hash recurrence and prefix (Q73)

`STFSpec/Codec/SszZeroHash.lean` supplies the two existing values and the two
ordinary public laws in §7, **discharged** for all mathematical Nat depths and
the complete ordered finite prefix. Every reference, builder, derived property,
control and client is private. The prefix is constructed by one linear list
traversal and one array conversion; no entry restarts the recurrence. This source
structure supplies no compiled sharing, one-time initialization or C1–C4 result.

| Pinned source | Lean operation / domain | Effects, failures and source premises | Laws / controls |
|---|---|---|---|
| EELS `utils/ssz.py:133–146,208–225,243–260,288–296` root caller context; eth-remerkleable 0.1.31 `remerkleable/settings.py:13,16–17,21,24–31`; `remerkleable/tree.py:109–110` | `Ssz.zeroHash : Nat → Base.Bytes32`; all-Nat mathematical zero/pair-SHA recurrence | pure; no model error or local handler. Original initialized globals, SHA implementation, aliases, constructors and successful host execution are source-correspondence premises; original table contains indices 0 through 255 only | ordinary `zeroHash_eq`; private zhP0–zhP3/zhP7/zhP9–zhP11 and C0/C1/C3–C5 |
| same ordered initialization; finite optimization prefix | `Ssz.zeroHashes : Array Base.Bytes32`; exact depths 0 through 64 | immutable mathematical value; no public depth cap, source mutation/cache or resource policy | ordinary complete `zeroHashes_toList`; private zhP4–zhP6/zhP8 and C2 |

Each pair preimage is exactly 64 bytes. Public Base width/append/export laws and
`Sha256.sha256_fipsDigest` discharge the local FIPS premise `512 < 2^64` and
retain the complete ordered preimage and digest trace. Symbolic SHA expressions
check composition; provider contracts supply algorithm fidelity. Mathematical
root 256 remains defined without claiming source `zero_node(256)` succeeds.
No original Python execution, digest literals or source-runtime profile is
released here; source-only groups 0–3 remain UNRUN. Root consumers retain the class/backing,
per-path table-index, override/alias/history and host premises described above.

### Physical-capacity Merkleization (Q74)

`STFSpec/Codec/SszMerkleize.lean` supplies exactly the helper and complete public
law in §5/§7. A private readable full List/tree reference and its padded-layer
fold agree with the packed Array interval traversal on the entire supported
domain. The executable passes offsets rather than copying child subtrees and
returns cached zero roots for wholly absent intervals. Existing zeroHashes roots
are extended above 64 by a single threaded recurrence. Actual-chunk work, depth
traversal/arithmetic and zero availability/extension are separate; no universal
all-depth O(chunks), exact runtime hash count, compiled sharing/lifetime or C1–C4
claim is made. Mathematical singleton paths are symbolic equations only.

| Pinned source | Lean operation / domain | Effects, failures and source premises | Law / controls |
|---|---|---|---|
| locked eth-remerkleable 0.1.31 `remerkleable/tree.py:242–263`; EELS `utils/ssz.py:133–146,208–225,243–260,288–296` caller context | `Ssz.merkleize chunks limit h`; physical count ≤ 2 to the inline least covering depth | pure ordered padded root; no overflow result or error converter. Declared constructor admission is separate; source original classes/backing/root/hash/globals/imported aliases/cache history/per-path zero-table availability and successful host execution remain premises | complete ordinary `merkleize_eq`; private merkleP0–merkleP9 and public-facade C0–C9 below |

Limits 0/1 select capacity 1, so a singleton at limit 0 has helper support. Limit 3
selects capacity 4: counts 3/4 retain depth 2, count 5 has no proof argument. No global
WF, WT or Rootable hypothesis is needed. Existing raw vocabulary/predicates and
pack/zero contracts remain unchanged. Plain padding does not bind counts.
Capacity alone proves no source success or depth 64/255 cap. No original source
execution/profile is released; source-runtime controls remain UNRUN.

### Progressive contents-tree Merkleization (Q75)

`STFSpec/Codec/SszMerkleizeProgressive.lean` supplies exactly the optional-depth
operation and complete public recurrence in §5/§7. A private source-shaped List
reference equals the packed traversal for every Array, offset and Nat depth.
The executable retains one original Array and advances an offset, extracting
only disjoint current windows. It never converts/copies the entire remaining
suffix, enumerates progressive levels up to n, or materializes exponential padding.
Each ordinary prefix uses the existing public physical helper with a private
capacity proof; its sparse traversal and self-contained 65-entry prefix/linear
zero extension retain their existing contract.

| Pinned source | Lean operation / domain | Effects, failures and source premises | Law / controls |
|---|---|---|---|
| locked eth-remerkleable 0.1.31 `remerkleable/progressive.py:25–32`; ordinary `tree.py:242–263`; EELS `utils/ssz.py:133–146,208–225,243–260,288–296` caller context | `Ssz.merkleizeProgressive chunks (depth := 0)`; every finite Array and every Nat starting depth | pure progressive contents root, no errors; original nodes/backings/classes/root/hash/globals/imported aliases/cache history/per-path zero availability and successful host execution remain premises | complete ordinary `merkleizeProgressive_eq`; private progressiveP0–progressiveP9 and facade-only C0–C9 below |

Empty at every depth returns zero32, including empty suffixes; it does not request
zeroHash(depth). Nonempty capacity is 2^depth, with suffix depth + 2. Source bulk
construction differs from append/navigation: a payload 19 tree splits 1 + 4 + 14,
and its final ordinary 14/16 subtree **does insert zeroHash 1**. The all-Nat law
implies no arbitrary-depth source success or global 64/255 cap. VirtualNode roots
can be available without traversing their children; root and navigation premises
must stay distinct. No original Python runtime/profile was released: the
source-only operational catalog remains UNRUN.

Actual chunk copying sums over disjoint windows; progressive levels, power/offset
arithmetic, ordinary subtree traversal depth, and each ordinary call's zero
availability/extension and allocation/conversions are separate costs. There is
no cross-call cache-reuse, universal all-depth O(n), exact runtime hash count,
compiled sharing/cache-lifetime, C1–C4 or resource claim. No D18 exception is adopted.


### SSZ length mix-in (Q76)

`STFSpec/Codec/SszMixInLength.lean`, exported through `STFSpec.Codec`, supplies
exactly the operation and complete ordinary public equation in §5/§7. The direct
executable SHA expression is also its legible reference. The natural count has
exactly one local strict bound; no WF, WT, Rootable, source or host premise is
added to the API. All support, derived/control/client declarations remain private.

| Pinned source | Lean operation / domain | Effects, failures and source premises | Law / controls |
|---|---|---|---|
| eth-remerkleable 0.1.31 `remerkleable/basic.py:90–97,226–227,303–309`, `core.py:303–305`, `settings.py:5,16–17`; ordinary `complex.py:336–368`, ByteList `byte_arrays.py:228–232`, progressive `progressive.py:88–119,265–266`; EELS `utils/ssz.py:130–146,214–230,264–325` and `forks/amsterdam/stateless.py:220–226,269–271` | `Ssz.mixInLength root len h`; arbitrary Bytes32 root and Nat count with `len < 2^256` | pure complete SHA256(root32 ++ countLE32); no model effects/error or handler. No input is available at/outside 2^256; no modulo completion, U256 argument, runtime branch or new guest diagnostic is selected | ordinary complete `mixInLength_eq`; private lengthP0–lengthP9 and independent facade C0–C9 in §4 |

Static correspondence retains actual standard source classes, exact 32-byte roots,
original basic backing/endian/hash/global/import aliases, PairNode cache history
and successful host operations. Contents backing is constructed before checked
`uint256(count)`; final PairNode construction follows its right-child expression.
Uncached child hashing is later, while cached roots may avoid child traversal.
This extracted successful-value helper proves no whole caller failure/resource
order. No original source was executed/imported/probed and source-only cases
remain UNRUN, with no runtime profile. The public Base digit law and Hash FIPS
law supply complete byte/digest composition, not a formal Python refinement.
Actual decoder/adapters and every nested count must still supply the local bound.
No input domain is narrowed to prove rootability; source failure cannot be mapped
to a new guest error here. Q77 supplies the local activity mix-in, and Q78 supplies
local Rootable support. Actual decoder/adapter support, enclosing roots/layout/
binding, guest/O2/O12/O13, resource and readiness gates remain open.

### SSZ active-field mix-in (Q77)

`STFSpec/Codec/SszMixInActiveFields.lean`, exported through `STFSpec.Codec`,
supplies exactly the operation and complete ordinary equation in §5/§7. The
readable bounded-width fold and complete SHA expression are the executable
reference. Exactly one local width proof is required; numeric fit is derived
privately. All authored model/support/derived/control/client declarations stay private.

| Pinned source | Lean operation / domain | Effects, failures and source premises | Law / controls |
|---|---|---|---|
| eth-remerkleable 0.1.31 `remerkleable/progressive.py:460–529,550–563`, `bitfields.py:381–416`, `core.py:187–188,235–247,326–341`, `tree.py:7–10,175–202,242–251`, `settings.py:2,9,16–17`; EELS `utils/ssz.py:133–135,231–258,287–295`, `forks/amsterdam/execution_engine/types.py:39–80` and `execution_engine/requests.py:96–117` | `Ssz.mixInActiveFields root active h`; arbitrary Bytes32 root and Bool list with `active.length ≤ 256` | pure SHA256(root32 ++ maskLE32); no effects/error/handler or runtime completion. Empty/allfalse/trailingfalse admitted mathematically; width 257 has no argument even if high bits are false | complete ordinary `mixInActiveFields_eq`; private groups 0–9 in the P family and independent facade C0–C9 in §4 |

Source class checks require nonempty, final true, matching population/fields,
width ≤ 256 and `more` membership at capacity before View fields and ordered
sparse position mapping. These are separate from the helper proof and nameless
WF/payload typing. Source contents construction inserts zero nodes at inactive
activity positions; the supplied root must already denote that tree. Sparse
field ordinal does not equal activity position. Eager class/content/mask
construction and later lazy/cached pair hashing have different order; supplied
backings may bypass reconstruction. Actual class identity, reflection/names,
32-byte root interpretation, hash/global/import aliases, backing/cache coherence
and host success remain local premises. Actual guest masks are all true with 19 and 5 entries; this supplies no user-mask acceptance or whole failure/resource law.
No original source execution/profile is released; source-only cases are UNRUN.
Existing Base/Hash contracts suffice, with no new provider or schema API.

### Local declared/source-shaped SSZ root support (Q78)

`STFSpec/Codec/SszRootable.lean`, exported through `STFSpec.Codec`, supplies
exactly `Ssz.Rootable` and the complete ordinary `Ssz.rootable_iff` in §7,
**discharged** for all raw descriptor/value pairs. Private structural descriptor/
value-list/field-list workers and ordinary list bridges implement that equation.
Every authored helper/reference/control/client is private; no instance or
runtime validator is introduced. Both public declarations retain named `t`/`v`.

| Source at pin / locked eth-remerkleable 0.1.31 | Operation/domain | Effects and failures | Law and controls/clients |
|---|---|---|---|
| `utils/ssz.py:91–95,179–225,263–325`; `basic.py:24–61,90–97,252–309` | `Ssz.Rootable`, all raw pairs; supported uint byte widths 1/2/4/8/16/32 with mathematical range; Bool stays distinct | pure Prop, no effects/errors/coercion/truncation | complete `rootable_iff`; rootableP0/rootableC0 all nine matches and 36 unmatched tag pairs; rootableP1/rootableC1 scalar widths/range/Bool |
| `byte_arrays.py:79–103,173–194,225–235`; `progressive.py:88–118,265–266` | same predicate; exact vector size, ordinary byte-list declared bound and actual byte count < 2^256; progressive byte count < 2^256 | no extra vector count bound or progressive ordinary cap | same law; rootableP2/rootableC2 exact/zero vectors and limit 0; rootableP4/rootableC4 symbolic byte ceilings |
| `complex.py:135–162,336–399`; `progressive.py:88–134`; `core.py:273–332` | same predicate; ordinary declared element bound, actual element count < 2^256, every actual child and basic classifier; progressive omits declared bound | direct basic widths inspected even when empty; Bool one byte/basic, fixed vectors composite | same law; rootableP3/rootableC3 complete support and child projections, rootableP4/rootableC4 both element ceilings; rootableP8/rootableC8 unused-composite/direct-basic contrasts |
| `utils/ssz.py:231–260`; `complex.py:768–819`; `progressive.py:460–530` | same predicate; nonempty ordinary fields, exact ordered arity/children; progressive final true, width ≤ 256, population and arity/children | sparse false slots denote depth 0 zero chunks in contents; no new container count bound, slot API, source name premise or root output | same law; rootableP5/rootableC5 arity/order failures, rootableP6/rootableC6 sparse/population/arity, rootableP7/rootableC7 masks 255/256/257 and malformed masks |
| ordinary structural recursion and public constructor laws | `Ssz.rootable_iff (t) (v)`, complete local-domain equation; private all-t/v Rootable→WT | logical characterization, not class admission or decoder/root-result equivalence | rootableP0–rootableP9 and rootableC0–rootableC9; rootableP9 value induction and rootableC9 independent descriptor induction; rootableP8/rootableC8 exact non-global-WF witnesses |

This is selected C, not a global WF/WT conjunction or physical-only admission.
An empty List0 of container[uint3] and an empty progressive list of container[]
are Rootable with false schema WF; an empty direct uint3 list is excluded by
basic classification. Every actual child still supplies its own support.
Construction of source classes visits unused schemas, so names/classes,
reflection/order/coercions, `more` at capacity 256 and actual mapping remain local
source-facing premises. The actual guest uses fixed ordinary/progressive schemas
with masks 19/5 and roots before semantic execution checks. Source-accepted bytes
retain their acceptance while the actual view→dataclass→fresh-view support bridge
is investigated. No execution-validity/nonempty-transactions/headers premise or
new decoder guard is selected. Q79 supplies raw roots separately.
Backing/cache/hash/global/alias/host coherence, source failure/resource order,
O2/O12/O13, binding/security, C1–C4 and readiness remain separate obligations.
There is no source execution or differential profile in this Prop-only slice.

### Computational SSZ roots and direct result law (Q79)

`STFSpec/Codec/SszRoot.lean`, exported through `STFSpec.Codec`, supplies exactly
`Ssz.hashTreeRoot (t) (v) (h : Ssz.Rootable t v)` and the complete ordinary
`Ssz.hashTreeRoot_eq` in §7, **discharged** on the unchanged Q78 domain. All authored
support, typed byte projections, actual-child traversal, slot construction,
references, derived laws, controls and clients remain private. No instance,
validator, runtime bound check, extra public law or schema/provider change is added.

| Source at pin / locked eth-remerkleable 0.1.31 | Operation/domain | Effects and failures | Law and controls/clients |
|---|---|---|---|
| `utils/ssz.py:91–95,133–135,200–225,263–296`; `basic.py:18–27,91–99,226–227,252–309`; `core.py:303–305` | `Ssz.hashTreeRoot`, uint/Bool branches under actual local support | full 32 low-first bytes; Bool byte 00/01, no hash/tag/count mix | complete `hashTreeRoot_eq`; rootP0/rootC0 whole arbitrary t/v/h law; rootP1/rootC1 all six widths/endpoints, full bytes and excluded tags/ranges |
| `utils/ssz.py:211–214,219–220,276–284`; `byte_arrays.py:80–104,134–140,170–197,228–232`; `progressive.py:88–135,239–266` | same operation, fixed/ordinary/progressive bytes | fixed vectors use declared chunk count without a mix; ordinary byte lists use declared limit in chunks; lists mix actual byte count | same law; rootP2/rootC2 vectors 0/1/31/32/33/48/96/256, byte limits 0/1/32/33 and same-pack/different-count; rootP5/rootC5 progressive empty/one |
| `utils/ssz.py:215–218,266–273`; `complex.py:140–161,333–399,492–493,512–513`; `core.py:292–293,312–323`; `progressive.py:25–32,88–135` | same operation, ordinary/progressive element lists | supported uint uses consecutive w-byte digits; Bool uses one byte each; every other descriptor is composite, including fixed vectors; count is actual elements | same law; rootP3/rootC3 packed uint64 list 5/Bool 33 and general size/unit/capacity proofs; rootP4/rootC4 composite order/duplicates and empty unused malformed schemas; rootP5/rootC5 boundaries 0/1/5/6/21/22 |
| `utils/ssz.py:221–222,243–260,264–265,288–296`; `complex.py:726–740,768–819,854–856`; `progressive.py:450–530`; `bitfields.py:378–410`; `core.py:326–341` | same operation, ordinary/progressive containers | exact ordered paired child roots; ordinary fields have no count mix; progressive false positions are depth 0 zeros in exactly mask.length slots, separately mixed with the full activity chunk | same law; rootP6/rootC6 fields/order/arity, rootP7/rootC7 sparse leading/internal gaps, 255/256 and excluded 257; ordinary linear-scan/rank-model equality and actual true-rank bounds |
| actual-value induction, public Rootable/pack/tree/mix/Base laws; actual schemas `forks/amsterdam/execution_engine/types.py:39–96`, `execution_engine/requests.py:41–126`, `blocks.py:38–63` | complete recursive equation and its local witnesses on C | no recursion into unused schemas; no extra count bound on fixed vectors/containers; no source, error or security completion outside C | rootP8/rootC8 real scalar projections, universally proof-independent ordered child certificates, capacities, nested byte/element counts and whole-law determination; rootP9/rootC9 Amsterdam schema/arity/whole-root recipes |

Every conditional witness in the public law is available under C. Proper actual
children supply recursive calls; exact arity prevents zip truncation. The private
linear mask scan equals the entire inline rank expression; true ranks are in
bounds, so its default root is unobservable under C. Actual-value induction shows
that any C-indexed function satisfying the entire equation has the same result.
No SHA injectivity premise is used, and this determination result is not request
binding or source success. An empty actual composite list does not inspect its
unused malformed schema; an empty direct unsupported uint list has no C proof.

Source correspondence retains original names/classes/reflection/coercions,
construction of unused schemas and capacity 256 `more`, genuine root/backing/cache/
hash/global/alias/endian coherence, actual executed-path zero-table availability,
successful host execution and decoder view→dataclass→fresh-view preservation.
The [original PR #239 review record](https://github.com/alexanderlhicks/leanerSTFSpec/pull/239#issuecomment-6433123624)
reports 72 source-labelled cases, two mathematical-only extensions and 21 excluded
cases with no root result.
These observations and the corresponding Lean comparison belong to the original
run; the ordinary symbolic proofs are separate. No new
accepted-domain restriction, decoder guard, execution-validity or nonempty-header/
transaction premise follows. O2/O12/O13, source failure/resource order, external
anchors, collision/security, C1–C4 and readiness stay with their existing owners.

### Computational forward SSZ serialization (Q80)

`STFSpec/Codec/SszEncode.lean` supplies exactly `Ssz.Serializable`, its complete
ordinary decoupled `serializable_iff`, proof-domain `Ssz.encode` and the complete
ordinary `encode_eq` in §5/§7. All support, logical lengths, readable references,
cached schema metadata, packed writers and derived proofs remain private.
**Discharged:** structural/proper-child termination; all-raw cached/uncached writer
equality (`prepareCached_eq`), ordinary executable/readable-reference equality
(`encode_reference`), supported exact logical length (`encode_size`), supported
fixed widths, constructive ordered certificate existence, proof independence and
whole-result determination. The inline recursor in the public support-law type is
complete and requires no private global name. Q67–Q79 contracts are unchanged.

| Source at pin / locked eth-remerkleable 0.1.31 | Supplied operation/domain | Effects and failures | Ordinary law and private evidence |
|---|---|---|---|
| `utils/ssz.py:91–95,208–210,271–272`; `basic.py:90–97,226–227,252–309` | `Ssz.encode`, actual uint at the six supported byte widths and fitting Nat | exact low-first digits; no result outside `Serializable` | `serializable_iff`/`encode_eq`; `SszEncodeControls` all widths/endpoints and `SszEncodeCallerProofs` excluded actual widths0/3/overflow |
| `utils/ssz.py:211–214,219–224,273–284`; `basic.py:21–27`; `byte_arrays.py:59–60,79–103,174–194,262–278`; `progressive.py:265–266` | same operation, Bool/fixed/ordinary/progressive bytes | byte00/01 or complete original bytes; exact vector size/ordinary limit only | both complete laws; whole-byte literal/native controls for zeros/order/size0, public-law wrong-tag/size/limit clients |
| `utils/ssz.py:215–218,266–270`; `complex.py:224–242,336–411`; `progressive.py:85–144,239–249` | same operation, both element-list families | fixed concatenation or ordered table/tails; ordinary count limit, actual child support and emitted starts | both complete laws; literal/native fixed0, empty unused malformed schema and nested cases; public-law symbolic offset clients |
| `utils/ssz.py:243–258,263–265,288–296`; `complex.py:768–819,866–878,963–981`; `progressive.py:440–532` | same operation, both container families | exact arity and ordered paired children; mask absent from wire | `encode_eq` mixed head/tail law; literal/native empty containers/arbitrary masks/equal offsets, public-law arity and mask clients |
| `complex.py:23–24,104–108,235–242,967–981`; `core.py:173–176`; `settings.py:5` | support at every actually written uint32 start, recursively | mathematical pure byte result; no failure priority or guest error mapping | private exact length/reference/cached-planner equality, structural termination/certificates/determination; independent facade clients; static packed-writer structure (§6), compiled allocation/throughput and C1–C4 remain open |

Source success remains conditional on actual names/classes/inheritance/reflection,
coercions, construction of unused schemas (including `more` at capacity256),
standard methods/builtins/little-endian bindings, faithful typed views/backing,
cache coherence and successful host streams/allocation/navigation. Source fresh
List/ProgressiveList and byte-list backing counts use uint256
(`complex.py:367`, `progressive.py:118`, `byte_arrays.py:228–232`); Q80 supplies no
such bounds. The mathematical length model is not an unconditional theorem about
Python `value_byte_length`; dynamic serializers use actual returned byte counts.
EELS `_to_view` converts ordered fields before enclosing view construction
(`utils/ssz.py:288–296`), so this support contract establishes no constructor,
coercion, stream or allocation failure order. Decoder scopes/metadata, source
admission, inverse/typed adapters, roots and guest outcomes stay separate.

## 4. Tests

- **EEST fixture areas.**
  - All 29030 guest records decode SSZ and compute the output root.
  - **O1 SSZ/schema rejection:** `amsterdam/eip8025_optional_proofs/stateless_input_bytes`. I checked all 9 records in the `blockchain_tests` copy, and each expects the zero sentinel: empty input, incomplete schema id, invalid first SSZ offset, missing SSZ body, shifted SSZ offsets, trailing garbage, truncated SSZ body, unsupported schema fork, unsupported schema revision. These are the only 9 zero-sentinel outputs in the corpus (a streamed count found 9 zero, 1199 false and 27822 true).
  - RLP headers: `eip8025_optional_proofs/witness_validation_headers` (malformed RLP header, non-contiguous chain, missing parent).
  - Transactions: `ported_static/stTransactionTest`, `prague/eip7702_set_code_tx`, `berlin/eip2930_access_list`, `cancun/eip4844_blobs`, `osaka/eip7934_block_rlp_limit`.
  - Receipts and withdrawals: `shanghai/eip4895_withdrawals`. Requests: `prague/eip6110_deposits`, `eip7002_el_triggerable_withdrawals`, `eip7251_consolidations`, `amsterdam/eip8282_builder_execution_requests`.
  - Addresses: `frontier/create`, `cancun/create`, `ported_static/stCreateTest`, `stCreate2`, `stRecursiveCreate`, `constantinople/eip1014_create2`.
- **EELS unit tests** (`tests/json_loader/`), to port as `#guard`s:
  - `test_rlp.py`: canonical integers `0x80`↦0, `0x01`, `0x7f`, `0x81 80`, `0x82 01 00`; `0x00`, `0x82 00 01` and `0x83 00 00 01` rejected for `Uint`, `U64` and `U256`.
  - `test_ssz.py`: nested round trip, collection limits, fixed-width integer round trip, offset-gap rejection (standard and nested progressive), non-empty list with zero first offset.
  - `test_transaction_codec.py`, `test_withdrawal_codec.py` (maximum and oversized `amount`), and `test_stateless_guest.py` (schema id).
- **`core` `#guard` cases.**
  - RLP encode:
    - `""`↦`80`, `00`↦`00`, `7f`↦`7f`, `80`↦`81 80`;
    - a 55-byte string ↦ `b7 ‖ …`, a 56-byte string ↦ `b8 38 ‖ …`;
    - `[]`↦`c0`, a 56-byte payload ↦ `f8 38 ‖ …`;
    - `Uint 0`↦`80`, `Uint 1024`↦`82 04 00`.
  - RLP decode rejects:
    - `""`, `81 05`, `b8 05 …` (long form for a short string), `b9 00 40 …` (leading-zero length);
    - `c1` (truncated), `05 06` and `c0 00` (trailing bytes), `c2 82 00` (truncated inner item);
    - `bf ff…ff` (a huge declared length, which must be rejected without allocating).
  - Typed decode rejects: `bool 02`, a 33-byte `U256`, a 19-byte `Address`. A `Bytes0 | Address` union succeeds on exactly one alternative.
  - Adversarial: 40,000-deep nesting. The spec decodes it, where the reference raises `RecursionError`; the typed decode then rejects it (D2r). 20,000-deep nesting, which the reference decodes, must also be rejected by the typed decode.
  - SSZ: a 43-byte `StatelessValidationResult` round trip; the zero sentinel encoding; boolean `02` rejected; offset gap rejected; offset below the fixed size; an offset beyond the scope; decreasing offsets; `ByteList` over its limit; 257 headers (`ssz_list(256)`) rejected at decode (O1).
  - SSZ roots: the empty progressive list root `= H(0^32, 0^32)`; a 3-field progressive container root; `ByteList[2^16]` roots near chunk boundaries (31/32/33 bytes).
  - Addresses: CREATE for a fixed sender at nonces 0–3, the four EIP-1014 CREATE2 examples, and nonce `2^64−1` (which makes the RLP integer 8 bytes long).
- **Implemented header-helper cases:** all 256 tags; exact string/list boundaries
  7f/80/b7/b8/bf/c0/f7/f8/ff; one-to-eight digits; truncated length digits before
  leading zero; asymmetric high-to-low digits; 2^64−1 payload declaration with
  nine-byte extent addition; nonzero/end/huge cursors; missing bodies, prefixed
  singleton<80, small long forms and trailing bytes accepted by the helper.
  Whole-item decode rejection cases above are covered by the raw-decoder guards.
- **Implemented typed-wire controls (Q68).** `RlpDecodeOfGuards.lean` supplies
  168 complete-result controls:22 Nat wires,22 typed encoder/decoder results,
  ten valid-raw typed failures,21 supplied-error controls,90 raw-first controls
  (30 malformed wires with Nat/accepting/rejecting decoders), and three complete
  custom successes. Typed `.truncated` and arbitrary literal contexts remain
  unchanged; private arbitrary-error forwarding covers every supplied diagnostic.
  Pure callback controls establish result selection, with no effect-trace claim.
  `RlpDecodeOfCallerProofs.lean` supplies the eight private client groups in §3.
  The narrow actual-source wire profile is described in §3; it retains intended
  source-class/reflection/callback/host and first-handler premises.
- **Implemented ByteArray instance controls.** The 102 complete outcomes and eight
  private public-law client groups are catalogued in §3. They retain complete
  payloads/diagnostics, Q47 and raw-before-typed order; the bounded source profile
  supplies separate source-event and mathematical common-channel observations.
- **Implemented Bool instance controls.** The 52 whole-result controls and eight
  private public-law client groups are catalogued in §3. Bool's finite domain is
  discharged privately; both invalid shape families preserve the same diagnostic.
- **Implemented U256 instance controls.** The 64 complete outcomes and eight
  private facade groups in §3 preserve minimal words, exact errors, accepted-wire
  reencoding and the separate Nat/ByteArray domains.
- **Implemented narrow unsigned controls.** The 147 complete outcomes and 24 private
  facade groups in §3 cover U64/U32/U8, exact errors and cross-width/Nat/ByteArray
  distinctions; each finite encoder domain is discharged privately.
- **Implemented fixed-byte controls.** The 256 complete controls and eight private
  facade groups in §3 preserve exact width/bytes, raw-first diagnostics, conditional
  wire inversion and symbolic domain boundaries. The separate 148-entry source
  profile admits only the four original declared classes, retaining native identity.
- **Property / differential tests.**
  - Random `RlpItem` round trip, and canonicality under mutation fuzzing.
  - Random well-typed SSZ values round trip.
  - SSZ mutation fuzzing comparing the strict decoder with "remerkleable decode plus re-encode check". This is differential only; the fixtures and the EELS source decide.

- **Implemented raw SSZ consumers.** `SszModelCallerProofs.lean` has five private
  consumer groups: arbitrary nested type mask/field/limit recovery, ordinary versus
  progressive type separation, complete nested value payload recovery (including
  arbitrary bytes and child lists), nested list/container separation and pairwise
  separation of all six nominal diagnostic tags. They use public constructors and
  ordinary inductive elimination, without an added public law family.
  `SszModelGuards.lean` has four bounded complete aggregate controls: all nine
  descriptor shapes with zero/unsupported/large raw Nat parameters and a trailing
  false mask; an independent 257-entry mask with empty fields; a mixed value with
  a large natural, complete zero-containing bytes, duplicate and empty nested
  children; and a child-order mutation rejected by that fixed-context observer.
  These are local model checks, without source execution, codec/schema acceptance,
  root or error-producer coverage.

- **Implemented structural sizing controls (Q67).**
  `SszFixedSizeGuards.lean` checks exactly 96 handwritten complete `Option Nat`
  expectations with stable per-case IDs: 12 uint, one bool, eight byte-vector,
  five byte-list, ten list, eight progressive-list, one progressive-byte-list,
  twenty container, twenty-four progressive-container and seven nested controls.
  They cover all nine constructors,
  zero/standard/unsupported/huge byte widths (including 2^64 and 2^256+17),
  variable zero limits/zero-width or malformed children, fixed zero versus none,
  duplicate and nested fixed fields, and early/late/nested variable fields.
  Independent empty, trailing-false, mismatched and 255/256/257-entry masks never
  select fields; at most 257 actual fields are allocated. S labels mark static
  conditional source consequences, D direct-dependency mapping consequences,
  and R the chosen raw completion. S/D do not assert actual class admission or
  source execution; G12 additionally requires a source field named `more`.
  Summation alone does not observe field permutations, so these controls make
  no field-order mutation claim.
- **Implemented private sizing consumers.** `SszFixedSizeCallerProofs.lean`
  imports only the Codec facade and uses the public equation and ordinary core
  laws. Its six groups derive all nine arbitrary constructor cases; complete
  optional sums and ordinary/progressive append composition (including empty,
  fixed and variable results); mask independence of results; list child/limit
  independence and variable propagation; prospective slot tables; and the
  positive-divisor boundary. The tables retain complete slots [2,1,0,4,3,8]
  totaling 18 and [32,1,8,2] totaling 43, without encoding offsets or supplying
  an actual guest schema. Fixed-zero examples disprove general positivity and
  unique element-count recovery; division/remainder recovery has its separate
  explicit positive-width premise. All support and proofs are private.
  No source execution, native CLI, codec/root or guest coverage is supplied.

- **Implemented Hash32 controls.** The 90 complete handwritten controls and eight
  private caller groups in §3 preserve every byte and actual nominal value. The
  separate 47-entry original Bytes32 profile and normal/optimized 118 helper fixtures
  retain the source failure chain, raw precedence and explicit native/host boundary.
  No crypto execution, generic schema or whole guest gate is claimed.

- **Implemented Address controls.** The 90 complete handwritten controls and eight
  private public-law caller groups in §3 retain exact 20-byte nominal values,
  complete checked constructors/wires and raw-first errors. The focused 47-entry
  original Bytes20 profile and normal/optimized 118 admission groups preserve
  original native class identity, the 36→262→171 length chain and singleton wires.
  The source/host/first-handler and broader guest/resource premises remain open.

- **Implemented generic List controls.** The 104 complete handwritten outcomes,
  ten private caller groups and separately generated 28 source guards are owned
  by §3. Normal/-O admission preparation has 96 groups and zero RLP entries.
  These counts are separate; none is a whole EthCodec/guest gate.

- **Implemented structural well-formedness controls (Q70).**
  `SszWellFormedControls.lean` supplies exactly 64 private signed proposition
  controls W01–W64, each proving complete WF or its negation through the public
  constructor law. They cover all nine branches, six admitted widths and adjacent
  invalid/huge widths, zero/huge lengths and limits, bad descendants beneath
  limit 0, duplicate and nested fields, ordinary/progressive emptiness, sparse,
  trailing false and mismatched masks, and dense/sparse lengths 255/256/257.
  Huge Nat parameters remain scalars; actual lists/masks have at most 257 entries.
  `SszWellFormedCallerProofs.lean` supplies exactly 15 private facade clients
  C01–C15: all arbitrary constructor clauses, limit independence, child elimination,
  complete Q67 independence counterexamples, fixed-zero positivity countermodels,
  mask-sensitive WF with mask-independent sizing, and distinct raw zero-width
  list values. C15 asserts neither typing nor equal encodings.
  Ordinary proof elaboration supplies this Prop-only slice's deterministic tests.
  There is no source-class validator in this nameless contract to compare
  differentially and no native WF runner is introduced. These controls supply no
  source execution/class admission, codec/root, guest/resource or cost result;
  future adapters/operations retain their source and differential obligations.

- **Implemented payload typing controls (Q71).**
  `SszWellTypedControls.lean` supplies 130 complete private signed propositions:
  wtM01–wtM45 (all nine descriptor by five value tags, including 36 mismatches),
  wtR01–wtR24 (six supported widths, raw 0/3, exact endpoints and symbolic huge width),
  wtB01–wtB12 (complete bytes and zero/exact/over-limit sizes), wtL01–wtL16
  (actual element recursion, empty malformed children and ordinary counts),
  wtF01–wtF18 (exact positional arity, repeats and mask independence), wtN01–wtN10
  (nesting and both WF/WT separation directions), and wtZ01–wtZ05 (fixed-zero
  typing/sizing/count noninjectivity, without an encode/decode claim). Negations
  and mixed conjunctions are preserved in the complete Lean statements. Actual
  arrays have at most 3 bytes, lists 3 entries and masks 2 bits; huge parameters
  are scalars and wtR24 uses a symbolic arbitrary-width proof.
  `SszWellTypedCallerProofs.lean` supplies 16 private public-law client groups
  wtP01–wtP16: actual member ranges/tags, count transport, ordinary/progressive
  equivalence, indexed alignment, repeated fields, vector/list sizes, raw-width
  monotonicity, mask-independent typing with mask-sensitive WF, separate WF/WT
  counterexamples, fixed-zero count-size noninjectivity, and nested assembly/
  projection. wtP09/wtP16 have two targets; wtP13 includes two explicit witnesses.
  All controls and clients elaborate through the public Codec facade, using only
  public WT/WF/sizing/model/core APIs. Ordinary proofs are deterministic checks;
  no Boolean validator, native runner or source-class differential schedule is
  introduced. Actual adapters/operations retain their differential obligations.

- **Implemented raw pack controls (Q72).** `SszPackControls.lean` proves exactly 15
  private complete literal groups packP00/packP01/packP31/packP32/packP33/packP63/
  packP64/packP65/packZ01/packZ32/packZL02/packZT02/packSW64/packE32/packE33.
  They compare complete ordered chunks and all 32 bytes of each chunk; the largest
  input is 65 bytes and the largest output has three chunks. Empty/exact/tail,
  zero preservation, swapped full chunks and slots 31/32 are explicit. Expected
  bytes are independent handwritten literals, not the packing algorithm.
  `SszPackCallerProofs.lean` imports only the Codec facade. Its six private groups
  independently derive (C1) complete reference/byte equality and output-array
  observation injectivity; (C2) count/width/empty/exact multiples; (C3) complete
  input-prefix recovery and packed adapter reconstruction; (C4) exact suffix
  padding and arbitrary full/tail padded windows with checked construction;
  (C5) same-length recovery and complete unequal-length equal-output witnesses
  packP01/packZT02 and packZ01/packZ32; (C6) aligned concatenation plus complete
  packSW64/packE32/packE33/packP65
  byte observations. The implementation's six private property groups prove
  the same mathematical obligations. Aligned concatenation requires the FIRST
  input's byte length divisible by 32; equal chunk arrays do not bind length.
  The clients use only the approved public pack law and public Base/core facts,
  with local private List mathematics, never implementation-private workers or
  provider storage/equations. These ordinary kernel proofs are deterministic
  model controls, with no native pack runner or source execution credit.

- **Zero-hash controls (Q73).** `SszZeroHashControls.lean` supplies twelve private
  mathematical groups: zhP0 complete zero bytes; zhP1 first root/exact 64 zero bytes;
  zhP2 second root/complete ordered preimage; zhP3 arbitrary successor/size/FIPS bound;
  zhP4 whole prefix/order/size; zhP5 every eligible lookup; zhP6 present 64/absent 65
  with defined root 65; zhP7 symbolic 255/256; zhP8 generic linear builder at
  0/1/2/all lengths, order/length/lookup; zhP9 all-Nat recurrence refinement with
  64/65; zhP10 arbitrary-step uniqueness and SHA specialization; zhP11 width and
  arbitrary Bytes32 pair/FIPS composition. Provider-private builder correctness
  and all-Nat reference equality are proved beside the implementation.
  `SszZeroHashCallerProofs.lean` imports only Codec and supplies six independent
  private clients: C0 zero bytes/width; C1 symbolic first roots/full preimages;
  C2 whole prefix/arbitrary lookup/64–65 boundary; C3 every successor's complete
  FIPS digest trace through public byte contracts; C4 caller recurrence equality
  by induction; C5 arbitrary uncached successor plus symbolic 255/256. Clients
  consume the two public laws and public Base/Hash/core facts only. Deep SHA
  recurrences are never evaluated by decision procedures. These are ordinary
  mathematical proofs; source-only groups 0–3 remain separately scoped and UNRUN.

- **Merkleization controls (Q74).** `SszMerkleizeControls.lean` supplies private
  merkleP0 covering/minimality/powers/adjacent powers/same buckets on all Nat; merkleP1 full
  supported-domain executable/reference/fold equality; merkleP2 arbitrary empty roots
  and high-depth symbolic cases; merkleP3 depth-zero and complete generic singleton
  paths; merkleP4 complete ordered two/three/four roots; merkleP5 ordered padded frontiers,
  even layers/halving/one final root; merkleP6 same-capacity transport and proof
  independence; merkleP7 unequal-count equal-root padding witnesses and invalid-domain
  propositions; merkleP8 complete 64-byte/order/FIPS composition; merkleP9 actual byte-count
  through public pack law to rounded capacity, preserving stronger admission.
  `SszMerkleizeCallerProofs.lean` imports only Codec and independently derives
  private C0–C9: empty 0/1/arbitrary depth; singleton 0/1; two/limit 2;
  three/limits 3–4; four/limits 3–4; five/limit 3 impossibility and related domains;
  singleton versus appended-zero at limit 2; complete ordered SHA/FIPS;
  arbitrary same-depth replacement; and byte 31/32/33/admitted packing bridges.
  All support is private local List mathematics and public Base/Hash/Codec laws;
  no provider-private workers, storage or generated equations are consumed.
  Complete symbolic expressions avoid expensive deep SHA evaluation.

- **Progressive controls (Q75).** `SszMerkleizeProgressiveControls.lean` supplies
  private progressiveP0 entire all-Array/all-Nat executable/reference/public recurrence;
  progressiveP1 empty all depths and complete singleton symbolic paths; progressiveP2 complete ordered
  roots at 1/2/5/6/21/22 with capacities 1/4/16/64; progressiveP3 arbitrary ordered segmentation
  and exact reconstruction; progressiveP4 every local physical bound and strict suffix descent;
  progressiveP5 complete ordinary padded frontier/pair fold plus the public ordinary-helper
  bridge; progressiveP6 default 0 insertion, underlying two-argument function type, odd shifted
  depths and symbolic 64/65/255/256; progressiveP7 complete ordered 64-byte preimages and local
  public FIPS composition; progressiveP8 arbitrary-data/depth finite right-fold equivalence;
  progressiveP9 unequal-count equal-root padding witness without a collision premise.
  `SszMerkleizeProgressiveCallerProofs.lean` imports only Codec and independently
  derives the same observable C0–C9 families through the public recurrence and
  ordinary/Base/Hash laws with caller-owned private mathematics. No client consumes
  provider-private workers, generated equations or private Base/Hash storage.
  Activity/source/Rootable/host separation remains explicit prose/premises, with
  no invented activity theorem or source execution. Deep hashes remain symbolic.

- **Length mix-in controls (Q76).** `SszMixInLengthControls.lean` supplies
  private lengthP0–lengthP9: complete arbitrary-root/admitted-Nat executable→public
  equation→List-byte reference; exact 64-byte ordered preimage; count 0/1 complete
  SHA expressions; count 255/256 low-to-high transition; maximum 2^256−1 with
  all 32 bytes 255 and excluded endpoint; exact root/count transport and proof
  independence; full local FIPS digest trace with 512 < 2^64; direct actual List/Bytes
  count consumers with exactly local bounds and full bytes; intended-count U256
  observation under the bound; and every count ≥ 2^256 lacks the API premise.
  `SszMixInLengthCallerProofs.lean` imports only Codec and independently derives
  private C0–C9 through the public mix-in/Base/Hash laws. Each full byte/digest
  statement preserves arbitrary root bytes, including leading/trailing zeros,
  and all 32 count digits. Closed digit checks evaluate only finite 32-byte lists;
  SHA expressions remain symbolic. No generated automatic equation or private
  provider representation is consumed. lengthP9/C9 assert genuine range impossibility;
  no reflexivity claim stands in for activity, security or source correspondence.
  These ordinary mathematical proofs close this finite catalog, not source-runtime,
  actual count-support, enclosing root/binding or guest/resource/readiness gates.

- **Active-field controls (Q77).** `SszMixInActiveFieldsControls.lean` supplies
  private groups 0–9 in the P family: arbitrary symbolic root/mask/local proof
  and complete 32-digit reference; exact ordered 64-byte preimage; empty masks
  and masks containing only false, with all 32 mask bytes zero; proof independence;
  all true masks with 7/8/9 entries and byte transitions; actual 19/5 masks;
  sparse activity positions 0/7/8/255; all 256 bits true and sole bit 255,
  plus excluded width 257; trailing false and padding to 256 preserve the result,
  with the distinct []/[false] equal-preimage witness; general value < 2^length,
  width-derived value < 2^256, full positional contribution and the complete Base
  byte law; full 64-byte FIPS composition and all digest bytes.
  `SszMixInActiveFieldsCallerProofs.lean` imports only Codec and independently
  mirrors C0–C9 with its own recursive numeric model, proved equal to the full
  fold. C0 exercises every named root/active/h argument. All full SHA expressions
  remain symbolic; no selected-byte/checksum test or provider-private shortcut is
  used. This catalog supplies mathematical laws, leaving source classes/root
  interpretation, actual decoder/rootability, binding and resources separate.

- **Implemented local root-support controls (Q78).**
  `SszRootableControls.lean` supplies private rootableP0–rootableP9, with supporting targets;
  `SszRootableCallerProofs.lean` mirrors the full checklist independently through
  the Codec facade as rootableC0–rootableC9. Each has 24 complete proposition targets plus one
  private zip-membership helper. rootableP0/rootableC0 state the entire selected equation over
  arbitrary t/v; rootableC0 explicitly uses `(t := t) (v := v)` on predicate and law.
  The constructor equation covers all nine matching and 36 unmatched tag pairs.
  rootableP1/rootableC1 cover all six uint widths, 0/3/>32, exact scalar endpoints and Bool tags.
  rootableP2/rootableC2 cover exact sizes, zero vectors/limit 0 and arbitrary vectors without a
  count bound. rootableP3/rootableC3 retain declared element limits, actual child membership and
  basic classification; rootableP4/rootableC4 provide the complete progressive clauses and four
  symbolic count-ceiling exclusions without huge allocations. rootableP5/rootableC5 retain
  nonempty ordinary fields, exact positional arity and missing/surplus/wrong tags.
  rootableP6/rootableC6 admit leading/internal false slots and reject population/arity failures.
  rootableP7/rootableC7 admit sparse masks of widths 255/256 and exclude a mask of
  width 257 ending in true with one field, plus empty/allfalse/trailingfalse masks.
  Raw width 256 support asserts no source-class or
  `more`-name admission. rootableP8/rootableC8 prove both specified non-global-WF witnesses,
  exclude empty unsupported direct basics and reject actual scalar/tag/arity
  failures. rootableP9/rootableC9 derive meaningful all-t/v Rootable→WT through public laws,
  independently by value and descriptor induction. No public derived theorem is
  added. Concrete masks have at most 257 positions, payloads at most one byte and
  actual lists at most two children. Ordinary proof elaboration supplies this
  slice's deterministic controls; actual codecs/adapters/root consumers retain
  source/differential, root-result, security and resource obligations.

### Computational SSZ root controls (Q79)

The new `SszRootControls.lean` rootP0–rootP9 and independent
`SszRootCallerProofs.lean` rootC0–rootC9 use the Codec facade and public laws only.
The groups retain complete bytes/digests or complete symbolic SHA expressions;
no selected-byte/checksum proxy or unequal-hash assertion is used.

| Family | Complete controls |
|---|---|
| rootP0/rootC0 | the entire approved equation for arbitrary t/v/h; the client uses all three named arguments |
| rootP1/rootC1 | R00–R01: six scalar widths at 0/maximum, uint16=258, both Bool values, unsupported widths, overflow and wrong tags |
| rootP2/rootC2 | R02–R05: vectors 0/1/31/32/33/48/96/256; declared byte limits 0/1/32/33; count 1/2 despite identical packed chunks; whole windows and ordered trees |
| rootP3/rootC3 | R06–R07: five uint64 values, 33 Bool values, consecutive typed bytes, complete chunks, general packed sizes/order/capacity and supported-width unit conversion |
| rootP4/rootC4 | R08–R10: composite vectors 1/32, ordered/swapped/duplicate chunks, empty unused malformed composite schemas, excluded direct uint3 basics |
| rootP5/rootC5 | R11–R12: progressive empty/one byte, five uint64 values and complete boundary recipes 0/1/5/6/21/22, prefix left/suffix right |
| rootP6/rootC6 | R13: ordinary uint8/uint16/Bool field order, whole roots, exact arity and no count mix |
| rootP7/rootC7 | R14–R16: internal/leading false slots, all 3 bits true, exact slot length/order/ranks, widths 255/256, complete activity bytes, excluded 257/empty/trailing-false/population/arity cases |
| rootP8/rootC8 | R17 and general witnesses: inner byte counts 0/1, outer element count 2, actual-child induction, proof independence and uniqueness from the whole recursive law; count 255/256/uint256 boundaries without huge allocations |
| rootP9/rootC9 | R18: actual nameless Amsterdam field recipes and arities 4/19/5/4/5/3/3/4/2, timestamp uint64, fee uint256, fixed vectors 48/96/256 and complete ordinary/progressive result recipes; actual supported empty payload/request models |

The finite statements are deliberately closed over complete models and mathematical
roots. All authored declarations are private. Actual generated matcher/congruence/
well-founded support is classified by its real provenance, Types, attributes,
axioms, ownership and incoming edges under the unchanged declaration policy.
The original PR #239 record reports a separately authenticated finite source/Lean
comparison passing all 74 complete 32-byte root results: 72 genuine source cases,
including the actual ExecutionPayload and NewPayloadRequest cases, and two
separately labelled mathematical-only extensions. The 21 excluded C cases were
not executed and have no root result. This source comparison was not replayed
during the current review.
Mathematical-only extensions and unsupported cases are not source successes.
No full schema/decoder/guest/security/resource/readiness result is supplied by
these tests.

### Supplied forward SSZ controls and clients (Q80)

`SszEncodeControls.lean` and `scripts/SszEncodeNativeTests.lean` retain61 complete
literal observations:52 EELS dataclass/view paths, three genuine locked-dependency
sparse-mask paths and six mathematical-only cases. The five byte-local extras cover empty
containers, a malformed mask and empty unsupported unused schemas. The extra43-byte
fixed layout has independent ordered vector/Bool/uint digits; it is no actual
`StatelessValidationResult` schema adapter or guest theorem. Every supported scalar
width has zero, maximum and asymmetric digit cases. Byte/list/container cases retain
zeros, empty/fixed-zero children, repeated offsets, nested dynamic heads/tails and
raw sparse masks. Largest source output32 bytes; largest mathematical output43;
actual list lengths at most3. No huge value is allocated.

`SszEncodeCallerProofs.lean` uses only the Codec facade and public equations.
It constructs nested support before result reasoning, derives payload typing by
induction, extracts exact shape/child support, constructs ordered certificates and
proves complete nested bytes. Family/mask transport preserves all bytes. Negative
clients cover actual widths0/3, scalar overflow, wrong tag, vector length, list
limit and arity. Symbolic clients distinguish written starts2^32−1/2^32, unconstrained
final payloads and the exact second dynamic start. Private ordinary production
proofs supply exact actual lengths, supported fixed widths, reference equality,
certificate existence, proof independence and whole-law determination.

The independent literal inventory is `ssz_encode_literals.json`.
`ssz_encode_differential.py` strictly checks all61 native rows, rejecting missing,
duplicate, wrong-class, wrong-size and changed-byte observations; its parser/type
regressions run normally and with Python `-O`. With an explicit frozen EELS
checkout, it additionally executes55 actual source paths. It authenticates the
`reference.toml` commit/lock, clean tracked source, locked ethereum-types and
eth-remerkleable versions and installed RECORD/current sources; targeted modules
are compiled freshly from those bytes, bypassing cached bytecode. Raw byte views
may return their exact original authenticated `RawBytesView` object; other results
must be exact bytes. Complete child and enclosing wrapper bytes are checked.
Interpreter/startup, installed RECORD and host execution remain trust inputs.
Mathematical cases are never executed or reported as source successes.

Reproduce after the ordinary build; no EELS fetch occurs in CI:

```sh
lake build ssz-encode-native-tests --wfail
lake exe check-decls SszEncodeNativeTests
lake exe ssz-encode-native-tests > .lake/ssz-encode.txt
python3 -B STFSpec/Conformance/Codec/ssz_encode_differential.py --check-target .lake/ssz-encode.txt
python3 -B scripts/test_ssz_encode_output_parser.py
python3 -B -O scripts/test_ssz_encode_output_parser.py
<EELS>/.venv/bin/python -I -B STFSpec/Conformance/Codec/ssz_encode_differential.py --eels <EELS> --check-target .lake/ssz-encode.txt
<EELS>/.venv/bin/python -I -B -O STFSpec/Conformance/Codec/ssz_encode_differential.py --eels <EELS> --check-target .lake/ssz-encode.txt
```

These finite original-source/literal/compiled comparisons prove no general source
refinement, decoder/inverse, class/count/host admission, failure priority, guest,
resource, security, cost or readiness obligation.

## 5. Interface

The namespace is `STFSpec.Codec`. All items are public unless marked internal.
Q72 interprets raw `Ssz.pack` as an exported component-internal helper, with only
the complete public byte-observation law in §7; its support remains Lean-private.

```lean
-- RLP
inductive RlpItem where
  | bytes (b : ByteArray)
  | list  (items : List RlpItem)
inductive RlpError where                     -- diagnostic only: EELS has one DecodingError
  | empty | truncated | trailing | nonCanonical (why : String) | shape (ctx : String)
namespace Rlp
  def Encodable : RlpItem → Prop       -- every encoded item length has an at-most-eight-byte length prefix
  def encode       : RlpItem → ByteArray      -- two-pass: size, then write (§6)
  def encodeBytes  : ByteArray → ByteArray
  def encodeLengthPrefix (short long : UInt8) (len : Nat) : ByteArray   -- internal; total scope Q47
  def decode       : ByteArray → Except RlpError RlpItem                 -- total, cursor-based
  def decodeItemLength : ByteArray → (pos : Nat) → Except RlpError Nat  -- internal
  -- typed layer
  def ofNat : Nat → RlpItem                    -- .bytes (Uint.toBeBytes n)
  def toNat : RlpItem → Except RlpError Nat    -- rejects lists and leading zero
  def toNatBounded (widthBytes : Nat) : RlpItem → Except RlpError Nat
  def toBool : RlpItem → Except RlpError Bool
  def toBytes : RlpItem → Except RlpError ByteArray
  def toFixed (n : Nat) : RlpItem → Except RlpError (FixedBytes n)
  def toList : RlpItem → Except RlpError (List RlpItem)
  def toFields (n : Nat) : RlpItem → Except RlpError (Vector RlpItem n)  -- dataclass arity check
  def union2 (f : RlpItem → Except RlpError α) (g : RlpItem → Except RlpError α) :
      RlpItem → Except RlpError α              -- exactly-one-success semantics
end Rlp
class RlpEncode (α : Type) where toRlp : α → RlpItem
-- supplied (Q68):
class RlpDecode (α : Type) where
  ofRlp : RlpItem → Except RlpError α
-- supplied: RlpEncode Nat, with toRlp exactly Rlp.ofNat
-- supplied: RlpDecode Nat, with ofRlp exactly Rlp.toNat
-- supplied: RlpEncode ByteArray / RlpDecode ByteArray, exactly .bytes / Rlp.toBytes
-- supplied: RlpEncode Bool / RlpDecode Bool, exactly the two byte models / Rlp.toBool
-- supplied: RlpEncode Base.U256 / RlpDecode Base.U256, minimal ofNat / bounded32 map ofNat
-- supplied: RlpEncode/RlpDecode Base.U64, Base.U32, Base.U8, minimal / bounded8/4/1 map ofNat
-- supplied: RlpEncode/RlpDecode (Base.FixedBytes n), exact byte leaf / Rlp.toFixed n
-- supplied: RlpEncode/RlpDecode Base.Hash32, exact32-byte leaf / toFixed32.map ofBytes32
-- supplied: RlpEncode/RlpDecode Base.Address, exact20-byte leaf / checked Address.ofBytes?
-- supplied (Q69): generic ordered RlpEncode/RlpDecode (List α), see exact forms below
instance {α : Type} [RlpEncode α] : RlpEncode (List α) where
  toRlp xs := .list (xs.map RlpEncode.toRlp)
instance {α : Type} [RlpDecode α] : RlpDecode (List α) where
  ofRlp item := (Rlp.toList item).bind
    (fun children => children.mapM (RlpDecode.ofRlp (α := α)))
-- other schema/element instances remain pending
def Rlp.encodeOf [RlpEncode α] (a : α) : ByteArray
-- supplied (Q68); exact equation in §7:
def Rlp.decodeTo {α : Type} [RlpDecode α] (b : ByteArray) : Except RlpError α

-- Derived addresses
def computeContractAddress (sender : Address) (nonce : Nat) : Address
def computeCreate2ContractAddress (sender : Address) (salt : Bytes32) (initCode : ByteArray) : Address
-- Query-generic forms (D5); the pure forms above are these at m := Id (definitional)
def computeContractAddressQ [Monad m] [KeccakQuery m] : Address → Nat → m Address
def computeCreate2ContractAddressQ [Monad m] [KeccakQuery m] :
    Address → Bytes32 → ByteArray → m Address     -- two queries: keccak initCode, then the preimage

-- SSZ: raw vocabulary, sizing, WF, WT and raw pack are supplied; other items remain future.
inductive SszType where
  | uint (bytes : Nat) | bool
  | byteVector (n : Nat) | byteList (limit : Nat)
  | list (elem : SszType) (limit : Nat) | progressiveList (elem : SszType)
  | progressiveByteList
  | container (fields : List SszType)
  | progressiveContainer (activeFields : List Bool) (fields : List SszType)
inductive SszValue where
  | uint (n : Nat) | bool (b : Bool) | bytes (b : ByteArray)
  | list (xs : List SszValue) | container (xs : List SszValue)
def SszType.WellFormed : SszType → Prop      -- supplied nameless structural judgment (Q70)
def SszValue.WellTyped : SszType → SszValue → Prop   -- supplied payload-only judgment (Q71)
def SszType.fixedSize? : SszType → Option Nat
inductive SszError where | length | offset | limit | boolByte | trailing | shape
namespace Ssz
  -- supplied forward contract (Q80); complete ordinary laws in §7:
  def Serializable (t : SszType) (v : SszValue) : Prop
  def encode (t : SszType) (v : SszValue) (h : Serializable t v) : ByteArray
  def decode : SszType → ByteArray → Except SszError SszValue          -- strict canonical
  def hashTreeRoot (t : SszType) (v : SszValue) (h : Rootable t v) : Bytes32 -- supplied computational root (Q79); unchanged local support (Q78)
  def pack : ByteArray → Array Base.Bytes32    -- supplied exported component helper (Q72)
  def merkleize (chunks : Array Base.Bytes32) (limit : Nat)
      (h : chunks.size ≤ 2 ^ (if limit ≤ 1 then 0 else Nat.log2 (limit - 1) + 1)) :
      Base.Bytes32 -- supplied physical-capacity helper (Q74)
  def merkleizeProgressive (chunks : Array Base.Bytes32) (depth : Nat := 0) :
      Base.Bytes32 -- supplied contents-tree helper (Q75)
  def mixInLength (root : Base.Bytes32) (len : Nat)
      (h : len < 2^256) : Base.Bytes32 -- supplied local-bound helper (Q76)
  def mixInActiveFields (root : Base.Bytes32) (active : List Bool)
      (h : active.length ≤ 256) : Base.Bytes32 -- supplied local-width helper (Q77)
  def zeroHashes : Array Base.Bytes32  -- supplied ordered prefix, depths 0..64 (Q73)
  def Rootable (t : SszType) (v : SszValue) : Prop -- supplied Q78 local support; complete law in §7
  def zeroHash : Nat → Base.Bytes32  -- supplied all-Nat recurrence (Q73)
end Ssz
class SszSchema (α : Type) where
  type : SszType
  fieldNames : List String   -- source field names in order (F13); checked against REFERENCE-RECORDS
  valid : α → Prop           -- the owner's wire-domain predicate, not an execution-validity test
  toValue : α → SszValue
  ofValue? : SszValue → Option α
def SszSchema.decodeBytes [SszSchema α] : ByteArray → Except SszError α
def SszSchema.encodeBytes [SszSchema α] : α → ByteArray
def SszSchema.hashTreeRoot [SszSchema α] : α → Bytes32
```

## 6. Data structures

| Type | Representation | Model / abstraction | Invariant | Persistence | Complexity |
|---|---|---|---|---|---|
| `RlpItem` | nested inductive over `ByteArray` and `List` | itself (it is the public model) | none | immutable; decoded nodes may be shared by snapshots read-only | `encode` O(n) via a size pass and one pre-sized write. A naive recursive `++` is O(n·depth), which is also what Python's slicing and joining cost, so it should be avoided. `decode` O(n) with a cursor, instead of Python's re-slicing at each level (O(n·depth)) |
| encoded bytes | `ByteArray` | `List UInt8` | canonical (image of `encode`) | linear while being built, then frozen | — |
| `SszType` | nested inductive | itself (raw model) | none; supplied `WellFormed` is a separate judgment | immutable | raw construction; supplied forward metadata/writer traversal below, decoder costs remain future |
| `SszValue` | nested inductive | itself (raw model); future typed views via `SszSchema` | none; `WellTyped t v` is a supplied separate judgment | immutable | raw construction; supplied forward metadata/writer traversal below, decoder costs remain future |
| `zeroHashes` | `Array Bytes32` from a linear prefix traversal | `z₀ = 0^32`, `z_{i+1} = H(z_i, z_i)` | the recurrence | read-only constant (not a cache in the §7 sense) | O(1) lookup after construction; compiled lifetime/cost unmeasured |
| merkleization | packed `Array Bytes32` with interval offsets and shared zero prefix | private complete ordered List/tree and padded fold | actual count fits rounded physical capacity | immutable input; local traversal/cache | actual populated intervals and depth traversal; absent subtrees use one cached root, without missing-leaf materialization or copied child subtrees. Above 64, extend zeros in one linear recurrence. Depth arithmetic and zero availability/extension are separate from actual-chunk work; no universal all-depth O(chunks), compiled lifetime or C1–C4 claim |

**No derived instances on the nested inductives** (F17). `deriving BEq`, `Repr` or `DecidableEq` on `RlpItem`, `SszType` or `SszValue` generates `partial` constants (for example `instBEqT.beq`), which D21 bans and only the compiled declaration check catches. Write structural instances by hand, as mutual structural recursions (a compiled prototype of the interfaces showed the pattern works). Non-nested types such as `RlpError` and `SszError` may derive them.

The supplied raw SSZ slice declares no authored instances or deriving clauses,
including on `SszError`. Its constructors, recursors and ordinary generated inductive facts
supply raw construction and elimination only. No schema admission, normalization
or executable semantic operation is hidden in the representation.

**Structural sizing implementation (Q67).** The readable descriptor/private-list
mutual recursion uses ordinary finite structural descent. Variable list branches
return `none` without inspecting their children or limits. Each container visits
its actual fields in order and stops at the first variable field; masks are not
read. The private worker/fold equality proves the single ordinary §7 law. There
is no second optimized model, mapped field list, public measure, fuel, validator,
instance, certificate, error type or extra public law. Widths and their sums remain
Nat metadata, without proportional byte allocation. Mathematical termination
supplies no practical host-depth, compiled ownership, allocation or cost guarantee.

**Structural well-formedness implementation (Q70).** Private mutual Prop
workers descend through each descriptor's child/actual field list and each list's
head/tail. A thin public predicate and private list-induction bridge expose
exactly the §7 constructor law. List elements are checked even at limit 0; masks
are inspected independently of the ordered actual fields. No Boolean traversal,
fuel, public termination helper, broad simp attribute, validator or error channel
is added. This is a logical judgment with no new executable hot path; ordinary
structural totality and proof controls imply no compiled resource/cost result.

**Payload typing implementation (Q71).** Private mutually structural Prop workers
visit actual value members and paired field/value heads. An ordinary private
paired-list induction proves exactly length equality plus every zipped pair;
a private member induction exposes actual-child recursion. The thin public
predicate and one complete ordinary iff add no runtime traversal, validator,
DecidablePred/instance, fuel, new relation, broad simp attribute or error channel.
Public-law clients require no worker or automatic equation declaration. No compiled
stack, allocation, source execution or cost result follows from these proofs.

**Raw pack construction (Q72).** `Array.ofFn` constructs exactly k=(n+31)/32
chunks. Each index reads the original packed ingress through public
`Bytes.extractPadded (32*i) 32` and checked `FixedBytes.ofBytes?`. The proved
size 32 discharges dependent Option elimination; no panic or new error branch
is introduced. The private range/window reference and complete ordinary public
observation equation retain every byte. Private List induction proves exact
flattened suffix padding and recovery; there is no compiler substitution.
Execution neither converts the whole input to a List per chunk nor repeatedly
copies the remaining input or concatenates growing output prefixes. Sequence
work/output storage are O(n+1), excluding arbitrary-precision index arithmetic
bit costs. FixedBytes construction traverses a bounded 32-byte window. Compiled
ownership, allocation/lifetime measurements, practical host bounds, native-client
ratios and composed C1–C4 remain unproved; no benchmark is supplied by this slice.

**Implemented encoder costs.** The first structural pass caches each subtree's
size and packed writer closure once. The second pass copies each header/payload
into one output buffer pre-sized from the cached root size, in child order; it
never recomputes child sizes or constructs subtree output buffers. Temporary
writer closures and cached prefixes are local to the call. Under `Encodable`,
headers have bounded width, giving O(nodes + output bytes) traversal/copy work;
this is not an arbitrary-precision arithmetic bit-cost or host-depth guarantee.
`encodedSize` alone runs the planning pass, including its temporary cache.
Generated C confirms this call structure and packed copy_slice/output-capacity
construction. Compiled whole-byte comparisons against `encodeModel` cover shallow
sibling and deep single-child trees plus asymmetric mixed order. Local construction
timings retain outputs until after timing; output cleanup and whole-process RSS do
not supply total allocated volume, peak-live allocation accounting, a native-client
comparison or C1–C4/guest acceptance. Those gates remain open (CONTRIBUTING §3).

**SSZ forward writer structure (Q80).** A private bottom-up cache computes
structural fixed widths once per raw descriptor node, including metadata of
unused schemas without checking WF. The actual-value planning pass reads cached
Option Nat widths in constant time, caches child sizes/writers and builds separate
ordered head/tail writer compositions. The final pass starts one packed
`ByteArray.emptyWithCapacity` at the computed size; every payload writer receives
and returns the same output accumulator, and no subtree wire buffers or recursive
payload concatenations are constructed. Ordinary cached/uncached writer equality
and readable-list-reference equality justify these operations. Static traversals
are linear in raw schema nodes, actual value occurrences/field entries and emitted
bytes, excluding arbitrary-precision arithmetic; a descriptor subtree reused by a
list is cached once. This removes repeated nested fixed-schema classification.
No compiled allocation/sharing/lifetime or throughput measurement is claimed;
practical host depth, native-client ratios and C1–C4 remain open. No local
performance exception is selected.

**Implemented raw decoder costs.** Each recursive window references the original
packed buffer. Byte leaves copy their exact validated scope once, including zero
bytes preserved as payload; lists allocate output nodes/ordered child metadata,
never nested payload copies or recursive byte concatenations. Child headers may
be read once for declared extent and again for exact child decoding, each with at
most eight digits. The joined loop accumulates a reversed child list and reverses
once per list. Analytical traversal/copy work is O(input bytes + output nodes),
with O(output bytes + output/temporary nodes) space, excluding arbitrary-precision
arithmetic bit costs and host stack/reclamation behavior. Bounded compiled probes
check complete trees and re-encoded bytes at depths32/128/256/512 and widths256/512;
decode/discard timings include output cleanup within each iteration. Generated C
supports the original-buffer/leaf-copy call structure. Static allocation-site
counts and process RSS do not measure dynamic allocator volume/peak-live space.
No all-host depth theorem, native-client ratio, guest cost gate or C1–C4 completion
is established. Q20/O12 remain with their owners.

**Implemented header costs.** The cursor checks availability before packed reads,
reads one tag and traverses at most eight original length digits by structural
recursion. It builds no suffix copy, list or declared-payload buffer. Header work
is bounded independently of declared payload length, including conceptual large
out-of-range offsets. The readable suffix/window model is proof-facing only.
Generated-C shape and finite native whole-result probes support that structure;
no whole-decoder O(n), allocator-volume, host-depth or guest-cost claim follows.

**Implemented leaf costs.** Raw shape observations (`toBytes`, `toList`) share the
input without traversing children. Boolean checks compare only the empty and
singleton byte shapes. Integer adapters inspect shape/first byte/size before the
Base Horner fold; leading-zero or over-width bounded inputs never construct the
large natural. Accepted numeric work traverses the bytes once, with growing
arbitrary-precision arithmetic costs; this is not a linear bit-cost claim.
`toFixed` checks size before the Base fixed-byte constructor and preserves its
public byte observation. `toFields` counts the list, then builds its array only
when arity matches; it does not deserialize or recurse into children. `union2`
performs both callbacks, costing their sum. Generated C inspection confirms the
integer guard order, both union applications and arity-before-array construction.
These are static code-shape observations, without allocator profiling, native
throughput/guest measurements or satisfaction of whole-codec cost gates. Schemas,
wire workloads and consumer lifetime/cleanup checks remain required (REVIEW C1;
CONTRIBUTING §3).

**Generic List implementation (Q69).** The readable ordered `map` model and public
core `mapM` traversal add no stored representation or private traversal worker.
Ordinary kernel proofs use public mapM_nil/mapM_cons; the core implementation's
structural totality and reversed accumulator do not prove compiler callback
traces, practical host stack, allocation bounds or C1–C4 acceptance.

## 7. Contract and laws

**RLP.**
- [T] `decode` is total: well-founded recursion on the remaining byte count, where each item consumes at least one byte. It allocates nothing proportional to a *declared* length before checking that length against the input.
- [C] Round trip: `Encodable x → decode (encode x) = .ok x`.
- [C] **Canonicality:** `decode b = .ok x → Encodable x ∧ encode x = b`. Together with the round trip, `decode b = .ok x ↔ Encodable x ∧ encode x = b`. This is the Lean form of D1r.
- [C] **Injectivity and prefix-freeness:** `Encodable x ∧ Encodable y ∧ encode x ++ r = encode y ++ s → x = y ∧ r = s`. These feed [S]: witness and header binding under Keccak collision resistance.
- [C] Integer canonicality: `toNat (.bytes b) = .ok n ↔ b = (Uint.toBeBytes n).toByteArray`; `toNatBounded w` additionally requires `b.size ≤ w`.
- [R] Typed round trips require the instance-specific model inverse premises as well
  as `Encodable (toRlp a)` to conclude `decodeTo (encodeOf a) = .ok a`. For List,
  these include membership-local `hElements` (Q69); the wire premise applies to
  the complete assembled model. `EthBlock` transaction/header/receipt codecs and
  `EthStateCommit` account leaves must supply their own instance premises.
- [R] `union2 f g x = .ok a` implies that exactly one of `f x`, `g x` succeeds.

**Supplied generic List laws (Q69).** Exactly these two ordinary public laws are
discharged; the namespace is `STFSpec.Codec`:

```lean
theorem Rlp.ofRlp_toRlp_list {α : Type} [RlpEncode α] [RlpDecode α]
    (xs : List α)
    (hElements : ∀ a ∈ xs,
      RlpDecode.ofRlp (RlpEncode.toRlp a) =
        (Except.ok a : Except RlpError α)) :
    RlpDecode.ofRlp (α := List α) (RlpEncode.toRlp xs) =
      (Except.ok xs : Except RlpError (List α))

theorem Rlp.decodeTo_encodeOf_list {α : Type} [RlpEncode α] [RlpDecode α]
    (xs : List α)
    (hElements : ∀ a ∈ xs,
      RlpDecode.ofRlp (RlpEncode.toRlp a) =
        (Except.ok a : Except RlpError α))
    (h : Rlp.Encodable (.list (xs.map RlpEncode.toRlp))) :
    Rlp.decodeTo (α := List α) (Rlp.encodeOf xs) =
      (Except.ok xs : Except RlpError (List α))
```

Model induction restricts membership-local agreement to the head and tail and
uses public mapM_nil/mapM_cons with ordinary Except equations. No Encodable
premise is needed for that model law, including recursive public-law lifting of
nested lists. The wire law composes public raw decode_encode at the complete
assembled-list h with that public model law. Public encodable_list_iff exposes
both every child and joined encoded payload length<2^64: individual child bounds
cannot replace h. Independent classes imply no nonempty inverse; neither law
implies generic successful-decoding-to-reencoding without additional element
model-recovery premises. The explicitly approved pair qualifies the generic
private/no-added-family wording below, without adding an open-ended helper family.
Empty lists have vacuous member agreement even for a failing decoder. First-error
equations preserve complete pure values, with no callback execution or cost claim.

**Supplied typed wrapper contract (Q68).** Inside
`namespace STFSpec.Codec`, the normative equation is literally:

```lean
def Rlp.decodeTo {α : Type} [RlpDecode α]
    (b : ByteArray) : Except RlpError α :=
  match Rlp.decode b with
  | .error e => .error e
  | .ok x => RlpDecode.ofRlp (α := α) x
```

Raw failure wins unchanged, without using a typed result. On raw success the
entire typed `Except` is returned unchanged. For correspondence, observe a result
with the existing fully typed expression
`(r : Except RlpError α).mapError (fun (_ : RlpError) => ())`.
This mathematical observation has type `Except Unit α`: every diagnostic becomes
`.error ()` and complete successful values remain unchanged. The source relation
maps outer `DecodingError` to that rejection channel and compares successes
through the local intended-source adapter. It claims no exception identity or
message/cause equality and handles no raw non-DecodingError host failure. There
is no exported projection function/type, new error, class proof field or public
helper-law family. Changing a provider's promised diagnostic changes the exact
wrapper result; guest handlers must use the common rejection classification with
reference phase/first-handler ordering intact.

The supplied Nat instance uses exactly `Rlp.toNat`. Its one ordinary
per-instance theorem, inside the same namespace, has exactly this type:

```lean
theorem Rlp.decodeTo_encodeOf_nat (n : Nat)
    (h : Rlp.Encodable (Rlp.ofNat n)) :
    Rlp.decodeTo (α := Nat) (Rlp.encodeOf n) =
      (Except.ok n : Except RlpError Nat)
```

This theorem is proved by composing public `decode_encode`
and `toNat_ofNat`, unfolding only the new wrapper/class adapters. Keep `h` for
arbitrary Nat (Q47). Generic private roundtrip callers additionally need their
own `ofRlp (toRlp a) = .ok a` premise: independent classes supply no inverse.
Private Nat success-to-reencoding clients can compose `toNat_eq_ok_iff`,
`decode_success_encodable` and `encode_eq_of_decode_eq_ok`; bounded callers
establish `Encodable` locally through public Base/leaf laws. Unfold neither raw
parser workers nor Base representations, and introduce no additional public
helper-law family. These private clients are supplied through the Codec facade.

The supplied ByteArray instances are exactly `.bytes` and `toBytes`. Their one
ordinary public per-instance law is discharged:

```lean
theorem Rlp.decodeTo_encodeOf_byteArray (b : ByteArray)
    (h : Rlp.Encodable (.bytes b)) :
    Rlp.decodeTo (α := ByteArray) (Rlp.encodeOf b) =
      (Except.ok b : Except RlpError ByteArray)
```

It composes public `decode_encode` and `toBytes_eq_ok_iff`, reducing only the
new adapters/wrappers. The explicit h is retained for arbitrary mathematical
ByteArray (Q47). Successful typed decoding recovers the exact byte leaf, its
Encodable domain and every original wire byte through public provider laws;
those recovery clients remain private. Q68 preserves all raw and typed results.

The supplied Bool encoder is exactly
`if b then .bytes ⟨#[1]⟩ else .bytes ByteArray.empty`, and its decoder is
exactly `Rlp.toBool`. Its single ordinary public law is discharged:

```lean
theorem Rlp.decodeTo_encodeOf_bool (b : Bool) :
    Rlp.decodeTo (α := Bool) (Rlp.encodeOf b) =
      (Except.ok b : Except RlpError Bool)
```

A private finite-domain argument uses `encodable_bytes_iff` for the zero/one-byte
models. The inverse composes public `decode_encode` and `toBool_eq_ok_iff`,
reducing only the new adapters and wrappers. No public Bool helper or domain
predicate is added. Nat and arbitrary ByteArray keep their explicit hypotheses;
generic independent classes still supply no arbitrary inverse. Accepted Bool
wire reencoding is proved by private public-law callers, with exact diagnostics
preserved before external common-channel observation.

The supplied U256 adapters are exactly `Rlp.ofNat x.toNat` and
`(Rlp.toNatBounded 32 item).map Base.U256.ofNat`. Their one ordinary public
per-instance law is discharged:

```lean
theorem Rlp.decodeTo_encodeOf_u256 (x : Base.U256) :
    Rlp.decodeTo (α := Base.U256) (Rlp.encodeOf x) =
      (Except.ok x : Except RlpError Base.U256)
```

A private finite-domain discharge composes `U256.toNat_lt`,
`Uint.size_toBeBytes_le_iff`, `Bytes.size_toByteArray` and `encodable_bytes_iff`:
minimal payload≤32<2^64. Public `decode_encode`,
`toNatBounded_eq_ok_item_iff` and `U256.ofNat_toNat` prove the inverse without
representation unfolding. The bounded success range also justifies exact
`ofNat` recovery, so an overflow never becomes a wrapped success. Nat and
arbitrary ByteArray retain their explicit encoder-domain hypotheses. Private
callers recover the exact raw model and every accepted source wire byte.

The narrow unsigned adapters use the same minimal model with widths 8/4/1 for
U64/U32/U8. Their ordinary public laws `Rlp.decodeTo_encodeOf_u64`,
`Rlp.decodeTo_encodeOf_u32` and `Rlp.decodeTo_encodeOf_u8` each take only the
corresponding nominal value x and conclude
`Rlp.decodeTo (Rlp.encodeOf x) = (Except.ok x : Except RlpError C)`.
The private domain proofs compose the respective `toNat_lt`,
`Uint.size_toBeBytes_le_iff`, `Bytes.size_toByteArray` and `encodable_bytes_iff`:
minimal payload≤8/4/1<2^64. Public `decode_encode`, bounded acceptance and
`ofNat_toNat` give the unconditional inverses; `toNat_ofNat_of_lt` gives exact
successful construction. The private clients recover every accepted raw item
and wire, preserve the complete bounded-map/error result and reject lists via
public bounded acceptance. Exact list diagnostics are tested, without unfolding
the private integer worker or introducing a new provider law. Nat and arbitrary
ByteArray retain their explicit encoder-domain premises.

The supplied nominal Hash32 adapters preserve the exact 32-byte leaf, decoding
through public toFixed 32 and ofBytes32. Their ordinary unconditional inverse is:

```lean
theorem Rlp.decodeTo_encodeOf_hash32 (x : Base.Hash32) :
    Rlp.decodeTo (α := Base.Hash32) (Rlp.encodeOf x) =
      (Except.ok x : Except RlpError Base.Hash32)
```

The payload domain is discharged privately from encodable_bytes_iff,
Bytes.size_toByteArray and Hash32.size_toBytes at 32. Public toFixed complete
acceptance, both Hash32/Bytes32 inverse and byte laws and raw decode_encode
supply exact nominal reconstruction. No separate public success/domain family
or changed generic-domain statement is introduced.

The supplied nominal Address encoder preserves the exact 20-byte leaf. Its decoder
composes public `Rlp.toBytes`, ordinary `Except.bind` and checked
`Address.ofBytes? (Bytes.ofByteArray b)` through `Option.elim`, retaining both
shape and fixed-length diagnostics. Its ordinary unconditional inverse is:

```lean
theorem Rlp.decodeTo_encodeOf_address (x : Base.Address) :
    Rlp.decodeTo (α := Base.Address) (Rlp.encodeOf x) =
      (Except.ok x : Except RlpError Base.Address)
```

The private finite-domain proof composes encodable_bytes_iff,
Bytes.size_toByteArray and Address.size_toBytes at 20. Public raw decode_encode,
both packed inverses and Address.ofBytes?_toBytes reconstruct the complete nominal
value. Complete constructor success/none iff and byte injectivity suffice for
private acceptance and reencoding clients. No private Address conversions,
numeric decoder detour or additional public helper/domain law is introduced.

The supplied generic fixed-byte adapters are the complete exact-width byte leaf
and `Rlp.toFixed n`. Their single ordinary public law is discharged:

```lean
theorem Rlp.decodeTo_encodeOf_fixedBytes (x : Base.FixedBytes n)
    (h : Rlp.Encodable (.bytes x.toBytes.toByteArray)) :
    Rlp.decodeTo (α := Base.FixedBytes n) (Rlp.encodeOf x) =
      (Except.ok x : Except RlpError (Base.FixedBytes n))
```

The proof composes public `decode_encode` and `toFixed_eq_ok_item_iff`.
The raw item inverse holds for arbitrary n without h. Privately,
`encodable_bytes_iff`, `Bytes.size_toByteArray` and `FixedBytes.size_toBytes`
identify h with n<2^64; no all-n wire premise or source class is inferred.
Private success clients recover the exact raw leaf, all bytes and original wire;
errors remain complete under Q68. Exact source-class/constructor/host and
first-handler premises remain separate from this ordinary Lean theorem.

**Discharged encoder laws.** `toList_encode` relates the packed encoder to
`encodeModel` for every item, including Q47 completion; `size_encode` and
`encodedSize_eq_model_length` equate size pass, output and reference widths.
`toList_encodeLengthPrefix` and `size_encodeLengthPrefix` expose exact headers;
`length_digits_value/width/head/order` give complete value, minimal width,
nonzero head and high-to-low digit order. Singleton/short/long byte and list laws
expose payload preservation and prefix cases. `encodePayloadModel_eq_flatMap`,
`encodePayloadModel_append` and `length_encodePayloadModel` establish ordered
child concatenation and sum of encoded widths, with empty and nested children
preserved. `Encodable` is characterized recursively by `encodable_bytes_iff` and
`encodable_list_iff`; standard tags do not wrap on this domain. These discharge
encoding model obligations; raw wire contracts are listed below.

**Supplied typed encoding composition.** `encodeOf` is the readable direct
composition with the one-field adapter, and Nat supplies exactly `ofNat`.
Private clients reduce these new references and compose the existing complete
byte-model and width laws. For Nat, `Encodable (ofNat n)` gives the raw-wire image
`decode (encodeOf n) = .ok (ofNat n)`; a private n<2^256 caller discharges that
premise using public Base/leaf laws. No all-Nat `Encodable` assertion or new public
law family is supplied. The per-instance Nat typed roundtrip above is supplied
with `RlpDecode` and `decodeTo`; Q68 fixes their diagnostic equation.

**Discharged raw decoder laws.** `decode_eq_model` preserves the whole result
including diagnostics and every nested child, with shared parser semantics as
specified in §3. `decode_window_model` observes exact clipped public byte windows.
`decode_empty`, `decode_single`/`decodeModel_single`,
`decodeModel_short_bytes`, `decodeModel_short_list_truncated/trailing` and
`decode_success_nonempty` establish their stated ordered cases/progress.
The raw parser terminates by consuming nonempty prefixes within bounded parent
windows. `decodeModel_encodeModel` and `decode_encode` prove a round trip for every
`Encodable` item. `decodeModel_success`, `decode_success_encodable` and
`encode_eq_of_decode_eq_ok` prove unconditional successful-domain membership and
exact input reencoding. `decode_eq_ok_iff` and `exists_decode_eq_ok_iff` characterize
the accepted image. `eq_of_encode_eq` and its iff companion `encode_inj` give
injectivity on `Encodable`; `encode_prefix_free` binds items and arbitrary byte
tails. `itemLengthModel_encodeModel` recovers the encoded first-item extent
independently of arbitrary trailing bytes. `RlpCanonicalCallerProofs.lean`
composes these public laws without provider representation unfolding. Typed/schema,
host-depth and security obligations remain separate; Q47 supplies no inverse or
binding outside the standard domain.

**Discharged header laws.** `decodeItemLength_eq_model` relates every packed cursor
to the readable suffix model. `decodeItemLength_single`, `short_bytes`, `short_list`
and `long` expose exact cases; the long equation gives header truncation before
leading-zero rejection and the public `Uint.ofBeBytes` value of the digit window.
`length_digits_bound` gives one-to-eight digits; `decodeItemLength_success_bound`
gives payload<2^64 and an unbounded tag+digits+payload extent, while `pos` and `lt`
give positive advancement and extent<2^64+9. `empty_iff` characterizes end/out-of-range
cursors. `window`, `suffix`, `header_congr` and `itemLengthModel_take_nine` preserve
window/offset semantics and ignore bytes outside the bounded header. These laws
supply no successful payload decode, canonicality or encode/decode inverse.

**Discharged model leaf laws.** The implementations export full integer
minimality biconditionals (`toNat_canonical_iff`, `toNat_eq_ok_iff`), bounded
canonicality/range (`toNatBounded_canonical_iff`, `toNatBounded_eq_ok_item_iff`),
zero-width acceptance (`toNatBounded_zero_iff`) and encoder round trip
(`toNat_ofNat`). Boolean, raw bytes, fixed length/byte observation and raw list
accept sets are `toBool_eq_ok_iff`, `toBytes_eq_ok_iff`, `toFixed_eq_ok_iff` and
`toList_eq_ok_iff`; `toFixed_eq_ok_item_iff` additionally pins model shape. `toFields_eq_ok_iff` preserves exactly the vector's ordered
fields; `toFields_wrong_arity` rejects before child typing. `union2_eq_ok_iff`
characterizes a sole success plus the other alternative's failure. These apply to
all model inputs, without wire-instance or child-schema claims. Integer
canonicality uses public Base fold/range/encoded-width and fixed-byte injectivity,
so it also proves the converse byte minimality rather than just value round trip.

**SSZ.**
Raw construction/elimination and Q67 structural sizing are supplied. Exactly one
ordinary public sizing law on every raw `SszType` is **discharged**, with the §5
value signature. Its type is recorded informally below; the checked proof belongs
to `STFSpec/Codec/SszFixedSize.lean`:

```lean
theorem SszType.fixedSize?_eq (t : SszType) :
  t.fixedSize? =
    match t with
    | .uint w => some w
    | .bool => some 1
    | .byteVector n => some n
    | .byteList _ => none
    | .list _ _ => none
    | .progressiveList _ => none
    | .progressiveByteList => none
    | .container fields | .progressiveContainer _ fields =>
        fields.foldr
          (fun field acc =>
            match field.fixedSize?, acc with
            | some n, some m => some (n + m)
            | _, _ => none)
          (some 0)
```

`some n` is raw structural fixed-class byte width, including zero; it asserts no
schema well-formedness, value typing, source-class admission, positive divisor,
codec success or rootability. `none` is structural variability, not an invalid
schema error. Thus unsupported uint widths return their raw width, byte vectors
may be fixed zero, and all list/byte-list branches are variable regardless of
limit or child validity. Both container branches take the optional sum of every
actual field, with empty result `some 0`: any variable field makes the result
`none`. Progressive sizing ignores the mask and neither filters, zips, pads nor
normalizes the field list. Arbitrary Nat widths add without a host-sized cap.

Q70 additionally supplies the §5 Prop judgment and exactly this ordinary
constructor law, **discharged** by `STFSpec/Codec/SszWellFormed.lean`:

```lean
theorem SszType.wellFormed_iff (t : SszType) :
    t.WellFormed ↔
      match t with
      | .uint w => w ∈ [1, 2, 4, 8, 16, 32]
      | .bool => True
      | .byteVector _ => True
      | .byteList _ => True
      | .list elem _ => elem.WellFormed
      | .progressiveList elem => elem.WellFormed
      | .progressiveByteList => True
      | .container fields =>
          fields ≠ [] ∧ ∀ field ∈ fields, field.WellFormed
      | .progressiveContainer mask fields =>
          mask.getLast? = some true ∧
          mask.length ≤ 256 ∧
          (mask.filter id).length = fields.length ∧
          ∀ field ∈ fields, field.WellFormed

```

Its nameless structural domain is separate from actual names/class construction,
value typing and operation domains. Every child is checked, including beneath
zero limits; fixed-zero vectors/fields and sparse length 256 masks are admitted.
The mask's last bit expresses nonemptiness and final activity, while true
population counts actual fields. There is no `WellTyped` implication, runtime
validator, diagnostic priority or codec/root success claim. In particular WF
implies neither positive `fixedSize?` nor unique zero-width-list count recovery.
Q67 stays total and independent, including unsupported widths and malformed
containers/masks. Future division/inverse consumers prove positivity locally.

Q71 supplies exactly the §5 payload predicate and this ordinary complete law,
**discharged** by `STFSpec/Codec/SszWellTyped.lean`:

```lean
theorem SszValue.wellTyped_iff (t : SszType) (v : SszValue) :
    SszValue.WellTyped t v ↔
      match t, v with
      | .uint width, .uint n => n < 2 ^ (8 * width)
      | .bool, .bool _ => True
      | .byteVector size, .bytes b => b.size = size
      | .byteList limit, .bytes b => b.size ≤ limit
      | .list elem limit, .list xs =>
          xs.length ≤ limit ∧ ∀ x ∈ xs, SszValue.WellTyped elem x
      | .progressiveList elem, .list xs =>
          ∀ x ∈ xs, SszValue.WellTyped elem x
      | .progressiveByteList, .bytes _ => True
      | .container fields, .container xs =>
          fields.length = xs.length ∧
            ∀ pair ∈ fields.zip xs, SszValue.WellTyped pair.1 pair.2
      | .progressiveContainer _ fields, .container xs =>
          fields.length = xs.length ∧
            ∀ pair ∈ fields.zip xs, SszValue.WellTyped pair.1 pair.2
      | _, _ => False
```

WT deliberately does not imply WF: raw uint 3 at value 0 and an empty list of
uint 3 are typed with malformed schemas. Conversely WF alone does not type
arbitrary wrong-tag/out-of-range payloads. Source names/classes/coercions, uint256 actual
counts, backing/cache, offsets/scope, positive-width inverse recovery and
codec/root/host premises remain separate. The literal length equality prevents
zip truncation; mask validity never changes the actual field payload judgment.

Q78 supplies the §5 local support predicate and exactly this complete ordinary
law, **discharged** by `STFSpec/Codec/SszRootable.lean`:

```lean
theorem Ssz.rootable_iff (t : SszType) (v : SszValue) :
    Ssz.Rootable t v ↔
      match t, v with
      | .uint w, .uint n =>
          w ∈ [1, 2, 4, 8, 16, 32] ∧ n < 2 ^ (8 * w)
      | .bool, .bool _ => True
      | .byteVector n, .bytes b => b.size = n
      | .byteList limit, .bytes b =>
          b.size ≤ limit ∧ b.size < 2 ^ 256
      | .list elem limit, .list xs =>
          xs.length ≤ limit ∧
          xs.length < 2 ^ 256 ∧
          (∀ x ∈ xs, Ssz.Rootable elem x) ∧
          match elem with
          | .uint w => w ∈ [1, 2, 4, 8, 16, 32]
          | .bool => True
          | .byteVector _ | .byteList _ | .list _ _ | .progressiveList _ |
            .progressiveByteList | .container _ | .progressiveContainer _ _ => True
      | .progressiveList elem, .list xs =>
          xs.length < 2 ^ 256 ∧
          (∀ x ∈ xs, Ssz.Rootable elem x) ∧
          match elem with
          | .uint w => w ∈ [1, 2, 4, 8, 16, 32]
          | .bool => True
          | .byteVector _ | .byteList _ | .list _ _ | .progressiveList _ |
            .progressiveByteList | .container _ | .progressiveContainer _ _ => True
      | .progressiveByteList, .bytes b => b.size < 2 ^ 256
      | .container fields, .container xs =>
          fields ≠ [] ∧
          fields.length = xs.length ∧
          ∀ pair ∈ fields.zip xs, Ssz.Rootable pair.1 pair.2
      | .progressiveContainer mask fields, .container xs =>
          mask.getLast? = some true ∧
          mask.length ≤ 256 ∧
          (mask.filter id).length = fields.length ∧
          fields.length = xs.length ∧
          ∀ pair ∈ fields.zip xs, Ssz.Rootable pair.1 pair.2
      | _, _ => False
```

The equation imposes declared sizes/limits and actual recursive counts, without
global WF on unused composite schemas. Rootable→WT is derived privately through
public laws; Rootable→WF is false by the §4 witnesses. Fixed vectors/containers
have no new count-mix-in bound. Lists of basic Bool use byte width 1; every other
non-uint descriptor, including fixed vectors, is composite. Source class mapping,
unused-schema construction, names and capacity-256 `more`, actual decoder/
reconstruction support and security/resource gates stay separate; Q79 supplies
raw root results.
The predicate supplies no hash, root output or source failure-order theorem.

Q72 supplies exactly this ordinary full-byte raw packing law,
**discharged** by `STFSpec/Codec/SszPack.lean`:

```lean
theorem Ssz.pack_toBytes (b : ByteArray) :
    (Ssz.pack b).toList.map (fun chunk => chunk.toBytes.toList) =
      (List.range ((b.size + 31) / 32)).map (fun i =>
        (b.toList.drop (32 * i)).take 32 ++
          List.replicate (32 - min 32 (b.size - 32 * i)) 0)
```

This law has no schema, WT/WF, source-class or host-allocation premise; its domain
is the finite mathematical input. Private consequences are the six groups in §4.
They retain the equal-length premise for recovery from equal chunk arrays and
the first-input 32-byte alignment premise for concatenation. No length/root binding,
canonicality, typed packing, Merkleization, mix-in or codec-domain law follows.

Q73 supplies exactly these two ordinary public laws, **discharged** by
`STFSpec/Codec/SszZeroHash.lean`:

```lean
theorem Ssz.zeroHash_eq (depth : Nat) :
    zeroHash depth = match depth with
      | 0 => (Base.FixedBytes.ofNat 0 : Base.Bytes32)
      | d + 1 =>
          let z := zeroHash d
          STFSpec.Hash.sha256 ((z.toBytes ++ z.toBytes).toByteArray)

theorem Ssz.zeroHashes_toList :
    zeroHashes.toList = (List.range 65).map zeroHash
```

Derived branch/width/lookup/uniqueness laws and construction support stay private.
Neither public law requires WF, WT, Rootable, a schema or a source-table premise.
Actual source correspondence uses §3's premises; root 256 is mathematical only.
The finite prefix imposes no depth limit on any tree or merkleization consumer.

Q74 supplies exactly one ordinary public law, **discharged** by
`STFSpec/Codec/SszMerkleize.lean`:

```lean
theorem Ssz.merkleize_eq (chunks : Array Base.Bytes32) (limit : Nat)
    (h : chunks.size ≤ 2 ^ (if limit ≤ 1 then 0 else Nat.log2 (limit - 1) + 1)) :
    merkleize chunks limit h =
      let depth := if limit ≤ 1 then 0 else Nat.log2 (limit - 1) + 1
      let zero := (Base.FixedBytes.ofNat 0 : Base.Bytes32)
      let pair := fun (left right : Base.Bytes32) =>
        STFSpec.Hash.sha256 ((left.toBytes ++ right.toBytes).toByteArray)
      ((List.range depth).foldl
        (fun layer _ => (List.range (layer.length / 2)).map (fun i =>
          pair (layer.getD (2 * i) zero) (layer.getD (2 * i + 1) zero)))
        (chunks.toList ++ List.replicate (2 ^ depth - chunks.size) zero)).headD zero
```

Every helper/reference/derived/control/client declaration stays private. The
proof argument is independent by proof irrelevance; no overflow runtime behavior
is chosen. Future recursive roots may carry the local Rootable premise supplied
separately by Q78. Q74 adds no WF/WT conjunction, constructor admission,
wrapper/class field or acceptance policy.

Q75 supplies exactly one ordinary public law, **discharged** by
`STFSpec/Codec/SszMerkleizeProgressive.lean`:

```lean
theorem Ssz.merkleizeProgressive_eq (chunks : Array Base.Bytes32) (depth : Nat) :
    merkleizeProgressive chunks depth =
      let zero := (Base.FixedBytes.ofNat 0 : Base.Bytes32)
      let pair := fun (left right : Base.Bytes32) =>
        STFSpec.Hash.sha256 ((left.toBytes ++ right.toBytes).toByteArray)
      if chunks.isEmpty then zero else
        let «prefix» := chunks.toList.take (2 ^ depth)
        let root := ((List.range depth).foldl
          (fun layer _ => (List.range (layer.length / 2)).map (fun i =>
            pair (layer.getD (2 * i) zero) (layer.getD (2 * i + 1) zero)))
          («prefix» ++ List.replicate (2 ^ depth - «prefix».length) zero)).headD zero
        pair root
          (merkleizeProgressive ((chunks.toList.drop (2 ^ depth)).toArray) (depth + 2))
```

All authored supporting declarations are private. The default 0 argument is
inserted at calls; the underlying function type still takes Nat. Local prefix
capacity follows from slicing and is discharged internally. The theorem covers
all finite arrays and every natural depth without a source-host success premise;
source correspondence separately retains the local premises in §3. No length or
activity mix-in, Rootable clause, acceptance/error policy or binding assumption is added.

Q76 supplies exactly this ordinary public law, **discharged** by
`STFSpec/Codec/SszMixInLength.lean`:

```lean
theorem Ssz.mixInLength_eq (root : Base.Bytes32) (len : Nat)
    (h : len < 2^256) :
    mixInLength root len h =
      STFSpec.Hash.sha256
        ((root.toBytes ++
          (Base.FixedBytes.ofLeNat len : Base.Bytes32).toBytes).toByteArray)
```

Public `FixedBytes.toBytes_ofLeNat` expands all 32 count bytes to
`Base.Bytes.generate 32 (fun i => UInt8.ofNat (len >>> (8 * i)))`.
The resulting full List reference is root.toBytes.toList followed by those
ordered 32 digits; zero bytes are retained throughout. The operation has exactly
one local Nat bound. Proof irrelevance and exact root/count equality preserve
its whole result without a hash-injectivity assumption. Natural List/Bytes
consumers supply the bound directly. Existing `U256.toNat_ofNat_of_lt` gives an
intended-count observation only under this bound, not wrapping admission.
All SHA messages have 64 bytes: the local FIPS 512 < 2^64 premise is independent of
count range. Boundary/outside counts cannot supply the API proof; this is neither
a runtime result nor a guest error choice. Source success/order, every actual
nested count bound and rootability, activity interpretation and collision freedom
remain separate. No global WF/WT/Rootable premise or new public helper is added.

Q77 supplies exactly this ordinary public law, **discharged** by
`STFSpec/Codec/SszMixInActiveFields.lean`:

```lean
theorem Ssz.mixInActiveFields_eq (root : Base.Bytes32) (active : List Bool)
    (h : active.length ≤ 256) :
    mixInActiveFields root active h =
      STFSpec.Hash.sha256
        ((root.toBytes ++
          (Base.FixedBytes.ofLeNat
            (active.foldr (fun bit n => (if bit then 1 else 0) + 2*n) 0)
            : Base.Bytes32).toBytes).toByteArray)
```

The head bit has weight 1; position i maps to byte i/8 with low-first bit i%8.
The public Base byte law expands every digit, including all zero tails. There
is no count, delimiter, tag or extra mask hash. Numeric fit follows privately
from value < 2^length and the sole caller width proof. All admitted positions retain
their power-of-two contribution. Empty/allfalse/trailingfalse masks remain valid
mathematical inputs, and []/[false] have the same preimage without invoking SHA
collision or injectivity. Padding to 256 preserves packing and the whole result.
Every message has 64 bytes and satisfies the FIPS bit-length premise independently
of source class admission. Width > 256 supplies no argument, rather than a runtime
error or truncating completion. Source class validity, contents-root meaning,
actual decoded/rootable inputs and enclosing roots/binding remain separate.

Q79 supplies exactly this complete ordinary public constructor-result law,
**discharged** by `STFSpec/Codec/SszRoot.lean`:

```lean
theorem Ssz.hashTreeRoot_eq (t : SszType) (v : SszValue)
    (h : Ssz.Rootable t v) :
  let R := Ssz.hashTreeRoot
  let result := R t v h
  let q : Nat → Nat := fun n => (n + 31) / 32
  let K : Nat → Nat := fun n =>
    2 ^ (if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1)
  let zero := (Base.FixedBytes.ofNat 0 : Base.Bytes32)
  let digits : Nat → Nat → List UInt8 := fun w n =>
    (List.range w).map (fun i => UInt8.ofNat (n >>> (8 * i)))
  let uintChunks : Nat → List Nat → Array Base.Bytes32 := fun w ns =>
    Ssz.pack ((ns.flatMap (digits w)).toByteArray)
  let boolChunks : List Bool → Array Base.Bytes32 := fun bs =>
    Ssz.pack ((bs.map (fun b => if b then (1 : UInt8) else 0)).toByteArray)
  let children : List (SszType × SszValue) → List Base.Bytes32 → Prop :=
    fun ps rs =>
      ps.length = rs.length ∧
      ∀ p ∈ ps.zip rs, ∀ hx : Ssz.Rootable p.1.1 p.1.2,
        R p.1.1 p.1.2 hx = p.2
  let slots : List Bool → List Base.Bytes32 → Array Base.Bytes32 := fun mask rs =>
    ((List.range mask.length).map (fun i =>
      if mask.getD i false then
        rs.getD ((mask.take i).filter id).length zero
      else zero)).toArray
  match t, v with
  | .uint _, .uint n =>
      result = (Base.FixedBytes.ofLeNat n : Base.Bytes32)
  | .bool, .bool b =>
      result = (Base.FixedBytes.ofLeNat (if b then 1 else 0) : Base.Bytes32)
  | .byteVector n, .bytes b =>
      ∀ hp : (Ssz.pack b).size ≤ K (q n),
        result = Ssz.merkleize (Ssz.pack b) (q n) hp
  | .byteList limit, .bytes b =>
      ∀ hp : (Ssz.pack b).size ≤ K (q limit), ∀ hn : b.size < 2^256,
        result = Ssz.mixInLength
          (Ssz.merkleize (Ssz.pack b) (q limit) hp) b.size hn
  | .list elem limit, .list xs =>
      match elem with
      | .uint w =>
          ∀ ns : List Nat, xs = ns.map SszValue.uint →
          ∀ hp : (uintChunks w ns).size ≤ K (q (limit * w)),
          ∀ hn : xs.length < 2^256,
            result = Ssz.mixInLength
              (Ssz.merkleize (uintChunks w ns) (q (limit * w)) hp) xs.length hn
      | .bool =>
          ∀ bs : List Bool, xs = bs.map SszValue.bool →
          ∀ hp : (boolChunks bs).size ≤ K (q limit),
          ∀ hn : xs.length < 2^256,
            result = Ssz.mixInLength
              (Ssz.merkleize (boolChunks bs) (q limit) hp) xs.length hn
      | .byteVector _ | .byteList _ | .list _ _ | .progressiveList _ |
        .progressiveByteList | .container _ | .progressiveContainer _ _ =>
          ∀ rs : List Base.Bytes32,
          children (xs.map (fun x => (elem, x))) rs →
          ∀ hp : rs.toArray.size ≤ K limit, ∀ hn : xs.length < 2^256,
            result = Ssz.mixInLength
              (Ssz.merkleize rs.toArray limit hp) xs.length hn
  | .progressiveList elem, .list xs =>
      match elem with
      | .uint w =>
          ∀ ns : List Nat, xs = ns.map SszValue.uint →
          ∀ hn : xs.length < 2^256,
            result = Ssz.mixInLength
              (Ssz.merkleizeProgressive (uintChunks w ns) 0) xs.length hn
      | .bool =>
          ∀ bs : List Bool, xs = bs.map SszValue.bool →
          ∀ hn : xs.length < 2^256,
            result = Ssz.mixInLength
              (Ssz.merkleizeProgressive (boolChunks bs) 0) xs.length hn
      | .byteVector _ | .byteList _ | .list _ _ | .progressiveList _ |
        .progressiveByteList |
        .container _ | .progressiveContainer _ _ =>
          ∀ rs : List Base.Bytes32,
          children (xs.map (fun x => (elem, x))) rs →
          ∀ hn : xs.length < 2^256,
            result = Ssz.mixInLength
              (Ssz.merkleizeProgressive rs.toArray 0) xs.length hn
  | .progressiveByteList, .bytes b =>
      ∀ hn : b.size < 2^256,
        result = Ssz.mixInLength
          (Ssz.merkleizeProgressive (Ssz.pack b) 0) b.size hn
  | .container fields, .container xs =>
      ∀ rs : List Base.Bytes32, children (fields.zip xs) rs →
      ∀ hp : rs.toArray.size ≤ K fields.length,
        result = Ssz.merkleize rs.toArray fields.length hp
  | .progressiveContainer mask fields, .container xs =>
      ∀ rs : List Base.Bytes32, children (fields.zip xs) rs →
      ∀ hm : mask.length ≤ 256,
        result = Ssz.mixInActiveFields
          (Ssz.merkleizeProgressive (slots mask rs) 0) mask hm
  | _, _ => False
```

The captured result precedes the dependent match. Local ns/bs projections,
proof-independent ordered child certificates and all rounded capacity/count/mask
bounds exist under C; they are not extra public arguments or vacuous conditions.
The whole recursive equation determines the supported result by proper actual
children. Scalar bytes, all byte/element count units, ordinary limits and finite
sparse positions are fixed by this statement. Source/decoder/class/host refinement,
failure ordering, O2/O12/O13, binding and cost/readiness obligations remain separate.

**Supplied forward serialization contract (Q80).** Exactly
four public declarations are supplied: `Ssz.Serializable`, `Ssz.serializable_iff`,
`Ssz.encode` and `Ssz.encode_eq`. Everything below is a complete informal signature
and equation; §3/§4 records the compiled implementation/proofs and finite evidence. All authored
workers, references, derived laws, controls and clients remain private; there is
no public size/layout/reference/helper, validator, instance or error API.

The ordinary public predicate law has exactly parameters `(t : SszType)` and
`(v : SszValue)` and conclusion `Ssz.Serializable t v ↔ RHS(t,v)`. Its statement
begins with the following entire lexical local recursive Nat-valued expression
`byteLength`, followed by the local folds below. Lists/sums are finite and ordered;
empty sums are0. This expression is complete even off support:

```text
byteLength(uint w, uint n) = w
byteLength(bool, bool b) = 1
byteLength(byteVector n, bytes b) = b.size
byteLength(byteList limit, bytes b) = b.size
byteLength(progressiveByteList, bytes b) = b.size
byteLength(list e limit, list xs) =
  match e.fixedSize? with
  | some w => w * xs.length
  | none => 4 * xs.length + sum(xs.map (fun x => byteLength(e,x)))
byteLength(progressiveList e, list xs) =
  match e.fixedSize? with
  | some w => w * xs.length
  | none => 4 * xs.length + sum(xs.map (fun x => byteLength(e,x)))
byteLength(container fs, container xs) =
  sum((fs.zip xs).map (fun (f,x) =>
    match f.fixedSize? with some w => w | none => 4 + byteLength(f,x)))
byteLength(progressiveContainer mask fs, container xs) =
  sum((fs.zip xs).map (fun (f,x) =>
    match f.fixedSize? with some w => w | none => 4 + byteLength(f,x)))
byteLength(unmatched tags) = 0
```

Recursion visits proper actual child values/list spines, with a structural or
size-of-value termination argument independent of fixed widths and byte slices;
no call descends into a synthetic enlarged value. The public statement uses
lexical `let rec` or an extensionally identical fully inlined recursor term, never
a private global name. Definitional reduction and the ordinary public law must
suffice for facade clients. Failed elaboration/client evidence must be reported
and the interface choice revisited; it authorizes no extra public size declaration.
A private logical-length worker may use the equivalent paired-field sum and a
private ordinary equality to this complete expression.

For `ps : List (SszType × SszValue)`, locally define
`H(ps) := sum(ps.map (fun (f,x) => f.fixedSize?.getD 4))` and
`ls(ps) := ps.map (fun (f,x) => byteLength(f,x))`. For `ls : List Nat`,
`starts(ps,ls)` is the ordered fold over `ps.zip ls` starting with cursor `H(ps)`
and empty output. A fixed pair (`f.fixedSize? = some w`) leaves both unchanged.
A variable pair appends its current cursor to output and then increases the
cursor by that pair's supplied length. Return the output, excluding the final
cursor. `fits(ps,ls) := ∀ o ∈ starts(ps,ls), o < 2^32`. Raw unequal-length lists
use the same zip fold; all public uses below have equal lengths.

The complete decoupled actual-value `serializable_iff` RHS is exactly:

| `t, v` | `RHS(t,v)` |
|---|---|
| `uint w, uint n` | `(w=1 ∨ w=2 ∨ w=4 ∨ w=8 ∨ w=16 ∨ w=32) ∧ n<2^(8*w)` |
| `bool, bool b` | `True` |
| `byteVector n, bytes b` | `b.size=n` |
| `byteList limit, bytes b` | `b.size≤limit` |
| `progressiveByteList, bytes b` | `True` |
| `list e limit, list xs` | `xs.length≤limit ∧ (∀ x ∈ xs, Ssz.Serializable e x) ∧ fits(ps,ls(ps))`, `ps=xs.map (fun x => (e,x))` |
| `progressiveList e, list xs` | `(∀ x ∈ xs, Ssz.Serializable e x) ∧ fits(ps,ls(ps))`, `ps=xs.map (fun x => (e,x))` |
| `container fs, container xs` | `fs.length=xs.length ∧ (∀ p ∈ fs.zip xs, Ssz.Serializable p.1 p.2) ∧ fits(ps,ls(ps))`, `ps=fs.zip xs` |
| `progressiveContainer mask fs, container xs` | `fs.length=xs.length ∧ (∀ p ∈ fs.zip xs, Ssz.Serializable p.1 p.2) ∧ fits(ps,ls(ps))`, `ps=fs.zip xs` |
| unmatched tags | `False` |

There is no encoder dependency in this predicate law, nor an implicit WF, WT,
Rootable, global size/count cap, mask condition, positive fixed-child width or
source-class premise. Actual scalar widths0/3 are unsupported; unused malformed
schemas under empty lists are not recursively required by support. Empty ordinary and
progressive containers encode empty, regardless of mask; all raw masks are
ignored by bytes. These are intentional mathematical extras relative to source
class construction (`utils/ssz.py:91–95,208–216`; `basic.py:252–309`;
`complex.py:800–804`; `progressive.py:460–486`). Nonempty fixed-zero-child lists
have forward support and encode empty. Even source-admitted `List[ByteVector0]`
cannot recover count from those bytes (`complex.py:188–195,224–242`); the inverse
domain must stay separate.

For the sole ordinary result law, locally set `bytes(b) := b.data.toList` and
`LE(w,n) := (List.range w).map (fun i => UInt8.ofNat ((n / 256^i) % 256))`.
For `bs : List ByteArray`, locally define
`cert(ps,bs) := ps.length=bs.length ∧ ∀ q ∈ ps.zip bs, ∀ hc : Ssz.Serializable q.1.1 q.1.2, Ssz.encode q.1.1 q.1.2 hc = q.2`.
`layout(ps,bs)` is the ordered fold over `ps.zip bs` starting at
`(cursor,head,tail)=(H(ps),[],[])`. A fixed pair appends the entire `bytes(b)` to
head, leaving cursor/tail unchanged. A variable pair appends `LE(4,cursor)` to
head and the entire `bytes(b)` to tail, then increments cursor by `b.size`.
Return `head ++ tail`. These are completely specified local finite list/fold
expressions in the theorem type, with no private global helper exposed.

`Ssz.encode_eq (t : SszType) (v : SszValue) (h : Ssz.Serializable t v)` captures
`r := bytes(Ssz.encode t v h)` before its dependent match. Its complete result
proposition `RHS(t,v,h)` is exactly:

| `t, v` | Result proposition |
|---|---|
| `uint w, uint n` | `r=LE(w,n)` |
| `bool, bool b` | `r=[if b then 1 else 0]` |
| `byteVector n, bytes b` | `r=bytes(b)` |
| `byteList limit, bytes b` | `r=bytes(b)` |
| `progressiveByteList, bytes b` | `r=bytes(b)` |
| `list e limit, list xs` | `∀ bs : List ByteArray, cert(ps,bs) → r=layout(ps,bs)`, `ps=xs.map (fun x => (e,x))` |
| `progressiveList e, list xs` | `∀ bs : List ByteArray, cert(ps,bs) → r=layout(ps,bs)`, `ps=xs.map (fun x => (e,x))` |
| `container fs, container xs` | `∀ bs : List ByteArray, cert(ps,bs) → r=layout(ps,bs)`, `ps=fs.zip xs` |
| `progressiveContainer mask fs, container xs` | `∀ bs : List ByteArray, cert(ps,bs) → r=layout(ps,bs)`, `ps=fs.zip xs` |
| unmatched tags | `False` |

Unmatched False is impossible under `h`, not a runtime fallback. Under support,
actual child support projections and equal-length cert lists must exist by taking
each child's encode; Prop proof irrelevance removes proof-choice ambiguity.
Private actual-value induction proves actual encoded length equals the local
logical length, fixed supported widths equal their actual bytes, ordinary full
reference equality (D25), proof independence and whole-law determination (§3). These
are discharged component proofs, not extra caller hypotheses or vacuous implications.
For fixed-element lists the layout is ordered child concatenation; dynamic lists
start at `4*count`; mixed containers retain all fixed head fields and dynamic
tails in order. Empty dynamic children allow equal offsets. Only starts actually
emitted must fit, recursively; no final cursor/payload `< 2^32` is required.
For example a single variable payload of mathematical length2^32 has only start4;
a later empty variable field can still require an unrepresentable written start.
Source decoder scope conversion and nested metadata limits are distinct
(`complex.py:210,956–960`; `progressive.py:248–249`).

This forward contract supplies no inverse/canonicality, formal source refinement,
source diagnostic/failure priority, schema/root/guest admission or resource policy.
The supplied cached packed writer and ordinary reference equalities are described
in §3/§6; §4 records independent facade clients. Static traversal/copy structure
does not establish measured allocation, throughput, native-client ratios or C1–C4.
Later private representation replacements must re-prove this unchanged complete
result law and ordinary readable-reference equality.

The inverse, canonicality, schema, binding and source/guest obligations below
remain prospective or conditional as qualified in each item. Their unresolved
domains and total completions remain in §10; the raw model, sizing, structural WF,
payload typing and raw pack controls alone discharge none of those obligations.

- [T] `decode` must be total. Recursion on the type and validated slice boundaries are the intended proof ingredients. Strictly smaller byte slices alone do not justify every sub-decode: zero-byte fixed children require a separate termination argument and an unresolved inverse domain. Offsets must be validated against the slice length before use.
- [C] **Prospective roundtrip:** with `h : Ssz.Serializable t v` and a separately resolved inverse-domain premise, require `decode t (Ssz.encode t v h) = .ok v`. Serializable, WT, WF and even a final byte-size bound do not recover zero-width fixed-element list counts. The exact inverse premise remains open (§10); no inverse theorem is supplied.
- [C] **Prospective canonicality:** `decode t b = .ok v` must imply `WellTyped t v` and provide `h : Ssz.Serializable t v` with `Ssz.encode t v h = b`. This is the future typed form of EELS's re-encode check (`ssz.py:144`). Equality of the accept set with an encoder image additionally needs the converse decoding/inverse premise on a resolved domain (S3; §10); the re-encode check alone does not supply it.
- [T] Q79 supplies the raw root operation, ordinary constructor law and actual-value termination on C. Actual-source refinement and O2 freedom still require every successfully decoded guest request to preserve its schema/values and inhabit that domain, with local class/host premises; S5 alone does not establish this.
- [C] Progressive contents-tree refinement is supplied by Q75 above. Q76 supplies the local length mix-in. Q77 supplies the local activity mix-in; Q79 supplies the raw enclosing root law; actual schema/source refinement remains separate. Q74 owns the ordinary physical helper.
- [C] Schema laws per `SszSchema α` instance: `valid a → ofValue? (toValue a) = some a ∧ WellTyped type (toValue a)`; conversely `WellTyped type v ∧ ofValue? v = some a → valid a ∧ toValue a = v`. This second direction prevents lossy schema conversions from changing the decoded request's commitment. The schema type itself is well formed.
- [S] **Binding:** on the actual guest schemas, with well-typed values, exact active-field interpretation and every length mix-in representable in uint256, equal `hashTreeRoot`s imply equal values or an explicit SHA-256 collision. This is the request-binding theorem of CONTRACT §7. Induct over the schema and Merkle tree: equal child preimages permit descent; unequal preimages with equal hash give the collision. Fixed widths and mixed-in lengths disambiguate padding. Extending this law to arbitrary `SszType` requires specifying inactive fields and the domain of unbounded progressive lengths; it is not asserted without those premises.

**Addresses.**
- [C] The implemented formulas return the final twenty bytes of `keccak256(encode (.list [.bytes a.toBytes, ofNat n]))` for CREATE, and `keccak256(0xff ‖ a ‖ s ‖ keccak256(c))` for CREATE2. Their `…Q` forms at `m := Id` equal the concrete endpoints by `rfl`.
- [C] Public query expansions preserve exact preimages/order and arbitrary-answer dependence. Byte-effect equations expose the final suffix through Base's `Address.toBytes_ofNat_toNat`. Pure-answer and StateT/ExceptT forwarding laws require `LawfulMonad`; lawful ExceptT failure laws retain the supplied original errors and suppress subsequent queries.
- [C] `encodable_computeContractAddress_preimage` establishes Q47's CREATE `Encodable` premise for every sender and nonce below 2^256. The API still accepts every Nat, with the total encoder completion outside that proved bound.
- [R] VM creation/state/gas/collision behavior and D5 generic interpretation coupling remain open; the address formulas alone supply none of them.

### Informal correctness argument

**Claim.** On the encodable domain, decoding accepts precisely the reference encodings, returns corresponding typed values or single-channel rejections on the local
source domain, and the guest-schema roots use the specified Merkle layout.

**Premises.** EthBase/Hash laws, exact schema field order and widths, both directions of each schema adapter, representable offsets/length mix-ins, local intended-source/class admission, successful reflection, callback refinement
and first-consuming-handler premises, and a resolved policy for reference
host-resource exceptions.

**Argument.** RLP prefix cases determine one extent; recurse only inside that extent and require full consumption. The shortest-length and integer checks give canonicality and prefix-freeness. Typed decoders then check constructor shape, arity and integer ranges. SSZ induction over types establishes fixed-size layouts and variable-offset boundaries; the strict decoder's accepted bytes must re-encode identically, while the reverse implication needs a separate proof that every canonical encoding decodes. The schema adapter transfers both results to the caller's type. Merkleization induction replaces padded subtrees with the zero-hash recurrence; progressive zero hashes are defined for every required depth, not just the cached prefix. Binding descends through equal child preimages; unequal preimages with equal digests expose a collision. Exact field interpretation and mixed-in lengths distinguish zero padding.

**Open obligations.** Rootability of every accepted guest input, unbounded progressive-length domains, RLP encodability of schema-produced items and all schema instances need proof. These domains must not become new acceptance limits without an explicit protocol decision. Generic inactive-field binding is not implied by the guest-schema result.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthHash`.
- **Used by:** `EthCommit` (node RLP), `EthVmInstructions` (CREATE/CREATE2 addresses), `EthBlock` (transaction/header/receipt RLP, withdrawal and request SSZ, BAL encoding), and transitively `EthStateCommit` (account leaf RLP), `EthStateWitness` and `EthStateless` (`StatelessInput` schema, output encoding, the request root).
- **Seams provided.** Generic RLP and SSZ with canonicality theorems. Schema owners write `SszSchema`/`RlpDecode` instances and prove only the per-instance schema laws. Contract-address derivation.
- **Cross-module invariants.** Future consumers use `decodeTo` wherever EELS uses
  `decode_to`, with Q68's exact result preservation and single-channel observation.
  This alone does not make D2r unobservable: actual schema-depth, local
  source/reflection/callback/host and first-handler premises remain required.
  Schema owners must mirror `_infer` exactly: field order, widths, limits, and
  progressive versus plain types. No new typed handoff is supplied by guidance.
- **Supplied List seam (Q69).** Consumers lift their actual member inverses through
  the public model law, recursively for nested lists, and supply complete assembled
  Encodable for the public wire law. [COMPOSITION §2](../COMPOSITION.md#typed-rlp-model-premise)
  owns that handoff; schema, local source/host and first-handler duties remain.
- **Supplied sizing premise (Q67).** Future inline/offset and fixed-element
  consumers use the single §7 equation and inspect the whole `Option Nat`.
  `some 0` remains fixed metadata; division/modulo, serialization inverses,
  actual schema admission and root operations each need their own local domain
  premises. Neither a blanket WF assumption nor sizing alone supplies them.
  The classifier and equation supply the local structural composition premise;
  actual codec/schema consumers remain future work.
- **Implemented header premise.** The extent helper supplies suffix/window
  correspondence and positive declared extents. Full parsers must still check
  declared extents against the current parent window before reading payloads,
  apply canonical item checks, recurse and require full consumption.
- **Relies on.** `EthHash.sha256` and `keccak256`, and `EthBase` byte conversions (in particular `Uint.toBeBytes 0 = empty`).

## 9. Open decisions

- **Q80** owns the forward serialization disposition; §5/§7 owns exactly its
  four-declaration contract. §3/§4 records its supplied code/proofs/controls;
  source/inverse/decoder/guest/resource bridges remain open in §10. It changes no Q67–Q79 provider contract.

- **Q79** owns the direct complete root-result disposition; §5/§7 owns exactly
  the supplied operation/equation. The actual source/decoder/class/host, guest,
  security and resource obligations remain in §10.

- **Q78** owns the approved local declared/source-shaped Rootable disposition;
  §5/§7 owns exactly the supplied predicate and complete ordinary law.
  The separate source/decoder/root/security/resource obligations remain in §10.

- **Q77** owns the approved local width disposition; §5/§7 owns exactly the
  supplied operation/equation. Q70/Q71 are unchanged; §10 retains actual source,
  root/decoder/guest and resource obligations.

- **Q76** owns the approved Nat count/local-bound disposition. §5/§7 owns
  exactly the supplied operation/equation; §10 retains actual count/root/source
  obligations without selecting a new global domain or guest error policy.

- **Q71** owns the approved payload-only typing disposition; §5/§7 owns exactly
  its predicate and complete constructor law. WF is separate and WT⇒WF is false;
  source/operation/codec/root domains in §10 remain open.

- **Q70** owns the approved nameless structural WF disposition; §5/§7 owns
  exactly the predicate and constructor law. Q71 owns payload typing; source
  names/classes and the operation domains in §10 remain separate.

- **Q69** owns the approved List disposition; §5/§7 owns its exact bounded
  instance/law contract. No new unresolved semantic choice is introduced.

- **Q68** owns the typed-wrapper diagnostic equation and conditional Nat theorem
  contract supplied in §5/§7; remaining instance/schema gaps are in §10.

- **Q67** owns the raw structural sizing disposition; §5/§7 specifies its
  supplied value/law contract. The residual SSZ domains in §10 stay open under Q70.

- **Q47** owns the total RLP encoder completion beyond `Encodable`; decoder acceptance and round-trip/canonicality contracts retain the domain in §7.

- **SSZ reference implementation** (DECISIONS B5, Q21/Q22; adopted provisionally): [ethereum/ssz-specs `lean/`](https://github.com/ethereum/ssz-specs/tree/main/lean) (@d4a0d75, MIT, Lean v4.33.1, no dependencies, `warningAsError`).
  - **Why it fits:** its types-as-data design (`Desc` declarations plus separate values) matches the `SszValue` + `WellTyped` resolution. It proves codec canonicality ("every accepted byte string is canonical"), round trips, admissibility, whole-value binding in SHA-256 collision form, progressive trees (EIP-7916/7495), and a merkleization cost bound.
  - **Status:** inspiration and reference now. It becomes a dependency only if the modules we import pass `check-decls` (D26) and match our decisions: strict decoding, error constructors per D14, and the schemas our guest needs (`StatelessInput` progressive lists, `NewPayloadRequest`).
  - **To check:** its handling of the offset-gap and misalignment cases that remerkleable accepts and EELS's re-encode check rejects, and its SHA-256 speed.

- **D5** (provisional, broad scope; B10): address derivation and transaction/header hashing go through `KeccakQuery` (A3). The public pure forms are the `Id` specialisations.
- **D14** (accepted): O1 (decode failures) needs explicit constructors. O2 (root failure) is **open**: prove it unreachable (S5; EthStateless L-root) and add a constructor only if that proof fails (DECISIONS §3, O2). The precedence between SSZ decode failure and schema-id failure is owned by `EthStateless`.
- **D18/D21** (accepted): no fast paths are planned. `@[csimp]` is banned; any later fast path is a representation replacement, or an executable definition with a legible reference and an equality proof.
- **P2:** the fixtures decide where they speak (9 O1 fixtures). Elsewhere the EELS re-encode check is the authority.
- RLP `RecursionError` (D2r): tracked under DISC-001 (DECISIONS Q20; O12, unresolved by design). The reproducer is probe `tx-deep-rlp-40000`.
- SSZ decoder formulation and value representation: resolved, DECISIONS B5 (Q21, Q22).

## 10. Gaps

- **Forward serialization (Q80) supplied; actual bridges open.** The exact four
  declarations, self-contained inline-recursion support law, actual-length/full
  reference and cached-planner equality, structural termination, constructive
  certificates, proof independence/determination, facade clients and61 literal/native
  controls are supplied (§3/§4). Fifty-five finite genuine source paths match the
  literals; six mathematical cases are separately labelled. Actual class/name/
  coercion/backing/cache/endian/host premises, universal source refinement and
  source diagnostic/failure/resource order remain open. Typed schema/output consumers,
  inverse/strict decoder scopes and fixed-zero count recovery, actual root/guest
  domains, O1/O2/O12/O13, binding, EEST/security, measured allocation/lifetime/
  throughput, C1–C4 and readiness remain open. Q67–Q79 contracts and remaining
  obligations are unchanged.

- **Computational raw roots (Q79) supplied; actual bridges open.** The operation,
  complete ordinary equation, actual-value termination, local witness availability
  and whole-law determination, with private rootP0–rootP9/rootC0–rootC9 complete
  controls/clients, are discharged. Actual source class/name/reflection/coercion/
  backing/cache/hash/global/alias/endian/host and executed-path zero-table premises,
  decoder view→dataclass→fresh-view support, typed SszSchema/root adapters, whole
  source construction/failure/resource order, O2/O12/O13, request binding/external
  anchors, EEST/guest/security, C1–C4 and readiness remain open. Finite source-vector
  evidence is bounded and distinguishes mathematical-only cases; it supplies no
  universal source/decoder or accepted-input theorem and adds no decoder guard.

- **Local root support (Q78) supplied; consuming bridges open.** The two public
  declarations and the complete private rootableP0–rootableP9/rootableC0–rootableC9
  control/client groups are discharged.
  Actual source view→dataclass→fresh-view support and source
  class/name/backing/cache/hash/global/alias/host premises,
  failure/resource order, O2/O12/O13, binding/security and C1–C4/readiness remain
  separate. No new decoder restriction or layer-readiness assertion follows.

- **Remaining APIs and composition.** See §3 for implemented APIs and §7 for
  public-law domains. The supplied independent classes, `encodeOf`/`decodeTo`,
  Nat/ByteArray adapters with conditional roundtrips and Bool/U256/U64/U32/U8 adapters with
  unconditional finite-domain roundtrips, plus generic FixedBytes n adapters with
  conditional wire inversion, and nominal Hash32/Address with unconditional finite-domain
  inversions and generic List adapters with membership-local model/wire laws,
  leave other encoding/decoding instances and element/schema decoders unimplemented.
  The supplied SSZ interfaces are raw vocabulary, structural sizing, nameless WF
  and payload typing, raw byte packing, zero hashes, the Q74/Q75
  ordinary/progressive contents trees, the Q76/Q77 length/activity mix-ins,
  Q78 local root support and the Q79 computational raw root; other SSZ semantic
  interfaces remain unimplemented.
  The whole typed-result equation and local single-channel
  observation are supplied without a new projection API. Local intended-source,
  reflection/callback/host and first-handler premises, actual schema-depth
  agreement and full-guest gates
  remain open. Raw `SszType`/`SszValue`/`SszError`
  vocabulary and structural
  `fixedSize?`, `WellFormed` and `WellTyped` with their single respective equations
  are supplied, together with raw `Ssz.pack`, zero hashes, the Q74/Q75
  ordinary/progressive contents trees, the Q76 local length and Q77 local activity
  mix-ins, `Ssz.Rootable`, the Q79 computational raw root and their complete
  public equations;
  schema, typed codec/root operations and error producers remain unimplemented.
  Generic List composition requires supplied child instances and local inverses;
  the `toFields` leaf does not discharge schema child typing, and local diagnostic
  correspondence does not implement the consuming header/transaction handlers.
  Whole EthCodec gates, schema proofs, security binding and cost/guest obligations
  remain open.

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **EIP cross-check missing.** The progressive merkleization order (subtree left, rest right) and the placement of the active-fields chunk were checked only against remerkleable, the pinned dependency. They have not been compared with EIP-7916 or EIP-7495 at the versions the fixtures were generated with. If they disagree, the fixtures still decide, but the discrepancy should be reported.
- **Computational raw root limits (Q79).** The C-indexed operation, complete
  ordinary constructor equation, rootP0–rootP9 and independent rootC0–rootC9 are
  supplied. Local projections, capacity/child witnesses and determination cover
  actual supported values. Finite source observations and executable Lean
  comparisons are separate evidence; they supply no general Python refinement,
  schema/class/decoder bridge, source failure/resource ordering or runtime guard.
  O2/O12/O13, EEST/guest, security/binding, C1–C4 and readiness gates stay open.
- **SSZ sizing limits (Q67).** The classifier, ordinary equation, structural
  termination and §4 private controls/clients are supplied. Conditional static
  source interpretation is not a formal Python refinement theorem or executed
  source comparison. Actual codec/schema consumers, source class admission,
  compiled feasibility, practical stack/resources and C1–C4 remain open; no
  larger G/S/W/R, EEST or guest readiness claim follows.
- **Active-field mix-in limits (Q77).** The two public declarations, complete
  equation and private groups 0–9 in the P family/facade C0–C9 are supplied. Source-only controls are
  UNRUN. Source names/class admission, sparse zero-node contents/root meaning,
  reflection/root widths/hash/global/alias/backing/cache/host premises and whole
  construction/failure/resource order remain local. Actual decoder/adapter-to-Rootable
  support, enclosing roots/guest binding, O2/O12/O13, EEST, security, cost and
  readiness gates remain open. Width alone does not prove source admission;
  packing supplies no raw-mask injectivity or changed guest accepted domain.
- **Length mix-in limits (Q76).** The two public declarations, complete
  successful-value equation, private lengthP0–lengthP9 and facade C0–C9 are supplied.
  Source-only cases remain UNRUN. Actual standard source class/root/backing/
  endian/hash/global/alias/cache/host premises and whole caller construction/
  failure/resource order remain separate. Actual decoder/adapter support for Q78
  and every nested count bound remain open, along with
  enclosing roots/layout/binding, guest/O2/O12/O13, security, EEST, G/S/W/R/C1–C4
  and readiness gates. No accepted-domain narrowing or new error mapping is adopted.
- **Progressive helper limits (Q75).** The two public declarations, all-domain
  packed/reference recurrence refinement, private progressiveP0–progressiveP9 and facade C0–C9 are supplied.
  Source-only operational controls remain UNRUN. Source node/backing/class/root/hash/
  global/alias/cache/per-path zero-table and successful-host premises stay local;
  bulk construction does not prove append/navigation correspondence. Q76 supplies
  the local length mix-in, Q77 the local activity mix-in, and Q78 local Rootable
  support. Actual schemas/decoder/adapter support, enclosing roots, outcomes,
  resources/C1–C4, security, EEST, guest and readiness gates remain open.
- **Merkleization limits (Q74).** Physical helper and its full ordinary law,
  private merkleP0–merkleP9 and separate public-only C0–C9 are supplied. Original source-runtime
  controls remain UNRUN. Q78 supplies local Rootable and its complete law;
  actual declared-count/class/backing admission, decoder/adapter-to-root-support
  proofs, typed-root/schema refinement and binding remain open; Q79 supplies
  the local raw root operation and its complete result law.
  The local length/activity mix-ins are supplied separately by Q76/Q77. The guest
  still accepts arbitrary bytes under CONTRACT; execution-invalid supported
  payloads root before inner validation. No O2/O12/O13, error/handler, resource, security or readiness gate closes.
- **Zero-hash limits (Q73).** The two values/two ordinary laws and twelve private
  mathematical/six independent facade client groups are supplied. Source-only
  groups 0–3 remain UNRUN: mutable/rebound globals, negative Python indices, custom
  hashes, aliases and cached PairNode history have no unconditional refinement.
  Original table access at 256 is outside its initialized domain, while the
  mathematical recurrence is total. No merkleization, mix-in, actual codec/root
  admission, outcome, compiled sharing/stack/resource, C1–C4, security, EEST,
  guest or readiness gate closes.
- **Raw pack limits (Q72).** The two declarations, six private ordinary property
  groups, six separate facade client groups and 15 complete mathematical controls
  are supplied. Static dependency/helper correspondence has the original
  bytes/helper/RootNode/Root/builtins and successful-host-allocation premises in
  §3; there is no executed source comparison or raw-pack source-run profile.
  Typed packing, adapters/inverses, actual codec/schema/class/count/backing/offset/
  cache/root domains and broader differential obligations remain open with their
  consumers. No hashing, mix-in, acceptance cap, diagnostic/outcome policy,
  compiled ownership/resource bound, C1–C4, security, EEST or guest gate closes.
- **Residual SSZ domains (Q70/Q71).** The nameless WF predicate, constructor law,
  private logical controls and facade clients are supplied. Actual Python names,
  inheritance/reflection/class admission (including `more` at capacity 256) remain
  source-mapping premises. Payload-only WT, its constructor law, 130 signed
  controls and 16 public-law client groups are supplied; WT⇒WF is deliberately
  false and consumers needing WF supply it separately. Count/uint256 backing,
  scope, cache and actual codec/root bridges remain open. Q80 selects forward
  offset support separately; its implementation, zero-fixed-element list inverse
  premises and total decoder completion remain open.
  Some fixed-zero schemas remain WF; positivity belongs locally at division/recovery.
  No source execution, class admission, runtime validator, error priority,
  acceptance cap, codec/root or larger readiness/resource/cost gate is supplied
  by this Prop-only implementation.
- **"EELS accepts exactly the image of `encode`" (S3)** remains a prospective
  domain-dependent claim. The re-encode check alone proves no reverse implication
  that every encoding decodes. Zero-width fixed-element lists obstruct a generic
  inverse argument in the pinned dependency: an offset bound `< 2^32` alone is
  insufficient, and byte-slice decrease is not universal around zero-byte children.
  Q80 selects only the forward domain; an appropriate inverse domain and total
  decoder completion remain open. No fix is supplied here. Future differential round-trip coverage must include every
  Amsterdam schema as well as the selected domain boundaries.
- **D2r agreement** (deep nesting) is argued on the spec side. No fixture exercises it; it is tracked under DISC-001 (DECISIONS Q20), with probe `tx-deep-rlp-40000` as the reference-side reproducer. The claim that "no transaction schema nests more than about 4 levels" needs a check against every transaction type, including access lists, authorization lists and blob hashes. It also applies to the untyped `rlp.decode` sites (`incremental_mpt.py:936`, `witness_state.py:112,198`), which are protected only by the 2^10-byte node limit. That argument holds only if every such input comes from a bounded witness field. This is unverified for `witness_state.py:198`.
- **Thin O1 coverage.** The 9 fixtures do not test: `boolean` bytes other than 0 or 1, per-element `ByteList` limits (a 1025-byte witness node, a 65537-byte code), 257 headers, a wrong `public_keys` element length (65 bytes), an empty non-zero-scope list, or offsets ≥ 2^31. `#guard`s are proposed, but these cases lack fixtures.
- **SSZ emitted-offset support** (S6/Q80) has supplied generic forward support/serialization (§3), without an actual output consumer theorem. No `Envelope` field exists for it; by DECISIONS B6 one is added only when a named consumer theorem needs it (see `EthBase`).
- **The binding [S] proof** is sketched only. It needs an owner in `EthSecurity`, and the SHA-256 assumption for requests must be reconciled with the Keccak ROM (D5).
- **Schema fidelity.** Field order is checkable through `SszSchema.fieldNames` (F13): a prototype script outside this repository compared each adapter's names with REFERENCE-RECORDS. The core has no such check yet, and names alone do not check widths, limits or progressive versus plain types against `_infer`. The proposal for those is a `#guard` comparing `hashTreeRoot` of a sample value with a stored root generated from EELS; the generator script and stored roots do not exist yet.
- **Reference evidence:** the D1r fuzzing ran under 0.1.7 (byte-identical `rlp.py`); a rerun under the locked 0.1.6 would remove the version caveat.
- **Address derivation ownership.** Placing it here (not in `EthVmInstructions`) is a judgement call made in this spec, not an ARCHITECTURE decision.
- **Performance.** Encoder structural/generated-C checks and local compiled construction diagnostics are bounded evidence (§6); allocator volume, cleanup/lifetime and native-client/guest cost acceptance remain open. Raw `decode` has bounded local compiled whole-tree and decode/discard diagnostics (§6); allocator volume, native-client/guest costs and SSZ decoding of a maximal witness remain unmeasured.
- **The fixed-arity tuple laxity (D4r)** is deliberately not modelled. Any EELS change that introduces a fixed-arity RLP tuple target would silently diverge.
