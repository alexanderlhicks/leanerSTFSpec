# `EthCodec`: RLP, SSZ, `hash_tree_root` and derived addresses

*Status: informal specification, draft. Date: 2026-10-01. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F1, F13, F17, F18 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D5, D14, D18, D21 · questions: B5/Q21/Q22, B10/Q12, Q20, F13, F17, O2.*

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

  So an offset gap silently misaligns the fields. I checked this: `C{a: uint16, b: ByteList[10], c: ByteList[10]}` with a 1-byte gap decodes to `b = 0x0061, c = 0x6263`. The re-encode check then rejects it. The spec's decoder must be a **strict canonical decoder** whose accept set is proved equal to the image of `encode` (§7).

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
- **S6. Output encoding.** The only SSZ value the guest *encodes* is the fixed-size 43-byte `StatelessValidationResult` (CONTRACT §3). Encoding arbitrary values can fail in remerkleable when an offset reaches 2^32 (`encode_offset` via `uint32`, `complex.py:23–24`). The spec's `encode` is total over well-typed values whose encoding has offsets `< 2^32`, and is stated with that hypothesis.

## 3. EELS source map

### Implemented RLP encoder slice

`STFSpec/Codec/RlpEncode.lean` implements the pure total encoder on the public
`RlpItem` model. **Discharged:** its packed output equals the total readable
byte-list reference on every item, and the computed size equals actual output
width. Standard RLP/pinned-source correspondence retains `Encodable` (Q47).
Byte/list payloads and all length digits are preserved in order; no wire decoder laws beyond the
implemented slice, wire canonicality, injectivity, schema instances or guest outcomes are implemented.

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
string lengths1024, sibling counts256 and mixed nested cases; typed integer models
include0/1/1024. It checks exact Python input/result classes before observations,
including11 negative shape controls. Whole returned bytes, byte helper dispatch,
sequence dispatch and joined payloads are compared, not checksums. Lengthy Lean
literals are chunked and constant-byte runs use `List.replicate`, without
changing limits or tested bytes. Interpreter/startup,
frozen installation and RECORD remain trust inputs. These are finite actual
encoder observations, not EEST guest execution or a Python equivalence proof.

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
Private header witnesses establish positive advancement and bounded header reads;
the mutual recursion decreases `2 * remainingBytes + stage` (item0, joined1).
The packed and list frontends share parser classification/ordered-error semantics:
the refinement proves storage correspondence, while authenticated source probes
independently audit those semantics. Universal `Encodable` round trip,
accepted-input canonicality/image equivalence and prefix-free/injective laws are
**pending**, as a separate dependent proof work item; no finite test discharges them.

| Locked dependency source | Lean declaration and public type | Domain, value/effects | Ordered failures and consuming handler | Public law and deterministic regression |
|---|---|---|---|---|
| `ethereum_rlp/rlp.py:143–162` (0.1.6) | `Rlp.decode : ByteArray → Except RlpError RlpItem`; proof-facing `decodeModel : List UInt8 → Except RlpError RlpItem` | all finite bytes; exact nested byte/list tree, pure/no effects | empty before dispatch; all errors refine DecodingError; header fallback O3 and payload O6 handlers remain unimplemented | `decode_eq_model`, `decode_empty`, `decode_success_nonempty`; empty/00/7f/80/81/ff |
| `ethereum_rlp/rlp.py:387–424` | private byte branches of `decode` | accepted exact byte leaf; copy only validated available scope | low tag with extra bytes: negative length; short extent truncation, trailing, prefixed low singleton; long digit truncation, leading zero, length<56, payload truncation, trailing | `decode_single`, `decodeModel_single`, `decodeModel_short_bytes`; 55/56/255/256 bytes and simultaneous failures; long equations pending |
| `ethereum_rlp/rlp.py:427–484` | private list branches/ordered joined cursor of `decode` | exact ordered children in original-input windows; no copied list payload | outer header/canonicality/extent/trailing before children; child permissive header, declared-extent truncation, exact child decode; first failure wins | `decodeModel_short_list_truncated`, `decodeModel_short_list_trailing`; empty/nested/asymmetric trees, malformed first/later child and outer-extent priority; inverse/canonicality pending |
| `ethereum_rlp/rlp.py:487–543` | private bounded window header descriptor in `decode` | at most eight original length digits; Nat extents; validated header endpoint | digit truncation before leading zero; header remains permissive about body and short/long form | advancing/bounded witnesses used by kernel-checked termination; all eight string/list long tags and tiny input declaring2^64−1 |
| derived storage observation | `decode_window_model` | clipped/empty/public Base extract, including conceptual huge offsets | same complete result and diagnostics as the exact list window | public Base window law; caller proof does not unfold the Base representation |

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
whole-wire, instance, schema and guest correspondence remain open (§10).
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

**Error correspondence.** All typed rejection constructors here are diagnostic
refinements of one dependency `DecodingError`. Shape, Boolean, width, field-count,
no-variant and multiple-variant diagnostics, and integer leading-zero
`nonCanonical`, must be consumed identically by the future `decodeTo` wrapper.
The dependency's `decode_to` wraps every typed exception (`rlp.py:167–171`), after
raw `decode` outside that wrapper. Future consuming handlers include the header
fallback (`stateless.py:234–237`) and transaction decode in
`execution_engine/new_payload.py:60–68` (CONTRACT O6); their composition is not
implemented by these leaves. `empty`, `truncated` and `trailing` are model error
constructors for future wire work and are never produced by this slice. No new
outcome or host-depth policy follows (D14, Q20, O12).

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

### Remaining source ownership

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `utils/ssz.py::_SszType` | 32 | `SszType` (inductive) | marker base class |
| `utils/ssz.py::_Uint` | 38 | `SszType.uint` | widths 1..32 bytes |
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
| `forks/amsterdam/utils/address.py::compute_contract_address` | 42 | `computeContractAddress` | A1 |
| `forks/amsterdam/utils/address.py::compute_create2_contract_address` | 66 | `computeCreate2ContractAddress` | A2 |

`to_address_masked` from the same file is claimed by `EthBase` (a pure conversion). `encode_account` (in `fork_types.py`) is claimed by `EthStateCommit`; its state-dependent encoding remains outside EthCodec.

**External semantics.** This module must specify these libraries completely:
- `ethereum_rlp.rlp` (`encode`, `decode`, `decode_to`, `With`) and `ethereum_rlp.Extended`, as E1–E3 and D1r–D4r. `With` custom decoders are not used in Amsterdam decode sites; I checked with a grep.
- `remerkleable.basic`, `.byte_arrays.{ByteList, ByteVector}`, `.complex.{Container, List}`, `.progressive.{ProgressiveList, ProgressiveByteList, ProgressiveContainer}`, as S2–S6.
- `hashlib.sha256` via `EthHash`.

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
- **Property / differential tests.**
  - Random `RlpItem` round trip, and canonicality under mutation fuzzing.
  - Random well-typed SSZ values round trip.
  - SSZ mutation fuzzing comparing the strict decoder with "remerkleable decode plus re-encode check". This is differential only; the fixtures and the EELS source decide.

## 5. Interface

The namespace is `STFSpec.Codec`. All items are public unless marked internal.

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
class RlpDecode (α : Type) where ofRlp : RlpItem → Except RlpError α
-- instances: Nat, U256, U64, U32, U8, Bool, ByteArray, FixedBytes n, Address, Hash32, List α
def Rlp.encodeOf [RlpEncode α] (a : α) : ByteArray
def Rlp.decodeTo [RlpDecode α] (b : ByteArray) : Except RlpError α     -- decode then ofRlp

-- Derived addresses
def computeContractAddress (sender : Address) (nonce : Nat) : Address
def computeCreate2ContractAddress (sender : Address) (salt : Bytes32) (initCode : ByteArray) : Address
-- Query-generic forms (D5); the pure forms above are these at m := Id (definitional)
def computeContractAddressQ [Monad m] [KeccakQuery m] : Address → Nat → m Address
def computeCreate2ContractAddressQ [Monad m] [KeccakQuery m] :
    Address → Bytes32 → ByteArray → m Address     -- two queries: keccak initCode, then the preimage

-- SSZ
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
def SszType.WellFormed : SszType → Prop      -- widths ∈ {1,2,4,8,16,32}; active fields end in 1, count = #fields ≤ 256
def SszValue.WellTyped : SszType → SszValue → Prop   -- ranges, exact lengths, limits
def SszType.fixedSize? : SszType → Option Nat
inductive SszError where | length | offset | limit | boolByte | trailing | shape
namespace Ssz
  def encode : SszType → SszValue → ByteArray
  def decode : SszType → ByteArray → Except SszError SszValue          -- strict canonical
  def hashTreeRoot : SszType → SszValue → Bytes32
  def pack : ByteArray → Array Bytes32                                  -- internal
  def merkleize (chunks : Array Bytes32) (limit : Nat) : Bytes32        -- zero-hash padded
  def merkleizeProgressive (chunks : Array Bytes32) : Bytes32
  def mixInLength (root : Bytes32) (len : Nat) : Bytes32
  def mixInActiveFields (root : Bytes32) (active : List Bool) : Bytes32
  def zeroHashes : Array Bytes32                                        -- constant, depth 0..64
  def Rootable (t : SszType) (v : SszValue) : Prop -- actual schema interpretation and representable mix-in lengths
  def zeroHash : Nat → Bytes32    -- recurrence for every depth; array prefix is only an optimisation
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
| `SszType` | inductive | itself | `WellFormed` | immutable constant per schema | — |
| `SszValue` | nested inductive | itself; typed views via `SszSchema` | `WellTyped t v` | immutable | `encode`/`decode` O(n · type depth) |
| `zeroHashes` | `Array Bytes32` built once | `z₀ = 0^32`, `z_{i+1} = H(z_i, z_i)` | the recurrence | read-only constant (not a cache in the §7 sense) | O(1) lookup |
| merkleization | `Array Bytes32` layers | the full padded binary tree | — | local, linear | O(chunks) hashes + O(log limit) zero-hash lookups. **Never O(limit)**: `ByteList[2^16]` has 2048 chunk leaves, and `List[_, 256]` must not hash 256 leaves when it has 3 elements |

**No derived instances on the nested inductives** (F17). `deriving BEq`, `Repr` or `DecidableEq` on `RlpItem`, `SszType` or `SszValue` generates `partial` constants (for example `instBEqT.beq`), which D21 bans and only the compiled declaration check catches. Write structural instances by hand, as mutual structural recursions (a compiled prototype of the interfaces showed the pattern works). Non-nested types such as `RlpError` and `SszError` may derive them.

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

## 7. Contract and laws

**RLP.**
- [T] `decode` is total: well-founded recursion on the remaining byte count, where each item consumes at least one byte. It allocates nothing proportional to a *declared* length before checking that length against the input.
- [C] Round trip: `Encodable x → decode (encode x) = .ok x`.
- [C] **Canonicality:** `decode b = .ok x → Encodable x ∧ encode x = b`. Together with the round trip, `decode b = .ok x ↔ Encodable x ∧ encode x = b`. This is the Lean form of D1r.
- [C] **Injectivity and prefix-freeness:** `Encodable x ∧ Encodable y ∧ encode x ++ r = encode y ++ s → x = y ∧ r = s`. These feed [S]: witness and header binding under Keccak collision resistance.
- [C] Integer canonicality: `toNat (.bytes b) = .ok n ↔ b = (Uint.toBeBytes n).toByteArray`; `toNatBounded w` additionally requires `b.size ≤ w`.
- [R] Typed round trips for each instance: `Encodable (toRlp a) → decodeTo (encodeOf a) = .ok a` (where toRlp is the instance adapter). This is used by `EthBlock` (transaction, header and receipt codecs) and `EthStateCommit` (account leaves).
- [R] `union2 f g x = .ok a` implies that exactly one of `f x`, `g x` succeeds.

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
encoding model obligations only; the decoder-dependent contracts above remain open.

**Discharged raw decoder laws.** `decode_eq_model` preserves the whole result
including diagnostics and every nested child, with shared parser semantics as
specified in §3. `decode_window_model` observes exact clipped public byte windows.
`decode_empty`, `decode_single`/`decodeModel_single`,
`decodeModel_short_bytes`, `decodeModel_short_list_truncated/trailing` and
`decode_success_nonempty` establish their stated ordered cases/progress.
Private advancing header witnesses and validated window endpoints discharge
kernel termination of the raw parser. The [C] `Encodable` inverse, canonicality,
image and prefix-free/injective contracts above remain pending and unchanged.

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
zero-width acceptance (`toNatBounded_zero_iff`) and encoder roundtrip
(`toNat_ofNat`). Boolean, raw bytes, fixed length/byte observation and raw list
accept sets are `toBool_eq_ok_iff`, `toBytes_eq_ok_iff`, `toFixed_eq_ok_iff` and
`toList_eq_ok_iff`; `toFixed_eq_ok_item_iff` additionally pins model shape. `toFields_eq_ok_iff` preserves exactly the vector's ordered
fields; `toFields_wrong_arity` rejects before child typing. `union2_eq_ok_iff`
characterizes a sole success plus the other alternative's failure. These apply to
all model inputs, without wire-instance or child-schema claims. Integer
canonicality uses public Base fold/range/encoded-width and fixed-byte injectivity,
so it also proves the converse byte minimality rather than just value roundtrip.

**SSZ.**
- [T] `decode` is total: recursion on the type, with each sub-decode on a strictly smaller slice. Offsets are validated against the slice length before use.
- [C] Round trip: `WellTyped t v → (encode t v).size < 2^32 → decode t (encode t v) = .ok v`.
- [C] **Canonicality:** `decode t b = .ok v → WellTyped t v ∧ encode t v = b`. This theorem is the Lean replacement for EELS's re-encode check (`ssz.py:144`). It pins the accept set to the image of `encode`, which is exactly the set EELS accepts. That EELS's set is exactly the image of `encode` is itself a claim about the reference, argued in S3 and tested differentially.
- [T] `hashTreeRoot` must terminate, and its reference refinement requires the schema’s Rootable domain (length mix-ins fit uint256 and fields have the exact interpretation). O2 freedom requires proving every successfully decoded guest request belongs to that domain; S5 alone does not establish this.
- [C] `merkleize` with `zeroHashes` equals naive merkleization over the full power-of-two padding. `merkleizeProgressive` is characterised by the recurrence in S4.
- [C] Schema laws per `SszSchema α` instance: `valid a → ofValue? (toValue a) = some a ∧ WellTyped type (toValue a)`; conversely `WellTyped type v ∧ ofValue? v = some a → valid a ∧ toValue a = v`. This second direction prevents lossy schema conversions from changing the decoded request's commitment. The schema type itself is well formed.
- [S] **Binding:** on the actual guest schemas, with well-typed values, exact active-field interpretation and every length mix-in representable in uint256, equal `hashTreeRoot`s imply equal values or an explicit SHA-256 collision. This is the request-binding theorem of CONTRACT §7. Induct over the schema and Merkle tree: equal child preimages permit descent; unequal preimages with equal hash give the collision. Fixed widths and mixed-in lengths disambiguate padding. Extending this law to arbitrary `SszType` requires specifying inactive fields and the domain of unbounded progressive lengths; it is not asserted without those premises.

**Addresses.**
- [C] `computeContractAddress a n = lastBytes20 (keccak256 (encode (.list [.bytes a.toBytes, ofNat n])))`, and likewise for CREATE2. The `…Q` forms at `m := Id` equal these by `rfl`.

### Informal correctness argument

**Claim.** On the encodable domain, decoding accepts precisely the reference encodings, returns the same typed value or error, and the guest-schema roots use the specified Merkle layout.

**Premises.** EthBase/Hash laws, exact schema field order and widths, both directions of each schema adapter, representable offsets/length mix-ins, and a resolved policy for reference host-resource exceptions.

**Argument.** RLP prefix cases determine one extent; recurse only inside that extent and require full consumption. The shortest-length and integer checks give canonicality and prefix-freeness. Typed decoders then check constructor shape, arity and integer ranges. SSZ induction over types establishes fixed-size layouts and variable-offset boundaries; the strict decoder's accepted bytes must re-encode identically, while the reverse implication needs a separate proof that every canonical encoding decodes. The schema adapter transfers both results to the caller's type. Merkleization induction replaces padded subtrees with the zero-hash recurrence; progressive zero hashes are defined for every required depth, not just the cached prefix. Binding descends through equal child preimages; unequal preimages with equal digests expose a collision. Exact field interpretation and mixed-in lengths distinguish zero padding.

**Open obligations.** Rootability of every accepted guest input, unbounded progressive-length domains, RLP encodability of schema-produced items and all schema instances need proof. These domains must not become new acceptance limits without an explicit protocol decision. Generic inactive-field binding is not implied by the guest-schema result.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthHash`.
- **Used by:** `EthCommit` (node RLP), `EthVmInstructions` (CREATE/CREATE2 addresses), `EthBlock` (transaction/header/receipt RLP, withdrawal and request SSZ, BAL encoding), and transitively `EthStateCommit` (account leaf RLP), `EthStateWitness` and `EthStateless` (`StatelessInput` schema, output encoding, the request root).
- **Seams provided.** Generic RLP and SSZ with canonicality theorems. Schema owners write `SszSchema`/`RlpDecode` instances and prove only the per-instance schema laws. Contract-address derivation.
- **Cross-module invariants.** Consumers must decode with `decodeTo` (typed) wherever EELS uses `decode_to`, so that D2r stays unobservable. Schema owners must mirror `_infer` exactly: field order, widths, limits, and progressive versus plain types.
- **Implemented header premise.** The extent helper supplies suffix/window
  correspondence and positive declared extents. Full parsers must still check
  declared extents against the current parent window before reading payloads,
  apply canonical item checks, recurse and require full consumption.
- **Relies on.** `EthHash.sha256` and `keccak256`, and `EthBase` byte conversions (in particular `Uint.toBeBytes 0 = empty`).

## 9. Open decisions

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

- **Implemented slice and remaining APIs.** Raw `RlpItem`/diagnostic `RlpError`, the two-pass encoder/total byte model/`Encodable`, the cursor `decodeItemLength`/header model and the nine typed model adapters in §3 are implemented with the §7 public laws. Raw wire decode/list cursors and storage/window/ordered-case laws are implemented; universal RLP inverses/canonicality/prefix-freeness remain pending. `RlpEncode`/`RlpDecode` instances, `encodeOf`/`decodeTo`, element/schema decoders, SSZ and derived addresses are unimplemented. The `toList`/`toFields` leaves do not discharge child typing, and local diagnostic correspondence does not implement the consuming header/transaction handlers. Whole EthCodec gates, all schema proofs, security binding and cost/guest obligations remain open.

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **EIP cross-check missing.** The progressive merkleization order (subtree left, rest right) and the placement of the active-fields chunk were checked only against remerkleable, the pinned dependency. They have not been compared with EIP-7916 or EIP-7495 at the versions the fixtures were generated with. If they disagree, the fixtures still decide, but the discrepancy should be reported.
- **"EELS accepts exactly the image of `encode`" (S3)** is argued from the re-encode check. It is not proved for remerkleable's `decode_bytes`, which could raise (and so reject) on some canonical input. This is unlikely but unverified. The differential round-trip fuzzing should cover every Amsterdam schema, not only toy containers.
- **Wire RLP canonicality** remains a separate dependent proof obligation after the implemented total raw decoder/storage refinement. It has finite fuzz/differential evidence and no universal proof yet; the model integer-leaf minimality laws in §7 are discharged. The prefix-freeness proof strategy is standard, but it is unwritten in Lean.
- **D2r agreement** (deep nesting) is argued on the spec side. No fixture exercises it; it is tracked under DISC-001 (DECISIONS Q20), with probe `tx-deep-rlp-40000` as the reference-side reproducer. The claim that "no transaction schema nests more than about 4 levels" needs a check against every transaction type, including access lists, authorization lists and blob hashes. It also applies to the untyped `rlp.decode` sites (`incremental_mpt.py:936`, `witness_state.py:112,198`), which are protected only by the 2^10-byte node limit. That argument holds only if every such input comes from a bounded witness field. This is unverified for `witness_state.py:198`.
- **Thin O1 coverage.** The 9 fixtures do not test: `boolean` bytes other than 0 or 1, per-element `ByteList` limits (a 1025-byte witness node, a 65537-byte code), 257 headers, a wrong `public_keys` element length (65 bytes), an empty non-zero-scope list, or offsets ≥ 2^31. `#guard`s are proposed, but these cases lack fixtures.
- **SSZ encode partiality at 2^32** (S6) is stated but has no consumer theorem using the hypothesis. No `Envelope` field exists for it; by DECISIONS B6 one is added only when a named consumer theorem needs it (see `EthBase`).
- **The binding [S] proof** is sketched only. It needs an owner in `EthSecurity`, and the SHA-256 assumption for requests must be reconciled with the Keccak ROM (D5).
- **Schema fidelity.** Field order is checkable through `SszSchema.fieldNames` (F13): a prototype script outside this repository compared each adapter's names with REFERENCE-RECORDS. The core has no such check yet, and names alone do not check widths, limits or progressive versus plain types against `_infer`. The proposal for those is a `#guard` comparing `hashTreeRoot` of a sample value with a stored root generated from EELS; the generator script and stored roots do not exist yet.
- **Reference evidence:** the D1r fuzzing ran under 0.1.7 (byte-identical `rlp.py`); a rerun under the locked 0.1.6 would remove the version caveat.
- **Address derivation ownership.** Placing it here (not in `EthVmInstructions`) is a judgement call made in this spec, not an ARCHITECTURE decision.
- **Performance.** Encoder structural/generated-C checks and local compiled construction diagnostics are bounded evidence (§6); allocator volume, cleanup/lifetime and native-client/guest cost acceptance remain open. Raw `decode` has bounded local compiled whole-tree and decode/discard diagnostics (§6); allocator volume, native-client/guest costs and SSZ decoding of a maximal witness remain unmeasured.
- **The fixed-arity tuple laxity (D4r)** is deliberately not modelled. Any EELS change that introduces a fixed-arity RLP tuple target would silently diverge.
