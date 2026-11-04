#!/usr/bin/env -S uv run --no-project --python 3.12 python
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Remap EELS `file:line` citations across a re-pin, and check that none is left behind.

Usage:
  remap_citations.py --apply --initial --eels CLONE   first run, on a tree whose unmarked
                                                      citations are at the old commit
  remap_citations.py --apply [--drop-resolved SEL…] [--relist SEL DOC:LINE]… [--eels CLONE
                             [--confirm SEL…] [--since REV]]
  remap_citations.py --check [--eels CLONE]

CLONE is an execution-specs clone holding both commits: the old one (e1a316a0, kept in
STFSpec/informal/citation-remap.json after the first run) and reference.toml's commit.

Scope: STFSpec/informal/**/*.md (except CONTRACT.md and the generated GAPS.md and
REFERENCE-RECORDS.md) and the comments and docstrings of STFSpec/**/*.lean and
scripts/**/*.lean. Python docstrings (the conformance drivers) are out of scope. A citation is
- `path.py:N`, `path.py:A–B`, or a list of these separated by `, ` or `/`;
- a declared abbreviation (`st:N`, `inc:N`, `ws:N`, `mpt:N`), or `I/` for `vm/instructions/`;
- a bare `:N`, or `name:N` inside backticks, which takes the file named before it in its
  block (paragraph, list item, table row, heading, or paragraph of a comment) if there is
  exactly one (or several names of one file), or the document's declared default file if
  there is none. Otherwise its file must be identified by evidence: among the files named
  before it in its block (or, if none, earlier in its Markdown section), exactly one
  defines a function, class, method or constant that contains every cited line and is
  named like an identifier before it in its block (snake-cased; in a table row, also an
  upper-case word such as an opcode);
- the `Line` cell of a §3 `| EELS item | Line |` table, which takes its row's `file::name`.
`path::name` names no line; like any file name, it only sets the inherited file. A path
resolves as written from the repository root, then under the document's declared base
directories, then (if it has a directory) under `src/ethereum/`, then by unique suffix,
preferring `forks/amsterdam/`, then the non-fork modules. A basename matching both an
execution-specs file and a file of a locked dependency (LOCKED) is ambiguous; one matching
only the latter, or under a THIRD_PARTY prefix, is third-party. A name `X.py` matching
nothing is the one file `…_X.py` named earlier in its section, if there is exactly one. A
block that mentions the new commit (`59c1473d`) is marked: its citations are never touched.

Rules. A citation into a file that did not change between the commits is left alone (its
lines are identical), and so is a third-party citation, an explicit citation of a
non-Python file, and a bare citation whose candidate block files are all unchanged or
third-party. A citation into a changed file is rewritten only when every range lies within
the file and maps through the `git diff -U0` hunks with neither endpoint in a hunk and no
hunk inside the range, and the mapped lines at the new commit equal the cited lines at the
old one. A §3 `Line` cell holding just the definition line of its item is also mapped to
that item's definition line at the new commit (the inventory rule). Everything else is
listed with its reason in STFSpec/informal/citation-remap-manual.txt: citations into
changed files that do not map, any in a block that mentions only the old commit, names
that resolve to no execution-specs or locked dependency file, and bare citations that
inherit a non-execution-specs file or whose file cannot be determined. A listed citation
stays at the old commit until reviewed, even inside a marked block. A reason ending "on a
line with rewritten citations" marks a line that now mixes the two commits.

State. --initial reads every unmarked citation as at the old commit (the GAPS-CROSSCUTTING
X16 rule before the remap). After it, an unmarked and unlisted citation is at the new
commit, and the tool recognises a pre-remap citation only by its recorded context: each
rewrite is recorded in STFSpec/informal/citation-remap.json with a hash of its document and
of the citation with up to 48 characters on each side within its block, before and after
the rewrite. A pre-remap citation whose context was edited, or that was written afresh, is
not recognised. A branch cut before the remap must therefore, right after merging main and
with conflicted lines resolved to the branch's pre-remap numbers, run --apply --since REV
--eels CLONE with REV the merged main commit: every citation on a line changed since REV
is read as at the old commit, and the run refuses any that would be shifted twice: one
that is a recorded rewrite in its recorded new context, or one whose text is a recorded
rewrite's new text in that document and also occurs in the text its diff hunk replaced at
REV (so it came from main); both comparisons ignore range-dash and list-spacing style.

Each list entry keeps its document, line, text, file and a context hash, and names only an
occurrence with the same text, file and context hash; --apply then refreshes its line. Any
other occurrence, including a cosmetic edit of the citation or an edit within 48 characters
of it, does not match: the entry fails --apply and --check ("listed citation changed or
removed") until it is resolved explicitly. SEL is DOC:LINE as listed, or DOC:LINE:CONTEXT
(a prefix of the context hash) when several entries share a line. Each SEL may be named by
only one of these:
- --drop-resolved SEL drops an entry whose citation was fixed or removed (and refuses one
  that still occurs);
- --relist SEL DOC:LINE re-keys an entry whose citation is still at the old commit but was
  moved, edited around or reformatted: to the one occurrence on DOC:LINE (same document)
  with the same file and the same text up to range-dash and list-spacing style, at its
  current line and context. It refuses when there is no such occurrence or several, or
  when it is already listed, a recorded rewrite or confirmed;
- --confirm SEL (with --eels) drops an entry whose unchanged citation a reviewer confirms
  is already correct at the new commit, refusing one whose range lies outside the file
  there, and records it so that it is never listed again.
--relist works within one document; for a citation moved to another document, drop its
entry with --drop-resolved and read its new line with --since. --apply also refreshes the
line of each recorded rewrite and confirmation that is still in its recorded context (the
record's lines are informational: --check ignores line drift there as in the list, and a
recorded rewrite whose context was later edited keeps its last line). With --eels, --apply
also refreshes listed reasons.

--check fails when a recorded pre-remap citation occurs (it is auto-mappable and unmapped),
when a listed citation changed or no longer occurs, when the list or the record is not in
canonical form, or when the record maps to a commit other than reference.toml's. Listed
status is not itself a failure (the list is the recorded manual work), and line drift is
ignored.
Without a record (a tree not yet remapped) it fails, and with --eels reports every citation
that --apply --initial would rewrite. With --eels and a record it also recomputes each
recorded rewrite and confirmation from the two commits, requires every listed citation to
be still not auto-mappable, and requires every listed reason to be current. Without --initial and
--since, --apply needs no clone.
"""
import argparse, ast, collections, dataclasses, hashlib, json, pathlib, re, subprocess, sys, tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent
OLD_COMMIT = "e1a316a06fc3d3e0a5da36fdc78580811e9d8a36"   # tests-zkevm@v21.0.0
LEDGER = "STFSpec/informal/citation-remap.json"
MANUAL = "STFSpec/informal/citation-remap-manual.txt"
SKIP = {"STFSpec/informal/CONTRACT.md", "STFSpec/informal/GAPS.md", "STFSpec/informal/REFERENCE-RECORDS.md"}
THIRD_PARTY = ("ethereum_rlp/", "ethereum_types/", "remerkleable/", "py_ecc/", "Crypto/", "cryptography/",
               "spec256k1/", "coincurve/", "ckzg/", "eth_typing/", "site-packages/")
WINDOW = 48
AMSTERDAM = "src/ethereum/forks/amsterdam/"
# The Python files of the locked dependencies that documents cite by package path
# (reference.toml [release.python_dependencies]; listed from the wheels on PyPI, sha256
# ethereum_rlp-0.1.6 f4144caa…, ethereum_types-0.4.1 33de3e2a…, eth_remerkleable-0.1.31
# 7e48ea1b…, py_ecc-8.0.0 c0b2dfc4…). A path matching one of these and no execution-specs
# file is third-party; one matching neither is listed.
LOCKED = tuple(f"{pkg}/{name}.py" for pkg, names in {
    "ethereum_rlp": "__init__ exceptions rlp",
    "ethereum_types": "__init__ bytes enum frozen numeric",
    "remerkleable": "__init__ basic bitfields byte_arrays complex core history progressive readonly_iters settings "
                    "subtree test_arithmetic test_impl test_typing tree union virtual",
    "py_ecc": "__init__ typing utils bls/__init__ bls/ciphersuites bls/constants bls/g2_primitives bls/hash "
              "bls/hash_to_curve bls/point_compression bls/typing bls12_381/__init__ bls12_381/bls12_381_curve "
              "bls12_381/bls12_381_pairing bn128/__init__ bn128/bn128_curve bn128/bn128_pairing fields/__init__ "
              "fields/field_elements fields/field_properties fields/optimized_field_elements optimized_bls12_381/__init__ "
              "optimized_bls12_381/constants optimized_bls12_381/optimized_clear_cofactor optimized_bls12_381/optimized_curve "
              "optimized_bls12_381/optimized_pairing optimized_bls12_381/optimized_swu optimized_bn128/__init__ "
              "optimized_bn128/optimized_curve optimized_bn128/optimized_pairing secp256k1/__init__ secp256k1/secp256k1",
}.items() for name in names.split())
# EthVmInstructions declares `I/`; other documents use it too, so it resolves everywhere.
PREFIXES = {"I/": AMSTERDAM + "vm/instructions/"}

# Per-document path conventions, taken from each conventions line. `declares` must occur in
# the document's first 15 lines, so that a changed convention fails loudly.
DOCS = {
    "EthBase": dict(declares="Paths without a prefix are relative to `src/ethereum/`", bases=["src/ethereum/"]),
    "EthBlock": dict(declares="Line references are to `src/ethereum/forks/amsterdam/`", bases=[AMSTERDAM]),
    "EthCodec": dict(declares="Unprefixed paths are relative to `src/ethereum/`", bases=["src/ethereum/"]),
    "EthCommit": dict(declares="`mpt:` = `merkle_patricia_trie.py`, `inc:` = `forks/amsterdam/incremental_mpt.py`, "
                               "`ws:` = `forks/amsterdam/witness_state.py`",
                      abbrevs={"mpt": "src/ethereum/merkle_patricia_trie.py", "inc": AMSTERDAM + "incremental_mpt.py",
                               "ws": AMSTERDAM + "witness_state.py"}),
    "EthCurve": dict(declares="Line numbers without a\npath refer to `src/ethereum/crypto/elliptic_curve.py`",
                     bare="src/ethereum/crypto/elliptic_curve.py"),
    "EthFork": dict(declares="Line references are to `src/ethereum/forks/amsterdam/`", bases=[AMSTERDAM]),
    "EthHash": dict(declares="Paths are relative to `src/ethereum/`", bases=["src/ethereum/"]),
    "EthPairing": dict(declares="Line numbers without a path refer to `src/ethereum/crypto/kzg.py`",
                       bare="src/ethereum/crypto/kzg.py"),
    "EthPrecompiles": dict(declares="`src/ethereum/forks/amsterdam/vm/precompiled_contracts/` unless they start with `crypto/`,\n"
                                    "`vm/` or a package name; `vm/` means `src/ethereum/forks/amsterdam/vm/`",
                           bases=[AMSTERDAM + "vm/precompiled_contracts/", AMSTERDAM]),
    "EthState": dict(declares="`forks/amsterdam/state_tracker.py` abbreviated `st:`", bases=["src/ethereum/"],
                     abbrevs={"st": AMSTERDAM + "state_tracker.py"}),
    "EthStateWitness": dict(declares="`ws:` = `forks/amsterdam/witness_state.py`", abbrevs={"ws": AMSTERDAM + "witness_state.py"}),
    "EthStateless": dict(declares="Source references are to `src/ethereum/forks/amsterdam/`", bases=[AMSTERDAM]),
    "EthVmCore": dict(declares="relative to `src/ethereum/forks/amsterdam/vm/`", bases=[AMSTERDAM + "vm/"]),
    "EthVmInstructions": dict(declares="relative to `src/ethereum/forks/amsterdam/vm/` unless stated otherwise; "
                                       "`I/` abbreviates `instructions/`",
                              bases=[AMSTERDAM + "vm/"]),
    "EthVmRunner": dict(declares="relative to `src/ethereum/forks/amsterdam/vm/`", bases=[AMSTERDAM + "vm/"]),
}

SEG = r"\d+(?:\s*[–-]\s*\d+)?"
SEGS = rf"{SEG}(?:(?:\s*,\s*|/:?){SEG})*"
FILE_RE = re.compile(r"(?<![\w/.\-])((?:[\w.\-]+/)*[\w\-]+\.(?:py|lean|md|toml|json|txt|sh|yml|yaml))"
                     rf"(?:(::[\w.*]+)|:({SEGS})(?![\w:]))?")
ABBREV_RE = re.compile(rf"(?<![\w/.\-])(st|inc|ws|mpt):({SEGS})(?![\w:])")
SYMBOL_RE = re.compile(rf"`([A-Za-z_][\w.]*):({SEGS})`")
BARE_RE = re.compile(rf"(?:^|(?<=[\s`(])):({SEGS})(?![\w:\]])")
CELL_RE = re.compile(rf"^{SEGS}$")
RANGE_SEP = re.compile(r"\s*[–-]\s*")
LIST_TAIL_RE = re.compile(r"\s*,\s*\d")


class Fail(Exception):
    pass


@dataclasses.dataclass
class Cite:
    doc: str
    line: int                 # 1-based line in the document
    start: int                # column span of the citation in that line
    end: int
    kind: str                 # path, abbrev, bare, symbol, table, mention (a file name only)
    text: str                 # the citation as written
    path: str                 # the file named or inherited, as written ("" if none)
    segs: list                # [[(start, end, value)], ...]: one or two numbers per range
    block: int
    window: str = ""
    offset: int = 0           # start of the citation in its block's text
    marks: frozenset = frozenset()
    note: str = ""            # a parse problem that forces manual review
    item: str = ""            # table: the claimed item
    resolved: str = ""
    status: str = ""
    reason: str = ""
    new: list = None          # new values, one per number
    scope: str = ""           # bare without a single file: where its candidates come from (block, section)
    candidates: list = dataclasses.field(default_factory=list)   # bare: files named earlier in the block or section
    named: list = dataclasses.field(default_factory=list)        # files named before it in its section
    hints: set = dataclasses.field(default_factory=set)          # bare: identifiers before it in its block

    def numbers(self):
        return [n for s in self.segs for n in s]

    def replaced(self, line: str, offset: int = 0) -> str:
        for (s, e, _), v in sorted(zip(self.numbers(), self.new), reverse=True):
            line = line[:s - offset] + str(v) + line[e - offset:]
        return line

    def new_text(self) -> str:
        return self.replaced(self.text, self.start)

    def key(self):
        return (self.doc, self.text, self.path)


def cited_numbers(text: str) -> list[int]:
    """The line numbers of a citation as written (its trailing list of lines)."""
    return [int(n) for n in re.findall(r"\d+", re.search(rf"(?:^|:)({SEGS})$", text)[1])]


def cited_ranges(text: str) -> list[list[int]]:
    m = re.search(rf"(?:^|:)({SEGS})$", text)
    return [[n[2] for n in s] for s in segments(m[1], 0)]


def segments(text: str, offset: int) -> list:
    nums = [(offset + m.start(), offset + m.end(), int(m[0])) for m in re.finditer(r"\d+", text)]
    out, i = [], 0
    while i < len(nums):
        if i + 1 < len(nums) and RANGE_SEP.fullmatch(text[nums[i][1] - offset:nums[i + 1][0] - offset]):
            out.append([nums[i], nums[i + 1]]); i += 2
        else:
            out.append([nums[i]]); i += 1
    return out


# ----------------------------------------------------------------------------- scanning

def skip_string(text: str, i: int) -> int:
    """The index after the Lean string literal starting at text[i] == '"'. In an interpolated
    string (`s!"…"`, `m!"…"`, …) a `{…}` holds an expression, which may hold strings."""
    interpolated, j, n = i > 0 and text[i - 1] == "!", i + 1, len(text)
    while j < n and text[j] != '"':
        if text[j] == "\\":
            j += 2
        elif interpolated and text[j] == "{":
            depth, j = 1, j + 1
            while j < n and depth:
                if text[j] == '"':
                    j = skip_string(text, j); continue
                depth += {"{": 1, "}": -1}.get(text[j], 0)
                j += 1
        else:
            j += 1
    return j + 1


def lean_comment_mask(text: str) -> list[bool]:
    """For each character of a Lean source: is it inside a comment (delimiters included)?"""
    flags, i, n, depth = [False] * len(text), 0, len(text), 0
    while i < n:
        if depth:
            if text.startswith("/-", i):
                depth += 1; flags[i] = flags[i + 1] = True; i += 2
            elif text.startswith("-/", i):
                depth -= 1; flags[i] = flags[i + 1] = True; i += 2
            else:
                flags[i] = True; i += 1
            continue
        c = text[i]
        if text.startswith("--", i):
            while i < n and text[i] != "\n":
                flags[i] = True; i += 1
            continue
        if text.startswith("/-", i):
            depth = 1; flags[i] = flags[i + 1] = True; i += 2; continue
        prev = text[i - 1] if i else " "
        m = re.match(r'r(#*)"', text[i:i + 12])
        if m and not (prev.isalnum() or prev in "_.'"):
            j = text.find('"' + m[1], i + len(m[0]))
            i = n if j < 0 else j + 1 + len(m[1]); continue
        if c == '"':
            i = skip_string(text, i); continue
        if c == "«":
            j = text.find("»", i + 1)
            i = n if j < 0 else j + 1; continue
        if c == "'" and not (prev.isalnum() or prev in "_'.!?"):
            m = re.match(r"'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\\n])'", text[i:i + 14])
            if m:
                i += len(m[0]); continue
        i += 1
    return flags


def lean_scan_lines(text: str) -> tuple[list[str], list[int]]:
    """Comment-only lines (code blanked, columns kept) and a block id per line: one per
    paragraph of a comment (a run of `--` lines counts as one comment)."""
    flags = lean_comment_mask(text)
    masked = "".join(ch if f or ch == "\n" else " " for ch, f in zip(text, flags)).split("\n")
    ids, cid, open_block = [], 0, False
    for ln in masked:
        body = re.sub(r"/--|/-!|/-|-/|--", "", ln).strip()
        if not body:
            ids.append(0)
            if not ln.strip():
                open_block = False
            elif re.fullmatch(r"\s*(/--|/-!|/-|-/|--)*\s*", ln) and ("-/" in ln or "/-" in ln):
                open_block = False
            continue
        if not open_block:
            cid += 1
        ids.append(cid); open_block = not ln.rstrip().endswith("-/")
    return masked, ids


def md_blocks(lines: list[str]) -> list[int]:
    """Block id per line (0 for blank lines): paragraphs, list items (with their continuation
    lines and nested items), table rows and headings."""
    ids, cid, item_indent, prev_blank = [], 0, None, True
    for ln in lines:
        s = ln.strip()
        if not s:
            ids.append(0); prev_blank, item_indent = True, None; continue
        if s.startswith("|") or s.startswith("#"):
            cid += 1; ids.append(cid); prev_blank, item_indent = True, None; continue
        indent = len(ln) - len(ln.lstrip())
        if re.match(r"\s*(?:[-*+]|\d+\.)\s", ln) and (item_indent is None or indent <= item_indent):
            cid += 1; item_indent = indent
        elif prev_blank:
            cid += 1
        ids.append(cid); prev_blank = False
    return ids


def window_hash(doc: str, block: str, start: int, end: int) -> str:
    """The context of a citation: its document, and the citation with up to WINDOW
    characters on each side within its block, whitespace collapsed; the citation itself is
    delimited, so two citations sharing a window have different contexts."""
    parts = (block[max(0, start - WINDOW):start], block[start:end], block[end:end + WINDOW])
    w = "\1".join(" ".join(x.split()) for x in parts)
    return hashlib.sha256(f"{doc}\0{w}".encode()).hexdigest()[:20]


def scan_lines(doc: str, lines: list[str], blocks: list[int], conf: dict, sec3: set[int], md: bool) -> list[Cite]:
    """The citations of one document in reading order. A bare citation inherits the file named
    before it in its block when there is exactly one such file, or else (none) the document's
    declared default file. Otherwise it records candidates, the files named before it in its
    block or (none, Markdown) earlier in its section from the nearest heading on, and hints,
    the identifiers before it in its block; classify() accepts a candidate only on definition
    evidence."""
    abbrevs, ctx, out = conf.get("abbrevs", {}), {}, []
    section, before = [], collections.defaultdict(str)
    for idx, line in enumerate(lines):
        b = blocks[idx]
        if not b:
            continue
        is_row = md and line.startswith("|")
        if md and line.startswith("#"):
            section = []
        found, taken = [], []
        def free(m):
            return not any(s <= m.start() < e or m.start() <= s < m.end() for s, e in taken)
        def add(c, span):
            found.append(c); taken.append(span)
        if idx in sec3:
            row = re.match(r"^\|\s*(.*?)\s*\|\s*(.*?)\s*\|", line)
            claim = re.search(r"`([\w./]+\.py)::([\w.]+)`", row[1]) if row else None
            if claim:
                add(Cite(doc, idx + 1, row.start(1) + claim.start(1), row.start(1) + claim.end(), "mention", claim[0],
                         claim[1], [], b), (row.start(1), row.end(1)))
            if claim and re.search(r"\d", row[2]):
                c = Cite(doc, idx + 1, row.start(2), row.end(2), "table", row[2], "src/ethereum/" + claim[1],
                         segments(row[2], row.start(2)), b, item=claim[2])
                if not CELL_RE.match(row[2]):
                    c.note = "line cell is not a plain list of lines"
                add(c, (row.start(2), row.end(2)))
        for m in FILE_RE.finditer(line):
            if not free(m):
                continue
            if m[3]:
                c = Cite(doc, idx + 1, m.start(), m.end(), "path", m[0], m[1], segments(m[3], m.start(3)), b)
                if LIST_TAIL_RE.match(line, m.end()):
                    c.note = "followed by an unparsed `, N` list"
            else:
                c = Cite(doc, idx + 1, m.start(), m.end(), "mention", m[0], m[1], [], b)
            add(c, (m.start(), m.end()))
        for m in ABBREV_RE.finditer(line):
            if not free(m):
                continue
            c = Cite(doc, idx + 1, m.start(), m.end(), "abbrev", m[0], abbrevs.get(m[1], ""), segments(m[2], m.start(2)), b)
            if m[1] not in abbrevs:
                c.note = "abbreviation not declared by this document"
            elif LIST_TAIL_RE.match(line, m.end()):
                c.note = "followed by an unparsed `, N` list"
            add(c, (m.start(), m.end()))
        for m in SYMBOL_RE.finditer(line):
            if free(m):
                add(Cite(doc, idx + 1, m.start() + 1, m.end() - 1, "symbol", m[0][1:-1], "",
                         segments(m[2], m.start(2)), b), (m.start(), m.end()))
        for m in BARE_RE.finditer(line):
            if free(m):
                c = Cite(doc, idx + 1, m.start(), m.end(), "bare", m[0], "", segments(m[1], m.start(1)), b)
                if LIST_TAIL_RE.match(line, m.end()):
                    c.note = "followed by an unparsed `, N` list"
                add(c, (m.start(), m.end()))
        for c in sorted(found, key=lambda c: c.start):
            if c.kind in ("bare", "symbol"):
                named = list(dict.fromkeys(reversed(ctx.get(b, []))))
                c.path = named[0] if len(named) == 1 else "" if named else conf.get("bare", "")
                if not c.path and (named or md):
                    c.scope = "block" if named else "section"
                    c.candidates = named or list(dict.fromkeys(reversed(section)))
                    text = before[b] + line[:c.start]
                    c.hints = set(re.findall(r"`([A-Za-z_][\w.]*)", text))
                    if c.kind == "symbol":
                        c.hints.add(c.text.split(":")[0])
                    if is_row:
                        c.hints |= set(re.findall(r"\b[A-Z][A-Z0-9]+\b", text))
            elif c.path:
                ctx.setdefault(b, []).append(c.path)
            c.named = section + ctx.get(b, [])
            c.offset = len(before[b]) + c.start
            if c.kind != "mention":
                out.append(c)
        section += [c.path for c in sorted(found, key=lambda c: c.start) if c.path and c.kind not in ("bare", "symbol")]
        before[b] += line + "\n"
    for c in out:
        c.window = window_hash(doc, before[c.block], c.offset, c.offset + c.end - c.start)
    return out


def scan_doc(root: pathlib.Path, rel: str, marks: tuple[str, str], text: str = None) -> tuple[list[str], list[Cite], dict]:
    text = (root / rel).read_text() if text is None else text
    lines, conf, sec3 = text.split("\n"), {}, set()
    if rel.endswith(".md"):
        if rel.startswith("STFSpec/informal/modules/"):
            conf = DOCS.get(pathlib.Path(rel).stem, {})
        if conf and conf["declares"] not in "\n".join(lines[:15]):
            raise Fail(f"{rel}: the conventions line no longer declares {conf['declares']!r}")
        scan, blocks = lines, md_blocks(lines)
        in3 = header = False
        for k, ln in enumerate(lines):
            if ln.startswith("## "):
                in3, header = ln.startswith("## 3. "), False
            elif not ln.startswith("|"):
                header = False
            elif in3 and ln.startswith("| EELS item | Line |"):
                header = True
            elif header and not ln.startswith("|---"):
                sec3.add(k)
    else:
        scan, blocks = lean_scan_lines(text)
    block_marks = collections.defaultdict(set)
    for k, ln in enumerate(scan):
        for tag, commit in zip(("new", "old"), marks):
            if blocks[k] and commit in ln:
                block_marks[blocks[k]].add(tag)
    cites = scan_lines(rel, scan, blocks, conf, sec3, rel.endswith(".md"))
    for c in cites:
        c.marks = frozenset(block_marks.get(c.block, ()))
    return lines, cites, conf


def documents(root: pathlib.Path) -> list[str]:
    docs = list((root / "STFSpec/informal").rglob("*.md"))
    docs += [p for d in ("STFSpec", "scripts") for p in (root / d).rglob("*.lean") if ".lake" not in p.parts]
    return sorted(r for r in (p.relative_to(root).as_posix() for p in docs) if r not in SKIP)


# ----------------------------------------------------------------------------- the reference

def git(cwd, *args) -> str:
    return subprocess.run(["git", "-C", str(cwd), "-c", "core.quotepath=off", *args],
                          capture_output=True, text=True, check=True).stdout


def diff_text(cwd, *args) -> str:
    """`git diff -U0 args` with every option that could alter its lines fixed: no rename
    detection, external diff, textconv, colour or relative paths, and a/ b/ prefixes."""
    return git(cwd, "diff", "--no-renames", "--no-ext-diff", "--no-textconv", "--no-color", "--no-relative",
               "--src-prefix=a/", "--dst-prefix=b/", "-U0", *args)


def diff_hunks(cwd, *args):
    """(file, side, hunk header match) for `git diff -U0 args`, with prefixes and options fixed
    whatever the user's configuration; side is old (the a/ name) or new (the b/ name)."""
    out = diff_text(cwd, *args)
    old = new = None
    parsed = False
    for ln in out.split("\n"):
        if ln.startswith("diff --git "):
            old = new = None
        elif ln.startswith("--- "):
            old = ln[6:] if ln.startswith("--- a/") else None
        elif ln.startswith("+++ "):
            new = ln[6:] if ln.startswith("+++ b/") else None
            parsed = True
        elif ln.startswith("@@ "):
            m = re.match(r"@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@", ln)
            if not m:
                raise Fail(f"unparsed diff hunk header: {ln}")
            if old:
                yield old, "old", m
            if new:
                yield new, "new", m
    if out.strip() and not parsed:
        raise Fail("git diff output has no file headers")


class Eels:
    """The old and new commits of an execution-specs clone."""
    def __init__(self, clone: pathlib.Path, old: str, new: str):
        self.clone, self.old, self.new = clone, old, new
        for c in (old, new):
            if self.git("cat-file", "-t", c).strip() != "commit":
                raise Fail(f"{clone}: commit {c} is not present")
        self.files = [f for f in self.git("ls-tree", "-r", "--name-only", old).split("\n") if f.endswith(".py")]
        self.fileset = set(self.files)
        self.changed = {f for f in self.git("diff", "--no-renames", "--name-only", old, new).split("\n") if f.endswith(".py")}
        self.deleted = {f for f in self.git("diff", "--no-renames", "--name-only", "--diff-filter=D", old, new).split("\n") if f}
        self.hunks = collections.defaultdict(list)
        for f, side, m in diff_hunks(self.clone, "--diff-algorithm=myers", old, new, "--", "*.py"):
            if side == "old":
                self.hunks[f].append(tuple(int(m[k]) if m[k] is not None else 1 for k in (1, 2, 3, 4)))
        self._text, self._defs = {}, {}

    def git(self, *args) -> str:
        return git(self.clone, *args)

    def text(self, commit: str, f: str):
        """The lines of f at commit (None if absent), counted as git counts them."""
        if (commit, f) not in self._text:
            r = subprocess.run(["git", "-C", str(self.clone), "cat-file", "blob", f"{commit}:{f}"],
                               capture_output=True, text=True)
            lines = r.stdout.split("\n") if r.returncode == 0 else None
            if lines and lines[-1] == "":
                lines.pop()
            self._text[(commit, f)] = lines
        return self._text[(commit, f)]

    def spans(self, commit: str, f: str) -> list[tuple[str, int, int, int]]:
        """(inventory name, definition line, first line with decorators, last line) of every
        top-level function, class, method and constant, as scripts/gen_eels_inventory.py
        names them."""
        if (commit, f) not in self._defs:
            out, src = [], self.text(commit, f)
            def span(name, node):
                first = min([node.lineno] + [d.lineno for d in getattr(node, "decorator_list", [])])
                out.append((name, node.lineno, first, node.end_lineno))
            for node in ast.parse("\n".join(src)).body if src is not None else []:
                if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                    span(node.name, node)
                    for sub in node.body if isinstance(node, ast.ClassDef) else []:
                        if isinstance(sub, (ast.FunctionDef, ast.AsyncFunctionDef)):
                            span(f"{node.name}.{sub.name}", sub)
                elif isinstance(node, (ast.Assign, ast.AnnAssign)):
                    for t in node.targets if isinstance(node, ast.Assign) else [node.target]:
                        if isinstance(t, ast.Name):
                            span(t.id, node)
            self._defs[(commit, f)] = out
        return self._defs[(commit, f)]

    def defs(self, commit: str, f: str) -> dict:
        out = collections.defaultdict(list)
        for name, line, _, _ in self.spans(commit, f):
            out[name].append(line)
        return out

    def map_line(self, f: str, n: int):
        """The new line of old line n, or None if a hunk changes it."""
        delta = 0
        for os_, oc, _, nc in self.hunks[f]:
            if oc == 0:
                if n > os_:
                    delta += nc; continue
                break
            if n < os_:
                break
            if n <= os_ + oc - 1:
                return None
            delta += nc - oc
        return n + delta

    def touching(self, f: str, a: int, b: int) -> list[str]:
        out = []
        for os_, oc, _, nc in self.hunks[f]:
            if oc and not (os_ + oc - 1 < a or os_ > b):
                out.append(f"{os_}" if oc == 1 else f"{os_}–{os_ + oc - 1}")
            elif not oc and a <= os_ < b:
                out.append(f"an insertion after {os_}")
        return out

    def resolve(self, path: str, conf: dict, named=()) -> tuple[str, str, list[str]]:
        """(kind, file, candidates). kind is eels (file resolved), ambiguous (several
        execution-specs candidates), third-party (a THIRD_PARTY prefix, or a path of a locked
        dependency matching no execution-specs file), short (a name `X.py` for the one file
        `…_X.py` named in `named`), other-file (not Python) or unknown."""
        if not path.endswith(".py"):
            return "other-file", "", []
        if any(path.startswith(t) or "/" + t in path for t in THIRD_PARTY):
            return "third-party", "", []
        for pre, full in {**PREFIXES, **conf.get("prefixes", {})}.items():
            if path.startswith(pre):
                path = full + path[len(pre):]
        for base in [""] + conf.get("bases", []) + (["src/ethereum/"] if "/" in path else []):
            if base + path in self.fileset:
                return "eels", base + path, [base + path]
        cands = [f for f in self.files if f.endswith("/" + path)]
        if len(cands) > 1:
            for sub in ([f for f in cands if f.startswith(AMSTERDAM)],
                        [f for f in cands if f.startswith("src/ethereum/") and not f.startswith("src/ethereum/forks/")]):
                if sub:
                    cands = sub; break
        locked = [f for f in LOCKED if f == path or f.endswith("/" + path)]
        if cands and locked and "/" not in path:
            return "ambiguous", "", cands + locked
        if len(cands) == 1:
            return "eels", cands[0], cands
        if cands:
            return "ambiguous", "", cands
        if locked:
            return "third-party", "", []
        if "/" not in path:
            short = {f for n in named for k, f, _ in [self.resolve(n, conf)] if k == "eels"
                     and f.rsplit("/", 1)[-1].endswith("_" + path)}
            if len(short) == 1:
                return "short", short.pop(), []
        return "unknown", "", []


def _ambiguous_parent(self, path: str, conf: dict, named) -> tuple:
    """For a short name `X.py`: the file `…_X.py` named earlier whose path is ambiguous, with
    its candidates, if there is exactly one."""
    if "/" in path:
        return None
    hits = {}
    for n in named:
        k, _, cands = self.resolve(n, conf)
        if k == "ambiguous" and any(f.rsplit("/", 1)[-1].endswith("_" + path) for f in cands):
            hits[n] = cands
    return next(iter(hits.items())) if len(hits) == 1 else None


Eels.ambiguous_parent = _ambiguous_parent


def snake(name: str) -> set[str]:
    base = name.split(".")[-1].strip("_")
    return {base.lower(), re.sub(r"(?<=[a-z0-9])(?=[A-Z])", "_", base).lower()}


def attribute(c: Cite, eels: Eels, conf: dict) -> str:
    """The section file a bare citation refers to, on definition evidence: the one candidate
    with a definition, named like one of the hints, whose lines contain every cited range."""
    hints = set().union(*(snake(h) for h in c.hints)) if c.hints else set()
    matches = {}
    for raw in c.candidates:
        _, target, _ = eels.resolve(raw, conf, c.named)
        if not target or target in matches.values():
            continue
        for name, _, first, last in eels.spans(eels.old, target):
            if name.split(".")[-1].strip("_").lower() in hints and all(first <= s[0][2] and s[-1][2] <= last for s in c.segs):
                matches[raw] = target
                break
    if len(set(matches.values())) == 1:
        return next(iter(matches))
    where = ("its block names several files" if c.scope == "block" else "its block names no file") + \
        f" ({', '.join(c.candidates)}{'' if c.scope == 'block' else ' in its section'})"
    c.reason = (f"{where}; several define a nearby name around it: {', '.join(matches)}" if matches
                else f"{where}; none defines a nearby name around it")
    return ""


def classify(c: Cite, eels: Eels, conf: dict) -> None:
    """Classify c, read as at the old commit: marked, third-party, other-file (a cited
    non-Python file), unchanged, same, auto or manual (with a reason); for same and auto,
    c.new holds the new numbers."""
    raw, via = c.path, ""
    if not raw and c.scope == "block":
        # Several names for one file (a path and its short name) are one file.
        kinds = [eels.resolve(f, conf, c.named) for f in c.candidates]
        if all(k in ("eels", "short") for k, _, _ in kinds) and len({t for _, t, _ in kinds}) == 1:
            raw = c.candidates[0]
    if not raw and c.candidates:
        raw = attribute(c, eels, conf)
        via = f" (identified among its {c.scope}'s files)" if raw else ""
        if not raw and c.scope == "block":
            # Whichever block file it means, nothing changed: every candidate is an unchanged
            # execution-specs file or a third-party one.
            kinds = [eels.resolve(f, conf, c.named) for f in c.candidates]
            if all(k == "third-party" or (k in ("eels", "short", "ambiguous") and not any(f in eels.changed for f in cs + [t]))
                   for k, t, cs in kinds):
                c.status, c.reason = "unchanged", ""; return
    if not raw:
        c.status = "manual"
        c.reason = c.note or c.reason or "no file named earlier in its block"
        return
    kind, target, cands = eels.resolve(raw, conf, c.named)
    inherited = c.kind in ("bare", "symbol")
    if kind == "third-party":
        c.status = "third-party"; return
    if kind == "other-file" and not inherited:
        c.status = "other-file"; return
    if kind in ("other-file", "unknown"):
        c.status = "manual"
        parent = eels.ambiguous_parent(raw, conf, c.named) if kind == "unknown" else None
        if parent:
            c.reason = (f"{'inherits ' if inherited else ''}{raw}, a short name for {parent[0]}, which is ambiguous "
                        f"between {', '.join(parent[1])}")
        else:
            c.reason = (f"inherits {raw}, which is not an execution-specs file" if inherited
                        else f"{raw} names no execution-specs or locked dependency file")
        return
    if kind == "ambiguous":
        if any(f in eels.changed for f in cands):
            c.status, c.reason = "manual", "ambiguous path: " + ", ".join(cands)
        else:
            c.status = "unchanged"
        return
    if kind == "short":
        via += f" (short name for the file named earlier)"
    c.resolved = target
    if target not in eels.changed:
        c.status = "unchanged"; return
    short = target.removeprefix("src/ethereum/") + via
    if c.note:
        c.status, c.reason = "manual", c.note; return
    if "old" in c.marks:
        c.status, c.reason = "manual", f"its block mentions {eels.old[:8]}"; return
    if target in eels.deleted:
        c.status, c.reason = "manual", f"{short} is deleted at {eels.new[:8]}"; return
    old_text, new_text = eels.text(eels.old, target), eels.text(eels.new, target)
    problems, new = [], []
    for seg in c.segs:
        a, b = seg[0][2], seg[-1][2]
        span = f"{a}" if a == b else f"{a}–{b}"
        if b < a or a < 1 or b > len(old_text):
            problems.append(f"{span} is not a line range of the file"); continue
        touched = eels.touching(target, a, b)
        if touched:
            problems.append(f"{span} touches changed lines {', '.join(touched)}"); continue
        na, nb = eels.map_line(target, a), eels.map_line(target, b)
        if nb > len(new_text) or old_text[a - 1:b] != new_text[na - 1:nb]:
            raise Fail(f"{c.doc}:{c.line}: {c.text}: mapped text differs outside every hunk")
        new += [na, nb] if len(seg) == 2 else [na]
    if c.kind == "table" and len(c.segs) == 1 and len(c.segs[0]) == 1:
        line = c.segs[0][0][2]
        olddefs, newdefs = eels.defs(eels.old, target).get(c.item, []), eels.defs(eels.new, target).get(c.item, [])
        if olddefs == [line] and len(newdefs) == 1:
            if not problems and new != newdefs:
                raise Fail(f"{c.doc}:{c.line}: {c.item}: hunk mapping {new} and definition line {newdefs} disagree")
            if problems:
                c.reason, problems, new = "definition line of the item", [], newdefs
    if problems:
        c.status, c.reason = "manual", f"{short}: " + "; ".join(problems); return
    c.new = new
    c.status = "same" if new == [n[2] for n in c.numbers()] else "auto"


# ----------------------------------------------------------------------------- state files

def render_manual(entries: list[dict], old: str, new: str) -> str:
    head = [
        f"# Status: generated review list for the EELS citation remap {old[:8]} -> {new[:8]} (GAPS-CROSSCUTTING X16).",
        "# Generated by scripts/remap_citations.py --apply; do not edit by hand.",
        "# Citations into files changed between the two commits that the remap did not rewrite. Each stays",
        f"# at {old[:8]} until reviewed, even inside a block marked with a commit. An entry is tracked by",
        "# its text, file and context hash only: any edit to the citation or its context fails --check until",
        "# resolved per entry, with --apply --drop-resolved DOC:LINE (the citation was fixed or removed),",
        "# --apply --relist DOC:LINE DOC:NEWLINE (still old, but moved, edited around or reformatted) or",
        f"# --apply --confirm DOC:LINE (already correct at {new[:8]}; recorded and never relisted).",
        "# Entries whose reason is \"inherits … not an execution-specs file\" may be citations of other",
        "# files (for example evm-asm `ZiskAccel.lean` or Lean `Operations.lean`): confirm them.",
        "# Columns (tab-separated): document:line; citation as written; file it names or inherits, as",
        "# written ('-' if none); reason; context hash.",
    ]
    rows = sorted(entries, key=lambda e: (e["doc"], e["line"], e["text"], e["path"], e["window"]))
    return "\n".join(head + [f"{e['doc']}:{e['line']}\t{e['text']}\t{e['path'] or '-'}\t{e['reason']}\t{e['window']}"
                             for e in rows]) + "\n"


def parse_manual(text: str) -> list[dict]:
    out = []
    for ln in text.split("\n"):
        if ln and not ln.startswith("#"):
            loc, cite, path, reason, window = ln.split("\t")
            doc, line = loc.rsplit(":", 1)
            out.append(dict(doc=doc, line=int(line), text=cite, path="" if path == "-" else path, reason=reason,
                            window=window))
    return out


def render_ledger(ledger: dict) -> str:
    """The record, one rewrite per line."""
    head = {k: v for k, v in ledger.items() if k != "entries"}
    rows = sorted(ledger["entries"], key=lambda e: (e["doc"], e["line"], e["old"], e["window"]))
    body = ",\n".join("  " + json.dumps(e, ensure_ascii=False) for e in rows)
    return json.dumps(head, indent=1, ensure_ascii=False)[:-2] + ',\n "entries": [\n' + body + "\n ]\n}\n"


def changed_lines_since(root: pathlib.Path, rev: str) -> dict[str, dict[int, str]]:
    """For each file changed since rev, each changed line of the working tree mapped to the
    text its hunk replaced (the lines at rev)."""
    out, new, hunk = collections.defaultdict(dict), None, None
    out_text = diff_text(root, rev, "--")
    parsed = False
    for ln in out_text.split("\n"):
        if ln.startswith("diff --git "):
            new = hunk = None
        elif ln.startswith("+++ "):
            new, parsed = (ln[6:] if ln.startswith("+++ b/") else None), True
        elif ln.startswith("--- "):
            pass
        elif ln.startswith("@@ "):
            m = re.match(r"@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@", ln)
            if not m:
                raise Fail(f"unparsed diff hunk header: {ln}")
            s, k = int(m[3]), int(m[4]) if m[4] is not None else 1
            hunk = {"removed": []}
            if new:
                for n in range(s, s + k):
                    out[new][n] = hunk
        elif ln.startswith("-") and hunk is not None:
            hunk["removed"].append(ln[1:])
    if out_text.strip() and not parsed:
        raise Fail("git diff output has no file headers")
    return {f: {n: "\n".join(h["removed"]) for n, h in lines.items()} for f, lines in out.items()}


def verify_ledger(ledger: dict, eels: Eels) -> list[str]:
    errs = []
    for e in ledger.get("confirmed", []):
        lines = eels.text(eels.new, e["target"]) if e["target"] else []
        if e["target"] and any(r[-1] > len(lines or []) for r in cited_ranges(e["text"])):
            errs.append(f"{LEDGER}: confirmed {e['doc']}:{e['line']} {e['text']} lies outside {e['target']} at {eels.new[:8]}")
    for e in ledger["entries"]:
        where = f"{LEDGER}: {e['doc']}:{e['line']} {e['old']} -> {e['new']}"
        olds, news = cited_ranges(e["old"]), cited_ranges(e["new"])
        if [len(s) for s in olds] != [len(s) for s in news] or e["target"] not in eels.changed:
            errs.append(f"{where}: shape or target mismatch"); continue
        if e.get("item"):
            if eels.defs(eels.old, e["target"]).get(e["item"]) != olds[0] or \
                    eels.defs(eels.new, e["target"]).get(e["item"]) != news[0]:
                errs.append(f"{where}: not the definition line of {e['item']}")
            continue
        old_text, new_text = eels.text(eels.old, e["target"]), eels.text(eels.new, e["target"])
        for so, sn in zip(olds, news):
            a, b, na, nb = so[0], so[-1], sn[0], sn[-1]
            if eels.touching(e["target"], a, b) or (eels.map_line(e["target"], a), eels.map_line(e["target"], b)) != (na, nb) \
                    or b > len(old_text) or nb > len(new_text) or old_text[a - 1:b] != new_text[na - 1:nb]:
                errs.append(f"{where}: does not follow the hunks")
    return errs


MIXED = "; on a line with rewritten citations"


def match_entries(entries: list[dict], cites: list[Cite]) -> list:
    """The occurrence each list entry names, or None. A new entry (no context yet) names the
    occurrence on its line with its text and file; a recorded one names only an occurrence
    with its recorded context hash, text and file. Nothing else matches: an entry whose
    citation or context changed must be resolved explicitly."""
    used, result = set(), [None] * len(entries)
    for i in sorted(range(len(entries)), key=lambda i: not entries[i]["window"]):
        e = entries[i]
        cands = [k for k, c in enumerate(cites) if k not in used and c.text == e["text"] and c.path == e["path"]
                 and (c.window == e["window"] if e["window"] else c.line == e["line"])]
        if cands:
            k = min(cands, key=lambda k: abs(cites[k].line - e["line"]))
            used.add(k)
            result[i] = cites[k]
    return result


def normal(text: str) -> str:
    """Citation text with range dashes and list spacing normalised (`13-15, 17` = `13–15,17`)."""
    return re.sub(r"\s*,\s*", ",", re.sub(r"\s*[–-]\s*", "–", text))


def entry_id(e: dict) -> str:
    return f"{e['doc']}:{e['line']}:{e['window'][:8]}"


def select_entries(selectors: list[str], entries: list[dict], option: str) -> list[dict]:
    """The list entries named by DOC:LINE or DOC:LINE:CONTEXT (a prefix of the context hash);
    each must name exactly one entry."""
    out = []
    for sel in selectors or []:
        m = re.fullmatch(r"(.+?):(\d+)(?::([0-9a-f]+))?", sel)
        if not m:
            raise Fail(f"{option} {sel}: expected DOC:LINE or DOC:LINE:CONTEXT")
        hits = [e for e in entries if e["doc"] == m[1] and e["line"] == int(m[2]) and e["window"].startswith(m[3] or "")]
        if len(hits) != 1:
            raise Fail(f"{option} {sel}: names {len(hits)} list entries; use " +
                       (", ".join(entry_id(e) for e in hits) if hits else "an entry's DOC:LINE as listed"))
        out.append(hits[0])
    return out


def run(args, quiet: bool = False) -> int:
    root = args.root.resolve()
    new = tomllib.loads((root / "reference.toml").read_text())["release"]["commit"]
    ledger_path, manual_path = root / LEDGER, root / MANUAL
    ledger = json.loads(ledger_path.read_text()) if ledger_path.exists() else None
    old = ledger["old"] if ledger else args.old
    if ledger and ledger["new"] != new:
        print(f"{LEDGER} maps to {ledger['new'][:8]}, but reference.toml pins {new[:8]}: remap for the new pin")
        return 1
    if args.initial and ledger:
        raise Fail(f"--initial: {LEDGER} exists, so the tree has already been remapped")
    if args.apply and not args.initial and not ledger:
        raise Fail(f"no {LEDGER}: pass --initial to remap a tree whose unmarked citations are at {old[:8]}")
    initial = args.initial or (args.check and not ledger)
    if (initial or args.since) and not args.eels:
        raise Fail("this mode needs --eels CLONE")
    eels = Eels(args.eels.resolve(), old, new) if args.eels else None
    since = changed_lines_since(root, args.since) if args.since else {}
    listed = parse_manual(manual_path.read_text()) if manual_path.exists() else []
    listed_keys = {(e["doc"], e["text"], e["path"]) for e in listed}
    recorded, recorded_new = (collections.defaultdict(lambda: collections.defaultdict(set)) for _ in range(2))
    new_texts = collections.defaultdict(set)
    for e in (ledger or {}).get("entries", []):
        recorded[e["doc"]][e["window"]].add((e["old"], e["new"]))
        recorded_new[e["doc"]][e["new_window"]].add(e["new"])
        new_texts[e["doc"]].add(normal(e["new"]))
    confirmed = {(e["doc"], e["window"], e["text"], e["path"]) for e in (ledger or {}).get("confirmed", [])}
    drop = select_entries(args.drop_resolved, listed, "--drop-resolved")
    confirm = select_entries(args.confirm, listed, "--confirm")
    if confirm and not eels:
        raise Fail("--confirm needs --eels CLONE, to check the citation against the new commit")
    relist = {}
    for sel, place in args.relist or []:
        e = select_entries([sel], listed, "--relist")[0]
        m = re.fullmatch(r"(.+?):(\d+)", place)
        if not m or m[1] != e["doc"]:
            raise Fail(f"--relist {sel} {place}: the occurrence must be DOC:LINE in {e['doc']}")
        relist[id(e)] = int(m[2])
    chosen = [id(e) for e in drop] + [id(e) for e in confirm] + list(relist)
    if len(chosen) != len(set(chosen)):
        raise Fail("an entry can be named only once across --drop-resolved, --confirm and --relist")
    fresh_confirmed = []
    failures, stats, fresh_manual, fresh_ledger, edits = [], collections.Counter(), [], [], {}
    restored, finals = collections.Counter(), {}
    for rel in documents(root):
        lines, cites, conf = scan_doc(root, rel, (new[:8], old[:8]))
        rewrites, doc_manual = [], []
        for c in cites:
            hit = {n for o, n in recorded[rel].get(c.window, ()) if o == c.text}
            in_since = c.line in since.get(rel, ())
            if in_since and (c.text in recorded_new[rel].get(c.window, ())
                             or normal(c.text) in new_texts[rel] and normal(c.text) in normal(since[rel][c.line])):
                failures.append(f"{rel}:{c.line}: {c.text} is a recorded rewrite, already at {new[:8]} (its context or "
                                f"the text it replaced at {args.since} has it); on a conflicted line keep the branch's "
                                "pre-remap numbers, then rerun --since")
                continue
            as_old = initial or in_since or bool(hit)
            if not as_old:
                continue
            if not hit and (rel, c.window, c.text, c.path) in confirmed:
                stats[(c.kind, "confirmed")] += 1; continue
            if "new" in c.marks:
                stats[(c.kind, "marked")] += 1; continue
            if eels:
                classify(c, eels, conf)
            if hit:
                if len(hit) > 1:
                    failures.append(f"{rel}:{c.line}: {c.text}: its recorded context maps to {sorted(hit)}"); continue
                target = next(iter(hit))
                if eels and (c.status != "auto" or c.new_text() != target):
                    failures.append(f"{rel}:{c.line}: {c.text}: recorded as -> {target}, recomputed as {c.status}"); continue
                c.new = cited_numbers(target)
                if len(c.new) != len(c.numbers()):
                    failures.append(f"{rel}:{c.line}: {c.text}: recorded replacement {target} has another shape"); continue
                c.status = "recorded"
            stats[(c.kind, c.status)] += 1
            if c.status in ("auto", "recorded"):
                rewrites.append(c)
            elif c.status == "manual":
                doc_manual.append(c)
        # A rewrite must not produce a citation that reads as a listed one.
        manual_texts = {(d, normal(x), q) for d, x, q in {m.key() for m in doc_manual} | listed_keys if d == rel}
        for c in list(rewrites):
            if c.status == "auto" and (rel, normal(c.new_text()), c.path) in manual_texts:
                rewrites.remove(c); doc_manual.append(c)
                c.status, c.reason = "manual", "rewriting it would make it read as a listed citation"
                stats[(c.kind, "auto")] -= 1; stats[(c.kind, "manual")] += 1
        mixed = {c.line for c in rewrites}
        fresh_manual += [dict(doc=rel, line=c.line, text=c.text, path=c.path, window="",
                              reason=c.reason + (MIXED if c.line in mixed else "")) for c in doc_manual]
        if rewrites and args.check:
            failures += [f"{rel}:{c.line}: {c.text} is at {old[:8]} and auto-mappable to {c.new_text()}; run --apply"
                         for c in rewrites]
        if rewrites:
            out = list(lines)
            for c in sorted(rewrites, key=lambda c: (c.line, -c.start)):
                out[c.line - 1] = c.replaced(out[c.line - 1])
                restored[rel] += c.status == "recorded"
                if c.status == "auto":
                    fresh_ledger.append(dict(doc=rel, line=c.line, target=c.resolved, kind=c.kind, old=c.text,
                                             new=c.new_text(), window=c.window, new_window="",
                                             **({"item": c.item} if c.reason == "definition line of the item" else {})))
            edits[rel] = "\n".join(out)
    # The list and the record against the final text.
    by_doc = collections.defaultdict(list)
    for k, e in enumerate(listed + fresh_manual):
        by_doc[e["doc"]].append(k)
    entries, keep = listed + fresh_manual, []
    fresh_by_doc = collections.defaultdict(list)
    for e in fresh_ledger:
        fresh_by_doc[e["doc"]].append(e)
    recorded_by_doc = collections.defaultdict(list)
    for e in (ledger or {}).get("entries", []) + (ledger or {}).get("confirmed", []):
        recorded_by_doc[e["doc"]].append(e)
    for rel in sorted(set(by_doc) | set(fresh_by_doc) | set(recorded_by_doc)):
        text = edits.get(rel)
        if text is None:
            if not (root / rel).exists():
                matched = [None] * len(by_doc[rel])
                cites, conf = [], {}
            else:
                text = (root / rel).read_text()
        if text is not None:
            _, cites, conf = scan_doc(root, rel, (new[:8], old[:8]), text)
            matched = match_entries([entries[k] for k in by_doc[rel]], cites)
        for e in fresh_by_doc[rel]:
            found = [c for c in cites if c.line == e["line"] and c.text == e["new"]]
            e["new_window"] = found[0].window
        # The record's lines are refreshed like the list's: a recorded rewrite (or confirmation)
        # still in its recorded context gets its current line; one whose context was edited
        # keeps its last line.
        if args.apply:
            seen = set()
            for e in recorded_by_doc[rel]:
                text_, window = (e["new"], e["new_window"]) if "new" in e else (e["text"], e["window"])
                cands = [c for c in cites if id(c) not in seen and c.text == text_ and c.window == window]
                if cands:
                    c = min(cands, key=lambda c: abs(c.line - e["line"]))
                    seen.add(id(c))
                    e["line"] = c.line
        taken = {id(c) for c in matched if c is not None}
        for k, c in zip(by_doc[rel], matched):
            e = entries[k]
            named = f"{entry_id(e)} `{e['text']}` (file {e['path'] or '-'})"
            if c is not None and id(e) in relist:
                failures.append(f"--relist {entry_id(e)}: {named} still occurs unchanged; there is nothing to relist")
            if c is None and id(e) in relist:
                line = relist[id(e)]
                cands = [o for o in cites if o.line == line and o.path == e["path"] and normal(o.text) == normal(e["text"])]
                problem = ("no occurrence with its text and file on that line" if not cands else
                           "several occurrences with its text and file on that line" if len(cands) > 1 else
                           "that occurrence is already listed" if id(cands[0]) in taken else
                           "that occurrence's text is a recorded rewrite's new text in this document"
                           if normal(cands[0].text) in new_texts[rel] else
                           "that occurrence is confirmed" if (rel, cands[0].window, cands[0].text, cands[0].path)
                           in confirmed else "")
                if problem:
                    failures.append(f"--relist {entry_id(e)} {rel}:{line}: {problem}")
                    keep.append(e)
                    continue
                c = cands[0]
                taken.add(id(c))
                print(f"relisted {named} at {rel}:{c.line} `{c.text}`")
            if c is None:
                if any(e is d for d in drop):
                    print(f"dropped resolved entry {named}")
                elif e in listed:
                    twins = [entry_id(x) for x in listed if x is not e and x["doc"] == e["doc"]
                             and (x["window"], x["text"], x["path"]) == (e["window"], e["text"], e["path"])]
                    which = (f"one of the indistinguishable entries {', '.join([entry_id(e)] + twins)} (same "
                             f"text, file and context) `{e['text']}`" if twins else named)
                    failures.append(f"{MANUAL}: listed citation changed or removed: {which}; resolve explicitly: "
                                    f"restore it; --apply --relist {entry_id(e)} DOC:LINE if it is unchanged at "
                                    f"another line or context; or --apply --drop-resolved {entry_id(e)} if it was "
                                    "fixed or removed")
                    keep.append(e)
                continue
            if any(e is d for d in drop):
                failures.append(f"--drop-resolved {entry_id(e)}: {named} still occurs unchanged; if it is already "
                                f"correct at {new[:8]}, use --confirm")
            if any(e is d for d in confirm):
                classify(c, eels, conf)
                outside = [f"{s[0][2]}–{s[-1][2]}" for s in c.segs
                           if c.resolved and s[-1][2] > len(eels.text(eels.new, c.resolved) or [])]
                if outside:
                    failures.append(f"--confirm {entry_id(e)}: {named}: {', '.join(outside)} lies outside "
                                    f"{c.resolved} at {new[:8]}")
                else:
                    print(f"confirmed at {new[:8]}: {named}")
                    fresh_confirmed.append(dict(doc=e["doc"], line=c.line, text=e["text"], path=e["path"],
                                                window=c.window, target=c.resolved))
                    continue
            if eels and not initial and not since:
                classify(c, eels, conf)
                base = e["reason"].removesuffix(MIXED)
                if c.status in ("auto", "same") and not (c.status == "auto" and (rel, c.new_text(), c.path) in listed_keys):
                    failures.append(f"{rel}:{c.line}: listed citation {c.text} is auto-mappable to {c.new_text()}")
                elif c.status == "manual" and c.reason != base and base != "rewriting it would make it read as a listed citation":
                    if args.check:
                        failures.append(f"{MANUAL}: {rel}:{e['line']} {e['text']}: reason is now {c.reason!r}; run --apply --eels")
                    else:
                        e["reason"] = c.reason + (MIXED if e["reason"].endswith(MIXED) else "")
            if args.apply:
                e.update(window=c.window, line=c.line, text=c.text)
            keep.append(e)
    if args.check:
        if ledger and eels:
            failures += verify_ledger(ledger, eels)
        if manual_path.exists() and manual_path.read_text() != render_manual(listed, old, new):
            failures.append(f"{MANUAL} is not in canonical form; run --apply")
        if ledger and ledger_path.read_text() != render_ledger(dict(ledger)):
            failures.append(f"{LEDGER} is not in canonical form; run --apply")
        if not ledger:
            failures.append(f"no {LEDGER}: the tree has not been remapped")
        if failures or not quiet:
            print("\n".join(failures + ([] if quiet else summary(stats, keep))))
        if not quiet or failures:
            print("remap_citations --check: " + (f"{len(failures)} problems" if failures else "ok"))
        return 1 if failures else 0
    if failures:
        print("\n".join(failures)); return 1
    for rel, after in edits.items():
        require_comment_only(rel, (root / rel).read_text(), after)
        (root / rel).write_text(after)
    led = ledger or {"generated_by": "scripts/remap_citations.py --apply --initial", "old": old, "new": new,
                     "window": WINDOW, "entries": []}
    led = {**led, "entries": list(led["entries"])}
    led["entries"] += fresh_ledger
    if fresh_confirmed or "confirmed" in led:
        led["confirmed"] = sorted(led.get("confirmed", []) + fresh_confirmed,
                                  key=lambda e: (e["doc"], e["line"], e["text"], e["window"]))
    ledger_path.write_text(render_ledger(led))
    manual_path.write_text(render_manual(keep, old, new))
    print("\n".join(summary(stats, keep)))
    print(f"rewrote {len(fresh_ledger)} citations and restored {sum(restored.values())} recorded rewrites "
          f"in {len(edits)} files; {len(keep)} listed for manual review")
    # A rewritten citation whose new context equals a recorded old one would be read back as
    # pre-remap; the result must pass the offline check.
    again = argparse.Namespace(**{**vars(args), "apply": False, "check": True, "initial": False, "since": None,
                                  "eels": None, "drop_resolved": None, "confirm": None, "relist": None})
    if run(again, quiet=True):
        raise Fail("the rewritten tree fails --check (a context collision?); see the output above")
    return 0


def require_comment_only(rel: str, before: str, after: str) -> None:
    """A rewrite of a Lean file may change only comment text."""
    if rel.endswith(".lean"):
        code = lambda t: "".join(ch for ch, f in zip(t, lean_comment_mask(t)) if not f)
        if code(before) != code(after):
            raise Fail(f"{rel}: the rewrite would change text outside comments")


def summary(stats, entries) -> list[str]:
    return [f"  {kind:8} {status:12} {n}" for (kind, status), n in sorted(stats.items()) if n] \
        + [f"  listed for manual review: {len(entries)}"]


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument("--apply", action="store_true", help="rewrite citations and update the list and the record")
    g.add_argument("--check", action="store_true", help="fail if --apply would rewrite anything or the list is stale")
    p.add_argument("--initial", action="store_true", help="read every unmarked citation as at the old commit")
    p.add_argument("--eels", type=pathlib.Path, help="execution-specs clone holding both commits")
    p.add_argument("--since", metavar="REV", help="read citations on lines changed since REV as at the old commit")
    p.add_argument("--drop-resolved", nargs="+", metavar="DOC:LINE[:CONTEXT]",
                   help="drop these list entries: their citation was fixed or removed")
    p.add_argument("--confirm", nargs="+", metavar="DOC:LINE[:CONTEXT]",
                   help="drop these list entries and record them as already correct at the new commit (needs --eels)")
    p.add_argument("--relist", nargs=2, action="append", metavar=("DOC:LINE[:CONTEXT]", "DOC:LINE"),
                   help="re-key a list entry to its unchanged citation at that line (in the same document)")
    p.add_argument("--old", default=OLD_COMMIT, help=argparse.SUPPRESS)
    p.add_argument("--root", type=pathlib.Path, default=ROOT, help=argparse.SUPPRESS)
    args = p.parse_args()
    if args.check and (args.initial or args.since or args.drop_resolved or args.confirm or args.relist):
        p.error("--initial, --since, --drop-resolved, --confirm and --relist are --apply options")
    try:
        return run(args)
    except Fail as e:
        print(e)
        return 1


if __name__ == "__main__":
    sys.exit(main())
