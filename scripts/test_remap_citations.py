#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Regressions for scripts/remap_citations.py on a synthetic execution-specs history and a
synthetic document tree; never touch the working repository. Git runs with no user or
system configuration, so the results do not depend on the host."""
import json
import os
import pathlib
import subprocess
import sys
import tempfile
import textwrap
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent
TOOL = ROOT / "scripts/remap_citations.py"
sys.path.insert(0, str(ROOT / "scripts"))
import remap_citations as R  # noqa: E402

AMS = "src/ethereum/forks/amsterdam/"
FORK, G1, GONE = AMS + "fork.py", AMS + "bls_g1.py", AMS + "gone.py"
VM_GAS, OSAKA_GAS = AMS + "vm/gas.py", "src/ethereum/forks/osaka/vm/gas.py"
VM_EXC, AMS_EXC = AMS + "vm/exceptions.py", AMS + "exceptions.py"
VMCORE_HEAD = ("# EthVmCore\n\n*Status: test.*\n\nPaths in `file:line` references are relative to "
               "`src/ethereum/forks/amsterdam/vm/` unless they start with another directory.\n\n")


def fork_source(new: bool) -> str:
    """40 lines. The new version inserts three lines at the top, changes line 20 and the
    definition line 25, and inserts two lines after line 30."""
    lines = [f"# line {k}" for k in range(1, 41)]
    lines[4] = "def check(tx: int) -> None:"          # 5
    lines[5] = "    return None"                      # 6
    lines[24] = "def settle(a: int) -> int:"          # 25
    lines[25] = "    return a"                         # 26
    if new:
        lines[19] = "# line 20, changed"
        lines[24] = "def settle(a: int, b: int) -> int:"
        lines = ["# new 1", "# new 2", "# new 3"] + lines[:30] + ["# inserted 1", "# inserted 2"] + lines[30:]
    return "\n".join(lines) + "\n"


def numbered(n: int, top: bool = False) -> str:
    return ("# new top\n" if top else "") + "".join(f"# l {k}\n" for k in range(1, n + 1))


class RemapCitations(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix="stfspec-remap-")
        self.addCleanup(temp.cleanup)
        base = pathlib.Path(temp.name)
        self.eels, self.root, self.gitconfig = base / "eels", base / "root", base / "gitconfig"
        self.gitconfig.write_text("")
        self.env = {**os.environ, "GIT_CONFIG_GLOBAL": str(self.gitconfig), "GIT_CONFIG_NOSYSTEM": "1",
                    "GIT_CONFIG_SYSTEM": os.devnull, "HOME": str(base)}
        self.eels.mkdir()
        self.git(self.eels, "init", "-q")
        files = {FORK: fork_source(False), G1: fork_source(False), GONE: numbered(10),
                 VM_GAS: numbered(40), OSAKA_GAS: numbered(40), VM_EXC: numbered(20), AMS_EXC: numbered(20),
                 "src/ethereum/state.py": numbered(40), "src/ethereum/utils/bytes.py": numbered(20),
                 AMS + "vm/bls12_381_pairing.py": numbered(20)}
        for path, text in files.items():
            (self.eels / path).parent.mkdir(parents=True, exist_ok=True)
            (self.eels / path).write_text(text)
        self.git(self.eels, "add", "-A"); self.git(self.eels, "commit", "-qm", "old")
        self.old = self.git(self.eels, "rev-parse", "HEAD")
        (self.eels / FORK).write_text(fork_source(True))
        (self.eels / G1).write_text(fork_source(True))
        (self.eels / VM_GAS).write_text(numbered(40, top=True))
        (self.eels / VM_EXC).write_text(numbered(20, top=True))
        (self.eels / "src/ethereum/utils/bytes.py").write_text(numbered(20, top=True))
        self.git(self.eels, "rm", "-q", GONE)
        self.git(self.eels, "commit", "-qam", "new")
        self.new = self.git(self.eels, "rev-parse", "HEAD")
        (self.root / "STFSpec/informal/modules").mkdir(parents=True)
        (self.root / "reference.toml").write_text(f'[release]\ncommit = "{self.new}"\n')

    def git(self, cwd, *args):
        return subprocess.run(["git", "-C", str(cwd), "-c", "user.name=t", "-c", "user.email=t@t",
                               "-c", "commit.gpgsign=false", *args],
                              capture_output=True, text=True, check=True, env=self.env).stdout.strip()

    def doc(self, body: str, path="STFSpec/informal/NOTES.md"):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(textwrap.dedent(body).replace("OLD8", self.old[:8]).replace("NEW8", self.new[:8]))
        return target

    def tool(self, *args, ok=True, eels=True):
        cmd = [sys.executable, "-I", str(TOOL), "--root", str(self.root), "--old", self.old, *args]
        if eels:
            cmd += ["--eels", str(self.eels)]
        r = subprocess.run(cmd, capture_output=True, text=True, env=self.env)
        (self.assertEqual if ok else self.assertNotEqual)(r.returncode, 0, r.stdout + r.stderr)
        return r.stdout + r.stderr

    def manual(self):
        return (self.root / R.MANUAL).read_text()

    def edit_state(self, path, transform):
        target = self.root / path
        target.write_text(transform(target.read_text()))

    # ------------------------------------------------------------------ mapping rules

    def test_shifted_lines(self):
        d = self.doc("""\
            One (`forks/amsterdam/fork.py:10`), a list `fork.py:8, 12–14` and a slash pair `fork.py:30/:31`.
            """)
        out = self.tool("--check", ok=False)
        self.assertIn("auto-mappable to forks/amsterdam/fork.py:13", out)
        self.tool("--apply", "--initial")
        self.assertIn("`forks/amsterdam/fork.py:13`", d.read_text())
        self.assertIn("`fork.py:11, 15–17`", d.read_text())
        self.assertIn("`fork.py:33/:36`", d.read_text())
        self.tool("--check")
        self.tool("--check", eels=False)

    def test_ranges_and_changed_hunks(self):
        d = self.doc("""\
            Across (`fork.py:18–22`), at (`fork.py:20`), beside (`fork.py:21`).

            Around an insertion (`fork.py:29–31`); up to it (`fork.py:29–30`); after it (`fork.py:31–32`).

            Last line (`fork.py:40`); past the end (`fork.py:41`), (`fork.py:39–41`).
            """)
        self.tool("--apply", "--initial")
        lines = d.read_text().split("\n")
        self.assertEqual(lines[0], "Across (`fork.py:18–22`), at (`fork.py:20`), beside (`fork.py:24`).")
        self.assertEqual(lines[2], "Around an insertion (`fork.py:29–31`); up to it (`fork.py:32–33`); "
                                   "after it (`fork.py:36–37`).")
        self.assertEqual(lines[4], "Last line (`fork.py:45`); past the end (`fork.py:41`), (`fork.py:39–41`).")
        listed = self.manual()
        self.assertIn("18–22 touches changed lines 20", listed)
        self.assertIn("20 touches changed lines 20", listed)
        self.assertIn("29–31 touches changed lines an insertion after 30", listed)
        self.assertIn("41 is not a line range of the file", listed)
        self.assertIn("39–41 is not a line range of the file", listed)
        self.tool("--check")

    def test_deleted_files(self):
        self.doc("Gone (`gone.py:3`).\n")
        self.tool("--apply", "--initial")
        self.assertIn(f"gone.py is deleted at {self.new[:8]}", self.manual())

    def test_bare_continuations(self):
        d = self.doc("""\
            Named (`fork.py:10`), then (`:12`) and (`:20`).

            No file in this paragraph (`:12`).

            Only an unchanged file `state.py:3` here, then (`:12`).

            Two files `state.py:3` and `fork.py:2`, then a bare `check` at (`:6`).
            """)
        self.tool("--apply", "--initial")
        lines = d.read_text().split("\n")
        self.assertIn("(`fork.py:13`), then (`:15`) and (`:20`)", lines[0])
        self.assertIn("(`:12`)", lines[2])
        self.assertIn("`state.py:3` here, then (`:12`)", lines[4])
        self.assertIn("`fork.py:5`, then a bare `check` at (`:9`)", lines[6])
        listed = self.manual()
        self.assertIn("NOTES.md:1\t:20\tfork.py\t", listed)
        self.assertIn("NOTES.md:3\t:12\t-\tits block names no file (fork.py in its section); none defines", listed)
        self.assertNotIn("NOTES.md:5", listed)
        self.tool("--check")

    def test_names_that_do_not_resolve_are_listed(self):
        d = self.doc("""\
            Short names (`bls_g1.py`): add (`g1.py:10`), then (`:12`).

            Unknown (`nowhere.py:10`); third party by basename (`rlp.py:10`, `numeric.py:7`).

            The table in [EthVmCore](`modules/EthVmCore.md`) says (`:10`).

            A Lean file `Foo.lean:10`, then (`:12`); another (`fork.py:11`, `:44`).

            Undeclared abbreviation (`st:10`).

            Pairing (`bls12_381_pairing.py`) [V].
            - (`pairing.py:5`), then (`:7`).
            """)
        self.tool("--apply", "--initial")
        lines = d.read_text().split("\n")
        self.assertIn("(`g1.py:13`), then (`:15`)", lines[0])
        self.assertIn("(`nowhere.py:10`); third party by basename (`rlp.py:10`, `numeric.py:7`)", lines[2])
        self.assertIn("says (`:10`)", lines[4])
        self.assertIn("`Foo.lean:10`, then (`:12`); another (`fork.py:14`, `:44`)", lines[6])
        listed = self.manual()
        self.assertIn("NOTES.md:3\tnowhere.py:10\tnowhere.py\tnowhere.py names no execution-specs", listed)
        self.assertNotIn("rlp.py", listed)
        self.assertNotIn("numeric.py", listed)
        self.assertIn("NOTES.md:5\t:10\tmodules/EthVmCore.md\tinherits modules/EthVmCore.md, which is not", listed)
        self.assertIn("NOTES.md:7\t:12\tFoo.lean\tinherits Foo.lean", listed)
        self.assertIn("NOTES.md:7\t:44\t-\tits block names several files", listed)
        self.assertIn("; on a line with rewritten citations", listed)
        self.assertIn("NOTES.md:9\tst:10\t-\tabbreviation not declared by this document", listed)
        self.assertIn("NOTES.md:12\tpairing.py:5\tpairing.py\tpairing.py, a short name for bls12_381_pairing.py, "
                      "which is ambiguous between", listed)
        self.assertIn("NOTES.md:12\t:7\tpairing.py\tinherits pairing.py, a short name for bls12_381_pairing.py", listed)
        self.tool("--check")

    def test_document_bases_and_suffix_preference(self):
        vmcore = self.doc(VMCORE_HEAD + "Base `exceptions.py:5`, `gas.py:10`.\n", "STFSpec/informal/modules/EthVmCore.md")
        notes = self.doc("Suffix `vm/gas.py:10`; ambiguous `exceptions.py:5`; also a dependency's `bytes.py:5`.\n")
        self.tool("--apply", "--initial")
        self.assertIn("Base `exceptions.py:6`, `gas.py:11`.", vmcore.read_text())
        self.assertIn("Suffix `vm/gas.py:11`; ambiguous `exceptions.py:5`;", notes.read_text())
        self.assertIn("`bytes.py:5`", notes.read_text())
        self.assertIn(f"ambiguous path: {AMS_EXC}, {VM_EXC}", self.manual())
        self.assertIn("ambiguous path: src/ethereum/utils/bytes.py, ethereum_types/bytes.py", self.manual())

    def test_declared_conventions_fail_closed(self):
        self.doc("# EthVmCore\n\nNo conventions line here (`gas.py:10`).\n", "STFSpec/informal/modules/EthVmCore.md")
        self.assertIn("no longer declares", self.tool("--apply", "--initial", ok=False))

    def test_already_marked_citations(self):
        d = self.doc("""\
            Shifted, at the new commit (`fork.py:13`, at `NEW8`).

            Recorded at OLD8: `fork.py:10`.
            """)
        self.tool("--apply", "--initial")
        text = d.read_text()
        self.assertIn("`fork.py:13`, at", text)
        self.assertIn("`fork.py:10`.", text)
        self.assertNotIn("NOTES.md:1\t", self.manual())
        self.assertIn(f"NOTES.md:3\tfork.py:10\tfork.py\tits block mentions {self.old[:8]}", self.manual())
        self.tool("--check")

    def test_unchanged_files(self):
        d = self.doc("""\
            Unchanged `state.py:10–12`, `src/ethereum/state.py:39`; third party `ethereum_rlp/rlp.py:10`.
            """)
        before = d.read_text()
        self.tool("--apply", "--initial")
        self.assertEqual(d.read_text(), before)
        self.assertEqual(json.loads((self.root / R.LEDGER).read_text())["entries"], [])
        self.assertNotIn("NOTES.md", self.manual())
        self.tool("--check")

    def test_table_definition_line(self):
        d = self.doc("""\
            ## 3. EELS source map

            | EELS item | Line | Spec declaration | Notes |
            |---|---|---|---|
            | `forks/amsterdam/fork.py::check` | 5 | `check` | body (:6) |
            | `forks/amsterdam/fork.py::settle` | 25 | `settle` | signature changed |
            | `forks/amsterdam/fork.py::settle` | 25–26 | `settle` | range |
            """)
        self.tool("--apply", "--initial")
        rows = d.read_text().split("\n")
        self.assertIn("| 8 | `check` | body (:9) |", rows[4])
        self.assertIn("| 28 | `settle` | signature changed |", rows[5])
        self.assertIn("| 25–26 |", rows[6])
        self.tool("--check")
        self.tool("--check", eels=False)

    def test_lean_comments_only(self):
        lean = self.doc('''\
            /-- Source `src/ethereum/forks/amsterdam/fork.py:10`. -/
            def s : String := "src/ethereum/forks/amsterdam/fork.py:10" -- `fork.py:11`
            /- outer /- inner -/ nested `fork.py:10` -/
            def a : String := "x -- `fork.py:10`"
            def b : String := r#"/- " -- `fork.py:10` -/"#
            def c : String := s!"{"--"} `fork.py:10`"
            def «d -- `fork.py:10`» : Nat := 1
            ''', "STFSpec/X.lean")
        self.tool("--apply", "--initial")
        self.assertEqual(lean.read_text().split("\n")[:7], [
            "/-- Source `src/ethereum/forks/amsterdam/fork.py:13`. -/",
            'def s : String := "src/ethereum/forks/amsterdam/fork.py:10" -- `fork.py:14`',
            "/- outer /- inner -/ nested `fork.py:13` -/",
            'def a : String := "x -- `fork.py:10`"',
            'def b : String := r#"/- " -- `fork.py:10` -/"#',
            'def c : String := s!"{"--"} `fork.py:10`"',
            "def «d -- `fork.py:10`» : Nat := 1"])

    def test_text_identity_guard(self):
        # A wrong diff (here: hunks that miss a change) must be caught by comparing the text.
        eels = R.Eels.__new__(R.Eels)
        eels.old, eels.new, eels.files, eels.fileset = "o" * 40, "n" * 40, [FORK], {FORK}
        eels.changed, eels.deleted, eels.hunks, eels._defs = {FORK}, set(), {FORK: []}, {}
        eels._text = {("o" * 40, FORK): ["a", "b", "c"], ("n" * 40, FORK): ["a", "B", "c"]}
        _, cites, conf = R.scan_doc(self.root, "STFSpec/informal/NOTES.md", ("n" * 8, "o" * 8),
                                    "See `forks/amsterdam/fork.py:2`.\n")
        with self.assertRaises(R.Fail):
            R.classify(cites[0], eels, conf)

    def test_comment_only_guard(self):
        R.require_comment_only("X.lean", "def x := 1 -- a 1\n", "def x := 1 -- a 2\n")
        with self.assertRaises(R.Fail):
            R.require_comment_only("X.lean", "def x := 1 -- a\n", "def x := 2 -- a\n")

    # ------------------------------------------------------------------ after the remap

    def test_after_the_remap(self):
        line = "Again (`fork.py:10`) here."
        d = self.doc(line + "\n")
        self.tool("--apply", "--initial")
        self.assertEqual(d.read_text(), "Again (`fork.py:13`) here.\n")
        d.write_text(d.read_text() + "\n" + line + "\n\nNew prose at the pin (`fork.py:10`).\n")
        out = self.tool("--check", ok=False, eels=False)
        self.assertIn("NOTES.md:3: fork.py:10 is at", out)
        self.assertNotIn("NOTES.md:5", out)
        self.tool("--apply", eels=False)
        self.assertEqual(d.read_text().split("\n")[2], "Again (`fork.py:13`) here.")
        self.assertIn("(`fork.py:10`).", d.read_text())
        self.tool("--check", eels=False)
        self.tool("--check")

    def entry(self, line):
        """The DOC:LINE:CONTEXT selector of the list entry on NOTES.md line `line`."""
        hits = [e for e in R.parse_manual(self.manual()) if e["doc"].endswith("NOTES.md") and e["line"] == line]
        self.assertEqual(len(hits), 1)
        return R.entry_id(hits[0])

    def test_twin_entries_fail_closed(self):
        d = self.doc("Across (`fork.py:18–22`) first.\n\nAgain across (`fork.py:18–22`) second.\n")
        self.tool("--apply", "--initial")
        d.write_text("Across (`fork.py:21–25`, fixed) first.\n\nAgain across (`fork.py:18–22`) second.\n")
        out = self.tool("--check", ok=False, eels=False)
        self.assertIn("listed citation changed or removed: STFSpec/informal/NOTES.md:1:", out)
        self.assertNotIn("NOTES.md:3:", out)
        self.assertIn("listed citation changed or removed", self.tool("--apply", ok=False, eels=False))
        self.assertIn("still occurs unchanged", self.tool("--apply", "--drop-resolved", self.entry(3), ok=False, eels=False))
        self.tool("--apply", "--drop-resolved", "STFSpec/informal/NOTES.md:1", eels=False)
        self.assertNotIn("NOTES.md:1\t", self.manual())
        self.assertIn("NOTES.md:3\tfork.py:18–22", self.manual())
        self.tool("--check")

    def test_marked_twin_does_not_take_over(self):
        d = self.doc("Across (`fork.py:18–22`).\n\nAt the pin, `NEW8`: (`fork.py:18–22`).\n")
        self.tool("--apply", "--initial")
        self.assertNotIn("NOTES.md:3", self.manual())
        d.write_text(d.read_text().replace("Across (`fork.py:18–22`)", "Across (`fork.py:21–25`)"))
        self.assertIn("NOTES.md:1:", self.tool("--check", ok=False, eels=False))

    def test_path_and_cosmetic_edits_fail_closed(self):
        d = self.doc("Across (`fork.py:18–22`).\n\nAlso (`fork.py:20`).\n")
        self.tool("--apply", "--initial")
        self.git(self.root, "init", "-q"); self.git(self.root, "add", "-A"); self.git(self.root, "commit", "-qm", "remap")
        d.write_text("Across (`forks/amsterdam/fork.py:18–22`).\n\nAlso (`fork.py:20`).\n")
        self.assertIn("NOTES.md:1:", self.tool("--check", ok=False, eels=False))
        d.write_text("Across (`fork.py:18-22`).\n\nAlso (`fork.py:20`).\n")
        self.assertIn("NOTES.md:1:", self.tool("--check", ok=False, eels=False))
        # Relist the reformatted citation: drop its entry while reading its line as old.
        self.tool("--apply", "--since", "HEAD", "--drop-resolved", self.entry(1))
        self.assertIn("NOTES.md:1\tfork.py:18-22\tfork.py\tforks/amsterdam/fork.py: 18–22 touches", self.manual())
        self.tool("--check")

    def test_drop_and_confirm_one_of_several(self):
        far = " " + "w" * 60 + "."
        d = self.doc(f"One (`fork.py:18–22`).\n\nTwo (`fork.py:18–22`){far}\n\nThree (`fork.py:18–22`).\n")
        self.tool("--apply", "--initial")
        self.git(self.root, "init", "-q"); self.git(self.root, "add", "-A"); self.git(self.root, "commit", "-qm", "remap")
        two = self.entry(3)
        d.write_text(d.read_text().replace("One (`fork.py:18–22`)", "One (`fork.py:21–25`)"))
        self.assertIn("names 0 list entries", self.tool("--apply", "--confirm", "STFSpec/informal/NOTES.md:4", ok=False, eels=False))
        self.tool("--apply", "--drop-resolved", self.entry(1), "--confirm", two)
        listed = self.manual()
        self.assertNotIn("NOTES.md:1\t", listed)
        self.assertNotIn("NOTES.md:3\t", listed)
        self.assertIn("NOTES.md:5\tfork.py:18–22", listed)
        confirmed = json.loads((self.root / R.LEDGER).read_text())["confirmed"]
        self.assertEqual([(e["line"], e["text"]) for e in confirmed], [(3, "fork.py:18–22")])
        self.tool("--check")
        ledger = json.loads((self.root / R.LEDGER).read_text())
        ledger["confirmed"][0]["text"] = "fork.py:46"
        (self.root / R.LEDGER).write_text(R.render_ledger(ledger))
        self.assertIn("confirmed STFSpec/informal/NOTES.md:3 fork.py:46 lies outside", self.tool("--check", ok=False))
        ledger["confirmed"][0]["text"] = "fork.py:18–22"
        (self.root / R.LEDGER).write_text(R.render_ledger(ledger))
        # A confirmed citation is never relisted, even when its line is read as old.
        self.git(self.root, "add", "-A"); self.git(self.root, "commit", "-qm", "reviewed")
        d.write_text(d.read_text().replace(far, far + " An addition far from the citation."))
        self.tool("--apply", "--since", "HEAD")
        self.assertNotIn("NOTES.md:3\t", self.manual())
        self.tool("--check")

    def commit_root(self, message="remap"):
        if not (self.root / ".git").exists():
            self.git(self.root, "init", "-q")
        self.git(self.root, "add", "-A"); self.git(self.root, "commit", "-qm", message)

    def test_relist_on_a_mixed_line(self):
        d = self.doc("A (`fork.py:10`) and B (`fork.py:18–22`) default follows.\n")
        self.tool("--apply", "--initial")
        self.assertIn("NOTES.md:1\tfork.py:18–22\tfork.py\t", self.manual())
        self.assertIn("on a line with rewritten citations", self.manual())
        self.commit_root()
        sel = self.entry(1)
        d.write_text("A (`fork.py:13`) and B (`fork.py:18–22`) default now follows.\n")
        out = self.tool("--check", ok=False, eels=False)
        self.assertIn(f"--apply --relist {sel} DOC:LINE", out)
        # Reading the line as old would shift A twice, so --since refuses it.
        self.assertIn("is a recorded rewrite", self.tool("--apply", "--since", "HEAD", "--drop-resolved", sel, ok=False))
        self.assertIn("no occurrence with its text and file on that line",
                      self.tool("--apply", "--relist", sel, "STFSpec/informal/NOTES.md:2", ok=False, eels=False))
        self.assertIn("must be DOC:LINE in", self.tool("--apply", "--relist", sel, "STFSpec/X.lean:1", ok=False, eels=False))
        self.tool("--apply", "--relist", sel, "STFSpec/informal/NOTES.md:1", eels=False)
        self.assertNotEqual(self.entry(1), sel)
        self.tool("--check")
        # Reformatted on the same mixed line: relisted to the new text.
        self.commit_root("context")
        d.write_text("A (`fork.py:13`) and B (`fork.py:18-22`) default now follows.\n")
        self.tool("--apply", "--relist", self.entry(1), "STFSpec/informal/NOTES.md:1", eels=False)
        self.assertIn("NOTES.md:1\tfork.py:18-22\tfork.py\t", self.manual())
        self.assertIn("nothing to relist",
                      self.tool("--apply", "--relist", self.entry(1), "STFSpec/informal/NOTES.md:1", ok=False, eels=False))
        self.tool("--check")

    def test_relist_refuses_listed_or_recorded_occurrences(self):
        d = self.doc("X (`fork.py:18–22`) one.\n\nY (`fork.py:18–22`) two.\n\nA (`fork.py:10`).\n")
        self.tool("--apply", "--initial")
        first = self.entry(1)
        d.write_text("X (`fork.py:18–22`) one, edited.\n\nY (`fork.py:18–22`) two.\n\nA (`fork.py:10`) z.\n")
        self.assertIn("already listed", self.tool("--apply", "--relist", first, "STFSpec/informal/NOTES.md:3",
                                                  ok=False, eels=False))
        self.tool("--apply", "--relist", first, "STFSpec/informal/NOTES.md:1", eels=False)

    def relist_error(self, sel, line):
        return self.tool("--apply", "--relist", sel, f"STFSpec/informal/NOTES.md:{line}", ok=False, eels=False)

    def test_collision_guard_ignores_dash_style(self):
        d = self.doc("X (`fork.py:20–21`) listed.\n\nR (`fork.py:17-18`) not rewritten.\n")
        self.tool("--apply", "--initial")
        self.assertIn("R (`fork.py:17-18`) not rewritten.", d.read_text())
        self.assertIn("NOTES.md:3\tfork.py:17-18\tfork.py\trewriting it would make it read as a listed", self.manual())

    def test_relist_refuses_a_recorded_rewrite_in_any_context(self):
        d = self.doc("R (`fork.py:17–18`) rewritten.\n")
        self.tool("--apply", "--initial")
        self.assertIn("R (`fork.py:20–21`) rewritten.", d.read_text())
        self.commit_root()
        # A branch written before the remap adds X, at the old commit: listed beside R.
        d.write_text(d.read_text() + "\nX (`fork.py:20-21`) listed.\n")
        self.tool("--apply", "--since", "HEAD")
        x = self.entry(3)
        d.write_text("R (`fork.py:20–21`), now with its prose reworded well past the old context.\n\nRemoved.\n")
        self.assertIn("is a recorded rewrite's new text in this document", self.relist_error(x, 1))

    def test_relist_refuses_confirmed_several_and_other_files(self):
        d = self.doc("A (`fork.py:18–22`) one.\n\nB (`fork.py:18–22`) two.\n\n"
                     "File `fork.py` named (`:20`) here.\n\nList (`fork.py:18–22, 30`) here.\n")
        self.tool("--apply", "--initial")
        a, b, bare, lst = self.entry(1), self.entry(3), self.entry(5), self.entry(7)
        self.tool("--apply", "--confirm", b)
        d.write_text("A (`fork.py:18–22`) one, edited.\n\nB (`fork.py:18–22`) two.\n\n"
                     "File `fork.py` named (`:20`) here, edited.\n\nList (`fork.py:18–22,30`) here.\n\n"
                     "New (`fork.py:18–22`) and again (`fork.py:18–22`).\n\nOther `state.py` then (`:20`).\n")
        self.assertIn("that occurrence is confirmed", self.relist_error(a, 3))
        self.assertIn("several occurrences with its text and file", self.relist_error(a, 9))
        self.assertIn("no occurrence with its text and file", self.relist_error(bare, 11))
        self.tool("--apply", "--relist", a, "STFSpec/informal/NOTES.md:1", "--relist", bare,
                  "STFSpec/informal/NOTES.md:5", "--relist", lst, "STFSpec/informal/NOTES.md:7", eels=False)
        self.assertIn("NOTES.md:7\tfork.py:18–22,30\tfork.py\t", self.manual())
        self.tool("--check")

    def test_record_lines_are_refreshed(self):
        d = self.doc("A (`fork.py:10`).\n")
        self.tool("--apply", "--initial")
        lines = lambda: [e["line"] for e in json.loads((self.root / R.LEDGER).read_text())["entries"]]
        self.assertEqual(lines(), [1])
        d.write_text("New first paragraph.\n\n" + d.read_text())
        self.tool("--check", eels=False)
        self.tool("--apply", eels=False)
        self.assertEqual(lines(), [3])
        self.tool("--check")

    def test_indistinguishable_twins_are_named_together(self):
        d = self.doc("Twin (`fork.py:18–22`).\n\nTwin (`fork.py:18–22`).\n")
        self.tool("--apply", "--initial")
        ids = [R.entry_id(e) for e in R.parse_manual(self.manual())]
        d.write_text("Twin (`fork.py:18–22`).\n\nTwin (`fork.py:21–25`).\n")
        out = self.tool("--check", ok=False, eels=False)
        self.assertIn("one of the indistinguishable entries", out)
        for i in ids:
            self.assertIn(i, out)

    def test_context_prefix_selection_and_single_use(self):
        d = self.doc("Twice (`fork.py:18–22`, `fork.py:20`).\n")
        self.tool("--apply", "--initial")
        entries = R.parse_manual(self.manual())
        twenty = next(e for e in entries if e["text"] == "fork.py:20")
        d.write_text("Twice (`fork.py:18–22`, `fork.py:23`).\n")
        self.assertIn("can be named only once", self.tool(
            "--apply", "--drop-resolved", R.entry_id(twenty), "--confirm", R.entry_id(twenty), ok=False))
        other = next(e for e in entries if e["text"] == "fork.py:18–22")
        # The edit is within the other citation's context too, so it is relisted in the same run.
        self.tool("--apply", "--drop-resolved", "STFSpec/informal/NOTES.md:1:" + twenty["window"][:6],
                  "--relist", R.entry_id(other), "STFSpec/informal/NOTES.md:1", eels=False)
        self.assertEqual([e["text"] for e in R.parse_manual(self.manual())], ["fork.py:18–22"])

    def test_confirm_checks_the_new_commit(self):
        self.doc("Past (`fork.py:46`).\n")
        self.tool("--apply", "--initial")
        sel = self.entry(1)
        self.assertIn("needs --eels", self.tool("--apply", "--confirm", sel, ok=False, eels=False))
        self.assertIn("46–46 lies outside", self.tool("--apply", "--confirm", sel, ok=False))
        self.assertIn(sel.rsplit(":", 1)[0], self.manual())

    def test_since_maps_new_prose_that_equals_a_recorded_rewrite(self):
        d = self.doc("A (`fork.py:10`).\n")
        self.tool("--apply", "--initial")
        self.commit_root()
        d.write_text(d.read_text() + "\nBranch prose cites the old line (`fork.py:13`) here.\n")
        self.tool("--apply", "--since", "HEAD")
        self.assertIn("(`fork.py:16`) here.", d.read_text())

    def test_selectors_must_name_one_entry(self):
        self.doc("Twice (`fork.py:18–22`, `fork.py:20`).\n")
        self.tool("--apply", "--initial")
        out = self.tool("--apply", "--confirm", "STFSpec/informal/NOTES.md:1", ok=False, eels=False)
        self.assertIn("names 2 list entries; use STFSpec/informal/NOTES.md:1:", out)

    def test_reasons_are_refreshed_with_the_reference(self):
        self.doc("Across (`fork.py:18–22`).\n")
        self.tool("--apply", "--initial")
        entries = R.parse_manual(self.manual())
        good = entries[0]["reason"]
        entries[0]["reason"] = "stale reason"
        (self.root / R.MANUAL).write_text(R.render_manual(entries, self.old, self.new))
        self.tool("--check", eels=False)
        self.assertIn("reason is now", self.tool("--check", ok=False))
        self.tool("--apply")
        self.assertEqual(R.parse_manual(self.manual())[0]["reason"], good)
        self.tool("--check")

    def test_list_entries_follow_their_context(self):
        self.doc("Across (`fork.py:18–22`).\n\nRecorded at OLD8 (`fork.py:18–22`).\n")
        self.tool("--apply", "--initial")
        self.doc("Recorded at OLD8 (`fork.py:18–22`).\n\nAcross (`fork.py:18–22`).\n")
        self.tool("--apply", eels=False)
        self.assertIn(f"NOTES.md:1\tfork.py:18–22\tfork.py\tits block mentions {self.old[:8]}", self.manual())
        self.assertIn("NOTES.md:3\tfork.py:18–22\tfork.py\tforks/amsterdam/fork.py: 18–22 touches", self.manual())
        self.tool("--check")

    def test_canonical_state_files(self):
        self.doc("Across (`fork.py:18–22`). Again (`fork.py:20`).\n\nShift (`fork.py:10`).\n")
        self.tool("--apply", "--initial")
        lines = self.manual().split("\n")
        self.edit_state(R.MANUAL, lambda t: "\n".join(lines[:-3] + [lines[-2], lines[-3]]) + "\n")
        self.assertIn("citation-remap-manual.txt is not in canonical form", self.tool("--check", ok=False, eels=False))
        self.tool("--apply", eels=False)
        self.edit_state(R.LEDGER, lambda t: t.replace('"window": 48', '"window":  48'))
        self.assertIn("citation-remap.json is not in canonical form", self.tool("--check", ok=False, eels=False))

    def test_record_and_list_are_verified_against_the_reference(self):
        d = self.doc("Shift (`fork.py:10`).\n\nAcross (`fork.py:18–22`).\n")
        self.tool("--apply", "--initial")
        ledger = json.loads((self.root / R.LEDGER).read_text())
        ledger["entries"][0]["new"] = "fork.py:14"
        (self.root / R.LEDGER).write_text(R.render_ledger(ledger))
        self.tool("--check", eels=False)
        self.assertIn("does not follow the hunks", self.tool("--check", ok=False))
        ledger["entries"][0]["new"] = "fork.py:13"
        (self.root / R.LEDGER).write_text(R.render_ledger(ledger))
        d.write_text(d.read_text() + "\nListed by hand (`fork.py:11`).\n")
        entries = R.parse_manual(self.manual()) + [dict(doc="STFSpec/informal/NOTES.md", line=5, text="fork.py:11",
                                                        path="fork.py", reason="by hand", window="")]
        (self.root / R.MANUAL).write_text(R.render_manual(entries, self.old, self.new))
        self.assertIn("listed citation fork.py:11 is auto-mappable", self.tool("--check", ok=False))
        entries[-1]["text"], entries[-1]["reason"] = "fork.py:18–22", "stale"
        d.write_text(d.read_text().replace("(`fork.py:11`)", "(`fork.py:18–22`)"))
        (self.root / R.MANUAL).write_text(R.render_manual(entries, self.old, self.new))
        self.assertIn("reason is now", self.tool("--check", ok=False))

    def test_collision_guard(self):
        d = self.doc("""\
            ## Section
            `fork.py:2` names the file.

            The `check` body (`:6`).

            Unattributed (`:9`).
            """)
        self.tool("--apply", "--initial")
        self.assertIn("The `check` body (`:6`).", d.read_text())
        self.assertIn("rewriting it would make it read as a listed citation", self.manual())

    def test_post_apply_self_check(self):
        self.doc("Same words in both of these (`fork.py:10`) end.\n\nSame words in both of these (`fork.py:7`) end.\n")
        self.assertIn("context collision", self.tool("--apply", "--initial", ok=False))

    def test_since_reads_new_lines_as_old(self):
        d = self.doc("Remapped (`fork.py:10`).\n")
        self.tool("--apply", "--initial")
        self.git(self.root, "init", "-q"); self.git(self.root, "add", "-A"); self.git(self.root, "commit", "-qm", "remap")
        d.write_text(d.read_text() + "\nFrom a branch written before the remap (`fork.py:11`).\n")
        self.tool("--apply", "--since", "HEAD")
        self.assertIn("(`fork.py:14`).", d.read_text())
        self.assertIn("Remapped (`fork.py:13`).", d.read_text())
        self.tool("--check")

    def test_since_refuses_a_recorded_rewrite_and_ignores_diff_config(self):
        self.gitconfig.write_text("[diff]\n\tnoprefix = true\n\tmnemonicPrefix = true\n")
        filler = " and " + "y" * 60 + "."
        d = self.doc("A (`fork.py:10`)" + filler + "\n")
        self.tool("--apply", "--initial")
        self.assertIn("A (`fork.py:13`)", d.read_text())
        self.git(self.root, "init", "-q"); self.git(self.root, "add", "-A"); self.git(self.root, "commit", "-qm", "remap")
        # A conflicted line resolved to the remapped A plus the branch's B: refused.
        d.write_text("A (`fork.py:13`)" + filler + " B (`fork.py:11`).\n")
        out = self.tool("--apply", "--since", "HEAD", ok=False)
        self.assertIn("is a recorded rewrite", out)
        # Resolved to the branch's pre-remap numbers instead: both are remapped once.
        d.write_text("A (`fork.py:10`)" + filler + " B (`fork.py:11`).\n")
        self.tool("--apply", "--since", "HEAD")
        self.assertIn("A (`fork.py:13`)", d.read_text())
        self.assertIn("B (`fork.py:14`)", d.read_text())

    def test_since_refuses_main_text_on_a_conflicted_line(self):
        d = self.doc("A (`fork.py:10`) and B.\n\nC (`fork.py:10–12`) and D.\n")
        self.tool("--apply", "--initial")
        self.git(self.root, "init", "-q"); self.git(self.root, "add", "-A"); self.git(self.root, "commit", "-qm", "remap")
        d.write_text("A (`fork.py:13`) and B (`fork.py:11`).\n\nC (`fork.py:13–15`) and D.\n")
        self.assertIn("is a recorded rewrite", self.tool("--apply", "--since", "HEAD", ok=False))
        self.assertEqual(d.read_text(), "A (`fork.py:13`) and B (`fork.py:11`).\n\nC (`fork.py:13–15`) and D.\n")
        # The guard ignores dash style: main's `13–15`, reformatted on the branch, is refused too.
        d.write_text("A (`fork.py:13`) and B.\n\nC (`fork.py:13-15`) and E (`fork.py:11`).\n")
        self.assertIn("fork.py:13-15 is a recorded rewrite", self.tool("--apply", "--since", "HEAD", ok=False))
        d.write_text("A (`fork.py:10`) and B (`fork.py:11`).\n\nC (`fork.py:13–15`) and D.\n")
        self.tool("--apply", "--since", "HEAD")
        self.assertEqual(d.read_text(), "A (`fork.py:13`) and B (`fork.py:14`).\n\nC (`fork.py:13–15`) and D.\n")

    def test_since_refuses_a_copied_remapped_paragraph(self):
        d = self.doc("A (`fork.py:10`) and more.\n")
        self.tool("--apply", "--initial")
        self.git(self.root, "init", "-q"); self.git(self.root, "add", "-A"); self.git(self.root, "commit", "-qm", "remap")
        d.write_text(d.read_text() + "\nA (`fork.py:13`) and more.\n")
        self.assertIn("is a recorded rewrite", self.tool("--apply", "--since", "HEAD", ok=False))

    def test_inherited_file_change_fails_closed(self):
        filler = " " + "w" * 60
        d = self.doc(f"File `fork.py` named here{filler} (`:20`).\n")
        self.tool("--apply", "--initial")
        self.assertIn("NOTES.md:1\t:20\tfork.py\t", self.manual())
        d.write_text(f"File `state.py` named here{filler} (`:20`).\n")
        self.assertIn("NOTES.md:1:", self.tool("--check", ok=False, eels=False))

    def test_textconv_is_ignored(self):
        attributes = self.gitconfig.parent / "attributes"
        attributes.write_text("*.py diff=strip\n*.md diff=strip\n")
        self.gitconfig.write_text(f"[core]\n\tattributesFile = {attributes}\n[diff \"strip\"]\n\ttextconv = sed 1d\n")
        d = self.doc("Shift (`fork.py:10`), table (`fork.py:29–30`).\n")
        self.tool("--apply", "--initial")
        self.assertEqual(d.read_text(), "Shift (`fork.py:13`), table (`fork.py:32–33`).\n")
        self.tool("--check")

    def test_pin_moved(self):
        self.doc("Text (`fork.py:10`).\n")
        self.tool("--apply", "--initial")
        (self.root / "reference.toml").write_text('[release]\ncommit = "0123456789abcdef0123456789abcdef01234567"\n')
        self.assertIn("remap for the new pin", self.tool("--check", ok=False, eels=False))


if __name__ == "__main__":
    unittest.main()
