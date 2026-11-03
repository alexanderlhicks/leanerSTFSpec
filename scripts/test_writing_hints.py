#!/usr/bin/env -S uv run --no-project --python 3.12 python
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Regression tests for the advisory writing script, `scripts/writing_hints.py`."""

from __future__ import annotations

import importlib.util
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

SCRIPTS = Path(__file__).resolve().parent
ROOT = SCRIPTS.parent


def load(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / filename)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


WRITING = load("writing_hints", "writing_hints.py")


def findings(text: str, path: str = "doc.md") -> list[str]:
    blocks = WRITING.file_blocks(path, text)
    return sorted({item.rule for item in WRITING.check_blocks(blocks)})


class WritingRuleTests(unittest.TestCase):
    def test_vocabulary_is_parsed(self) -> None:
        general, history = WRITING.avoid_words()
        self.assertIn("utilize", general)
        self.assertIn("e.g.", general)
        self.assertIn("no longer", history)
        self.assertIn("matches geth", general)
        self.assertNotIn("now", history)
        self.assertNotIn("new", history)

    def test_sentence_length(self) -> None:
        long_sentence = " ".join(["word"] * 26) + "."
        self.assertEqual(findings(long_sentence), ["S1"])
        self.assertEqual(findings(" ".join(["word"] * 25) + "."), [])
        self.assertEqual(findings("1. " + " ".join(["word"] * 21) + "."), ["S1"])
        self.assertEqual(findings("- " + " ".join(["word"] * 21) + "."), [])

    def test_text_in_parentheses_is_a_separate_sentence(self) -> None:
        inner = " ".join(["word"] * 40)
        self.assertEqual(findings(f"The bound holds ({inner})."), ["S1"])
        self.assertEqual(findings(f"The bound holds (see ({inner}))."), ["S1"])
        self.assertEqual(findings("The bound holds (for each code)."), [])

    def test_one_word_elements(self) -> None:
        sentence = ("The law `getStorage_setStorage_same (h : a ≠ b)` and $x \\le 2^{256}$ "
                    "from CONTRIBUTING §5.3 and [the page](https://example.org/a.b) hold "
                    "(for every account that this page lists) here.")
        self.assertEqual(findings(sentence), [])
        counted = WRITING.mask(sentence, collapse_parentheses=True)
        self.assertEqual(WRITING.word_count(counted), 13)

    def test_sentence_can_start_with_a_lowercase_filename(self) -> None:
        text = " ".join(["word"] * 20) + ". pr-scope.py " + " ".join(["word"] * 20) + "."
        self.assertEqual(findings(text), [])
        self.assertEqual(len(WRITING.sentences(text)), 2)

    def test_license_text_is_exempt_but_later_prose_is_checked(self) -> None:
        legal = "## Licensing\n\nEnsure these terms; do not change them.\n"
        self.assertEqual(findings(legal, "CONTRIBUTING.md"), [])
        nested = legal + "\n### Conditions\n\nWe utilize these terms.\n"
        self.assertEqual(findings(nested, "CONTRIBUTING.md"), [])
        resumed = nested + "\n## Next steps\n\nWe utilize the lemma.\n"
        self.assertEqual(findings(resumed, "CONTRIBUTING.md"), ["W1"])
        self.assertEqual(findings("Ensure these terms; do not change them.", "LICENSE.md"), [])
        fenced = "```md\n## License\n```\n\nWe utilize the lemma.\n"
        self.assertEqual(findings(fenced), ["W1"])

    def test_mathematical_terms_are_not_blanket_vocabulary_bans(self) -> None:
        for text in ["The following are equivalent.", "Every valid block has a header.",
                     "The space is simply connected.", "This functor is essentially surjective.",
                     "Complete the pull request template."]:
            self.assertNotIn("W1", findings(text), text)

    def test_paragraph_length(self) -> None:
        self.assertEqual(findings(" ".join(["One sentence."] * 7)), ["P2"])
        self.assertEqual(findings(" ".join(["One sentence."] * 6)), [])

    def test_punctuation(self) -> None:
        self.assertEqual(findings("The code is linear; it is also cyclic."), ["U1"])
        self.assertEqual(findings("The code is linear — it is also cyclic."), ["U2"])
        self.assertEqual(findings("The Reed–Solomon code has rate 1–2 in this range."), [])
        self.assertEqual(findings("Write `a; b` in Lean."), [])
        self.assertEqual(findings("The outcomes O1–O13 and the questions Q1–Q46 are listed."), [])
        self.assertEqual(findings("A; b."), ["U1"])
        # A semicolon near the start of a block gives an excerpt from the start, not from the end.
        blocks = WRITING.file_blocks("doc.md", "A; b. " + " ".join(["word"] * 10) + " end.")
        excerpt = [item.excerpt for item in WRITING.check_blocks(blocks) if item.rule == "U1"]
        self.assertEqual(len(excerpt), 1)
        self.assertTrue(excerpt[0].startswith("A; b."), excerpt[0])

    def test_definition_separator_is_not_a_clause_join(self) -> None:
        for dash in ["—", "–", "--"]:
            for term in ["`Δ₀(u, v)`", "``Δ₀(u, v)``", "$\\delta$", "**Relative distance**"]:
                with self.subTest(dash=dash, term=term):
                    self.assertEqual(findings(f"- {term} {dash} `hammingDist u v`."), [])
        self.assertNotIn("U2", findings("- `Λ(C, δ, f)` and `Λ(C, δ)` — write `Code.Lambda C δ`."))
        self.assertEqual(findings("- `Gadget/` (§2.1) — the gadget matrix."), [])
        self.assertEqual(findings("- `EvalSplit.lean` (§4, Eq. (12)) — the matrix split."), [])

    def test_definition_description_is_still_checked(self) -> None:
        self.assertEqual(findings("- `δ` — We utilize the lemma."), ["W1"])
        self.assertEqual(findings("- `δ` — relative distance — it is bounded."), ["U2"])
        self.assertEqual(findings("- `δ` — relative distance.\n  The code is linear — it is cyclic."), ["U2"])
        self.assertEqual(findings("- `C` is linear — it is cyclic."), ["U2"])
        self.assertEqual(findings("- `C` (§2.1) is linear — it is cyclic."), ["U2"])
        self.assertEqual(findings("| Term | Description |\n|---|---|\n| `C` is linear — it is cyclic. | Bound |"), ["U2"])

    def test_words(self) -> None:
        self.assertEqual(findings("Use a ring, e.g. the integers."), ["W7"])
        self.assertEqual(findings("We utilize the lemma."), ["W1"])
        self.assertEqual(findings("Set up the build."), ["W6"])
        self.assertEqual(findings("The word ends in a vowel."), [])
        self.assertEqual(findings("Don't run the build."), ["S5"])
        self.assertEqual(findings("The prover's message is short."), [])

    def test_verbs(self) -> None:
        self.assertEqual(findings("The lemma has changed."), ["V1"])
        self.assertEqual(findings("The verifier is rejecting the proof string."), ["V1"])
        self.assertEqual(findings("The polynomials have bounded degree."), [])
        self.assertEqual(findings("The witness is missing."), [])
        self.assertEqual(findings("Using the lemma, we bound the error."), ["V2"])
        self.assertEqual(findings("Folding halves the length of the word."), [])
        self.assertEqual(findings("During a merge, the base is the merge base."), [])
        self.assertEqual(findings("The request may have failed."), [])
        self.assertEqual(findings("The bottleneck is hashing."), [])
        self.assertEqual(findings("The gas metering is pending."), [])

    def test_bare_this(self) -> None:
        self.assertEqual(findings("The bound is tight. This is the main result."), ["S7"])
        self.assertEqual(findings("The bound is tight. This lemma is the main result."), [])

    def test_history_words_apply_to_library_text_only(self) -> None:
        module = "STFSpec/informal/modules/EthBase.md"
        self.assertEqual(findings("The lemma is no longer needed.", module), ["C8"])
        self.assertEqual(findings("/-- The lemma is no longer needed. -/", "STFSpec/Base/Bytes.lean"), ["C8"])
        self.assertEqual(findings("The lemma is no longer needed.", "WRITING.md"), ["C8"])
        self.assertEqual(findings("The lemma is no longer needed.", "body.md"), [])
        self.assertEqual(findings("The lemma is no longer needed.", "STFSpec/informal/DECISIONS.md"), [])
        self.assertEqual(findings("The new code is now linear.", module), [])

    def test_exempt_text(self) -> None:
        text = ("Avoid \"e.g.; it's robust\" in prose.\n\n# Heading; with e.g. a dash — here\n\n"
                "```\nlet x := 1; e.g.\n```\n\n<!-- e.g.; utilize -->\n")
        self.assertEqual(findings(text), [])

    def test_table_cells_and_header(self) -> None:
        text = "| Rule; header | Use |\n|---|---|\n| One cell; two | Fine. |\n"
        self.assertEqual(findings(text), ["U1"])


class StfspecConventionTests(unittest.TestCase):
    def test_section_reference_is_one_word(self) -> None:
        counted = WRITING.mask("Read CONTRIBUTING §5.3, REVIEW §§3–4 and §7.", True)
        self.assertEqual(WRITING.word_count(counted), 5)

    def test_verification_markers_and_identifiers(self) -> None:
        self.assertEqual(findings("The order matches EELS `block.py:58` [V]. D14 and DISC-001 apply."), [])

    def test_generated_files_are_excluded(self) -> None:
        self.assertFalse(WRITING.checked_path("STFSpec/informal/GAPS.md"))
        self.assertFalse(WRITING.checked_path("STFSpec/informal/REFERENCE-RECORDS.md"))
        self.assertTrue(WRITING.checked_path("STFSpec/informal/GAPS-CROSSCUTTING.md"))
        self.assertFalse(WRITING.checked_path("scripts/differential.py"))

    def test_exit_code_is_advisory(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            page = Path(directory) / "page.md"
            page.write_text("We utilize the lemma; it is robust.\n", encoding="utf-8")
            with mock.patch("sys.stdout", io.StringIO()) as output:
                self.assertEqual(WRITING.main(["writing_hints.py", str(page)]), 0)
        self.assertIn("[U1]", output.getvalue())
        self.assertIn("writing hint(s)", output.getvalue())

    def test_other_file_types_are_refused(self) -> None:
        with mock.patch("sys.stderr", io.StringIO()):
            with self.assertRaises(SystemExit) as raised:
                WRITING.main(["writing_hints.py", "scripts/differential.py"])
        self.assertEqual(raised.exception.code, 2)


class SpellingTests(unittest.TestCase):
    def test_ise_forms_are_reported(self) -> None:
        for text in ["We optimise the map.", "The organisation is clear.", "Initialise the state.",
                     "The interface is specialised to `Id`."]:
            self.assertEqual(findings(text), ["W8"], text)

    def test_oxford_and_american_spellings_are_accepted(self) -> None:
        for text in ["We optimize the behaviour.", "We optimize the behavior.", "Analyse the trie.",
                     "The premises hold otherwise.", "The bound is precise.", "Revise the text."]:
            self.assertEqual(findings(text), [], text)


class ToolingRegressionTests(unittest.TestCase):
    def test_inflected_words_to_avoid(self) -> None:
        for text in ["We are ensuring the order.", "The helper utilizes a map.",
                     "The proof is leveraging a lemma."]:
            self.assertIn("W1", findings(text), text)

    def test_latin_abbreviation_is_reported_once(self) -> None:
        blocks = WRITING.file_blocks("doc.md", "Use a map, e.g. a tree.")
        self.assertEqual([item.rule for item in WRITING.check_blocks(blocks)], ["W7"])

    def test_history_scope_does_not_depend_on_the_path_form(self) -> None:
        relative = "STFSpec/informal/modules/EthBase.md"
        real_read = Path.read_text

        def read(path: Path, *args, **kwargs) -> str:
            # The test replaces only the module page. It reads the vocabulary from the repository.
            if path.name == "EthBase.md":
                return "It is no longer used.\n"
            return real_read(path, *args, **kwargs)

        for form in [relative, "./" + relative, str(ROOT / relative)]:
            with self.subTest(form=form):
                with mock.patch.object(Path, "read_text", read), \
                     mock.patch.object(Path, "is_file", return_value=True), \
                     mock.patch("sys.stdout", io.StringIO()) as output:
                    WRITING.main(["writing_hints.py", form])
                self.assertIn("[C8]", output.getvalue())

    def test_missing_file_is_a_usage_error(self) -> None:
        with mock.patch("sys.stderr", io.StringIO()):
            with self.assertRaises(SystemExit) as raised:
                WRITING.main(["writing_hints.py", "no-such-file.md"])
        self.assertEqual(raised.exception.code, 2)


class LeanExtractionTests(unittest.TestCase):
    def test_doc_comments_and_line_numbers(self) -> None:
        source = ('/-! # Title\n\nThe module; with a problem. -/\n'
                  'def f : Nat := 1 -- a trailing comment; also a problem\n'
                  'def s : String := "-- not a comment; ok"\n'
                  '/-- The definition utilizes `x; y`. -/\n'
                  'theorem t : True := trivial\n')
        blocks = WRITING.lean_blocks("A.lean", source)
        lines = {block.line: block.text for block in blocks}
        self.assertIn(3, lines)
        self.assertIn(4, lines)
        self.assertIn(6, lines)
        self.assertNotIn(5, lines)
        rules = {(item.line, item.rule) for item in WRITING.check_blocks(blocks)}
        self.assertEqual(rules, {(3, "U1"), (4, "U1"), (6, "W1")})

    def test_character_literals_do_not_start_strings(self) -> None:
        source = ("def quote : Char := '\"'\n"
                  "def escaped : Char := '\\''\n"
                  "def x' : Nat := 1\n"
                  "/-- The definition utilizes a quote. -/\n"
                  "def y : Nat := 2\n")
        blocks = WRITING.lean_blocks("A.lean", source)
        rules = {(item.line, item.rule) for item in WRITING.check_blocks(blocks)}
        self.assertEqual(rules, {(4, "W1")})


class ChangedLineTests(unittest.TestCase):
    def test_only_changed_blocks_are_checked(self) -> None:
        git_env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
        with tempfile.TemporaryDirectory() as directory, \
                mock.patch.dict(os.environ, git_env, clear=True):
            root = Path(directory)
            empty = root / "empty-git-config"
            empty.mkdir()
            # Isolate both fixture commands and WRITING.git from the caller's Git setup.
            os.environ.update({
                "GIT_CONFIG_NOSYSTEM": "1",
                "GIT_CONFIG_SYSTEM": os.devnull,
                "GIT_CONFIG_GLOBAL": os.devnull,
                "GIT_CONFIG_COUNT": "3",
                "GIT_CONFIG_KEY_0": "commit.gpgsign",
                "GIT_CONFIG_VALUE_0": "false",
                "GIT_CONFIG_KEY_1": "core.hooksPath",
                "GIT_CONFIG_VALUE_1": str(empty),
                "GIT_CONFIG_KEY_2": "init.templateDir",
                "GIT_CONFIG_VALUE_2": str(empty),
            })

            def run(*args: str) -> None:
                subprocess.run(["git", *args], cwd=root, check=True, capture_output=True)

            run("init", "-q", "-b", "main")
            run("config", "user.email", "test@example.org")
            run("config", "user.name", "Test")
            (root / "page.md").write_text("Old text; with a semicolon.\n\nA clean line.\n")
            run("add", "page.md")
            run("commit", "-q", "-m", "base")
            run("checkout", "-q", "-b", "topic")
            (root / "page.md").write_text(
                "Old text; with a semicolon.\n\nA clean line.\n\nNew text; also bad.\n")
            (root / "untracked.md").write_text("Untracked; ignored.\n")
            (root / "sp ace.md").write_text("Spaced; name.\n")
            run("add", "sp ace.md")
            with mock.patch.object(WRITING, "ROOT", root):
                blocks = WRITING.changed_blocks("main")
            self.assertEqual([(block.path, block.line) for block in blocks], [("page.md", 5), ("sp ace.md", 1)])
            for setting in ["diff.mnemonicPrefix", "diff.noprefix"]:
                run("config", setting, "true")
                with mock.patch.object(WRITING, "ROOT", root):
                    blocks = WRITING.changed_blocks("main")
                self.assertEqual([block.path for block in blocks], ["page.md", "sp ace.md"], setting)
                run("config", "--unset", setting)


if __name__ == "__main__":
    unittest.main()
