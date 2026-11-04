#!/usr/bin/env -S uv run --no-project --python 3.12 python
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Regression tests for the advisory prose script, `scripts/writing_hints.py`."""

from __future__ import annotations

import importlib.util
import io
from contextlib import chdir
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


    def test_definition_description_is_still_checked(self) -> None:
        self.assertEqual(findings("- `δ` — We utilize the lemma."), ["W1"])

    def test_words(self) -> None:
        self.assertEqual(findings("Use a ring, e.g. the integers."), ["W7"])
        self.assertEqual(findings("We utilize the lemma."), ["W1"])
        self.assertEqual(findings("Set up the build."), ["W6"])
        self.assertEqual(findings("The value ends in a zero byte."), [])
        self.assertEqual(findings("Don't run the build."), ["S5"])
        self.assertEqual(findings("The prover's message is short."), [])


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
        text = "| Utilize this header | Use |\n|---|---|\n| We utilize this cell. | Fine. |\n"
        self.assertEqual(findings(text), ["W1"])


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
        self.assertIn("[WRITING W1]", output.getvalue())
        self.assertIn("writing suggestion(s)", output.getvalue())

    def test_other_file_types_are_refused(self) -> None:
        with mock.patch("sys.stderr", io.StringIO()):
            with self.assertRaises(SystemExit) as raised:
                WRITING.main(["writing_hints.py", "scripts/differential.py"])
        self.assertEqual(raised.exception.code, 2)


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
                with chdir(ROOT), mock.patch.object(Path, "read_text", read), \
                     mock.patch.object(Path, "is_file", return_value=True), \
                     mock.patch("sys.stdout", io.StringIO()) as output:
                    WRITING.main(["writing_hints.py", form])
                self.assertIn("[WRITING C8]", output.getvalue())

    def test_empty_stdin_label_is_valid(self) -> None:
        with mock.patch("sys.stdin", io.StringIO("A complete sentence.")), \
                mock.patch("sys.stdout", io.StringIO()) as output:
            self.assertEqual(WRITING.main(["writing_hints.py", "--stdin", ""]), 0)
        self.assertIn("No writing suggestions.", output.getvalue())

    def test_valid_symlink_keeps_the_target_history_scope(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            target = root / "STFSpec/informal/modules/EthBase.md"
            target.parent.mkdir(parents=True)
            target.write_text("It is no longer used.\n")
            alias = root / "alias.md"
            alias.symlink_to(target)
            with mock.patch.object(WRITING, "ROOT", root), \
                    mock.patch("sys.stdout", io.StringIO()) as output:
                self.assertEqual(WRITING.main(["writing_hints.py", str(alias)]), 0)
            self.assertIn("[WRITING C8]", output.getvalue())

    def test_missing_file_is_a_usage_error(self) -> None:
        with mock.patch("sys.stderr", io.StringIO()):
            with self.assertRaises(SystemExit) as raised:
                WRITING.main(["writing_hints.py", "no-such-file.md"])
        self.assertEqual(raised.exception.code, 2)


class LeanExtractionTests(unittest.TestCase):
    def test_structural_indentation_preserves_prose_and_relative_code(self) -> None:
        for indentation in ['    ', '\t', '  ']:
            with self.subTest(indentation=repr(indentation)):
                source = ('namespace N\n' + indentation + '/--\n'
                          + indentation + 'We utilize the helper.\n\n'
                          + indentation + '    We utilize code here.\n\n'
                          + indentation + 'We utilize actual prose.\n'
                          + indentation + '-/\nend N\n')
                found = WRITING.check_blocks(WRITING.lean_blocks('A.lean', source))
                self.assertEqual([(f.line, f.rule) for f in found], [(3, 'W1'), (7, 'W1')])

    def test_doc_comments_and_line_numbers(self) -> None:
        source = ('/-! # Title\n\nWe utilize this module. -/\n'
                  'def f : Nat := 1 -- We utilize this value.\n'
                  'def s : String := "-- utilize is not a comment"\n'
                  '/-- The definition utilizes `x; y`. -/\n'
                  'theorem t : True := trivial\n')
        blocks = WRITING.lean_blocks("A.lean", source)
        lines = {block.line: block.text for block in blocks}
        self.assertIn(3, lines)
        self.assertIn(4, lines)
        self.assertIn(6, lines)
        self.assertNotIn(5, lines)
        rules = {(item.line, item.rule) for item in WRITING.check_blocks(blocks)}
        self.assertEqual(rules, {(3, "W1"), (4, "W1"), (6, "W1")})

    def test_unterminated_comment_keeps_its_final_characters(self) -> None:
        blocks = WRITING.lean_blocks('A.lean', '/-- First line.\nWe utilize')
        found = WRITING.check_blocks(blocks)
        self.assertEqual([(item.line, item.rule) for item in found], [(2, 'W1')])
        self.assertTrue(found[0].excerpt.endswith('utilize'))

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


class WritingRegressionTests(unittest.TestCase):
    def test_findings_point_to_the_source_line(self) -> None:
        text = ('The [reference](https://example.org/a(b)) and `x` agree.\n'
                'The quoted "a; b" is code here.\n'
                'We utilize the last line.\n')
        found = WRITING.check_blocks(WRITING.file_blocks('page.md', text))
        item = next(f for f in found if f.rule == 'W1')
        self.assertEqual(item.line, 3)
        self.assertEqual(item.excerpt, 'utilize')
        self.assertNotIn('Code', item.excerpt)

    def test_line_numbers_in_lists_and_lean_comments(self) -> None:
        cases = [('- First line.\n  We utilize the second line.\n', 'page.md', 2),
                 ('/-! First line.\nWe utilize the second line.\n-/', 'A.lean', 2),
                 ('-- First line.\n-- We utilize the second line.\n', 'A.lean', 2)]
        for text, path, line in cases:
            with self.subTest(path=path, text=text):
                found = WRITING.check_blocks(WRITING.file_blocks(path, text))
                self.assertEqual([f.line for f in found if f.rule == 'W1'], [line])

    def test_word_findings_keep_source_spelling_and_line(self) -> None:
        text = 'A clean line with `code`.\nWe utilize the lemma.\n'
        found = WRITING.check_blocks(WRITING.file_blocks('page.md', text))
        self.assertEqual([(f.line, f.excerpt) for f in found if f.rule == 'W1'], [(2, 'utilize')])

    def test_parenthetical_length_finding_points_inside_the_parenthesis(self) -> None:
        text = 'A short sentence (\n' + ' '.join(['word'] * 30) + ').'
        found = WRITING.check_blocks(WRITING.file_blocks('page.md', text))
        self.assertEqual([f.line for f in found if f.rule == 'S1'], [2])


    def test_latin_abbreviations_have_one_finding(self) -> None:
        for word in ['e.g.', 'i.e.', 'etc.', 'cf.', 'resp.']:
            pattern = WRITING.word_pattern([word])
            blocks = WRITING.file_blocks('page.md', f'Use {word} here.')
            found = [f for b in blocks for f in WRITING.check_block(b, pattern, None)]
            self.assertEqual([f.rule for f in found], ['W7'])

    def test_final_e_verbs_keep_ing_inflections(self) -> None:
        pattern = WRITING.word_pattern(['ensure', 'utilize', 'leverage'])
        for word in ['ensure', 'ensures', 'ensured', 'ensuring', 'utilizing', 'leveraging']:
            self.assertIsNotNone(pattern.fullmatch(word), word)
        self.assertIsNone(pattern.fullmatch('reassuring'))

    def test_fences_use_their_opening_character_and_length(self) -> None:
        for opening, inner in [('~~~~', '```'), ('````', '```'), ('~~~', '```')]:
            text = f'{opening}\n{inner}\nUtilize ignored code.\n{opening}\n\nWe utilize prose.\n'
            found = WRITING.check_blocks(WRITING.file_blocks('page.md', text))
            self.assertEqual([(f.line, f.rule) for f in found], [(6, 'W1')])

    def test_visible_prose_after_comments_and_thematic_breaks(self) -> None:
        for text in ['<!-- comment --> We utilize prose.',
                     '---\nWe utilize prose.\n---', '#1431 utilizes prose.']:
            self.assertIn('W1', findings(text), text)
        self.assertEqual(findings('    Utilize example code.\n'), [])
        self.assertEqual(findings('---\nstatus: utilize metadata\n---\nClean prose.'), [])

    def test_literal_comment_markers_do_not_hide_prose(self) -> None:
        for text in ['The token `<!--` opens a comment.\nWe utilize prose.\n',
                     '```\n<!--\n```\nWe utilize prose.\n',
                     'The token `<!--` is code, as is `-->`.\nWe utilize prose.\n',
                     'The token `some\n<!--\ntext` is literal.\nWe utilize prose.\n',
                     'The text \\<!-- is literal.\nWe utilize prose.\n',
                     'The text \\<!-- utilizes a literal; --> stays visible.']:
            with self.subTest(text=text):
                self.assertIn('W1', findings(text))
        text = 'A clean line.\n    We utilize this paragraph continuation.\n'
        self.assertIn('W1', findings(text))

    def test_indented_list_continuations_remain_prose(self) -> None:
        for text in ['- Outer item.\n\n    - We utilize prose.\n',
                     '1. Outer item.\n\n    1. We utilize prose.\n',
                     '- Outer item.\n\n    We utilize prose.\n']:
            with self.subTest(text=text):
                self.assertIn('W1', findings(text))

    def test_raw_lean_strings_do_not_create_comments(self) -> None:
        for value in ['r#"a " -- utilize fake comment"#', 'r"a\\"']:
            text = f'def s := {value}\n-- We utilize prose.\n'
            found = WRITING.check_blocks(WRITING.file_blocks('A.lean', text))
            self.assertEqual([(f.line, f.rule) for f in found], [(2, 'W1')])

    def test_escaped_newlines_in_lean_strings_keep_comment_locations(self) -> None:
        text = 'def s := "a\\\nb"\n-- We utilize prose.\n'
        found = WRITING.check_blocks(WRITING.file_blocks('A.lean', text))
        self.assertEqual([(f.line, f.rule) for f in found], [(3, 'W1')])


    def test_wrapped_phrasal_and_history_terms_remain_visible(self) -> None:
        self.assertIn('W6', findings('Carry\nout the test.'))
        self.assertIn('C8', findings('The lemma is no\nlonger needed.', 'WRITING.md'))

    def test_wrapped_straight_quotes_are_one_exempt_element(self) -> None:
        text = ('"essentially\nsurjective". Review their meaning. Do not delete them as '
                'isolated words. "Negligible" retains its technical meaning.')
        self.assertEqual(findings(text), [])
        text = 'The text "utilize quoted\nwords; ignored" is literal.\nWe utilize prose.'
        found = WRITING.check_blocks(WRITING.file_blocks('page.md', text))
        self.assertEqual([f.line for f in found if f.rule == 'W1'], [3])


class ChangedFileRegressionTests(unittest.TestCase):
    def setUp(self) -> None:
        super().setUp()
        environment = {key: value for key, value in os.environ.items() if not key.startswith('GIT_')}
        environment.update(GIT_CONFIG_NOSYSTEM='1', GIT_CONFIG_GLOBAL=os.devnull,
                           GIT_CONFIG_SYSTEM=os.devnull)
        patcher = mock.patch.dict(os.environ, environment, clear=True)
        patcher.start(); self.addCleanup(patcher.stop)
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        patcher = mock.patch.object(WRITING, 'ROOT', self.root)
        patcher.start(); self.addCleanup(patcher.stop)
        self.git('init', '-q', '-b', 'main', '--template=')
        self.git('config', 'user.email', 'test@example.org')
        self.git('config', 'user.name', 'Test')
        self.git('config', 'commit.gpgsign', 'false')
        self.git('config', 'core.hooksPath', os.devnull)
        self.git('commit', '-q', '--allow-empty', '-m', 'base')
        self.git('checkout', '-q', '-b', 'topic')

    def git(self, *args: str) -> None:
        subprocess.run(['git', *args], cwd=self.root, check=True, capture_output=True)

    def test_git_settings_and_quoted_paths_do_not_hide_changes(self) -> None:
        names = ['page.md', 'space name.md', 'café.md', 'quote"name.md', 'back\\slash.md',
                 'line\nbreak.md', ':(glob)nothing.md', ':(literal)foo.md', 'a[1].md', 'a*.md']
        for name in names:
            (self.root / name).write_text('Good line.\nWe utilize the second line.\n')
        self.git('add', '.')
        for option in ['diff.noprefix', 'diff.mnemonicPrefix', 'core.quotePath']:
            for value in ['true', 'false']:
                with self.subTest(option=option, value=value):
                    self.git('config', option, value)
                    found = WRITING.check_blocks(WRITING.changed_blocks('main'))
                    self.assertEqual({f.path for f in found if f.rule == 'W1'}, set(names))
                    self.assertEqual({f.line for f in found if f.rule == 'W1'}, {2})

    def test_renames_check_only_edited_prose(self) -> None:
        old, new = 'old café.md', 'new name.md'
        text = 'We utilize unchanged prose.\n\nA clean line.\n'
        (self.root/old).write_text(text)
        self.git('add', '.')
        self.git('commit', '-q', '-m', 'base prose')
        self.git('branch', '-f', 'main', 'HEAD')
        self.git('mv', old, new)
        (self.root/new).write_text(text + '\nWe utilize changed prose.\n')
        self.git('add', '.')
        found = WRITING.check_blocks(WRITING.changed_blocks('main'))
        self.assertEqual([(f.path, f.line) for f in found if f.rule == 'W1'], [(new, 5)])

    def test_inter_hunk_context_does_not_mark_unchanged_prose_as_changed(self) -> None:
        page = self.root / 'page.md'
        page.write_text('First line.\n\nWe utilize unchanged prose.\n\nLast line.\n')
        self.git('add', '.')
        self.git('commit', '-q', '-m', 'base prose')
        self.git('branch', '-f', 'main', 'HEAD')
        page.write_text('Revised first.\n\nWe utilize unchanged prose.\n\nRevised last.\n')
        self.git('config', 'diff.interHunkContext', '10')
        self.assertEqual(WRITING.added_lines('main'), {'page.md': {1, 5}})
        self.assertNotIn('W1', [f.rule for f in WRITING.check_blocks(WRITING.changed_blocks('main'))])

    def test_changed_symlink_sources_have_no_target_line_attribution(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory) / 'outside.md'
            target.write_text('First paragraph.\n\nWe utilize external prose.\n')
            (self.root / 'alias.md').symlink_to(target)
            (self.root / 'good.md').write_text('We utilize actual prose.\n')
            self.git('add', '.')
            diagnostics = []
            blocks = WRITING.changed_blocks('main', diagnostics)
            self.assertEqual([(b.path, b.line) for b in blocks], [('good.md', 1)])
            self.assertEqual([(f.path, f.rule) for f in diagnostics], [('alias.md', 'Input')])
            self.assertIn('link-text diff', diagnostics[0].message)
            with mock.patch('sys.stdout', io.StringIO()) as output:
                self.assertEqual(WRITING.main(['writing_hints.py', '--base', 'main']), 0)
            self.assertIn('1 Input diagnostic(s)', output.getvalue())
            self.assertNotIn('rules Input', output.getvalue())

    def test_non_utf8_and_dangling_symlinks_are_advisory(self) -> None:
        (self.root / 'invalid.md').write_bytes(b'Caf\xe9; text.\n')
        (self.root / 'dangling.md').symlink_to('missing-target')
        (self.root / 'good.md').write_text('We utilize prose.\n')
        self.git('add', '.')
        with mock.patch('sys.stdout', io.StringIO()) as output:
            self.assertEqual(WRITING.main(['writing_hints.py', '--base', 'main']), 0)
        self.assertIn('not UTF-8', output.getvalue())
        self.assertIn('symlink', output.getvalue())
        self.assertIn('W1', output.getvalue())
        self.assertNotIn('No writing suggestions', output.getvalue())
        with mock.patch('sys.stdout', io.StringIO()) as output:
            self.assertEqual(WRITING.main(['writing_hints.py', str(self.root/'invalid.md')]), 0)
        self.assertIn('not UTF-8', output.getvalue())

    def test_invalid_byte_stdin_has_an_input_diagnostic(self) -> None:
        environment = dict(os.environ, PYTHONIOENCODING='utf-8:surrogateescape')
        result = subprocess.run([sys.executable, WRITING.__file__, '--stdin', 'body'],
                                input=b'\xff\n', capture_output=True, env=environment)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(b'not UTF-8', result.stdout)
        self.assertIn(b'1 Input diagnostic(s)', result.stdout)
        self.assertNotIn(b'rules Input', result.stdout)

    def test_missing_base_and_broken_configuration_are_errors(self) -> None:
        with mock.patch('sys.stderr', io.StringIO()) as error:
            with self.assertRaises(SystemExit) as result:
                WRITING.main(['writing_hints.py', '--base', 'missing-base'])
        self.assertEqual(result.exception.code, 2)
        self.assertIn('git failed', error.getvalue())
        with mock.patch('sys.stderr', io.StringIO()), mock.patch('sys.stdin', io.StringIO('')):
            with self.assertRaises(SystemExit) as result:
                WRITING.main(['writing_hints.py', '--stdin', 'body', '--vocabulary',
                              str(self.root/'missing-vocabulary')])
        self.assertEqual(result.exception.code, 2)


class SimpleSuggestionTests(unittest.TestCase):
    def test_grammar_and_structure_are_left_to_review(self) -> None:
        for text in ['The verifier is rejecting the message.', 'The lemma has changed.',
                     'Using the lemma, we bound the error.', 'The bound holds. This is the main result.',
                     'The code is linear; it is cyclic.', 'The code is linear — it is cyclic.',
                     'Before making a change, run the tests.', ' '.join(['One sentence.'] * 7)]:
            with self.subTest(text=text):
                self.assertEqual(findings(text), [])

    def test_suggestions_preserve_success_and_plain_terminology(self) -> None:
        with mock.patch('sys.stdin', io.StringIO('We utilize this lemma.')), \
                mock.patch('sys.stdout', io.StringIO()) as output:
            self.assertEqual(WRITING.main(['writing_hints.py', '--stdin', 'body']), 0)
        self.assertIn('1 writing suggestion(s)', output.getvalue())
        self.assertIn('leave clear, correct text alone', output.getvalue())

    def test_vocabulary_heading_can_be_numbered(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            vocabulary = Path(directory) / 'vocabulary.md'
            vocabulary.write_text('## 6. Words to avoid\n\n| Avoid | Use |\n|---|---|\n'
                                  '| "utilize" | use |\n')
            self.assertEqual(WRITING.avoid_words(vocabulary), (['utilize'], []))


if __name__ == "__main__":
    unittest.main()
