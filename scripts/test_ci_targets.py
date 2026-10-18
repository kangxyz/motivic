"""CI coverage fixtures for source outside curated roots and affected consumers."""
# Authors: kangxyz
from pathlib import Path
from contextlib import redirect_stdout
import io
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from ci_targets import main, select_client, select_targets, validation_scope


class TargetSelectionTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.write('Motivic.lean', 'import Motivic.Public\n')
        self.write('Motivic/Public.lean', 'import Motivic.Public.Core\n')
        self.write('Motivic/Public/Core.lean', 'import Mathlib.Algebra.Group.Basic\n')
        self.write('Motivic/Optional/Computation.lean', 'import Mathlib.Algebra.Group.Basic\n')
        self.write('MotivicTest.lean', 'import MotivicTest.PublicAPI\n')
        self.write('MotivicTest/PublicAPI.lean', 'import Motivic.Public\n')

    def write(self, name, content):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)

    def test_optional_changed_leaf_is_built_without_unrelated_roots(self):
        self.assertEqual(select_targets(self.root, ['Motivic/Optional/Computation.lean']),
                         ['Motivic.Optional.Computation'])

    def test_optional_leaf_adds_import_only_facade_without_directory(self):
        self.write('Motivic/NormEndpoint.lean', '''/- Header with /- nested comment -/ def text. -/
module

public import
  Motivic.Optional.Computation

/-! An optional public endpoint, outside the default core. -/
@[expose] public section
''')
        self.assertFalse((self.root / 'Motivic/NormEndpoint').exists())
        self.assertEqual(select_targets(self.root, ['Motivic/Optional/Computation.lean']),
                         ['Motivic.NormEndpoint', 'Motivic.Optional.Computation'])

    def test_optional_endpoint_and_facade_select_terminal_test_without_default_expansion(self):
        self.write('Motivic/Optional/AffineLineEndpoint.lean',
                   'import Mathlib.Algebra.Group.Basic\nexample : True := by trivial\n')
        self.write('Motivic/AffineLine.lean', 'import Motivic.Optional.AffineLineEndpoint\n')
        self.write('MotivicTest/SheafCohomologyAffineLineHigherVanishing.lean',
                   'import Motivic.AffineLine\nexample : True := by trivial\n#print axioms True.intro\n')
        self.write('MotivicTest/Unrelated.lean',
                   'import Motivic.Public\nexample : True := by trivial\n')
        terminal = 'MotivicTest.SheafCohomologyAffineLineHigherVanishing'
        for changed, expected in (
                ('Motivic/Optional/AffineLineEndpoint.lean',
                 ['Motivic.AffineLine', 'Motivic.Optional.AffineLineEndpoint', terminal]),
                ('Motivic/AffineLine.lean', ['Motivic.AffineLine', terminal])):
            with self.subTest(changed=changed):
                self.assertEqual(select_targets(self.root, [changed]), expected)

    def test_mixed_config_or_tool_change_retains_changed_optional_leaf(self):
        for infrastructure in ('lake-manifest.json', 'scripts/build.py'):
            with self.subTest(infrastructure=infrastructure):
                self.assertEqual(select_targets(self.root, [infrastructure,
                                  'Motivic/Optional/Computation.lean']),
                                 ['Motivic', 'Motivic.Optional.Computation', 'MotivicTest'])

    def test_client_only_source_and_config_select_public_build_and_client(self):
        for path in ('examples/downstream/MotivicClient.lean',
                     'examples/downstream/lakefile.toml',
                     'examples/downstream/lean-toolchain'):
            with self.subTest(path=path):
                targets = select_targets(self.root, [path])
                self.assertEqual(targets, ['Motivic'])
                self.assertTrue(select_client(self.root, [path], targets))
                self.assertEqual(validation_scope([path]), (True, []))

    def test_public_changes_select_client_but_unrelated_optional_and_docs_do_not(self):
        self.write('examples/downstream/MotivicClient.lean', 'module\npublic import Motivic\n')
        self.assertTrue(select_client(self.root, ['Motivic/Public/Core.lean'],
                                     select_targets(self.root, ['Motivic/Public/Core.lean'])))
        self.assertFalse(select_client(self.root, ['Motivic/Optional/Computation.lean'],
                                      select_targets(self.root, ['Motivic/Optional/Computation.lean'])))
        self.assertFalse(select_client(self.root, ['examples/downstream/README.md'], []))

    def test_docs_only_selects_no_lean(self):
        self.assertEqual(select_targets(self.root, ['README.md', 'doc/INTERFACES.md']), [])

    def test_changed_public_dependency_adds_only_reachable_public_consumers(self):
        targets = select_targets(self.root, ['Motivic/Public/Core.lean'])
        self.assertEqual(targets, ['Motivic', 'Motivic.Public', 'Motivic.Public.Core', 'MotivicTest', 'MotivicTest.PublicAPI'])
        self.assertNotIn('Motivic.Optional.Computation', targets)

    def test_first_push_cli_selects_both_roots_without_git_history(self):
        result = subprocess.run([sys.executable, str(Path(__file__).with_name('ci_targets.py')),
                                 '--root', str(self.root), '--event', 'push',
                                 '--base', '0' * 40], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), 'Motivic MotivicTest')

    def test_pin_or_tool_change_selects_both_roots(self):
        for changed in ('lake-manifest.json', 'scripts/build.py', '.github/workflows/ci.yml'):
            self.assertEqual(select_targets(self.root, [changed]), ['Motivic', 'MotivicTest'])

    def test_manual_targets_are_existing_local_modules(self):
        self.assertEqual(select_targets(self.root, [], full=True,
                                        manual=['Motivic.Optional.Computation']),
                         ['Motivic.Optional.Computation'])
        with self.assertRaisesRegex(ValueError, 'existing local'):
            select_targets(self.root, [], manual=['Mathlib.Algebra.Group.Basic'])


class ValidationScopeTests(unittest.TestCase):
    def test_docs_only_skips_structural_and_tool_checks(self):
        self.assertEqual(validation_scope(['README.md', 'doc/DEVELOPMENT.md',
                                           'scripts/README.md', '.github/README.md']), (False, []))

    def test_lean_and_pin_changes_check_structure_without_tool_fixture_replay(self):
        for path in ('Motivic/Optional/Computation.lean', 'MotivicTest/PublicAPI.lean',
                     'lake-manifest.json', 'lean-toolchain'):
            with self.subTest(path=path):
                self.assertEqual(validation_scope([path]), (True, []))

    def test_current_tool_dependencies_select_only_their_owned_fixtures(self):
        groups = {
            'test_ci_targets.py': ('ci_targets.py', 'test_ci_targets.py'),
            'test_build.py': ('build.py', 'test_build.py'),
            'test_build_client.py': ('build_client.py', 'test_build_client.py'),
            'test_repository.py': ('cache.py', 'check_repository.py', 'test_repository.py'),
        }
        for fixture, tools in groups.items():
            for tool in tools:
                with self.subTest(tool=tool):
                    structural, selected = validation_scope(['scripts/' + tool])
                    self.assertEqual(selected, [fixture])
                    self.assertEqual(structural, tool == 'check_repository.py')

    def test_shared_parser_setup_and_unknown_tools_select_safe_full_scope(self):
        self.assertEqual(validation_scope([], setup=True), (True, ['test_*.py']))
        for path in ('scripts/library_sources.py', 'scripts/new_tool.py',
                     'scripts/test_new_tool.py', '.github/workflows/ci.yml'):
            with self.subTest(path=path):
                self.assertEqual(validation_scope([path]), (True, ['test_*.py']))
        self.assertEqual(validation_scope(['scripts/library_sources.py', 'scripts/build.py']),
                         (True, ['test_*.py']))

    def test_explicit_manual_acceptance_checks_structure_without_unchanged_tool_tests(self):
        self.assertEqual(validation_scope([], manual=True), (True, []))

    def test_first_setup_cli_emits_all_scope_outputs_before_any_check(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / 'Motivic.lean').write_text('module\n')
            (root / 'MotivicTest.lean').write_text('module\n')
            output = root / 'outputs'
            result = subprocess.run([sys.executable, str(Path(__file__).with_name('ci_targets.py')),
                                     '--root', str(root), '--event', 'push', '--base', '0' * 40,
                                     '--github-output', str(output)], capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            values = dict(line.split('=', 1) for line in output.read_text().splitlines())
            self.assertEqual(values, dict(lean='true', targets='Motivic MotivicTest',
                                          client='false', structural='true', tool_tests='test_*.py'))

    def test_docs_only_cli_keeps_outputs_valid_when_checks_are_skipped(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / 'Motivic.lean').write_text('module\n')
            (root / 'MotivicTest.lean').write_text('module\n')
            output = root / 'outputs'
            argv = ['ci_targets.py', '--root', str(root), '--event', 'push',
                    '--base', '1' * 40, '--github-output', str(output)]
            with patch.object(sys, 'argv', argv), patch('ci_targets.subprocess.check_output',
                    return_value=b'README.md\0.github/README.md\0'), redirect_stdout(io.StringIO()):
                self.assertEqual(main(), 0)
            values = dict(line.split('=', 1) for line in output.read_text().splitlines())
            self.assertEqual(values, dict(lean='false', targets='',
                                          client='false', structural='false', tool_tests=''))


if __name__ == '__main__':
    unittest.main()
