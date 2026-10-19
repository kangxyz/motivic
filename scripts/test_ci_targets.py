"""Finite selector/transport fixtures; no Lean, native caches or mathematical replay."""
# Authors: kangxyz
from pathlib import Path
import base64
import gzip
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import unittest

from ci_targets import CONFIG_INPUTS, comparison_base, changed_paths, encode_targets, make_plan, select_client, select_targets, validation_scope


class Fixture(unittest.TestCase):
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
        self.write('examples/downstream/MotivicClient.lean', 'import Motivic\n')

    def write(self, name, content):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)


class TargetSelectionTests(Fixture):
    def test_optional_leaf_does_not_select_unrelated_roots(self):
        self.assertEqual(select_targets(self.root, ['Motivic/Optional/Computation.lean']),
                         ['Motivic.Optional.Computation'])

    def test_all_actual_consumers_include_implementations_and_tests(self):
        self.write('Motivic/Consumer.lean', 'import Motivic.Optional.Computation\nexample : True := by trivial\n')
        self.write('MotivicTest/Consumer.lean', 'import Motivic.Consumer\nexample : True := by trivial\n')
        plan = make_plan(self.root, ['Motivic/Optional/Computation.lean'])
        self.assertEqual(plan['targets'], ['Motivic.Consumer', 'Motivic.Optional.Computation', 'MotivicTest.Consumer'])
        self.assertEqual(plan['providers'], ['Motivic.Optional.Computation'])
        self.assertFalse(plan['client'])

    def test_changed_public_dependency_retains_required_roots_and_client(self):
        plan = make_plan(self.root, ['Motivic/Public/Core.lean'])
        self.assertEqual(plan['targets'], ['Motivic', 'Motivic.Public', 'Motivic.Public.Core',
                                          'MotivicTest', 'MotivicTest.PublicAPI'])
        self.assertEqual(plan['providers'], ['Motivic.Public.Core'])
        self.assertTrue(plan['client'])

    def test_deleted_provider_keeps_current_consumers_but_absent_name_is_not_built(self):
        (self.root / 'Motivic/Public/Core.lean').unlink()
        targets = select_targets(self.root, ['Motivic/Public/Core.lean'])
        self.assertIn('Motivic.Public', targets)
        self.assertNotIn('Motivic.Public.Core', targets)

    def test_docs_and_tool_changes_do_not_request_native_work(self):
        for path in ('README.md', 'docs/evidence.json', 'docs/history/Old.lean',
                     'scripts/build.py', '.github/workflows/ci.yml', 'unknown/config.json'):
            self.assertEqual(select_targets(self.root, [path]), [], path)
        self.assertEqual(validation_scope(['docs/evidence.json']), (True, []))

    def test_pin_change_requires_explicit_scope_without_root_fallback(self):
        with self.assertRaisesRegex(ValueError, 'explicit targets'):
            select_targets(self.root, ['lake-manifest.json'])
        self.assertEqual(select_targets(self.root, ['lake-manifest.json'],
                         manual=['Motivic.Optional.Computation']), ['Motivic.Optional.Computation'])

    def test_full_is_explicit_and_includes_optional_leaves(self):
        targets = select_targets(self.root, [], full=True)
        self.assertEqual(targets, sorted(targets))
        self.assertIn('Motivic.Optional.Computation', targets)
        with self.assertRaisesRegex(ValueError, 'existing local'):
            select_targets(self.root, [], manual=['Mathlib'])

    def test_test_only_retains_direct_producers_before_tests_without_unrelated_client(self):
        plan = make_plan(self.root, ['MotivicTest/PublicAPI.lean'])
        self.assertEqual(plan['providers'], ['Motivic.Public'])
        self.assertIn('Motivic.Public', plan['lint'])
        self.assertIn('MotivicTest.PublicAPI', plan['targets'])
        self.assertFalse(plan['client'])
        self.assertNotIn('Motivic.Optional.Computation', plan['targets'])

    def test_explicit_manual_test_target_retains_its_production_prerequisites(self):
        plan = make_plan(self.root, [], manual=['MotivicTest.PublicAPI'])
        self.assertEqual(plan['providers'], ['Motivic.Public'])
        self.assertIn('Motivic.Public', plan['targets'])
        self.assertIn('Motivic.Public', plan['lint'])

    def test_client_input_checks_its_real_imports_and_no_optional_leaf(self):
        plan = make_plan(self.root, ['examples/downstream/MotivicClient.lean'])
        self.assertTrue(plan['client'])
        self.assertEqual(plan['providers'], ['Motivic'])
        self.assertEqual(plan['targets'], ['Motivic'])
        self.assertNotIn('Motivic.Optional.Computation', plan['targets'])
        self.assertFalse(select_client(self.root, ['examples/downstream/README.md'], []))

    def test_tools_select_their_affected_fixtures(self):
        for path in ('scripts/build.py', 'scripts/build_modules.py'):
            self.assertEqual(validation_scope([path]),
                             (True, ['test_build.py', 'test_validate.py']))
        self.assertEqual(validation_scope(['scripts/ci_targets.py']),
                         (True, ['test_ci_targets.py', 'test_validate.py']))
        self.assertEqual(validation_scope(['scripts/cache_bootstrap.py']),
                         (True, ['test_repository.py', 'test_validate.py']))
        self.assertEqual(validation_scope(['scripts/new_tool.py']), (True, ['test_*.py']))


class GitFixture(Fixture):
    def git(self, *args):
        return subprocess.check_output(['git', *args], cwd=self.root).decode().strip()

    def setUp(self):
        super().setUp()
        self.git('init', '-q')
        self.git('config', 'user.name', 'Fixture')
        self.git('config', 'user.email', 'fixture@example.invalid')
        self.git('add', '.')
        self.git('commit', '-qm', 'fixture')
        self.base = self.git('rev-parse', 'HEAD')

    def cli(self, *args):
        return subprocess.run([sys.executable, str(Path(__file__).with_name('ci_targets.py')),
                               '--root', str(self.root), *args], capture_output=True, text=True)


class GitScopeTests(GitFixture):
    def test_true_initial_commit_uses_root_diff_not_curated_or_full_defaults(self):
        self.write('lake-manifest.json', '{}\n')
        self.assertEqual(comparison_base(self.root, '0' * 40, 'HEAD'), '--root')
        result = self.cli('--base', '0' * 40)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('Motivic.Optional.Computation', result.stdout)

    def test_shallow_boundary_is_not_misidentified_as_true_initial_commit(self):
        self.write('README.md', 'change\n')
        self.git('add', '.')
        self.git('commit', '-qm', 'second')
        clone = self.root / 'shallow'
        subprocess.run(['git', 'clone', '-q', '--depth', '1', self.root.as_uri(), str(clone)], check=True)
        with self.assertRaisesRegex(ValueError, 'shallow'):
            comparison_base(clone, '0' * 40, 'HEAD')

    def test_unknown_explicit_base_fails_without_full_fallback(self):
        result = self.cli('--base', 'missing-base')
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, '')

    def test_new_branch_derives_fetched_default_merge_base(self):
        self.git('update-ref', 'refs/remotes/origin/main', self.base)
        self.write('README.md', 'change\n')
        self.git('add', '.')
        self.git('commit', '-qm', 'docs')
        self.assertEqual(comparison_base(self.root, '0' * 40, 'HEAD', 'main'), self.base)
        result = self.cli('--base', '0' * 40, '--default-branch', 'main')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), '')

    def test_unresolvable_missing_base_is_actionable_and_manual_targets_still_work(self):
        self.write('README.md', 'change\n')
        self.git('add', '.')
        self.git('commit', '-qm', 'second')
        result = self.cli('--event', 'workflow_dispatch', '--base', '')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('trustworthy', result.stderr)
        result = self.cli('--event', 'workflow_dispatch', '--base', '',
                          '--manual-targets', 'Motivic.Optional.Computation')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), 'Motivic.Optional.Computation')

    def test_rename_tracks_old_and_new_names_and_deleted_consumers(self):
        self.git('mv', 'Motivic/Public/Core.lean', 'Motivic/Public/Renamed.lean')
        paths = changed_paths(self.root, self.base, 'HEAD')
        self.assertIn('Motivic/Public/Core.lean', paths)
        self.assertIn('Motivic/Public/Renamed.lean', paths)
        targets = select_targets(self.root, paths)
        self.assertIn('Motivic.Public', targets)
        self.assertIn('Motivic.Public.Renamed', targets)
        self.assertNotIn('Motivic.Public.Core', targets)

    def test_docs_only_cli_emits_static_only_plan(self):
        self.write('docs/evidence.json', '{}\n')
        output = self.root / 'outputs'
        result = self.cli('--base', self.base, '--github-output', str(output))
        self.assertEqual(result.returncode, 0, result.stderr)
        values = dict(line.split('=', 1) for line in output.read_text().splitlines())
        plan = json.loads(gzip.decompress(base64.b64decode(values['plan_gzip_base64'])))
        self.assertFalse(plan['targets'])
        self.assertEqual(values['lean'], 'false')
        self.assertEqual(values['structural'], 'true')
        self.assertEqual(values['tool_tests'], '')

    def test_head_must_match_checked_out_sources(self):
        self.write('README.md', 'change\n')
        self.git('add', '.')
        self.git('commit', '-qm', 'second')
        result = self.cli('--base', self.base, '--head', self.base)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('checked-out', result.stderr)


class DependencyScopeTests(GitFixture):
    def setUp(self):
        super().setUp()
        self.old, self.new = '1' * 40, '2' * 40
        self.configure(self.old)
        self.git('add', '.')
        self.git('commit', '-qm', 'old pin')
        self.base = self.git('rev-parse', 'HEAD')
        before = self.hashes()
        self.configure(self.new)
        self.record = dict(version=1, dependency=dict(name='Aglib', before=self.old, after=self.new),
                           before=before, after=self.hashes(), targets=['Motivic.Public.Core'])
        self.save_record()

    def configure(self, revision):
        self.write('lakefile.toml', f'[[require]]\nname = "Aglib"\nrev = "{revision}"\n')
        self.write('lake-manifest.json', json.dumps(dict(packages=[dict(name='Aglib', rev=revision)])))
        self.write('lean-toolchain', 'leanprover/lean4:v4.34.1\n')

    def hashes(self):
        return {name: hashlib.sha256((self.root / name).read_bytes()).hexdigest()
                if (self.root / name).exists() else None for name in CONFIG_INPUTS}

    def save_record(self):
        self.write('.github/dependency-scope.json', json.dumps(self.record))

    def test_accepted_transition_selects_reviewed_provider_consumers_tests_and_client(self):
        plan_path = self.root / 'plan.json'
        result = self.cli('--base', self.base, '--plan', str(plan_path))
        self.assertEqual(result.returncode, 0, result.stderr)
        plan = json.loads(plan_path.read_text())
        self.assertEqual(plan['targets'], ['Motivic', 'Motivic.Public', 'Motivic.Public.Core',
                                           'MotivicTest', 'MotivicTest.PublicAPI'])
        self.assertEqual(plan['providers'], ['Motivic.Public.Core'])
        self.assertTrue(plan['client'])
        self.assertFalse(plan['full'])
        self.assertEqual(plan['dependency_scope_sha256'], hashlib.sha256(
            (self.root / '.github/dependency-scope.json').read_bytes()).hexdigest())

    def test_unchanged_metadata_test_seed_does_not_select_unrelated_providers_or_client(self):
        self.record['targets'] = ['MotivicTest.PublicAPI']
        self.save_record()
        plan_path = self.root / 'plan.json'
        result = self.cli('--base', self.base, '--plan', str(plan_path))
        self.assertEqual(result.returncode, 0, result.stderr)
        plan = json.loads(plan_path.read_text())
        self.assertEqual(plan['targets'], ['MotivicTest', 'MotivicTest.PublicAPI'])
        self.assertEqual(plan['lint'], ['MotivicTest.PublicAPI'])
        self.assertEqual(plan['providers'], [])
        self.assertFalse(plan['client'])

    def test_real_test_edit_during_upgrade_retains_its_production_prerequisites(self):
        self.record['targets'] = ['MotivicTest.PublicAPI']
        self.save_record()
        self.write('MotivicTest/PublicAPI.lean', 'import Motivic.Public\n-- Actual test edit\n')
        plan_path = self.root / 'plan.json'
        result = self.cli('--base', self.base, '--plan', str(plan_path))
        self.assertEqual(result.returncode, 0, result.stderr)
        plan = json.loads(plan_path.read_text())
        self.assertEqual(plan['providers'], ['Motivic.Public'])
        self.assertEqual(plan['targets'], ['Motivic.Public', 'MotivicTest', 'MotivicTest.PublicAPI'])
        self.assertEqual(plan['lint'], ['Motivic.Public', 'MotivicTest.PublicAPI'])

    def test_missing_malformed_and_wrong_schema_records_fail_closed(self):
        path = self.root / '.github/dependency-scope.json'
        for content in (None, '{', '{}', json.dumps(dict(self.record, version=True)),
                        json.dumps(dict(self.record, unexpected=True))):
            with self.subTest(content=content):
                if content is None:
                    path.unlink()
                else:
                    path.write_text(content)
                result = self.cli('--base', self.base)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, '')
                self.assertIn('dependency-scope.json', result.stderr)

    def test_stale_before_after_and_incomplete_configuration_bindings_fail(self):
        for side in ('before', 'after'):
            for mutation in ('stale', 'missing'):
                with self.subTest(side=side, mutation=mutation):
                    original = self.record[side].copy()
                    if mutation == 'stale':
                        self.record[side]['lakefile.toml'] = '0' * 64
                    else:
                        del self.record[side]['lakefile.lean']
                    self.save_record()
                    result = self.cli('--base', self.base)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout, '')
                    self.record[side] = original

    def test_unexpected_configuration_change_fails(self):
        self.write('lean-toolchain', 'unexpected compiler\n')
        result = self.cli('--base', self.base)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('after configuration: lean-toolchain', result.stderr)

    def test_declared_revisions_must_match_both_lakefile_and_manifest(self):
        for side in ('before', 'after'):
            with self.subTest(side=side):
                original = self.record['dependency'][side]
                self.record['dependency'][side] = '3' * 40
                self.save_record()
                result = self.cli('--base', self.base)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('revision disagrees', result.stderr)
                self.record['dependency'][side] = original
        self.write('lake-manifest.json', json.dumps(dict(packages=[dict(name='Aglib', rev=self.old)])))
        self.record['after'] = self.hashes()
        self.save_record()
        result = self.cli('--base', self.base)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('revision disagrees', result.stderr)

    def test_invalid_empty_duplicate_and_nonlocal_targets_fail(self):
        for targets in ([], ['Mathlib'], ['Motivic.Missing'], ['Motivic.Public.Core'] * 2, [1]):
            with self.subTest(targets=targets):
                self.record['targets'] = targets
                self.save_record()
                result = self.cli('--base', self.base)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, '')

    def test_following_docs_push_ignores_retained_even_malformed_record(self):
        self.git('add', '.')
        self.git('commit', '-qm', 'upgrade')
        base = self.git('rev-parse', 'HEAD')
        self.write('docs/update.md', 'documentation\n')
        self.write('.github/dependency-scope.json', 'malformed retained record')
        result = self.cli('--base', base)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), '')

    def test_explicit_manual_and_full_routes_do_not_require_metadata(self):
        (self.root / '.github/dependency-scope.json').unlink()
        for extra in (['--manual-targets', 'Motivic.Optional.Computation'], ['--full']):
            with self.subTest(extra=extra):
                result = self.cli('--base', self.base, *extra)
                self.assertEqual(result.returncode, 0, result.stderr)

    def test_transported_plan_revalidates_record_bytes_before_any_native_work(self):
        plan = self.root / 'plan.json'
        result = self.cli('--base', self.base, '--plan', str(plan))
        self.assertEqual(result.returncode, 0, result.stderr)
        validate = Path(__file__).with_name('validate.py')
        argv = [sys.executable, str(validate), '--root', str(self.root), '--plan', str(plan), '--list']
        accepted = subprocess.run(argv, capture_output=True, text=True)
        self.assertEqual(accepted.returncode, 0, accepted.stderr)
        path = self.root / '.github/dependency-scope.json'
        path.write_text(path.read_text() + '\n')
        rejected = subprocess.run(argv, capture_output=True, text=True)
        self.assertNotEqual(rejected.returncode, 0)
        self.assertIn('selection changed', rejected.stderr)
        self.assertFalse((self.root / '.lake').exists())


class TargetTransportTests(unittest.TestCase):
    def test_large_ordered_selection_roundtrips_deterministically(self):
        targets = [f'Motivic.AlgebraicGeometry.Selected.Module{i:05d}' for i in range(3015)]
        self.assertGreater(len(' '.join(targets).encode()), 128 * 1024)
        encoded = encode_targets(targets)
        self.assertLess(len(encoded), 128 * 1024)
        self.assertEqual(gzip.decompress(base64.b64decode(encoded, validate=True)).decode().splitlines(), targets)
        self.assertEqual(encoded, encode_targets(targets))

    def test_workflow_gates_every_native_step_and_uses_exact_plan(self):
        workflow = (Path(__file__).resolve().parents[1] / '.github/workflows/ci.yml').read_text()
        self.assertIn("if: needs.source.outputs.lean == 'true'", workflow)
        self.assertIn('--plan "$RUNNER_TEMP/validation-plan.json"', workflow)
        self.assertIn('plan_gzip_base64: ${{ steps.scope.outputs.plan_gzip_base64 }}', workflow)
        self.assertNotIn('export_targets=', workflow)
        self.assertNotIn('default: Motivic MotivicTest', workflow)
        self.assertNotIn("needs.source.outputs.client == 'true' ||", workflow)


if __name__ == '__main__':
    unittest.main()
