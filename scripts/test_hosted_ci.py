# Authors: kangxyz
"""Committed hosted migration fixtures; no Lean, network or external caches."""
import copy
import hashlib
import os
import re
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from ci_policy import CORE_ENTRYPOINTS, PROTOCOL, TOOLING_REVISION
from shared_workflow import (INITIAL_PARENT, INITIAL_PATHS, REPAIR_PARENT, FOLLOWUP_PARENT, REPAIR_TOOL_PATHS,
                             MotivicAdapter, admitted_baseline, hosted_scope, initial_identity)

ROOT = Path(__file__).resolve().parents[1]


class API:
    def __init__(self, head, *, native='success', finalize='success'):
        self.head, self.native, self.finalize = head, native, finalize

    def get(self, path, **query):
        return {'full_name': 'kangxyz/motivic', 'default_branch': 'main'}

    def pages(self, path, key, **query):
        if key == 'workflow_runs':
            yield dict(id=3, run_attempt=1, head_sha=self.head, status='completed',
                       conclusion='success', head_branch='main', path=PROTOCOL.workflow_path,
                       event='push', head_repository={'full_name': 'kangxyz/motivic'},
                       html_url='https://github.com/kangxyz/motivic/actions/runs/3')
        else:
            yield dict(name='library', status='completed', conclusion='success', steps=[
                dict(name=PROTOCOL.native_step, status='completed', conclusion=self.native),
                dict(name=PROTOCOL.finalize_step, status='completed', conclusion=self.finalize)])


class HostedEnrollmentTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name) / 'repo'
        self.root.mkdir()
        self.write('Motivic.lean', 'module\n')
        self.write('MotivicTest.lean', 'module\n')
        self.write('Motivic/Orphan.lean', 'module\n')
        self.write('MotivicTest/Orphan.lean', 'module\n')
        self.write('examples/downstream/MotivicClient.lean', 'import Motivic\n')
        self.write('lean-toolchain', 'leanprover/lean4:v4.28.0\n')
        self.write('lake-manifest.json', '{}\n')
        for path in [*CORE_ENTRYPOINTS, PROTOCOL.workflow_path, 'scripts/ci_policy.py']:
            target = self.root / path
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / path, target)
        self.git('init', '-q')
        self.git('config', 'user.name', 'CI fixture')
        self.git('config', 'user.email', 'fixture@example.invalid')
        self.commit('fixture parent')
        self.parent = self.git('rev-parse', 'HEAD')
        self.write('docs/DEVELOPMENT.md', 'Fixture cutover\n')
        self.commit('CI-only cutover')
        self.head = self.git('rev-parse', 'HEAD')
        self.addCleanup(patch.stopall)
        patch('shared_workflow.INITIAL_PARENT', self.parent).start()
        patch.dict(os.environ, MOTIVIC_TOOLING_REVISION=TOOLING_REVISION).start()
        self.adapter = MotivicAdapter()

    def write(self, path, value):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(value)

    def git(self, *args):
        return subprocess.check_output(['git', *args], cwd=self.root, stderr=subprocess.PIPE).decode().strip()

    def commit(self, label):
        self.git('add', '.')
        self.git('commit', '-qm', label)

    def application(self):
        from lean_ci.engine import Application
        return Application(self.root, self.adapter)

    def plan(self):
        return self.application().plan('kangxyz/motivic', 'main', self.head,
                                       Path(self.tmp.name) / 'state')

    def test_fixed_cutover_parent_and_exact_owned_paths(self):
        self.assertEqual(INITIAL_PARENT, '0fcc528c48128a37a04f3a6db8b4833cedb4d891')
        self.assertTrue(initial_identity(self.root, self.head))
        self.assertIn('scripts/test_hosted_ci.py', INITIAL_PATHS)
        self.assertNotIn('lake-manifest.json', INITIAL_PATHS)
        self.assertNotIn('Motivic/Orphan.lean', INITIAL_PATHS)

    def test_initial_scope_enrolls_orphan_modules_tests_and_client_without_fake_history(self):
        with patch('shared_workflow.admitted_baseline', side_effect=AssertionError('API fallback')):
            plan = self.plan()
        self.assertEqual(plan['baseline']['kind'], 'initial-enrollment')
        self.assertNotIn('verified_base', plan['baseline'])
        self.assertNotIn('base', plan['baseline'])
        scope = plan['scope']
        self.assertEqual(scope['targets'], ['Motivic', 'Motivic.Orphan', 'MotivicTest', 'MotivicTest.Orphan'])
        self.assertEqual(scope['providers'], ['Motivic', 'Motivic.Orphan'])
        self.assertEqual(scope['lint'], scope['targets'])
        self.assertEqual(scope['tool_tests'], ['test_*.py'])
        self.assertTrue(scope['client'])
        self.assertFalse(scope['full'])
        self.assertEqual(plan['required_phases'], ['source', 'native'])
        tasks = self.adapter.tasks(self.root, plan, 'native', Path(self.tmp.name) / 'native')
        ids = [t['id'] for t in tasks]
        provider_checks = [task for task in tasks if task['id'].startswith('providers/declarations/')]
        self.assertEqual([task['modules'] for task in provider_checks],
                         [[name] for name in scope['providers']])
        self.assertTrue(all(ids.index(task['id']) < ids.index('consumers/build')
                            for task in provider_checks))
        self.assertLess(ids.index('consumers/build'), ids.index('client/build'))
        self.assertTrue(all(t['check_kind'] == 'declaration-exact-origin'
                            for t in tasks if t.get('check_kind', '').startswith('declaration')))

    def test_initial_scope_and_repository_revalidated_at_every_phase(self):
        plan = self.plan()
        for mutate in ('scope', 'repository', 'head', 'baseline'):
            bad = copy.deepcopy(plan)
            if mutate == 'scope':
                bad['scope']['targets'].remove('MotivicTest.Orphan')
            elif mutate == 'repository':
                bad['repository'] = 'someone/motivic'
            elif mutate == 'head':
                bad['head'] = self.parent
            else:
                bad['baseline']['verified_base'] = self.parent
            with self.subTest(mutate=mutate), self.assertRaises(ValueError):
                self.adapter.validate_plan(self.root, bad)

    def test_later_head_never_bootstraps_after_evidence_failure(self):
        self.write('docs/DEVELOPMENT.md', 'Later documentation\n')
        self.commit('later head')
        later = self.git('rev-parse', 'HEAD')
        self.assertFalse(initial_identity(self.root, later))
        from lean_ci.github import BaselineError
        with patch('shared_workflow.admitted_baseline', side_effect=BaselineError('missing history')) as select:
            with self.assertRaisesRegex(BaselineError, 'missing history'):
                self.adapter.plan(self.root, 'kangxyz/motivic', 'main', later)
        select.assert_called_once()

    def test_exact_repair_parent_is_fixed_and_pins_are_not_admitted_owners(self):
        self.assertEqual(REPAIR_PARENT, 'c793b96eb87eee540e665058e83e5f05d5c95683')
        self.assertEqual(FOLLOWUP_PARENT, 'cc5c5d57e05a51ec7b1e7d6994646b306059130e')
        self.assertNotIn('lake-manifest.json', REPAIR_TOOL_PATHS)
        self.assertNotIn('.github/dependency-scope.json', REPAIR_TOOL_PATHS)

    def test_explicit_followup_keeps_complete_enrollment_without_api_fallback(self):
        followup_parent = self.head
        self.write('scripts/test_validate.py', '# repaired task-shape fixture\n')
        self.commit('repair source fixtures after failed enrollment')
        self.head = self.git('rev-parse', 'HEAD')
        with patch('shared_workflow.FOLLOWUP_PARENT', followup_parent), \
                patch('shared_workflow.admitted_baseline', side_effect=AssertionError('API fallback')):
            plan = self.plan()
            self.application().validate_plan(plan)
        self.assertEqual(plan['baseline']['parent'], followup_parent)
        self.assertEqual(plan['baseline']['kind'], 'initial-enrollment')
        self.assertIn('repair', plan['baseline']['selection_reason'])
        self.assertNotIn('base', plan['baseline'])
        self.assertNotIn('verified_base', plan['baseline'])
        self.assertEqual(plan['scope']['targets'], ['Motivic', 'Motivic.Orphan',
                                                  'MotivicTest', 'MotivicTest.Orphan'])
        self.assertEqual(plan['scope']['lint'], plan['scope']['targets'])
        self.assertEqual(plan['scope']['tool_tests'], ['test_*.py'])
        self.assertTrue(plan['scope']['client'])
        self.assertEqual(plan['required_phases'], ['source', 'native'])

    def test_direct_repair_admits_only_the_exact_new_batch_fixture_owner(self):
        from shared_workflow import repair_path
        self.assertIn('scripts/test_declaration_batch.py', REPAIR_TOOL_PATHS)
        self.assertFalse(repair_path('scripts/test_declaration_batch_extra.py'))
        repair_parent = self.head
        self.write('scripts/test_declaration_batch.py', '# owned batch fixture\n')
        self.commit('enroll exact batch fixture')
        with patch('shared_workflow.REPAIR_PARENT', repair_parent):
            self.assertTrue(initial_identity(self.root, self.git('rev-parse', 'HEAD')))

    def test_explicit_direct_repair_enrolls_complete_scope_without_api_or_fake_base(self):
        repair_parent = self.head
        self.write('Motivic/New.lean', 'module\n')
        self.write('MotivicTest/New.lean', 'module\n')
        self.write('docs/RECOVERY.md', 'Source correspondence\n')
        self.write('AGENTS.md', 'Updated interface summary\n')
        self.commit('explicit enrollment repair')
        self.head = self.git('rev-parse', 'HEAD')
        with patch('shared_workflow.REPAIR_PARENT', repair_parent), \
                patch('shared_workflow.admitted_baseline', side_effect=AssertionError('API fallback')):
            plan = self.plan()
            self.application().validate_plan(plan)
            baseline, scope = plan['baseline'], plan['scope']
            self.assertEqual(baseline['kind'], 'initial-enrollment')
            self.assertEqual(baseline['parent'], repair_parent)
            self.assertNotIn('verified_base', baseline)
            self.assertNotIn('base', baseline)
            self.assertIn('Motivic.New', scope['providers'])
            self.assertIn('Motivic.Orphan', scope['providers'])
            self.assertIn('MotivicTest.New', scope['targets'])
            self.assertIn('MotivicTest.Orphan', scope['targets'])
            self.assertEqual(scope['lint'], scope['targets'])
            self.assertEqual(scope['tool_tests'], ['test_*.py'])
            self.assertTrue(scope['client'])
            self.assertFalse(scope['full'])
            for key in ('targets', 'providers', 'lint'):
                bad = copy.deepcopy(plan)
                bad['scope'][key].remove('Motivic.Orphan')
                with self.subTest(key=key), self.assertRaises(ValueError):
                    self.adapter.validate_plan(self.root, bad)
            tasks = self.adapter.tasks(self.root, plan, 'native', Path(self.tmp.name) / 'repair-native')
            self.assertTrue(all(t['check_kind'] == 'declaration-exact-origin'
                                for t in tasks if t.get('check_kind', '').startswith('declaration')))
            style = next(t for t in tasks if t.get('check_kind') == 'style-exact-source')
            self.assertEqual(style['source_modules'], scope['targets'])

    def test_repair_rejects_changed_pins_unrecognized_paths_and_lookalikes(self):
        repair_parent = self.head
        tree = self.git('rev-parse', 'HEAD^{tree}')
        for path in ('lean-toolchain', 'lakefile.toml', 'lakefile.lean', 'lake-manifest.json',
                     '.github/dependency-scope.json', 'scripts/unreviewed.py',
                     'examples/downstream/MotivicClient.lean', ' docs/RECOVERY.md',
                     'Motivic/opaque.bin', 'unexpected.txt'):
            with self.subTest(path=path):
                self.git('read-tree', '--reset', '-u', tree)
                self.write(path, 'Unadmitted change\n')
                self.git('add', '.')
                changed_tree = self.git('write-tree')
                head = self.git('commit-tree', changed_tree, '-p', repair_parent, '-m', 'rejected repair')
                with patch('shared_workflow.REPAIR_PARENT', repair_parent):
                    self.assertFalse(initial_identity(self.root, head))

    def test_repair_rejects_merges_empty_changes_and_grandchildren(self):
        repair_parent = self.head
        tree = self.git('rev-parse', 'HEAD^{tree}')
        empty = self.git('commit-tree', tree, '-p', repair_parent, '-m', 'empty repair')
        self.write('Motivic/Orphan.lean', 'module\n-- repaired\n')
        self.commit('repair')
        repair = self.git('rev-parse', 'HEAD')
        tree = self.git('rev-parse', 'HEAD^{tree}')
        merge = self.git('commit-tree', tree, '-p', repair_parent, '-p', self.parent, '-m', 'merge repair')
        self.write('docs/RECOVERY.md', 'Later documentation\n')
        self.commit('later head')
        later = self.git('rev-parse', 'HEAD')
        with patch('shared_workflow.REPAIR_PARENT', repair_parent):
            self.assertTrue(initial_identity(self.root, repair))
            for head in (empty, merge, later):
                with self.subTest(head=head):
                    self.assertFalse(initial_identity(self.root, head))
            from lean_ci.github import BaselineError
            with patch('shared_workflow.admitted_baseline', side_effect=BaselineError('missing history')) as select:
                with self.assertRaisesRegex(BaselineError, 'missing history'):
                    self.adapter.plan(self.root, 'kangxyz/motivic', 'main', later)
            select.assert_called_once()

    def test_repair_cannot_delete_an_existing_orphan_source(self):
        repair_parent = self.head
        self.git('rm', 'Motivic/Orphan.lean')
        self.commit('delete enrolled orphan')
        with patch('shared_workflow.REPAIR_PARENT', repair_parent):
            self.assertFalse(initial_identity(self.root, self.git('rev-parse', 'HEAD')))

    def test_repair_still_requires_exact_reviewed_workflow_and_recipe(self):
        repair_parent = self.head
        for path in (PROTOCOL.workflow_path, 'scripts/lint_declarations.py'):
            with self.subTest(path=path):
                self.write(path, (self.root / path).read_text() + '\n')
                self.git('add', '.')
                tree = self.git('write-tree')
                head = self.git('commit-tree', tree, '-p', repair_parent, '-m', 'unreviewed repair')
                with patch('shared_workflow.REPAIR_PARENT', repair_parent):
                    self.assertTrue(initial_identity(self.root, head))
                    with self.assertRaisesRegex(ValueError, 'not reviewed'):
                        self.adapter.plan(self.root, 'kangxyz/motivic', 'main', head)
                self.git('checkout', repair_parent, '--', path)

    def test_cutover_with_unowned_diff_or_merge_cannot_enroll(self):
        self.write('Motivic/Orphan.lean', 'module\n-- changed\n')
        self.git('add', '.')
        self.git('commit', '--amend', '-qm', 'not CI only')
        self.assertFalse(initial_identity(self.root, self.git('rev-parse', 'HEAD')))
        tree = self.git('rev-parse', 'HEAD^{tree}')
        merge = self.git('commit-tree', tree, '-p', self.parent, '-p', self.head, '-m', 'merge')
        self.assertFalse(initial_identity(self.root, merge))

    def test_whitespace_path_cannot_impersonate_an_owned_cutover_path(self):
        self.write(' docs/DEVELOPMENT.md', 'Unowned lookalike\n')
        self.git('add', '.')
        self.git('commit', '--amend', '-qm', 'lookalike owner')
        self.assertFalse(initial_identity(self.root, self.git('rev-parse', 'HEAD')))

    def test_verified_ancestor_requires_native_and_finalizer_not_skipped(self):
        from lean_ci.github import BaselineError
        for native, final in [('skipped', 'success'), ('success', 'skipped'), ('failure', 'success')]:
            with self.subTest(native=native, finalize=final), self.assertRaisesRegex(BaselineError, 'No verified'):
                admitted_baseline(self.root, 'kangxyz/motivic', 'main', self.head,
                                  api=API(self.head, native=native, finalize=final))
        verified = admitted_baseline(self.root, 'kangxyz/motivic', 'main', self.head, api=API(self.head))
        self.assertEqual(verified['verified_base'], self.head)
        self.assertEqual(verified['run_attempt'], 1)

    def test_clean_source_and_independent_tooling_pin_guards_remain_strict(self):
        plan = self.plan()
        self.assertEqual(plan['tooling_revision'], TOOLING_REVISION)
        self.assertIn('lake-manifest.json', plan['source_files'])
        self.assertIn('scripts/ci_policy.py', plan['source_files'])
        before = (self.root / 'lake-manifest.json').read_bytes()
        with patch.dict(os.environ, MOTIVIC_TOOLING_REVISION='f' * 40):
            with self.assertRaisesRegex(ValueError, 'tooling pin'):
                self.application().validate_plan(plan)
        self.assertEqual((self.root / 'lake-manifest.json').read_bytes(), before)
        self.write('lake-manifest.json', '{"changed":true}\n')
        with self.assertRaisesRegex(ValueError, 'working-tree changes'):
            self.application().validate_plan(plan)

    def test_missing_phase_cannot_finalize_or_leave_publication_outputs(self):
        self.plan()
        output = Path(self.tmp.name) / 'outputs.jsonl'
        output.write_text('stale mappings\n')
        sidecar = output.with_suffix('.jsonl.coverage.json')
        sidecar.write_text('stale coverage\n')
        with self.assertRaises((OSError, ValueError)):
            self.application().finalize(Path(self.tmp.name) / 'state', output, toolchain={})
        self.assertFalse(output.exists())
        self.assertFalse(sidecar.exists())

    def test_current_identity_is_exact_and_old_workflow_is_not_admitted(self):
        from lean_ci.github import workflow_kind
        workflow = (ROOT / PROTOCOL.workflow_path).read_bytes()
        self.assertEqual(workflow_kind(workflow, PROTOCOL), 'core')
        self.assertIsNone(workflow_kind(workflow + b'\n', PROTOCOL))
        old = subprocess.check_output(['git', 'show', INITIAL_PARENT + ':' + PROTOCOL.workflow_path], cwd=ROOT)
        self.assertIsNone(workflow_kind(old, PROTOCOL))
        for path, expected in CORE_ENTRYPOINTS.items():
            self.assertEqual(hashlib.sha256((ROOT / path).read_bytes()).hexdigest(), expected, path)


class HostedWorkflowTests(unittest.TestCase):
    def test_job_environment_uses_only_server_available_contexts(self):
        workflow = (ROOT / PROTOCOL.workflow_path).read_text()
        environment = workflow.split('    env:\n', 1)[1].split('    steps:\n', 1)[0]
        contexts = set(re.findall(r'\$\{\{\s*([A-Za-z_][A-Za-z0-9_]*)\.', environment))
        self.assertLessEqual(contexts, {'github', 'needs', 'strategy', 'matrix', 'vars', 'secrets', 'inputs'})
        self.assertIn('echo "MOTIVIC_CI_STATE=$RUNNER_TEMP/motivic-ci-state" >> "$GITHUB_ENV"', workflow)

    def test_publication_requires_finalization_and_cache_saves_keep_partial_progress(self):
        workflow = (ROOT / PROTOCOL.workflow_path).read_text()
        stage = workflow.split('      - name: Stage native artifacts', 1)[1].split('      - name:', 1)[0]
        self.assertIn("steps.finalize.outcome == 'success'", stage)
        self.assertIn('coverage: ${{ runner.temp }}/native-outputs.jsonl.coverage.json', stage)
        saves = [chunk for chunk in workflow.split('      - name: ')[1:]
                 if chunk.startswith(('Save dependency', 'Save incremental', 'Save native'))]
        self.assertEqual(len(saves), 3)
        for chunk in saves:
            condition = next(line for line in chunk.splitlines() if 'if:' in line)
            self.assertIn('always()', condition)
            self.assertNotIn('finalize', condition)
            self.assertNotIn("steps.checks.outcome == 'success'", condition)
        self.assertNotIn('github.event.before', workflow)
        self.assertNotIn('scripts/validate.py', workflow)
        self.assertEqual(workflow.count('ref: ' + TOOLING_REVISION), 2)

    def test_progress_cache_restores_exact_namespace_and_saves_failed_prefix(self):
        from lean_ci.cli import main as cli_main
        # The actual core CLI accepts the same explicit path used by the action.
        application = unittest.mock.Mock()
        application.run_phase.return_value = {'status': 'completed'}
        with patch('builtins.print'):
            self.assertEqual(cli_main(['native', '--state', '/tmp/state',
                                       '--progress', '/tmp/motivic-check-progress'],
                                      application=application), 0)
        application.run_phase.assert_called_once_with(
            Path('/tmp/state'), 'native', Path('/tmp/motivic-check-progress'))
        workflow = (ROOT / PROTOCOL.workflow_path).read_text()
        restore = workflow.split('      - name: Restore compatible individual check progress\n', 1)[1]
        restore = restore.split('      - name:', 1)[0]
        save = workflow.split('      - name: Save individual check progress,', 1)[1]
        save = save.split('      - name:', 1)[0]
        native = workflow.split('      - name: Validate selected providers', 1)[1]
        native = native.split('      - name:', 1)[0]
        path = '${{ runner.temp }}/motivic-check-progress'
        self.assertIn('path: ' + path, restore)
        self.assertIn('path: ' + path, save)
        self.assertIn('--progress "$RUNNER_TEMP/motivic-check-progress"', native)
        primary = next(line.strip()[5:] for line in restore.splitlines() if line.strip().startswith('key: '))
        prefix = restore.split('restore-keys: |\n', 1)[1].strip()
        self.assertEqual(primary, prefix + '${{ github.run_id }}-${{ github.run_attempt }}')
        for value in ('motivic-check-progress-v1-', 'runner.os', 'runner.arch',
                      'env.MOTIVIC_TOOLING_REVISION', 'lean-toolchain', 'lakefile.toml',
                      'lakefile.lean', 'lake-manifest.json', 'scripts/ci_policy.py'):
            self.assertIn(value, prefix)
        self.assertIn("always() && steps.check-progress.outputs.cache-primary-key != ''", save)
        self.assertIn('key: ${{ steps.check-progress.outputs.cache-primary-key }}', save)
        self.assertNotIn('checks.outcome', save)
        self.assertNotIn('finalize.outcome', save)
        self.assertIn('timeout-minutes: 300', native)
        self.assertIn('timeout-minutes: 360', workflow)
        self.assertNotIn('workflow_run:', workflow)


if __name__ == '__main__':
    unittest.main()
