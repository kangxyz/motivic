"""Per-origin batch policy/progress fixtures, without Lean, Git or native lint.

Synthetic reflective bindings and receipts exercise orchestration only. They do
not certify a native import closure, declaration predicate or complete phase.
"""
import json
import os
from pathlib import Path
import sys
import tempfile
import threading
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from lean_ci.batch import check_group
from lean_ci.execution import TaskRunner
from lean_ci.runtime import NativeRuntime
from lean_ci.state import CheckInputs, InputDrift, TemporalInputs, digest
import shared_workflow
from shared_workflow import DRIVERS, declaration_check, resource_config, runtime_environment


class FixtureAdapter:
    def binding(self, root, task, toolchain, reflection=None, observations=None):
        raw = {origin: observations.hash_file(root / (origin + '.lean'))
               for origin in task['modules']}
        return {'arguments': task['command'], 'modules': task['modules'], 'raw_inputs': raw,
                'environment_boundary': task['environment_boundary'],
                'reflective_imports': {'fixture-source-closure': digest(raw)}}


class FixtureExecutor:
    def __init__(self, *, fail=None, barrier=None):
        self.fail, self.barrier, self.calls = fail, barrier, []

    def run(self, task, directory, *, cancelled):
        origin = task['modules'][0]
        self.calls.append(origin)
        if self.barrier:
            self.barrier.wait(timeout=2)
        if origin == self.fail:
            raise ValueError('synthetic origin failure: ' + origin)
        return {'receipt': {'state': 'completed', 'command': task['command'],
                'cwd': task['cwd'], 'exit_code': 0, 'guard_failure': None,
                'owned_group_gone': True}}


class DeclarationBatchTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='motivic-check-batch-')
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name).resolve()
        self.root = self.directory / 'repo'
        self.root.mkdir()
        self.origins = ['Motivic.A', 'Motivic.B']
        for origin in self.origins:
            (self.root / (origin + '.lean')).write_text('fixture source ' + origin)
        self.prefix = self.directory / 'managed'
        (self.prefix / 'bin').mkdir(parents=True)
        self.lean = self.prefix / 'bin/lean'
        self.lean.write_text('#!/bin/false\n')
        self.lean.chmod(0o755)

    def environment(self, jobs):
        profile = {'schema_version': 1, 'jobs': jobs, 'threads': 1,
                   'lean_memory_mib': 64, 'rss_limit_mib': 512, 'lean': str(self.lean)}
        return {'R5_LEAN_REMOTE_PROFILE': json.dumps(profile), 'LEAN': str(self.lean),
                'LEAN_SYSROOT': str(self.prefix)}

    def tasks(self):
        return [dict(task, cwd=str(self.root)) for task in
                declaration_check(self.root, self.origins, 'providers', False)]

    def test_exact_origins_keep_argv_import_boundary_and_admitted_caps(self):
        for jobs, expected in ((2, 2), (16, 8)):
            with self.subTest(jobs=jobs), patch.dict(os.environ, self.environment(jobs), clear=True):
                tasks = self.tasks()
                runtime = NativeRuntime(self.root, resource_config(), runtime_environment())
                self.assertEqual(check_group(tasks, runtime), expected)
                self.assertEqual([task['modules'] for task in tasks], [[origin] for origin in self.origins])
                self.assertEqual([task['command'] for task in tasks],
                    [[sys.executable, str(self.root / 'scripts/lint_declarations.py'),
                      '--root', str(self.root), '--no-build', origin] for origin in self.origins])
                for task in tasks:
                    self.assertEqual(task['environment_boundary']['origins'], task['modules'])
                    self.assertEqual(task['environment_boundary']['declarations'], 'exact-defining-origin')
                    self.assertTrue(task['capped'])
                excessive = [dict(task, check_batch=dict(task['check_batch'], jobs=jobs + 1))
                             for task in tasks]
                with self.assertRaisesRegex(ValueError, 'resource profile'):
                    check_group(excessive, runtime)
        with patch.dict(os.environ, {}, clear=True):
            self.assertEqual({task['check_batch']['jobs'] for task in self.tasks()}, {1})

    def test_native_package_full_case_and_empty_selection_are_unchanged(self):
        with patch.dict(os.environ, {}, clear=True):
            actual = declaration_check(self.root, self.origins, 'providers', True)
            self.assertEqual(actual, [dict(id='providers/declarations', kind='check',
                command=['lake', 'env', 'lean', '--run', DRIVERS[0], '--no-build', *self.origins],
                check_kind='declaration-native-package', modules=self.origins, capped=True,
                environment_boundary={'mode': 'separate-import-environment-per-origin',
                    'origins': self.origins, 'declarations': 'native-package-prefix'})])
            self.assertEqual(declaration_check(self.root, [], 'providers', False), [])

    def test_failed_origin_retains_peer_and_only_changed_origin_invalidates_key(self):
        with patch.dict(os.environ, self.environment(2), clear=True):
            tasks = self.tasks()
            runner = TaskRunner()
            runner.root, runner.adapter = self.root, FixtureAdapter()
            runner.runtime = NativeRuntime(self.root, resource_config(), runtime_environment())
            plan = {'repository': 'fixture/motivic', 'implementation': 'fixture-core'}
            progress = self.directory / 'progress'

            def attempt(executor, name):
                return runner.run_tasks(plan, tasks, self.directory / name, progress, {},
                                        TemporalInputs(), executor=executor)

            first = FixtureExecutor(fail=self.origins[0], barrier=threading.Barrier(2))
            with self.assertRaisesRegex(ValueError, 'synthetic origin failure'):
                attempt(first, 'first')
            records = [json.loads(path.read_text()) for path in progress.glob('*.json')]
            self.assertEqual(len(records), 1)
            retained = records[0]
            self.assertEqual(retained['binding']['modules'], [self.origins[1]])
            self.assertEqual(retained['binding']['environment_boundary']['origins'], [self.origins[1]])

            retry = FixtureExecutor()
            outcomes = attempt(retry, 'retry')
            self.assertEqual(retry.calls, [self.origins[0]])
            self.assertEqual([item['result']['mode'] for item in outcomes], ['performed', 'reused'])
            records = [json.loads(path.read_text()) for path in progress.glob('*.json')]
            self.assertEqual(len({record['key'] for record in records}), 2)

            (self.root / (self.origins[1] + '.lean')).write_text('changed fixture source')
            changed = FixtureExecutor()
            outcomes = attempt(changed, 'changed')
            self.assertEqual(changed.calls, [self.origins[1]])
            self.assertEqual([item['result']['mode'] for item in outcomes], ['reused', 'performed'])
            self.assertNotEqual(outcomes[1]['result']['success']['key'], retained['key'])


class SharedBatchLoaderTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='motivic-batch-loader-')
        self.addCleanup(self.temporary.cleanup)
        self.tooling = Path(self.temporary.name).resolve()
        self.package = self.tooling / 'ci/lean_ci'
        self.package.mkdir(parents=True)
        self.revision = 'a' * 40
        for name in ('__init__.py', 'recipe.py', 'local.py'):
            (self.package / name).write_text('# pinned fixture ' + name + '\n')

    def repository_bytes(self, command, *, cwd, stderr):
        self.assertEqual(cwd, self.tooling)
        self.assertEqual(stderr, shared_workflow.subprocess.PIPE)
        if command == ['git', 'rev-parse', 'HEAD']:
            return (self.revision + '\n').encode()
        if command == ['git', 'ls-tree', '-r', '--name-only', self.revision, '--', 'ci/lean_ci']:
            return ''.join(path.relative_to(self.tooling).as_posix() + '\n'
                           for path in sorted(self.package.glob('*.py'))).encode()
        if command[:2] == ['git', 'show']:
            revision, relative = command[2].split(':', 1)
            self.assertEqual(revision, self.revision)
            return (self.tooling / relative).read_bytes()
        raise AssertionError('Unexpected loader source action: ' + repr(command))

    def environment(self):
        return {'MOTIVIC_TOOLING_ROOT': str(self.tooling),
                'MOTIVIC_TOOLING_REVISION': self.revision}

    def test_missing_batch_capability_rejected_before_import(self):
        with patch.dict(os.environ, self.environment(), clear=True), \
             patch.object(shared_workflow.subprocess, 'check_output', side_effect=self.repository_bytes), \
             patch.object(shared_workflow.importlib, 'import_module') as load:
            with self.assertRaisesRegex(ValueError, 'batch.*adopt the reviewed common tooling commit'):
                shared_workflow.shared_api()
            load.assert_not_called()

    def test_batch_capable_pinned_enrollment_is_accepted(self):
        (self.package / 'batch.py').write_text('# pinned fixture batch.py\n')
        module = SimpleNamespace(__file__=str(self.package / '__init__.py'))
        with patch.dict(os.environ, self.environment(), clear=True), \
             patch.object(shared_workflow.subprocess, 'check_output', side_effect=self.repository_bytes) as source, \
             patch.dict(sys.modules, {'lean_ci': module}), \
             patch.object(sys, 'path', list(sys.path)), \
             patch.object(shared_workflow.importlib, 'import_module', return_value=module) as load:
            self.assertIs(shared_workflow.shared_api(), module)
            load.assert_called_once_with('lean_ci')
            self.assertEqual(sys.path[0], str(self.tooling / 'ci'))
        self.assertEqual(source.call_count, 6)


class GraphMemoTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='motivic-graph-memo-')
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve() / 'repo'
        (self.root / 'Motivic/Empty').mkdir(parents=True)
        (self.root / 'MotivicTest').mkdir()
        (self.root / 'Motivic.lean').write_text('import Motivic.A\n')
        (self.root / 'Motivic/A.lean').write_text('import Motivic.B\n')
        (self.root / 'Motivic/B.lean').write_text('def dependency := 1\n')
        (self.root / 'Motivic/C.lean').write_text('def unrelated := 1\n')
        self.whole = TemporalInputs()

    def test_graph_parsed_once_across_individual_check_observers(self):
        expected = shared_workflow.graph(self.root)
        with patch.object(shared_workflow, 'graph', wraps=shared_workflow.graph) as parsed:
            first = shared_workflow._native_source_graph(self.root, CheckInputs(self.whole))
            second = shared_workflow._native_source_graph(self.root, CheckInputs(self.whole))
        self.assertEqual(parsed.call_count, 1)
        self.assertEqual(first, expected)
        self.assertEqual(second, expected)
        self.assertIn(self.root / 'Motivic/C.lean', self.whole.files)
        enrolled = {path for path, excluded in self.whole.directories}
        self.assertIn(self.root / 'Motivic/Empty', enrolled)
        self.assertNotIn(self.root.parent, enrolled)

    def test_selected_and_unselected_source_drift_rejected(self):
        for name in ('A', 'C'):
            with self.subTest(source=name):
                whole = TemporalInputs()
                shared_workflow._native_source_graph(self.root, CheckInputs(whole))
                path = self.root / ('Motivic/' + name + '.lean')
                path.write_text(path.read_text() + '\n-- changed source\n')
                with self.assertRaises(InputDrift):
                    shared_workflow._native_source_graph(self.root, CheckInputs(whole))

    def test_enrollment_addition_in_preexisting_empty_directory_rejected(self):
        shared_workflow._native_source_graph(self.root, self.whole)
        (self.root / 'Motivic/Empty/New.lean').write_text('def newlyEnrolled := 1\n')
        with self.assertRaisesRegex(InputDrift, 'enrollment'):
            shared_workflow._native_source_graph(self.root, self.whole)

    def test_no_observer_always_reads_fresh_graph(self):
        with patch.object(shared_workflow, 'graph', wraps=shared_workflow.graph) as parsed:
            before = shared_workflow._native_source_graph(self.root, None)
            (self.root / 'Motivic/A.lean').write_text('import Motivic\n')
            after = shared_workflow._native_source_graph(self.root, None)
        self.assertEqual(parsed.call_count, 2)
        self.assertNotEqual(before[1]['Motivic.A'], after[1]['Motivic.A'])

    def test_new_source_under_preexisting_ignored_name_subtree_invalidates_cache(self):
        subtree = self.root / 'Motivic/.lake'
        subtree.mkdir()
        shared_workflow._native_source_graph(self.root, self.whole)
        (subtree / 'New.lean').write_text('def newlyEnrolled := 1\n')
        with self.assertRaisesRegex(InputDrift, 'enrollment'):
            shared_workflow._native_source_graph(self.root, self.whole)


if __name__ == '__main__':
    unittest.main()
