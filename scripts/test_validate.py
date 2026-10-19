"""Command-level selected validation fixtures; all native tools are stand-ins."""
# Authors: kangxyz
from contextlib import redirect_stdout
import io
import os
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from ci_targets import make_plan
from validate import main
from shared_workflow import MotivicAdapter, local_inputs, recipe, admitted_baseline, resource_config
import lint_style
import lint_declarations
import hashlib


class ValidationOrderTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.write('Motivic/Provider.lean', 'import Mathlib.Algebra.Group.Basic\n')
        self.write('Motivic/Consumer.lean', 'import Motivic.Provider\nexample : True := by trivial\n')
        self.write('Motivic/Unrelated.lean', 'module\n')
        self.write('MotivicTest/Selected.lean', 'import Motivic.Consumer\n')
        self.receipts = self.root / 'receipts'

    def write(self, path, source):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(source)

    def selected(self, changed, **kwargs):
        return recipe(self.root, make_plan(self.root, changed), 'check', self.receipts, **kwargs)

    def test_shared_recipe_preserves_order_exact_modules_and_actual_predicates(self):
        tasks = self.selected(['Motivic/Provider.lean'], export=True)
        ids = [task['id'] for task in tasks]
        for before, after in [('prepare/cache', 'providers/build'),
                              ('providers/build', 'providers/declarations'),
                              ('providers/declarations', 'selected/style'),
                              ('selected/style', 'consumers/build'),
                              ('consumers/build', 'affected-consumers/declarations')]:
            self.assertLess(ids.index(before), ids.index(after))
        builds = [t for t in tasks if t['kind'] == 'build']
        self.assertEqual([t['modules'] for t in builds],
                         [['Motivic.Provider'], ['Motivic.Consumer', 'MotivicTest.Selected']])
        self.assertTrue(all('Motivic.Unrelated' not in t['command'] for t in tasks))
        for task in builds:
            self.assertEqual(task['command'][3:3 + len(task['modules'])], ['+' + n for n in task['modules']])
            self.assertIn('mapping', task)
        checks = [t for t in tasks if t['kind'] == 'check']
        self.assertEqual([t['modules'] for t in checks],
                         [['Motivic.Provider'], [], ['Motivic.Consumer', 'MotivicTest.Selected']])
        self.assertEqual(checks[1]['source_modules'], ['Motivic.Provider'])
        self.assertEqual(checks[0]['environment_boundary']['mode'], 'separate-import-environment-per-origin')
        self.assertNotIn('export-only', ' '.join(' '.join(t['command']) for t in tasks))

    def test_import_only_roots_do_not_expand_optional_families(self):
        self.write('Motivic.lean', 'module\npublic import Motivic.Provider\n')
        tasks = self.selected(['Motivic.lean'])
        self.assertEqual(next(t for t in tasks if t['kind'] == 'build')['modules'], ['Motivic'])
        declaration = next(t for t in tasks if t.get('check_kind') == 'declaration-exact-origin')
        self.assertEqual(declaration['modules'], ['Motivic'])
        self.assertTrue(all('Motivic.Unrelated' not in t['command'] for t in tasks))

    def test_docs_only_remains_source_only_without_native_preparation(self):
        tasks = self.selected(['docs/checks.json', 'README.md'])
        self.assertEqual([t['id'] for t in tasks], ['source/structure'])
        self.assertFalse(tasks[0]['native'])
        self.assertFalse(self.receipts.exists())

    def test_client_has_own_workspace_and_setup_before_build(self):
        self.write('Motivic.lean', 'import Motivic.Provider\n')
        self.write('examples/downstream/MotivicClient.lean', 'import Motivic\n')
        tasks = self.selected(['Motivic.lean'])
        ids = [t['id'] for t in tasks]
        self.assertLess(ids.index('providers/declarations'), ids.index('prepare/client'))
        self.assertLess(ids.index('prepare/client'), ids.index('client/build'))
        setup = next(t for t in tasks if t['id'] == 'prepare/client')
        self.assertEqual(setup['established_paths'], ['examples/downstream/lake-manifest.json'])
        client = next(t for t in tasks if t['id'] == 'client/build')
        self.assertEqual(client['cwd'], str(self.root / 'examples/downstream'))
        self.assertEqual(client['modules'], ['MotivicClient'])
        self.assertEqual(client['command'], ['lake', '--rehash', 'build', '+MotivicClient'])

    def test_enrollment_precedes_selection_and_includes_untracked_and_absent_candidates(self):
        self.write('Motivic/New/Untracked.lean', 'module\n')
        paths = [p['path'] if isinstance(p, dict) else p
                 for p in local_inputs(self.root, targets=['Motivic.Provider'])]
        for path in ['Motivic/New/Untracked.lean', 'Motivic/New', 'Motivic.lean',
                     'lakefile.lean', 'lean-toolchain', '.github/dependency-scope.json',
                     'scripts/shared_workflow.py', 'scripts']:
            self.assertIn(path, paths)
        self.assertNotIn('examples/downstream/lake-manifest.json', paths)

    def test_missing_selected_sources_fail_before_execution(self):
        plan = make_plan(self.root, ['Motivic/Provider.lean'])
        (self.root / 'Motivic/Provider.lean').unlink()
        with self.assertRaisesRegex(ValueError, 'existing local'):
            recipe(self.root, plan, 'check', self.receipts)

    def test_cli_delegates_once_to_application_check_without_execution_loop(self):
        from types import SimpleNamespace
        plan = make_plan(self.root, ['Motivic/Provider.lean'])
        plan['basis'] = dict(event='push', base='BASE', head='HEAD', default_branch='',
                             full=False, manual_targets='')
        application = unittest.mock.Mock()
        application.check.return_value = {'status': 'complete'}
        argv = ['validate.py', '--root', str(self.root), '--base', 'BASE',
                '--receipt-dir', str(self.receipts)]
        with patch.object(sys, 'argv', argv), patch('validate.from_arguments', return_value=plan), \
                patch('validate.shared_api'), patch('validate.create_application', return_value=application), \
                patch('validate.subprocess.run') as run, redirect_stdout(io.StringIO()):
            self.assertEqual(main(), 0)
        application.check.assert_called_once_with(state=self.receipts, requested_base='BASE',
                                                  targets=[], progress=None, outputs=None)
        run.assert_not_called()

    def test_missing_baseline_does_not_query_api_or_fall_back_to_previous_push(self):
        from lean_ci.github import BaselineError
        api = unittest.mock.Mock()
        with self.assertRaisesRegex(BaselineError, 'unfinished upgrade'):
            admitted_baseline(self.root, 'kangxyz/motivic', 'main', 'f' * 40, api=api)
        api.get.assert_not_called()
        api.pages.assert_not_called()

    def test_remote_profile_alias_and_resource_controls_are_declared(self):
        config = resource_config()
        self.assertIn('R5_LEAN_REMOTE_PROFILE', config.names('profile'))
        self.assertEqual(config.value({'MOTIVIC_BUILD_THREADS': '7'}, 'build_thread'), '7')


class SharedLocalBoundaryTests(unittest.TestCase):
    setUp = ValidationOrderTests.setUp
    write = ValidationOrderTests.write
    selected = ValidationOrderTests.selected
    def test_worktree_source_only_uses_shared_runtime_without_toolchain_or_baseline(self):
        from shared_workflow import create_application
        from lean_ci.resources import run as guarded_run
        self.write('scripts/check_repository.py', 'pass\n')
        scope = make_plan(self.root, ['README.md'])
        scope['basis'] = dict(event='local', base='BASE', head='HEAD', default_branch='',
                              full=False, manual_targets='')
        with tempfile.TemporaryDirectory() as external, \
                patch('shared_workflow.shared_api'), \
                patch('shared_workflow.selection', return_value=scope), \
                patch('lean_ci.local.git', return_value=b'f' * 40), \
                patch('lean_ci.local.observe_git_basis'), \
                patch('lean_ci.resources.run', side_effect=lambda *args, **kwargs:
                      guarded_run(*args, sampler=lambda group: [], **kwargs)), \
                patch('lean_ci.runtime.compiler_identity') as compiler, \
                patch('shared_workflow.admitted_baseline') as baseline:
            result = create_application(self.root).check(state=Path(external), requested_base='BASE')
        self.assertEqual(result['status'], 'complete')
        self.assertEqual(result['source_basis'], {'kind': 'working-tree', 'head': 'f' * 40})
        self.assertIn('Motivic/Provider.lean', result['source_files'])
        compiler.assert_not_called()
        baseline.assert_not_called()
        self.assertFalse((self.root / '.lake').exists())

    def test_selected_import_and_checker_bytes_invalidate_check_binding(self):
        from shared_workflow import binding
        from types import SimpleNamespace
        reflection = SimpleNamespace(closure=lambda roots: {'roots': sorted(set(roots)), 'digest': 'fixture'})
        task = next(t for t in self.selected(['Motivic/Provider.lean'])
                    if t['id'] == 'affected-consumers/declarations')
        self.write('scripts/lint_declarations.py', '# original checker\n')
        with patch('lean_ci.state.module_identity', return_value={'depHash': 'fixture', 'outputs': {}}):
            before = binding(self.root, task, {}, reflection=reflection)
            self.write('Motivic/Provider.lean', 'import Mathlib.Algebra.Group.Basic\n-- changed source\n')
            changed_source = binding(self.root, task, {}, reflection=reflection)
            self.write('scripts/lint_declarations.py', '# changed checker\n')
            changed_checker = binding(self.root, task, {}, reflection=reflection)
        self.assertNotEqual(before, changed_source)
        self.assertNotEqual(changed_source, changed_checker)
        self.assertIn('Motivic/Provider.lean', before['raw_inputs'])
        self.assertEqual(before['environment_boundary']['mode'], 'separate-import-environment-per-origin')


class StyleBindingBoundaryTests(unittest.TestCase):
    setUp = ValidationOrderTests.setUp
    write = ValidationOrderTests.write
    selected = ValidationOrderTests.selected

    def style_fixture(self):
        self.write('MotivicTest/New.lean', 'import Motivic.Provider\n-- new unbuilt test source\n')
        self.write('.lake/packages/mathlib/scripts/lint-style.lean', 'import Lean\n')
        self.write('.lake/packages/Cli/Cli/Basic.lean', 'import Lean\n-- optional runtime source\n')
        self.write('scripts/library_sources.py', '# loaded local parser support\n')
        helper = self.root / 'tooling/scripts/run_style_linter.py'
        self.write('tooling/scripts/run_style_linter.py', '# actual external style helper\n')
        task = next(t for t in self.selected(['MotivicTest/New.lean']) if t['id'] == 'selected/style')
        return helper, task

    def test_new_unbuilt_consumer_style_never_queries_subject_traces(self):
        from shared_workflow import binding
        from lean_ci.state import TemporalInputs
        from types import SimpleNamespace
        helper, task = self.style_fixture()
        observations = TemporalInputs()
        reflection = SimpleNamespace(closure=lambda roots: {'roots': sorted(set(roots)), 'digest': 'runtime-fixture'})
        with patch.dict(os.environ, MOTIVIC_TOOLING_ROOT=str(helper.parents[1])), \
                patch('lean_ci.state.module_identity', side_effect=AssertionError('subject artifact query')) as native:
            value = binding(self.root, task, {}, reflection, observations)
            self.assertEqual(task['modules'], [])
            self.assertIn('MotivicTest.New', task['source_modules'])
            self.assertEqual(value['native'], {})
            self.assertIn('MotivicTest.New', value['modules'])
            self.assertIn('MotivicTest/New.lean', value['raw_inputs'])
            self.assertNotIn('MotivicTest.New', value['reflective_imports']['roots'])
            self.assertNotIn('Motivic.Provider', value['reflective_imports']['roots'])
            # The subsequent consumer build may create/update subject artifacts
            # without invalidating a source-only style check already completed.
            self.write('.lake/build/lib/lean/MotivicTest/New.trace', 'new consumer build output\n')
            observations.assert_stable()
            self.assertEqual(binding(self.root, task, {}, reflection, observations), value)
        native.assert_not_called()

    def test_changed_actual_external_helper_and_loaded_support_reject_reuse(self):
        from shared_workflow import binding
        from lean_ci.state import InputDrift, Progress, TemporalInputs
        from types import SimpleNamespace
        helper, task = self.style_fixture()
        reflection = SimpleNamespace(closure=lambda roots: {'roots': sorted(set(roots)), 'digest': 'runtime-fixture'})
        observed = TemporalInputs()
        with patch.dict(os.environ, MOTIVIC_TOOLING_ROOT=str(helper.parents[1])), \
                patch('lean_ci.state.module_identity', side_effect=AssertionError('subject artifact query')):
            before = binding(self.root, task, {}, reflection, observed)
            self.assertIn(str(helper), before['raw_inputs'])
            self.assertNotIn(str(helper.with_name('lint_style_runtime.py')), before['raw_inputs'])
            self.assertIn('scripts/library_sources.py', before['raw_inputs'])
            self.assertIn('.lake/packages/Cli/Cli/Basic.lean', before['raw_inputs'])
            progress = Progress(self.root / '.lake/fixture-progress')
            command = task['command']
            receipt = dict(state='completed', exit_code=0, guard_failure=None,
                           owned_group_gone=True, command=command, cwd=str(self.root))
            progress.save(before, receipt, command)
            self.assertIsNotNone(progress.lookup(before))
            helper.write_text('# changed actual external style helper\n')
            changed_helper = binding(self.root, task, {}, reflection, TemporalInputs())
            self.assertIsNone(progress.lookup(changed_helper))
            with self.assertRaises(InputDrift):
                observed.assert_stable()
            self.write('scripts/library_sources.py', '# changed loaded parser support\n')
            changed_support = binding(self.root, task, {}, reflection, TemporalInputs())
            self.assertNotEqual(changed_helper, changed_support)
            self.assertIsNone(progress.lookup(changed_support))


class NativeApplicationFactoryTests(unittest.TestCase):
    setUp = ValidationOrderTests.setUp
    write = ValidationOrderTests.write

    def test_admitted_git_free_factory_uses_same_recipe_runtime_and_profile(self):
        from shared_workflow import create_application, create_native_application, MotivicAdapter
        from lean_ci.engine import Application
        from lean_ci.runtime import NativeRuntime
        self.assertFalse((self.root / '.git').exists())
        with patch.dict(os.environ, R5_LEAN_REMOTE_PROFILE='already-admitted-profile'), \
                patch('shared_workflow.shared_api', side_effect=AssertionError('ordinary Git admission')) as admission, \
                patch('shared_workflow.subprocess.check_output', side_effect=AssertionError('Git query')):
            native = create_native_application(self.root, self.root, {})
        admission.assert_not_called()
        self.assertIsInstance(native, Application)
        self.assertIsInstance(native.adapter, MotivicAdapter)
        self.assertIsInstance(native.runtime, NativeRuntime)
        self.assertEqual(native.root, self.root)
        self.assertEqual(native.package_cwd, self.root)
        self.assertEqual(native.runtime.environment['R5_LEAN_REMOTE_PROFILE'], 'already-admitted-profile')
        self.assertIn('R5_LEAN_REMOTE_PROFILE', native.runtime.resource_config.names('profile'))
        with patch('shared_workflow.shared_api') as admission:
            ordinary = create_application(self.root)
        admission.assert_called_once_with()
        plan = {'scope': make_plan(self.root, ['Motivic/Provider.lean'])}
        directory = self.root / 'fixture-task-plan'
        self.assertEqual(native.adapter.tasks(self.root, plan, 'native', directory),
                         ordinary.adapter.tasks(self.root, plan, 'native', directory))

    def test_native_factory_rejects_unassigned_coordinate_mappings(self):
        from shared_workflow import create_native_application
        for package, mapping in ((self.root / 'other', {}), (self.root, {'repository_package': 'lean'}),
                                 (self.root, None)):
            with self.subTest(package=package, mapping=mapping), \
                    self.assertRaisesRegex(ValueError, 'root == package_cwd'):
                create_native_application(self.root, package, mapping)

    def test_ordinary_factory_still_requires_git_revision_admission(self):
        from shared_workflow import create_application
        with patch('shared_workflow.shared_api', side_effect=ValueError('ordinary pin guard')) as admission:
            with self.assertRaisesRegex(ValueError, 'ordinary pin guard'):
                create_application(self.root)
        admission.assert_called_once_with()


class DeclarationOriginTests(unittest.TestCase):
    setUp = ValidationOrderTests.setUp
    write = ValidationOrderTests.write
    def test_exact_origin_filter_is_the_only_pinned_driver_change(self):
        native = ('before\n' + lint_declarations.ENUMERATION +
                  '    let linters ← getChecks (slow := true) (runAlways := none) (runOnly := none)\n'
                  '    let results ← lintCore decls linters (inIO := true) (currentModule := module)\n'
                  'after\n').encode()
        with patch('lint_declarations.DRIVER_SHA256', hashlib.sha256(native).hexdigest()):
            adapted = lint_declarations.adapt(native)
        self.assertEqual(adapted.replace(lint_declarations.ORIGIN_FILTER, '', 1), native.decode())
        self.assertIn('env.getModuleIdxFor? name', adapted)
        self.assertIn('env.header.moduleNames[index]! == module', adapted)
        self.assertNotIn('module.isPrefixOf', adapted)
        self.assertIn('| none => false', adapted)
        with self.assertRaisesRegex(ValueError, 'differs'):
            lint_declarations.adapt(native + b'changed')

    def test_adapter_runs_only_explicit_origins_and_preserves_the_pinned_source(self):
        native = ('before\n' + lint_declarations.ENUMERATION + 'after\n').encode()
        path = self.root / '.lake/packages/batteries/scripts/runLinter.lean'
        path.parent.mkdir(parents=True)
        path.write_bytes(native)
        argv = ['lint_declarations.py', '--root', str(self.root), '--no-build',
                'Motivic.Provider', 'Motivic.Provider']
        observed = []
        def native_call(argv, **kwargs):
            observed.append((argv, Path(argv[argv.index('--run') + 1]).read_text()))
            return subprocess.CompletedProcess([], 0)
        wrapper = '/private/tmp/selected-lean-wrapper'
        with patch.object(sys, 'argv', argv), patch.dict(os.environ, LEAN=wrapper), \
                patch('lint_declarations.DRIVER_SHA256', hashlib.sha256(native).hexdigest()), \
                patch('lint_declarations.subprocess.run', side_effect=native_call) as run:
            self.assertEqual(lint_declarations.main(), 0)
        self.assertEqual(run.call_count, 1)
        self.assertEqual(observed[0][0][:3], ['lake', 'env', wrapper])
        self.assertEqual(observed[0][0][observed[0][0].index('--no-build') + 1:], ['Motivic.Provider'])
        self.assertIn(lint_declarations.ORIGIN_FILTER, observed[0][1])
        self.assertEqual(path.read_bytes(), native)

    def test_distinct_origins_run_in_separate_processes_with_the_same_adapter(self):
        native = ('before\n' + lint_declarations.ENUMERATION + 'after\n').encode()
        path = self.root / '.lake/packages/batteries/scripts/runLinter.lean'
        path.parent.mkdir(parents=True)
        path.write_bytes(native)
        argv = ['lint_declarations.py', '--root', str(self.root), '--no-build',
                'Motivic.Provider', 'Motivic.Consumer', 'Motivic.Provider']
        observed = []
        def native_call(argv, **kwargs):
            observed.append((argv, kwargs, Path(argv[argv.index('--run') + 1]).read_text()))
            return subprocess.CompletedProcess(argv, 0)
        wrapper = '/private/tmp/selected-lean-wrapper'
        with patch.object(sys, 'argv', argv), patch.dict(os.environ, LEAN=wrapper), \
                patch('lint_declarations.DRIVER_SHA256', hashlib.sha256(native).hexdigest()), \
                patch('lint_declarations.subprocess.run', side_effect=native_call):
            self.assertEqual(lint_declarations.main(), 0)
        self.assertEqual(len(observed), 2)
        for (command, kwargs, adapted), origin in zip(observed, ['Motivic.Provider', 'Motivic.Consumer']):
            self.assertEqual(command[:4], ['lake', 'env', wrapper, '--run'])
            self.assertEqual(command[5:], ['--no-build', origin])
            self.assertEqual(kwargs, {'cwd': self.root})
            self.assertEqual(adapted, native.decode().replace(
                lint_declarations.ENUMERATION,
                lint_declarations.ENUMERATION + lint_declarations.ORIGIN_FILTER))
        self.assertEqual(observed[0][0][4], observed[1][0][4])
        self.assertEqual(path.read_bytes(), native)

    def test_origin_process_failure_stops_later_origins_and_preserves_exit_code(self):
        native = ('before\n' + lint_declarations.ENUMERATION + 'after\n').encode()
        path = self.root / '.lake/packages/batteries/scripts/runLinter.lean'
        path.parent.mkdir(parents=True)
        path.write_bytes(native)
        argv = ['lint_declarations.py', '--root', str(self.root), '--no-build',
                'Motivic.Provider', 'Motivic.Consumer', 'Motivic.Unrelated']
        for returncodes in ([23], [0, 7]):
            with self.subTest(returncodes=returncodes), patch.object(sys, 'argv', argv), \
                    patch('lint_declarations.DRIVER_SHA256', hashlib.sha256(native).hexdigest()), \
                    patch('lint_declarations.subprocess.run', side_effect=[
                        subprocess.CompletedProcess([], code) for code in returncodes]) as run:
                self.assertEqual(lint_declarations.main(), returncodes[-1])
            self.assertEqual([call.args[0][5:] for call in run.call_args_list],
                             [['--no-build', origin] for origin in
                              ['Motivic.Provider', 'Motivic.Consumer'][:len(returncodes)]])

    def test_normal_and_full_routes_keep_their_distinct_origin_predicates(self):
        plan = make_plan(self.root, ['Motivic/Provider.lean'])
        tasks = recipe(self.root, plan, 'check', self.receipts, skip_static=True, skip_cache=True)
        checks = [t for t in tasks if t.get('check_kind', '').startswith('declaration')]
        self.assertEqual([t['modules'] for t in checks],
                         [['Motivic.Provider'], ['Motivic.Consumer', 'MotivicTest.Selected']])
        self.assertTrue(all(t['check_kind'] == 'declaration-exact-origin' for t in checks))
        plan['full'] = True
        tasks = recipe(self.root, plan, 'check', self.receipts, skip_static=True, skip_cache=True)
        checks = [t for t in tasks if t.get('check_kind', '').startswith('declaration')]
        self.assertTrue(all(t['check_kind'] == 'declaration-native-package' for t in checks))
        self.assertTrue(all('.lake/packages/batteries/scripts/runLinter.lean' in t['command'] for t in checks))


class StyleRuntimeTests(unittest.TestCase):
    def test_readiness_uses_published_pure_inspector_without_compiler_or_lake(self):
        from types import SimpleNamespace
        helper = SimpleNamespace(plan_runtime=lambda root, sysroot: {'missing_prerequisites': []})
        with tempfile.TemporaryDirectory() as temporary:
            argv = ['lint_style.py', '--root', temporary, '--check-prerequisites', '--sysroot', temporary]
            with patch.object(sys, 'argv', argv), patch('lint_style.runtime', return_value=helper), \
                    patch('lint_style.subprocess.run') as run, redirect_stdout(io.StringIO()):
                self.assertEqual(lint_style.main(), 0)
            run.assert_not_called()
            self.assertFalse((Path(temporary) / '.lake').exists())

    def test_isolated_driver_receives_exact_targets_and_preserves_dependency_sources(self):
        from types import SimpleNamespace
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            driver = root / 'lint-style.lean'
            native_source = ('before\n' + lint_style.IMPORT_ENUMERATION + 'after\n').encode()
            driver.write_bytes(native_source)
            helper = SimpleNamespace(
                lake_environment=lambda root: dict(lean='fixture-lean', LEAN_PATH='cached'),
                plan_runtime=lambda root, sysroot: dict(missing_prerequisites=[],
                    isolated_compile_modules=[], driver=str(driver), lake_shared_library='fixture-Lake'),
                seed_cached_namespaces=lambda overlay, plan: None)
            observed = []
            def native(argv, **kwargs):
                if '--print-prefix' in argv:
                    return subprocess.CompletedProcess([], 0, stdout='fixture-prefix')
                if '--run' in argv:
                    shim = Path(argv[argv.index('--run') + 1])
                    observed.append(shim.with_name('MotivicStyleDriver.lean').read_text())
                    self.assertFalse(shim.with_name('MotivicStyleSelection.lean').exists())
                return subprocess.CompletedProcess([], 0)
            wrapper = '/private/tmp/selected-lean-wrapper'
            with patch.dict(os.environ, LEAN=wrapper), \
                    patch('lint_style.DRIVER_SHA256', hashlib.sha256(native_source).hexdigest()), \
                    patch('lint_style.subprocess.run', side_effect=native) as run:
                self.assertEqual(lint_style.run(root, ['Motivic.Selected'], helper), 0)
            self.assertTrue(all(call.args[0][0] == wrapper for call in run.call_args_list))
            self.assertTrue(run.call_args_list[-1].kwargs['env']['LEAN_PATH'].endswith(os.pathsep + 'cached'))
            self.assertEqual(run.call_args_list[-1].args[0][-1], 'Motivic.Selected')
            self.assertNotIn('Aglib', run.call_args_list[-1].args[0])
            self.assertNotIn('MotivicStyleSelection', run.call_args_list[-1].args[0])
            self.assertEqual(observed, ['before\n' + lint_style.EXACT_ENUMERATION + 'after\n'])
            self.assertEqual(driver.read_bytes(), native_source)

    def test_exact_source_enumeration_is_only_change_to_enabled_style_driver(self):
        native = ('before\n' + lint_style.IMPORT_ENUMERATION +
                  '  let numberErrors := (← lintModules opts nolints allModuleNames style fix)\n'
                  '    + (← missingInitImports opts).toUInt32 + (← undocumentedScripts opts).toUInt32\n'
                  '    + (← modulesNotUpperCamelCase opts allModuleNames).toUInt32\n'
                  '    + (← modulesOSForbidden opts allModuleNames).toUInt32\n'
                  'after\n').encode()
        with patch('lint_style.DRIVER_SHA256', hashlib.sha256(native).hexdigest()):
            adapted = lint_style.adapt_driver(native)
        self.assertEqual(adapted.replace(lint_style.EXACT_ENUMERATION,
                                        lint_style.IMPORT_ENUMERATION, 1), native.decode())
        self.assertIn('let allModuleNames := originModules', adapted)
        self.assertNotIn('originModules.flatMapM', adapted)
        with self.assertRaisesRegex(ValueError, 'differs'):
            lint_style.adapt_driver(native + b'changed')


@unittest.skipUnless(os.environ.get('MOTIVIC_NATIVE_STYLE_ROOT'),
                     'requires an explicitly prepared native fixture package and runtime')
class NativeStyleScopeTests(unittest.TestCase):
    def test_clean_selected_importing_unrelated_bad_source_passes_and_selected_bad_fails(self):
        root = Path(os.environ['MOTIVIC_NATIVE_STYLE_ROOT']).resolve()
        selected = root / 'Motivic/Smoke/StyleSelected.lean'
        unrelated = root / 'Motivic/Smoke/StyleUnrelated.lean'
        bad = root / 'Motivic/Smoke/StyleBad.lean'
        self.assertIn('Motivic.Smoke.StyleUnrelated', selected.read_text())
        self.assertTrue(any(line.rstrip() != line for line in unrelated.read_text().splitlines()))
        self.assertTrue(any(line.rstrip() != line for line in bad.read_text().splitlines()))
        script = str(Path(__file__).with_name('lint_style.py'))
        clean_result = subprocess.run([sys.executable, script, '--root', str(root),
                                       'Motivic.Smoke.StyleSelected'], capture_output=True, text=True)
        self.assertEqual(clean_result.returncode, 0, clean_result.stdout + clean_result.stderr)
        bad_result = subprocess.run([sys.executable, script, '--root', str(root),
                                     'Motivic.Smoke.StyleBad'], capture_output=True, text=True)
        self.assertNotEqual(bad_result.returncode, 0)
        diagnostic = bad_result.stdout + bad_result.stderr
        self.assertIn('StyleBad.lean', diagnostic)
        self.assertIn('This line ends with some whitespace', diagnostic)


if __name__ == '__main__':
    unittest.main()
