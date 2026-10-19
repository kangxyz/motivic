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
from validate import commands, main
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
        return commands(self.root, make_plan(self.root, changed), self.receipts,
                        outputs=self.root / 'outputs.jsonl', **kwargs)

    def test_provider_compile_lint_style_before_consumers_and_exact_no_build_export(self):
        selected = self.selected(['Motivic/Provider.lean'])
        build = next(i for i, argv in enumerate(selected) if 'build.py' == Path(argv[1]).name)
        declarations = next(i for i, argv in enumerate(selected) if ('lean' in argv or any(Path(arg).name == 'lint_declarations.py' for arg in argv)))
        style = next(i for i, argv in enumerate(selected) if any(Path(arg).name == 'lint_style.py' for arg in argv))
        consumer = next(i for i, argv in enumerate(selected) if '--receipt-dir' in argv
                        and str(self.receipts / 'consumers') in argv)
        self.assertLess(build, declarations)
        self.assertLess(declarations, style)
        self.assertLess(style, consumer)
        self.assertIn('--no-build', selected[declarations])
        self.assertIn('--capped-toolchain', selected[style])
        self.assertTrue(all('Motivic.Unrelated' not in argv for argv in selected))
        export = selected[-1]
        self.assertIn('--export-only', export)
        start = export.index('--outputs') + 2
        self.assertEqual(export[start:], make_plan(self.root, ['Motivic/Provider.lean'])['targets'])

    def test_affected_consumer_declarations_are_linted_after_build_without_repeating_providers(self):
        selected = self.selected(['Motivic/Provider.lean'])
        declaration_steps = [(i, argv[argv.index('--no-build') + 1:])
                             for i, argv in enumerate(selected) if ('lean' in argv or any(Path(arg).name == 'lint_declarations.py' for arg in argv))]
        self.assertEqual(len(declaration_steps), 2)
        self.assertEqual(declaration_steps[0][1], ['Motivic.Provider'])
        self.assertEqual(declaration_steps[1][1], ['Motivic.Consumer', 'MotivicTest.Selected'])
        consumer_build = next(i for i, argv in enumerate(selected)
                              if str(self.receipts / 'consumers') in argv)
        self.assertLess(declaration_steps[0][0], consumer_build)
        self.assertLess(consumer_build, declaration_steps[1][0])
        self.assertLess(declaration_steps[1][0], len(selected) - 1)
        style = next(argv for argv in selected
                     if any(Path(arg).name == 'lint_style.py' for arg in argv))
        self.assertEqual(style[style.index('--root') + 2:], ['Motivic.Provider'])
        self.assertNotIn('Motivic.Unrelated', sum((origins for _, origins in declaration_steps), []))

    def test_changed_import_only_root_still_compiles_and_receives_style_and_origin_checks(self):
        self.write('Motivic.lean', 'module\npublic import Motivic.Provider\n')
        selected = self.selected(['Motivic.lean'])
        build = next(argv for argv in selected if Path(argv[1]).name == 'build.py')
        self.assertEqual(build[-1], 'Motivic')
        declarations = next(argv for argv in selected
                            if any(Path(arg).name == 'lint_declarations.py' for arg in argv))
        self.assertEqual(declarations[declarations.index('--no-build') + 1:], ['Motivic'])
        style = next(argv for argv in selected
                     if any(Path(arg).name == 'lint_style.py' for arg in argv))
        self.assertEqual(style[style.index('--root') + 2:], ['Motivic'])

    def test_test_only_change_keeps_producer_lint_before_test(self):
        selected = self.selected(['MotivicTest/Selected.lean'])
        build = next(argv for argv in selected if Path(argv[1]).name == 'build.py')
        self.assertEqual(build[-1], 'Motivic.Consumer')
        style = next(i for i, argv in enumerate(selected) if any(Path(arg).name == 'lint_style.py' for arg in argv))
        consumer = next(i for i, argv in enumerate(selected) if str(self.receipts / 'consumers') in argv)
        self.assertLess(style, consumer)
        self.assertIn('MotivicTest.Selected', selected[-1])

    def test_docs_evidence_only_runs_static_without_cache_or_native_tools(self):
        selected = self.selected(['docs/checks.json', 'README.md'])
        self.assertEqual(len(selected), 1)
        self.assertEqual(Path(selected[0][1]).name, 'check_repository.py')
        self.assertFalse(self.receipts.exists())

    def test_tool_only_changes_run_curated_native_modules_and_client_after_fixtures(self):
        self.write('Motivic.lean', 'import Motivic.Provider\n')
        self.write('MotivicTest.lean', 'import MotivicTest.Selected\n')
        self.write('examples/downstream/MotivicClient.lean', 'import Motivic\n')
        selected = self.selected(['scripts/build.py'])
        self.assertEqual([argv[-1] for argv in selected[1:3]], ['test_build.py', 'test_validate.py'])
        cache = next(i for i, argv in enumerate(selected) if Path(argv[1]).name == 'cache.py')
        self.assertEqual(selected[cache][-2:], ['Motivic', 'MotivicTest'])
        self.assertIn('--lint-runtime', selected[cache])
        providers = next(i for i, argv in enumerate(selected)
                         if str(self.receipts / 'providers') in argv)
        consumers = next(i for i, argv in enumerate(selected)
                         if str(self.receipts / 'consumers') in argv)
        declarations = [(i, argv[argv.index('--no-build') + 1:])
                        for i, argv in enumerate(selected)
                        if any(Path(arg).name == 'lint_declarations.py' for arg in argv)]
        style = next(i for i, argv in enumerate(selected)
                     if any(Path(arg).name == 'lint_style.py' for arg in argv))
        client = next(i for i, argv in enumerate(selected) if Path(argv[1]).name == 'build_client.py')
        self.assertEqual(selected[providers][-1:], ['Motivic'])
        self.assertEqual(selected[consumers][-1:], ['MotivicTest'])
        self.assertEqual([names for _, names in declarations], [['Motivic'], ['MotivicTest']])
        self.assertEqual(selected[style][-2:], ['Motivic', 'MotivicTest'])
        self.assertLess(2, cache)
        self.assertLess(cache, providers)
        self.assertLess(providers, declarations[0][0])
        self.assertLess(declarations[0][0], style)
        self.assertLess(style, consumers)
        self.assertLess(consumers, declarations[1][0])
        self.assertLess(declarations[1][0], client)
        self.assertFalse(any('Motivic.Provider' in argv or 'Motivic.Consumer' in argv for argv in selected))
        docs_only = self.selected(['docs/checks.json', 'scripts/README.md'])
        self.assertEqual(len(docs_only), 1)
        self.assertEqual(Path(docs_only[0][1]).name, 'check_repository.py')

    def test_missing_plan_targets_fail_before_execution(self):
        plan = make_plan(self.root, ['Motivic/Provider.lean'])
        (self.root / 'Motivic/Provider.lean').unlink()
        with self.assertRaisesRegex(ValueError, 'existing local'):
            commands(self.root, plan, self.receipts)

    def test_list_is_read_only_and_does_not_invoke_any_compiler_or_cache(self):
        argv = ['validate.py', '--root', str(self.root), '--manual-targets', 'Motivic.Provider',
                '--base', '', '--list']
        with patch.object(sys, 'argv', argv), patch('validate.subprocess.run') as run, \
                redirect_stdout(io.StringIO()):
            self.assertEqual(main(), 0)
        run.assert_not_called()
        self.assertFalse((self.root / '.lake').exists())

    def test_failed_provider_lint_stops_before_consumers_client_or_export(self):
        plan = make_plan(self.root, ['Motivic/Provider.lean'])
        selected = commands(self.root, plan, self.receipts, skip_static=True, skip_cache=True)
        argv = ['validate.py', '--root', str(self.root), '--manual-targets', 'Motivic.Provider',
                '--base', '', '--skip-static', '--skip-cache', '--receipt-dir', str(self.receipts)]
        # from_arguments is pure selector output here, not a fabricated successful native run.
        with patch.object(sys, 'argv', argv), patch('validate.from_arguments', return_value=plan), \
                patch('validate.subprocess.run', side_effect=[subprocess.CompletedProcess([], 0),
                                                             subprocess.CompletedProcess([], 0),
                                                             subprocess.CompletedProcess([], 7)]) as run, \
                redirect_stdout(io.StringIO()):
            self.assertEqual(main(), 7)
        self.assertEqual(run.call_count, 3)
        self.assertEqual(run.call_args_list[2].args[0], selected[2])


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

    def test_normal_routes_use_origin_adapter_but_explicit_full_keeps_native_driver(self):
        plan = make_plan(self.root, ['Motivic/Provider.lean'])
        selected = commands(self.root, plan, self.receipts, skip_static=True, skip_cache=True)
        lint_steps = [argv for argv in selected
                      if any(Path(arg).name == 'lint_declarations.py' for arg in argv)]
        self.assertEqual(len(lint_steps), 2)
        self.assertEqual([argv[argv.index('--no-build') + 1:] for argv in lint_steps],
                         [['Motivic.Provider'], ['Motivic.Consumer', 'MotivicTest.Selected']])
        plan['full'] = True
        full = commands(self.root, plan, self.receipts, skip_static=True, skip_cache=True)
        self.assertFalse(any(any(Path(arg).name == 'lint_declarations.py' for arg in argv) for argv in full))
        self.assertEqual(sum('.lake/packages/batteries/scripts/runLinter.lean' in argv for argv in full), 2)


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
