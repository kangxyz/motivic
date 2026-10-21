# Authors: kangxyz
"""Small boundary fixtures; no Lean compiler or dependency checkout required."""
import json
from contextlib import redirect_stderr, redirect_stdout
import hashlib
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from cache import cache_roots, main as cache_main
import cache_bootstrap
from check_repository import PINS, check_configuration, check_sources
from library_sources import lean_imports


class RepositoryBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.write('Motivic.lean', 'public import Motivic.Core\n')
        self.write('Motivic/Core.lean', 'public import Mathlib.Algebra.Group.Basic\n')
        self.write('MotivicTest/Client.lean', 'import Motivic\n')

    def write(self, name, content):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)

    def configuration(self):
        config = ('name = "Motivic"\ndefaultTargets = ["Motivic"]\n'
                  'testDriver = "MotivicTest"\n'
                  '[[lean_lib]]\nname = "Motivic"\n'
                  '[[lean_lib]]\nname = "MotivicTest"\nglobs = ["MotivicTest.+"]\n')
        packages = []
        for name, (url, revision) in PINS.items():
            config += f'[[require]]\nname = "{name}"\ngit = "{url}"\nrev = "{revision}"\n'
            packages.append(dict(name=name, url=url, rev=revision, inputRev=revision,
                                 type='git', inherited=False))
        self.write('lakefile.toml', config)
        self.write('lean-toolchain', 'leanprover/lean4:v4.34.1\n')
        self.write('lake-manifest.json', json.dumps(dict(name='Motivic', packages=packages)))
        return config, packages

    def test_test_leaves_need_no_aggregator_but_keep_import_checks(self):
        self.configuration()
        self.write('MotivicTest/Nested/Leaf.lean', 'import Motivic.Core\n')
        self.assertFalse((self.root / 'MotivicTest.lean').exists())
        self.assertEqual(check_configuration(self.root), [])
        self.assertEqual(check_sources(self.root), ([], 4))
        self.write('MotivicTest/Nested/Leaf.lean', 'import MotivicTest.Missing\n')
        self.assertEqual(check_sources(self.root)[0],
                         ['MotivicTest.Nested.Leaf: missing local import MotivicTest.Missing'])

    def test_missing_production_root_is_still_rejected(self):
        (self.root / 'Motivic.lean').unlink()
        self.write('MotivicTest/Client.lean', 'import Motivic.Core\n')
        self.assertEqual(check_sources(self.root)[0],
                         ['Missing public source root: Motivic.lean'])

    def test_test_discovery_configuration_rejects_missing_or_wrong_globs(self):
        config, _ = self.configuration()
        for replacement in ('', 'globs = []\n', 'globs = ["MotivicTest"]\n',
                            'globs = ["MotivicTest.*"]\n'):
            with self.subTest(replacement=replacement):
                self.write('lakefile.toml', config.replace('globs = ["MotivicTest.+"]\n',
                                                          replacement))
                errors = check_configuration(self.root)
                self.assertEqual(len(errors), 1, errors)
                self.assertIn('MotivicTest must discover test modules', errors[0])
        self.write('lakefile.toml', config.replace('testDriver = "MotivicTest"',
                                                 'testDriver = "Motivic"'))
        self.assertEqual(check_configuration(self.root), ['testDriver must be MotivicTest'])

    def test_production_components_accept_canonical_names_but_reject_lowercase_child(self):
        self.write('Motivic/Cohomology/A1/H1/ZMod/Basic.lean',
                   'module\npublic import Mathlib.lowercase\nnamespace lowercase\nend lowercase\n')
        self.write('MotivicTest/lowercase.lean', 'module\n')
        self.assertEqual(check_sources(self.root)[0], [])
        self.write('Motivic/Sites/Smooth/Units/s.lean', 'module\n')
        errors, _ = check_sources(self.root)
        self.assertEqual(len(errors), 1, errors)
        self.assertIn('Motivic.Sites.Smooth.Units.s', errors[0])
        self.assertIn('production module components must use PascalCase', errors[0])

    def test_root_namespace_commands_reject_nested_literal_root_names(self):
        for path in ('Motivic/Aglib/AlgebraicGeometry/FiniteFiber.lean',
                     'MotivicTest/FiniteFiber.lean',
                     'examples/downstream/MotivicClient.lean'):
            for command in ('namespace _root_.PrimeSpectrum.FiniteFiber', 'namespace _root_'):
                with self.subTest(path=path, command=command):
                    self.write(path, 'module\nnamespace AlgebraicGeometry.Scheme\n'
                               + command + '\nend\nend AlgebraicGeometry.Scheme\n')
                    errors, _ = check_sources(self.root)
                    self.assertEqual(len(errors), 1, errors)
                    self.assertIn(f'{path}:3: namespace _root_ does not escape', errors[0])
                    self.assertIn('close and reopen namespaces instead', errors[0])
            (self.root / path).unlink()

    def test_root_namespace_comments_strings_and_distinct_identifiers_are_ignored(self):
        self.write('Motivic/Core.lean', '''module
/- namespace _root_.PrimeSpectrum /- namespace _root_ -/ -/
-- namespace _root_
def text := "namespace _root_.PrimeSpectrum.FiniteFiber"
namespace _root_namespace
end _root_namespace
namespace AlgebraicGeometry.Scheme
end AlgebraicGeometry.Scheme
namespace PrimeSpectrum.FiniteFiber
end PrimeSpectrum.FiniteFiber
''')
        self.assertEqual(check_sources(self.root)[0], [])

    def test_subject_can_depend_on_core_but_actual_cycle_fails(self):
        self.write('Motivic/RingTheory/Bridge.lean', 'import Motivic.Core\n')
        self.assertEqual(check_sources(self.root)[0], [])
        self.write('Motivic/Core.lean', 'import Motivic.RingTheory.Bridge\n')
        errors, _ = check_sources(self.root)
        self.assertTrue(any('Import cycle:' in error for error in errors), errors)

    def test_candidate_and_external_dependencies_allow_host_consumers(self):
        self.write('Motivic/Aglib/RingTheory/Basic.lean',
                   'public import Mathlib.Algebra.Group.Basic\npublic import Aglib.FieldTheory.Basic\n'
                   'public import Std\nnamespace Motivic.HostNamespace\nend Motivic.HostNamespace\n')
        self.write('Motivic/Aglib/RingTheory/Bridge.lean',
                   'public import Motivic.Aglib.RingTheory.Basic\n')
        self.write('Motivic/Core.lean', 'public import Motivic.Aglib.RingTheory.Bridge\n')
        self.assertEqual(check_sources(self.root)[0], [])

    def test_candidate_cannot_import_host_leaf_or_package_root(self):
        for host in ('Motivic.Core', 'Motivic'):
            with self.subTest(host=host):
                self.write('Motivic/Aglib/RingTheory/Bridge.lean', f'public import {host}\n')
                errors, _ = check_sources(self.root)
                self.assertEqual(len(errors), 1, errors)
                self.assertIn(f'candidate imports host module {host}', errors[0])

    def test_candidate_intermediate_host_edge_is_rejected_at_its_owner(self):
        self.write('Motivic/Aglib/RingTheory/Entry.lean',
                   'public import Motivic.Aglib.RingTheory.Bridge\n')
        self.write('Motivic/Aglib/RingTheory/Bridge.lean', 'public import Motivic.Core\n')
        errors, _ = check_sources(self.root)
        self.assertEqual(len(errors), 1, errors)
        self.assertIn('Motivic.Aglib.RingTheory.Bridge: candidate imports host module Motivic.Core',
                      errors[0])
        self.write('Motivic/Core.lean', 'public import Motivic.Aglib.RingTheory.Entry\n')
        errors, _ = check_sources(self.root)
        self.assertTrue(any('candidate imports host module' in error for error in errors), errors)
        self.assertTrue(any('Import cycle:' in error for error in errors), errors)

    def test_indirect_test_leak_is_detected_at_its_production_edge(self):
        self.write('Motivic/Bridge.lean', 'import MotivicTest.Client\n')
        self.write('Motivic/Core.lean', 'import Motivic.Bridge\n')
        errors, _ = check_sources(self.root)
        self.assertTrue(any('production imports test' in error for error in errors), errors)

    def test_lexical_noise_does_not_hide_missing_import_or_forbidden_code(self):
        self.write('Motivic/Core.lean', '''/- sorry /- import Tests.Old -/ axiom -/
def text := "unsafe import Quillen.Old"
public import
  Motivic.Missing
theorem bad : True := by sorry
''')
        errors, _ = check_sources(self.root)
        self.assertEqual(sum('forbidden token' in error for error in errors), 1, errors)
        self.assertTrue(any('missing local import Motivic.Missing' in error for error in errors))
        self.assertFalse(any('obsolete import' in error for error in errors))
        self.assertEqual(lean_imports('import «Tests».Old -- comment\n'), ['Tests.Old'])

    def test_cache_walk_follows_reachable_upstream_without_whole_library(self):
        self.write('Motivic/Core.lean', 'import Aglib.Focused\n')
        self.write('.lake/packages/Aglib/Aglib/Focused.lean',
                   'import Mathlib.Algebra.Group.Basic\n')
        self.write('.lake/packages/Aglib/Aglib/Unrelated.lean',
                   'import Mathlib\n')
        self.assertEqual(cache_roots(self.root, ['Motivic']), ['Mathlib.Algebra.Group.Basic'])
        self.write('Motivic/Core.lean', 'import Mathlib\n')
        with self.assertRaisesRegex(ValueError, 'Whole Mathlib'):
            cache_roots(self.root, ['Motivic'])

    def style_driver(self):
        self.write('.lake/packages/mathlib/scripts/lint-style.lean',
                   'import Lake.CLI.Main\nimport Lean.Elab.ParseImportsFast\n'
                   'import Batteries.Data.String.Basic\nimport Mathlib.Tactic.Linter.TextBased\n'
                   'import ImportGraph.Imports.FromSource\nimport Cli.Basic\n')

    def test_lint_runtime_fetches_exact_cached_leaves_without_optional_support_roots(self):
        self.style_driver()
        argv = ['cache.py', '--root', str(self.root), '--lint-runtime', 'Motivic']
        with patch.object(sys, 'argv', argv), patch('cache.subprocess.run',
                return_value=subprocess.CompletedProcess([], 0)) as run:
            self.assertEqual(cache_main(), 0)
        run.assert_called_once()
        self.assertEqual(run.call_args.args[0], ['lake', 'exe', 'cache', 'get',
                         'Batteries.Data.String.Basic', 'Mathlib.Algebra.Group.Basic',
                         'Mathlib.Tactic.Linter.TextBased'])
        self.assertEqual(run.call_args.kwargs['cwd'], self.root.resolve())
        self.assertTrue(run.call_args.kwargs['check'])

    def test_lint_runtime_list_is_read_only_and_ordinary_cache_scope_is_unchanged(self):
        self.style_driver()
        for flag, expected in (([], ['Mathlib.Algebra.Group.Basic']),
                               (['--lint-runtime'], ['Batteries.Data.String.Basic',
                                'Mathlib.Algebra.Group.Basic', 'Mathlib.Tactic.Linter.TextBased'])):
            with self.subTest(flag=flag):
                output = io.StringIO()
                argv = ['cache.py', '--root', str(self.root), '--list', *flag, 'Motivic']
                with patch.object(sys, 'argv', argv), patch('cache.subprocess.run') as run, \
                        redirect_stdout(output):
                    self.assertEqual(cache_main(), 0)
                run.assert_not_called()
                self.assertEqual(output.getvalue().splitlines(), expected)
        self.assertFalse((self.root / '.lake/build').exists())

    def test_pin_drift_is_detected_before_dependency_resolution(self):
        _, packages = self.configuration()
        self.assertEqual(check_configuration(self.root), [])
        packages[0]['rev'] = '0' * 40
        self.write('lake-manifest.json', json.dumps(dict(name='Motivic', packages=packages)))
        self.assertTrue(any('manifest differs' in error for error in check_configuration(self.root)))

    def test_independent_client_boundary_and_placeholder_policy(self):
        self.write('examples/downstream/MotivicClient.lean', 'import Motivic.Core\n')
        errors, count = check_sources(self.root)
        self.assertEqual(errors, [])
        self.assertEqual(count, 4)
        self.write('Motivic/Core.lean', 'import MotivicClient\n')
        self.assertTrue(any('imports independent client' in error
                            for error in check_sources(self.root)[0]))
        self.write('Motivic/Core.lean', 'import Mathlib.Algebra.Group.Basic\n')
        self.write('examples/downstream/MotivicClient.lean',
                   'import Motivic.Missing\ntheorem bad : True := by sorry\n')
        errors, _ = check_sources(self.root)
        self.assertTrue(any('missing project import' in error for error in errors))
        self.assertTrue(any('forbidden token sorry' in error for error in errors))


class CacheBootstrapTests(unittest.TestCase):
    setUp = RepositoryBoundaryTests.setUp
    write = RepositoryBoundaryTests.write

    def prepare(self):
        self.write('.lake/packages/mathlib/Mathlib/Algebra/Group/Basic.lean', 'module\n')
        self.write('.lake/packages/batteries/Batteries/Data/String/Basic.lean', 'module\n')
        guard = '''import json
def limits():
    return dict(lean_memory_mb=4096,rss_limit_mb=8192,sample_seconds=0.1,
                physical_memory_bytes=16384*1024*1024,lean_threads=1,max_active_lean=1)
def run(command, *, cwd, receipt, budget, env):
    print(json.dumps(dict(command=command,cwd=str(cwd),receipt=str(receipt),budget=budget,env=env)))
    return 17
'''
        build = '''from contextlib import contextmanager
@contextmanager
def capped_toolchain(root, threads=1):
    yield dict(root=str(root),threads=threads,finite_heap_mib=4096)
'''
        self.write('tooling/scripts/resource_guard.py', guard)
        self.write('tooling/scripts/build_serial.py', build)
        return guard, build

    def test_focused_cold_bootstrap_retains_caps_receipt_and_exit_with_tool_fanout(self):
        guard, build = self.prepare()
        command = ['lake', 'exe', 'cache', 'get', 'Mathlib.Algebra.Group.Basic',
                   'Batteries.Data.String.Basic']
        receipt = self.root / 'receipt.json'
        argv = ['--tooling', str(self.root / 'tooling'), '--receipt', str(receipt), '--', *command]
        output = io.StringIO()
        with patch.object(cache_bootstrap, 'GUARD_SHA256', {hashlib.sha256(guard.encode()).hexdigest()}), \
                patch.object(cache_bootstrap, 'BUILD_SHA256', hashlib.sha256(build.encode()).hexdigest()), \
                patch.object(Path, 'cwd', return_value=self.root), patch.object(sys, 'path', sys.path.copy()), \
                patch.dict(sys.modules), redirect_stdout(output):
            self.assertEqual(cache_bootstrap.main(argv), 17)
        observed = json.loads(output.getvalue())
        self.assertEqual(observed['command'], command)
        self.assertEqual(observed['receipt'], str(receipt))
        self.assertEqual(observed['budget'], dict(lean_memory_mb=4096, rss_limit_mb=8192,
                         sample_seconds=0.1, physical_memory_bytes=16384*1024*1024,
                         lean_threads=1, max_active_lean=None, native_build_threads=1))
        self.assertEqual(observed['env']['threads'], 1)
        self.assertEqual(observed['env']['finite_heap_mib'], 4096)

    def test_bootstrap_rejects_unscoped_foreign_or_option_commands(self):
        self.prepare()
        prefix = ['lake', 'exe', 'cache', 'get']
        for command in (prefix, [*prefix, 'Mathlib'], [*prefix, 'Batteries'],
                        [*prefix, 'Aglib.Focused'], [*prefix, '--force'],
                        [*prefix, 'Mathlib.Missing'], ['bash', '-c', 'lake exe cache get'],
                        ['lake', 'build', 'Mathlib.Algebra.Group.Basic']):
            with self.subTest(command=command), self.assertRaises(ValueError):
                cache_bootstrap.validate_command(command, self.root)

    def test_changed_vendor_sources_fail_before_execution(self):
        guard, build = self.prepare()
        argv = ['--tooling', str(self.root / 'tooling'), '--receipt', str(self.root / 'receipt.json'),
                '--', 'lake', 'exe', 'cache', 'get', 'Mathlib.Algebra.Group.Basic']
        for changed in ('guard', 'build'):
            with self.subTest(changed=changed), \
                    patch.object(cache_bootstrap, 'GUARD_SHA256',
                                 {'0' * 64} if changed == 'guard' else {hashlib.sha256(guard.encode()).hexdigest()}), \
                    patch.object(cache_bootstrap, 'BUILD_SHA256',
                                 '0' * 64 if changed == 'build' else hashlib.sha256(build.encode()).hexdigest()), \
                    patch.object(Path, 'cwd', return_value=self.root), \
                    patch('cache_bootstrap.load') as load, redirect_stderr(io.StringIO()):
                self.assertEqual(cache_bootstrap.main(argv), 125)
                load.assert_not_called()

    def test_guarded_cache_wrapper_dispatches_focused_bootstrap_and_budget_overrides(self):
        self.prepare()
        argv = ['cache.py', '--root', str(self.root), '--guarded', 'Motivic']
        with patch.object(sys, 'argv', argv), patch.dict(os.environ,
                MOTIVIC_TOOLING_ROOT=str(self.root / 'tooling'), MOTIVIC_LEAN_MEMORY_MB='4096',
                MOTIVIC_RSS_LIMIT_MB='8192'), patch('cache.subprocess.run') as run:
            self.assertEqual(cache_main(), 0)
        run.assert_called_once()
        command = run.call_args.args[0]
        self.assertEqual(Path(command[1]).name, 'cache_bootstrap.py')
        self.assertEqual(command[command.index('--tooling') + 1], str((self.root / 'tooling').resolve()))
        self.assertEqual(command[command.index('--') + 1:],
                         ['lake', 'exe', 'cache', 'get', 'Mathlib.Algebra.Group.Basic'])
        self.assertEqual(run.call_args.kwargs['env']['AGLIB_LEAN_MEMORY_MB'], '4096')
        self.assertEqual(run.call_args.kwargs['env']['AGLIB_RSS_LIMIT_MB'], '8192')


if __name__ == '__main__':
    unittest.main()
