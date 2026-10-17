# Authors: kangxyz
"""Small boundary fixtures; no Lean compiler or dependency checkout required."""
import json
from pathlib import Path
import tempfile
import unittest

from cache import cache_roots
from check_repository import PINS, check_configuration, check_sources
from library_sources import lean_imports


class RepositoryBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.write('Motivic.lean', 'public import Motivic.Core\n')
        self.write('Motivic/Core.lean', 'public import Mathlib.Algebra.Group.Basic\n')
        self.write('MotivicTest.lean', 'import MotivicTest.Client\n')
        self.write('MotivicTest/Client.lean', 'import Motivic\n')

    def write(self, name, content):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)

    def test_candidate_can_depend_on_core_but_actual_cycle_fails(self):
        self.write('Motivic/Aglib/Bridge.lean', 'import Motivic.Core\n')
        self.assertEqual(check_sources(self.root)[0], [])
        self.write('Motivic/Core.lean', 'import Motivic.Aglib.Bridge\n')
        errors, _ = check_sources(self.root)
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

    def test_pin_drift_is_detected_before_dependency_resolution(self):
        config = ('name = "Motivic"\ndefaultTargets = ["Motivic"]\n'
                  'testDriver = "MotivicTest"\n'
                  '[[lean_lib]]\nname = "Motivic"\n'
                  '[[lean_lib]]\nname = "MotivicTest"\n')
        packages = []
        for name, (url, revision) in PINS.items():
            config += f'[[require]]\nname = "{name}"\ngit = "{url}"\nrev = "{revision}"\n'
            packages.append(dict(name=name, url=url, rev=revision, inputRev=revision,
                                 type='git', inherited=False))
        self.write('lakefile.toml', config)
        self.write('lean-toolchain', 'leanprover/lean4:v4.34.1\n')
        self.write('lake-manifest.json', json.dumps(dict(name='Motivic', packages=packages)))
        self.assertEqual(check_configuration(self.root), [])
        packages[0]['rev'] = '0' * 40
        self.write('lake-manifest.json', json.dumps(dict(name='Motivic', packages=packages)))
        self.assertTrue(any('manifest differs' in error for error in check_configuration(self.root)))

    def test_independent_client_boundary_and_placeholder_policy(self):
        self.write('examples/downstream/MotivicClient.lean', 'import Motivic.Core\n')
        errors, count = check_sources(self.root)
        self.assertEqual(errors, [])
        self.assertEqual(count, 5)
        self.write('Motivic/Core.lean', 'import MotivicClient\n')
        self.assertTrue(any('imports independent client' in error
                            for error in check_sources(self.root)[0]))
        self.write('Motivic/Core.lean', 'import Mathlib.Algebra.Group.Basic\n')
        self.write('examples/downstream/MotivicClient.lean',
                   'import Motivic.Missing\ntheorem bad : True := by sorry\n')
        errors, _ = check_sources(self.root)
        self.assertTrue(any('missing project import' in error for error in errors))
        self.assertTrue(any('forbidden token sorry' in error for error in errors))


if __name__ == '__main__':
    unittest.main()
