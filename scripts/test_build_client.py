# Authors: kangxyz
"""Independent-client cache ownership and guarded acceptance fixtures, without Lean."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from build_client import prepare


class ClientBuildTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='motivic client ')
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.client = self.root / 'examples/downstream'
        self.client.mkdir(parents=True)
        self.packages = self.root / '.lake/packages'
        self.packages.mkdir(parents=True)
        (self.root / 'lean-toolchain').write_text('leanprover/lean4:fixture\n')
        (self.client / 'lean-toolchain').write_text('leanprover/lean4:fixture\n')
        (self.client / 'MotivicClient.lean').write_text('module\npublic import Motivic\n')
        (self.client / 'lakefile.toml').write_text('''name = "MotivicClient"
[[lean_lib]]
name = "MotivicClient"
leanOptions = {autoImplicit = false, warningAsError = true}
[[require]]
name = "Motivic"
path = "../.."
''')
        self.manifest = {'name': 'Motivic', 'version': '1.2.0', 'lakeDir': '.lake',
            'packagesDir': '.lake/packages', 'packages': [
                {'name': 'Aglib', 'type': 'git', 'rev': 'locked-aglib', 'inherited': False},
                {'name': 'mathlib', 'type': 'git', 'rev': 'locked-mathlib', 'inherited': False}]}
        (self.root / 'lake-manifest.json').write_text(json.dumps(self.manifest) + '\n')

    def test_inherits_exact_pins_and_shares_only_this_checkout_packages(self):
        original = (self.root / 'lake-manifest.json').read_bytes()
        self.assertEqual(prepare(self.root), self.client)
        manifest = json.loads((self.client / 'lake-manifest.json').read_text())
        self.assertEqual(manifest['name'], 'MotivicClient')
        self.assertEqual([(r['name'], r['rev'], r['inherited']) for r in manifest['packages'][:-1]],
                         [('Aglib', 'locked-aglib', True), ('mathlib', 'locked-mathlib', True)])
        self.assertEqual(manifest['packages'][-1]['dir'], '../..')
        self.assertEqual((self.client / '.lake/packages').resolve(), self.packages)
        self.assertFalse((self.client / '.lake/build').is_symlink())
        self.assertEqual((self.root / 'lake-manifest.json').read_bytes(), original)
        prepare(self.root)  # Repeated preparation preserves the same owned cache.

    def test_rejects_foreign_packages_without_overwriting_user_state(self):
        (self.client / '.lake').mkdir()
        foreign = self.root / 'foreign-packages'
        foreign.mkdir()
        (self.client / '.lake/packages').symlink_to(foreign, target_is_directory=True)
        manifest = self.client / 'lake-manifest.json'
        manifest.write_text('user manifest\n')
        with self.assertRaisesRegex(ValueError, 'foreign cache'):
            prepare(self.root)
        self.assertEqual(manifest.read_text(), 'user manifest\n')
        self.assertEqual((self.client / '.lake/packages').resolve(), foreign)

    def test_rejects_shared_build_outputs_and_toolchain_drift(self):
        (self.client / 'lean-toolchain').write_text('different\n')
        with self.assertRaisesRegex(ValueError, 'same pinned'):
            prepare(self.root)
        (self.client / 'lean-toolchain').write_text('leanprover/lean4:fixture\n')
        (self.client / '.lake').mkdir()
        (self.client / '.lake/build').symlink_to(self.root / 'foreign-build')
        with self.assertRaisesRegex(ValueError, 'owned directories'):
            prepare(self.root)

    def test_guarded_helper_receives_client_root_caps_and_failure_is_fatal(self):
        helper = self.root / 'tooling/scripts/build_serial.py'
        helper.parent.mkdir(parents=True)
        helper.write_text('''import json,os,sys
from pathlib import Path
print(json.dumps({'args':sys.argv[1:], 'cwd':str(Path.cwd()),
 'caps':[os.environ.get('AGLIB_'+n) for n in ['BUILD_THREADS','LEAN_MEMORY_MB','RSS_LIMIT_MB']]}))
sys.exit(int(os.environ.get('FIXTURE_EXIT','0')))
''')
        env = dict(os.environ, MOTIVIC_TOOLING_ROOT=str(self.root / 'tooling'),
                   MOTIVIC_BUILD_THREADS='2', MOTIVIC_LEAN_MEMORY_MB='12800',
                   MOTIVIC_RSS_LIMIT_MB='13824')
        command = [sys.executable, str(Path(__file__).with_name('build_client.py')),
                   '--root', str(self.root), '--receipt-dir', '.lake/verification/client']
        for code in (0, 23):
            with self.subTest(exit_code=code):
                result = subprocess.run(command, env=dict(env, FIXTURE_EXIT=str(code)),
                                        capture_output=True, text=True)
                self.assertEqual(result.returncode, code, result.stderr)
                got = json.loads(result.stdout)
                self.assertEqual(got['cwd'], str(self.client))
                self.assertEqual(got['caps'], ['2', '12800', '13824'])
                self.assertEqual(got['args'], ['--root', str(self.client), '--rehash',
                    '--receipt-dir', str(self.root / '.lake/verification/client'), 'MotivicClient'])

    def test_workflow_accepts_client_before_publishing(self):
        workflow = (Path(__file__).resolve().parents[1] / '.github/workflows/ci.yml').read_text()
        export = workflow.index('name: Export current core and selected-target native mappings')
        client = workflow.index('name: Build the independent public client')
        self.assertLess(workflow.index('id: build\n'), export)
        self.assertLess(export, client)
        self.assertLess(client, workflow.index('id: native-stage'))
        client_step = workflow[client:].split('\n      - name:', 1)[0]
        self.assertIn("needs.source.outputs.client == 'true' ||", client_step)
        self.assertIn("(github.event_name == 'push' && github.ref == 'refs/heads/main')", client_step)
        # Keep the existing GitHub cache path schema/version for both restore and save.
        self.assertEqual(workflow.count('          path: .lake/build\n'), 2)
        self.assertNotIn('path: examples/downstream/.lake/build', workflow)
        self.assertNotIn('            examples/downstream/.lake/build', workflow)


if __name__ == '__main__':
    unittest.main()
