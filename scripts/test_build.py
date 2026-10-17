# Authors: kangxyz
"""Exercise the public build wrapper against a stand-in helper, without Lean."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


class BuildForwardingTests(unittest.TestCase):
    def test_existing_calls_and_optional_mapping_export_share_the_guarded_route(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            (root / 'Motivic').mkdir()
            (root / 'Motivic/Selected.lean').write_text('module\n')
            helper = root / 'tooling/scripts/build_serial.py'
            helper.parent.mkdir(parents=True)
            helper.write_text('import json,sys\nprint(json.dumps(sys.argv[1:]))\n')
            script = Path(__file__).with_name('build.py')
            environment = dict(os.environ, MOTIVIC_TOOLING_ROOT=str(root / 'tooling'))
            base = [sys.executable, str(script), '--root', str(root),
                    '--receipt-dir', 'receipts']
            for extra in ([], ['--outputs', 'mapping outputs.jsonl']):
                result = subprocess.run([*base, *extra, 'Motivic.Selected'],
                                        env=environment, capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                forwarded = json.loads(result.stdout)
                self.assertIn('--rehash', forwarded)
                self.assertEqual(forwarded[-1], 'Motivic.Selected')
                self.assertEqual(forwarded[forwarded.index('--receipt-dir') + 1], str(root / 'receipts'))
                if extra:
                    self.assertEqual(forwarded[forwarded.index('--outputs') + 1],
                                     str(root / 'mapping outputs.jsonl'))
                else:
                    self.assertNotIn('--outputs', forwarded)


if __name__ == '__main__':
    unittest.main()
