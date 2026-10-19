# Authors: kangxyz
"""Exercise the public build wrapper against a stand-in helper, without Lean."""
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

from build import command
import build_modules


class BuildForwardingTests(unittest.TestCase):
    def test_existing_calls_and_optional_mapping_export_share_the_guarded_route(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            (root / 'Motivic').mkdir()
            (root / 'Motivic/Selected.lean').write_text('module\n')
            helper = root / 'tooling/scripts/build_serial.py'
            helper.parent.mkdir(parents=True)
            helper.write_text('raise RuntimeError("must not execute while planning")\n')
            for outputs in (None, root / 'mapping outputs.jsonl'):
                forwarded = command(root, ['Motivic.Selected'], root / 'receipts',
                                    root / 'tooling', outputs)
                self.assertEqual(Path(forwarded[1]).name, 'build_modules.py')
                self.assertEqual(forwarded[2], str(helper))
                self.assertIn('--rehash', forwarded)
                self.assertEqual(forwarded[-1], '+Motivic.Selected')
                self.assertEqual(forwarded[forwarded.index('--receipt-dir') + 1], str(root / 'receipts'))
                if outputs:
                    self.assertEqual(forwarded[forwarded.index('--outputs') + 1],
                                     str(root / 'mapping outputs.jsonl'))
                else:
                    self.assertNotIn('--outputs', forwarded)

    def test_export_only_fails_closed_without_invoking_compiler_or_serial_build(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            (root / 'Motivic').mkdir()
            (root / 'Motivic/Selected.lean').write_text('module\n')
            helper = root / 'tooling/scripts/build_serial.py'
            helper.parent.mkdir(parents=True)
            helper.write_text('raise RuntimeError("export must not run the compiling helper")\n')
            guard = helper.with_name('resource_guard.py')
            guard.write_text('import json,sys\nprint(json.dumps(sys.argv[1:]))\nsys.exit(3)\n')
            result = subprocess.run([sys.executable, str(Path(__file__).with_name('build.py')),
                '--root', str(root), '--export-only', '--outputs', 'outputs.jsonl',
                'Motivic.Selected'], env=dict(os.environ, MOTIVIC_TOOLING_ROOT=str(root / 'tooling')),
                capture_output=True, text=True)
            self.assertEqual(result.returncode, 3, result.stderr)
            forwarded = json.loads(result.stdout)
            native = forwarded[forwarded.index('--') + 1:]
            self.assertEqual(native, ['lake', '--rehash', '--no-build', 'build',
                                     '+Motivic.Selected', '-o', str(root / 'outputs.jsonl')])

    def test_export_root_facades_use_module_selectors_without_selecting_whole_libraries(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            for name in ('Motivic', 'MotivicTest'):
                (root / (name + '.lean')).write_text('module\n')
            helper = root / 'tooling/scripts/build_serial.py'
            helper.parent.mkdir(parents=True)
            helper.write_text('raise RuntimeError("must not execute while planning")\n')
            helper.with_name('resource_guard.py').write_text('')
            targets = ['Motivic', 'MotivicTest']
            outputs = root / 'selected.jsonl'
            argv = command(root, targets, root / 'receipts', root / 'tooling', outputs,
                           export_only=True)
            self.assertEqual(argv[argv.index('--') + 1:],
                             ['lake', '--rehash', '--no-build', 'build',
                              '+Motivic', '+MotivicTest', '-o', str(outputs)])
            self.assertNotIn(str(helper), argv)
            ordinary = command(root, targets, root / 'receipts', root / 'tooling')
            self.assertEqual(ordinary[-2:], ['+Motivic', '+MotivicTest'])
            self.assertIn(str(helper), ordinary)

    def test_adapter_validates_plain_names_but_keeps_probe_and_fallback_module_selectors(self):
        fake = '''import argparse,json
from pathlib import Path
events=[]
def source_order(root, targets):
    events.append({'stage':'source_order','targets':targets})
    for target in targets:
        if not (root / Path(*target.split('.')).with_suffix('.lean')).is_file():
            raise ValueError('missing source')
def native(argv, receipt):
    events.append({'stage':'guarded_native','argv':argv,'receipt':str(receipt)})
def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--root',type=Path,required=True)
    parser.add_argument('--receipt-dir',type=Path,required=True)
    parser.add_argument('--rehash',action='store_true')
    parser.add_argument('--outputs',type=Path)
    parser.add_argument('targets',nargs='+')
    a=parser.parse_args()
    source_order(a.root,a.targets)
    lake=['lake']+(['--rehash'] if a.rehash else [])
    outputs=['-o',str(a.outputs)] if a.outputs else []
    native(lake+['--no-build','build',*a.targets,*outputs],a.receipt_dir/'cached-check.json')
    if PROBE_CODE == 3:
        native(lake+['build',*a.targets,*outputs],a.receipt_dir/'graph-build.json')
    print(json.dumps(events))
    return 0 if PROBE_CODE in (0,3) else PROBE_CODE
'''
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            for target in ('Motivic', 'MotivicTest', 'Motivic.Selected'):
                path = root.joinpath(*target.split('.')).with_suffix('.lean')
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('module\n')
            helper = root / 'build_serial.py'
            for code in (0, 3, 7):
                with self.subTest(probe_code=code):
                    source = fake + f'\nPROBE_CODE={code}\n'
                    helper.write_text(source)
                    targets = ['Motivic', 'MotivicTest', 'Motivic.Selected']
                    argv = [str(helper), '--root', str(root), '--receipt-dir', str(root / 'receipts'),
                            '--rehash', '--outputs', str(root / 'outputs.jsonl'),
                            *('+' + target for target in targets)]
                    output = io.StringIO()
                    with patch.object(build_modules, 'DRIVER_SHA256', hashlib.sha256(source.encode()).hexdigest()), \
                            patch.object(sys, 'argv', []), patch.object(sys, 'path', sys.path.copy()), \
                            redirect_stdout(output):
                        self.assertEqual(build_modules.main(argv), 0 if code in (0, 3) else code)
                    events = json.loads(output.getvalue())
                    self.assertEqual(events[0], {'stage': 'source_order', 'targets': targets})
                    expected = ['lake', '--rehash', '--no-build', 'build',
                                '+Motivic', '+MotivicTest', '+Motivic.Selected',
                                '-o', str(root / 'outputs.jsonl')]
                    self.assertEqual(events[1]['argv'], expected)
                    self.assertEqual(events[1]['receipt'], str(root / 'receipts/cached-check.json'))
                    self.assertEqual(len(events), 3 if code == 3 else 2)
                    if code == 3:
                        self.assertEqual(events[2]['argv'], [arg for arg in expected if arg != '--no-build'])
                        self.assertEqual(events[2]['receipt'], str(root / 'receipts/graph-build.json'))

    def test_adapter_rejects_changed_helper_before_execution(self):
        with tempfile.TemporaryDirectory() as temporary:
            helper = Path(temporary) / 'build_serial.py'
            helper.write_text('raise RuntimeError("unreviewed helper must not execute")\n')
            output = io.StringIO()
            with redirect_stderr(output):
                self.assertEqual(build_modules.main([str(helper)]), 1)
            self.assertIn('differs from the reviewed source', output.getvalue())


if __name__ == '__main__':
    unittest.main()
