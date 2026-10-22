"""Native entry forwarding fixtures; no Lean, cache mutation or hosted lifecycle."""
from contextlib import redirect_stderr
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import validate as entry
import shared_workflow as controls


class NativeEntryTests(unittest.TestCase):
    def test_native_options_are_forwarded_once_without_an_adapter_or_plan(self):
        options = ['--base', 'base', '--head', 'head', '--full', '--source-only',
                   '--progress', '/tmp/progress', '--state', '/tmp/state',
                   '--outputs', '/tmp/outputs.jsonl', '--list']
        with patch('validate.shared_api'), \
                patch('lean_ci.cli.main', return_value=7) as native:
            self.assertEqual(entry.main(options), 7)
        native.assert_called_once()
        self.assertEqual(native.call_args.args, (['check', *options],))
        options = native.call_args.kwargs
        self.assertEqual(options['root'], entry.ROOT)
        self.assertEqual(options['production'], ('Motivic',))
        self.assertNotIn('adapter', options)
        self.assertNotIn('check_targets', options)
        self.assertTrue(options['source_checks'])
        self.assertTrue(all(command[0] == sys.executable for command in options['source_checks']))
        self.assertTrue(all(Path(command[1]).is_file() for command in options['source_checks']))
        self.assertTrue(all('downstream' not in ' '.join(command) for command in options['source_checks']))

    def test_no_arguments_request_native_final_check_without_a_fake_source_baseline(self):
        with patch('validate.shared_api'), patch('lean_ci.cli.main', return_value=0) as native:
            self.assertEqual(entry.main([]), 0)
        self.assertEqual(native.call_args.args, (['check'],))

    def test_explicit_tooling_checkout_uses_scripts_package(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout = Path(directory).resolve()
            package = checkout / 'scripts/lean_ci'
            package.mkdir(parents=True)
            (package / '__init__.py').write_text('')
            with patch.object(sys, 'path', sys.path.copy()), \
                    patch('shared_workflow.importlib.import_module', return_value='selected-package') as load:
                self.assertEqual(controls.shared_api(checkout), 'selected-package')
                self.assertEqual(sys.path[0], str(checkout / 'scripts'))
            load.assert_called_once_with('lean_ci')

    def test_old_ci_directory_is_not_an_implicit_tooling_fallback(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout = Path(directory).resolve()
            (checkout / 'ci/lean_ci').mkdir(parents=True)
            (checkout / 'ci/lean_ci/__init__.py').write_text('')
            with self.assertRaisesRegex(ValueError, 'scripts/lean_ci'):
                controls.shared_api(checkout)

    def test_configuration_and_command_failures_do_not_become_success(self):
        with patch('validate.shared_api', side_effect=ValueError('missing tooling')), \
                patch('lean_ci.cli.main') as native, redirect_stderr(io.StringIO()):
            self.assertEqual(entry.main([]), 2)
        native.assert_not_called()
        with patch('validate.shared_api'), \
                patch('lean_ci.cli.main', side_effect=subprocess.CalledProcessError(3, ['lake'])), \
                redirect_stderr(io.StringIO()):
            self.assertEqual(entry.main([]), 2)

    def test_resource_overrides_and_existing_remote_profile_are_preserved(self):
        config = controls.resource_config()
        self.assertIn('R5_LEAN_REMOTE_PROFILE', config.names('profile'))
        self.assertIn('AGLIB_BUILD_THREADS', config.names('build_thread'))
        self.assertIn('AGLIB_LEAN_MEMORY_MB', config.names('memory'))
        self.assertIn('AGLIB_RSS_LIMIT_MB', config.names('rss'))

    def test_removed_protocol_and_custom_checker_files_are_absent(self):
        obsolete = ['ci_targets.py', 'ci_policy.py', 'lint_declarations.py', 'lint_style.py']
        for name in obsolete:
            self.assertFalse((entry.ROOT / 'scripts' / name).exists(), name)


if __name__ == '__main__':
    unittest.main()
