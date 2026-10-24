#!/usr/bin/env python3
# Authors: kangxyz
"""Locate the installed or explicitly selected shared toolkit."""
import importlib
import os
from pathlib import Path
import sys
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def shared_api(tooling_root=None):
    """Use the installed package or an explicitly selected tooling checkout."""
    location = tooling_root or os.environ.get('MOTIVIC_TOOLING_ROOT') or os.environ.get('LEAN_CI_TOOLING_ROOT')
    if location:
        package = Path(location).expanduser().resolve() / 'scripts'
        if not (package / 'lean_ci/__init__.py').is_file():
            raise ValueError('Tooling checkout does not provide scripts/lean_ci: ' + str(package.parent))
        sys.path.insert(0, str(package))
    try:
        package = importlib.import_module('lean_ci')
        importlib.import_module('lean_ci.motivic')
        return package
    except ImportError as error:
        raise ValueError('Install lean-incremental-ci 0.3 or newer, or select its checkout with MOTIVIC_TOOLING_ROOT') from error



def forward(action, argv=None, tooling_root=None):
    try:
        shared_api(tooling_root)
        from lean_ci.cli import main
        arguments = list(sys.argv[1:] if argv is None else argv)
        if action == 'check':
            return main(['check', *arguments], root=ROOT)
        return main(['motivic', action, '--root', str(ROOT), *arguments])
    except (OSError, ValueError, ImportError, subprocess.SubprocessError) as error:
        print('Lean toolkit command failed: ' + str(error), file=sys.stderr)
        return 2
