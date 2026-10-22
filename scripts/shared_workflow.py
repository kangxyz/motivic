#!/usr/bin/env python3
# Authors: kangxyz
"""Locate shared native tooling and retain Motivic's resource overrides."""
import importlib
import os
from pathlib import Path
import sys

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
        return importlib.import_module('lean_ci')
    except ImportError as error:
        raise ValueError('Install lean-incremental-ci or set MOTIVIC_TOOLING_ROOT explicitly') from error


def runtime_environment():
    environment = dict(os.environ)
    # Preserve the existing Motivic override precedence and otherwise inherit
    # the admitted caller's wrappers/profile, limits and toolchain options.
    for suffix in ('BUILD_THREADS', 'LEAN_MEMORY_MB', 'RSS_LIMIT_MB'):
        if 'MOTIVIC_' + suffix in environment:
            environment['AGLIB_' + suffix] = environment['MOTIVIC_' + suffix]
    return environment


def resource_config():
    from lean_ci.resources import ResourceConfig
    return ResourceConfig(prefix='MOTIVIC', profile_keys=('R5_LEAN_REMOTE_PROFILE', 'AGLIB_REMOTE_PROFILE'),
                          memory_keys=('AGLIB_LEAN_MEMORY_MB',), rss_keys=('AGLIB_RSS_LIMIT_MB',),
                          build_thread_keys=('AGLIB_BUILD_THREADS',))
