#!/usr/bin/env python3
# Authors: kangxyz
"""Run the shared native checks for the Motivic Lake package."""
from pathlib import Path
import subprocess
import sys

from shared_workflow import ROOT, shared_api, resource_config, runtime_environment


def main(argv=None):
    try:
        shared_api()
        from lean_ci.cli import main as native_main
        return native_main(['check', *(sys.argv[1:] if argv is None else argv)],
                           root=ROOT, production=('Motivic',),
                           source_checks=((sys.executable, str(ROOT / 'scripts/check_repository.py'), '--root', '.'),),
                           resource_config=resource_config(), environment=runtime_environment())
    except (OSError, ValueError, ImportError, subprocess.SubprocessError) as error:
        print('Native validation failed: ' + str(error), file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.dont_write_bytecode = True
    raise SystemExit(main())
