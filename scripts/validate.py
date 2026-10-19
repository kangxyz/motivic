#!/usr/bin/env python3
# Authors: kangxyz
"""Run Motivic final checks through the independently pinned shared Lean recipe."""
import argparse
import json
from pathlib import Path
import subprocess
import sys

from ci_targets import ROOT, arguments, from_arguments
from shared_workflow import MotivicAdapter, create_application, shared_api


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    arguments(parser)
    parser.add_argument('--plan', type=Path)
    parser.add_argument('--receipt-dir', type=Path, help='external shared-core state directory')
    parser.add_argument('--progress', type=Path, help='external compatible check progress store')
    parser.add_argument('--outputs', type=Path, help='external validated native mapping export')
    parser.add_argument('--skip-static', action='store_true', help='caller retains compatible source checks')
    parser.add_argument('--skip-cache', action='store_true', help='matching dependency caches are already restored')
    parser.add_argument('--list', action='store_true', help='print shared task declarations without executing tools')
    args = parser.parse_args()
    try:
        root = args.root.resolve()
        plan = json.loads(args.plan.read_text()) if args.plan else from_arguments(args)
        if args.plan and from_arguments(argparse.Namespace(root=root, **plan['basis'])) != plan:
            raise ValueError('Validation selection changed since this plan; select the current affected scope again')
        # The scope is selected under the local worktree envelope, even when the
        # supplied selection was transported by an outer committed CI caller.
        plan = dict(plan, basis=dict(plan['basis'], event='local', head='HEAD'))
        options = dict(full=plan['full'], default_branch=plan['basis']['default_branch'],
                       expected_plan=plan, skip_static=args.skip_static,
                       skip_cache=args.skip_cache, export=args.outputs is not None)
        if args.list:
            shared_api()
            directory = args.receipt_dir or Path('/tmp/motivic-shared-plan')
            for task in MotivicAdapter(**options).tasks(root, {'scope': plan}, 'check', directory):
                print(json.dumps(task, sort_keys=True))
            return 0
        result = create_application(root, **options).check(
            state=args.receipt_dir, requested_base=plan['basis']['base'] or None,
            targets=plan['basis']['manual_targets'].split(), progress=args.progress, outputs=args.outputs)
        print(json.dumps(result, indent=2, sort_keys=True))
        return 0
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        print(f'Selected validation failed: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
