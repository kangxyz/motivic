#!/usr/bin/env python3
# Authors: kangxyz
"""Compatibility entry for one shared-core semantic module build or no-build export."""
import argparse
from pathlib import Path
import sys

from library_sources import ROOTS, module_path
from shared_workflow import ROOT, shared_api


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--receipt-dir', type=Path, required=True)
    parser.add_argument('--rehash', action='store_true')
    parser.add_argument('--outputs', type=Path)
    parser.add_argument('--export-only', action='store_true')
    parser.add_argument('targets', nargs='+', help='bare semantic Motivic/MotivicTest module names')
    args = parser.parse_args(argv)
    try:
        root = args.root.resolve()
        for name in args.targets:
            if name.split('.')[0] not in ROOTS or not (root / module_path(name)).is_file():
                raise ValueError('Expected an existing local Motivic/MotivicTest target: ' + name)
        shared_api()
        from lean_ci import build, resources
        from shared_workflow import resource_config, runtime_environment
        config = resource_config()
        environment = runtime_environment()
        if not args.export_only:
            return build.build(root, args.targets, args.receipt_dir, rehash=args.rehash,
                               outputs=args.outputs, config=config, environment=environment, selection='module')
        if args.outputs is None:
            raise ValueError('--export-only requires --outputs')
        args.receipt_dir.mkdir(parents=True, exist_ok=True)
        args.outputs.parent.mkdir(parents=True, exist_ok=True)
        command = ['lake', *(['--rehash'] if args.rehash else []), '--no-build', 'build',
                   *build.native_targets(args.targets, 'module'), '-o', str(args.outputs.resolve())]
        with build.capped_toolchain(root, build.build_threads(environment, config), environment=environment, config=config) as environment:
            return resources.run(command, cwd=root, env=environment,
                                 receipt=args.receipt_dir / 'export.json',
                                 budget=resources.limits(environment, config=config), config=config)
    except (OSError, ValueError) as error:
        print(f'Focused module build failed: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
