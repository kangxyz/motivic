#!/usr/bin/env python3
# Authors: kangxyz
"""Build explicit local targets through Aglib's guarded incremental Lake driver."""
import argparse
from datetime import datetime, timezone
import os
from pathlib import Path
import subprocess
import sys

from library_sources import module_path

ROOT = Path(__file__).resolve().parents[1]


def command(root: Path, targets: list[str], receipt_dir: Path,
            tooling: Path | None = None, outputs: Path | None = None,
            export_only: bool = False) -> list[str]:
    for target in targets:
        if target.split('.')[0] not in {'Motivic', 'MotivicTest'} or not (
                root / module_path(target)).is_file():
            raise ValueError(f'Expected an existing local Motivic/MotivicTest target: {target}')
    if not targets:
        raise ValueError('At least one explicit build target is required')
    helper = (tooling or root / '.lake/packages/Aglib') / 'scripts/build_serial.py'
    if not helper.is_file():
        raise ValueError(f'Missing guarded build helper {helper}; resolve dependencies or set MOTIVIC_TOOLING_ROOT')
    if export_only:
        if outputs is None:
            raise ValueError('--export-only requires --outputs')
        guard = helper.parent / 'resource_guard.py'
        if not guard.is_file():
            raise ValueError(f'Missing resource guard {guard}')
        return [sys.executable, str(guard.resolve()), '--capped-toolchain',
                '--receipt', str(receipt_dir / 'export.json'), '--',
                'lake', '--rehash', '--no-build', 'build', *targets, '-o', str(outputs)]
    argv = [sys.executable, str(helper.resolve()), '--root', str(root), '--rehash',
            '--receipt-dir', str(receipt_dir)]
    if outputs is not None:
        argv.extend(['--outputs', str(outputs)])
    return [*argv, *targets]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--receipt-dir', type=Path)
    parser.add_argument('--outputs', type=Path, help='export native Lake input-to-output mappings')
    parser.add_argument('--export-only', action='store_true',
                        help='export verified selected mappings with --no-build; fail on cache misses')
    parser.add_argument('targets', nargs='+')
    args = parser.parse_args()
    root = args.root.resolve()
    stamp = datetime.now(timezone.utc).strftime('%Y%m%d-%H%M%S-%f')
    receipts = args.receipt_dir or Path('.lake/verification') / ('build-' + stamp)
    if not receipts.is_absolute():
        receipts = root / receipts
    outputs = args.outputs
    if outputs is not None and not outputs.is_absolute():
        outputs = root / outputs
    environment = dict(os.environ)
    for name in ('BUILD_THREADS', 'LEAN_MEMORY_MB', 'RSS_LIMIT_MB'):
        if 'MOTIVIC_' + name in environment:
            environment['AGLIB_' + name] = environment['MOTIVIC_' + name]
    tooling = environment.get('MOTIVIC_TOOLING_ROOT')
    try:
        argv = command(root, args.targets, receipts, Path(tooling) if tooling else None, outputs, args.export_only)
        if args.export_only:
            receipts.mkdir(parents=True, exist_ok=True)
            outputs.parent.mkdir(parents=True, exist_ok=True)
        return subprocess.run(argv, cwd=root, env=environment).returncode
    except (OSError, ValueError) as error:
        print(f'Focused build failed: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
