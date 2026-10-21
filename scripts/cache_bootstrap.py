#!/usr/bin/env python3
# Authors: kangxyz
"""Run focused Mathlib cache acquisition with the pinned bootstrap resource caps."""
import argparse
import hashlib
import importlib.util
from pathlib import Path
import re
import subprocess
import sys

GUARD_SHA256 = {
    '6823119b2c785f99cf8143ef97c8bd5b4cdd442697213510abe483e46d67b0fb',
    '4286c5b59df8a86e067e4bca288b38b1f0d9a341aba86cbbab1b463c86873e2f',
}
BUILD_SHA256 = 'd8a17817fb612923fc8edae53956715cf517286bf2e5c4fa9ef4e4613c8c98a3'
LEAF = re.compile(r"(?:Mathlib|Batteries)(?:\.[A-Za-z_][A-Za-z0-9_']*)+")


def validate_command(command: list[str], root: Path) -> None:
    if command[:4] != ['lake', 'exe', 'cache', 'get'] or len(command) == 4:
        raise ValueError('Cache bootstrap requires lake exe cache get with explicit leaf roots')
    for name in command[4:]:
        if LEAF.fullmatch(name) is None:
            raise ValueError('Cache bootstrap requires explicit Mathlib./Batteries. module leaves')
        package = 'mathlib' if name.startswith('Mathlib.') else 'batteries'
        path = root / '.lake/packages' / package / Path(*name.split('.')).with_suffix('.lean')
        if not path.is_file():
            raise ValueError(f'Missing focused cache source: {name}')


def checked_source(path: Path, expected: set[str]) -> bytes:
    source = path.read_bytes()
    if hashlib.sha256(source).hexdigest() not in expected:
        raise ValueError(f'Bootstrap helper differs from reviewed source: {path}')
    return source


def load(path: Path, name: str, source: bytes):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    exec(compile(source, str(path), 'exec'), module.__dict__)
    return module


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tooling', type=Path, required=True)
    parser.add_argument('--receipt', type=Path, required=True)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    try:
        root = Path.cwd()
        validate_command(command, root)
        directory = args.tooling.resolve() / 'scripts'
        guard_path, build_path = directory / 'resource_guard.py', directory / 'build_serial.py'
        guard_source = checked_source(guard_path, GUARD_SHA256)
        build_source = checked_source(build_path, {BUILD_SHA256})
        sys.path.insert(0, str(directory))
        guard = load(guard_path, 'resource_guard', guard_source)
        build = load(build_path, 'build_serial', build_source)
        budget = guard.limits()
        # Match vendor bootstrap semantics: only cache-tool compilation may fan out.
        budget['max_active_lean'] = None
        budget['native_build_threads'] = 1
        with build.capped_toolchain(root, threads=1) as environment:
            return guard.run(command, cwd=root, receipt=args.receipt, budget=budget, env=environment)
    except (OSError, ValueError, ImportError, subprocess.SubprocessError) as error:
        print(f'Focused cache bootstrap failed: {error}', file=sys.stderr)
        return 125


if __name__ == '__main__':
    raise SystemExit(main())
