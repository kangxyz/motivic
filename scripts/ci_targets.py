#!/usr/bin/env python3
"""Select changed local modules and their affected public consumers for CI."""
# Authors: kangxyz
import argparse
import os
from pathlib import Path
import subprocess
import sys

from library_sources import is_import_surface, lean_imports, module_name, source_modules

ROOT = Path(__file__).resolve().parents[1]
DEFAULTS = ('Motivic', 'MotivicTest')
CONFIG_INPUTS = {'lakefile.toml', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain'}
CLIENT = 'examples/downstream/'


def client_input(path: str) -> bool:
    return path.startswith(CLIENT) and (path.endswith('.lean')
        or path[len(CLIENT):] in CONFIG_INPUTS)


def select_client(root: Path, changed: list[str], targets: list[str]) -> bool:
    if any(client_input(path) for path in changed):
        return True
    source = root / CLIENT / 'MotivicClient.lean'
    return source.is_file() and any(name in targets for name in lean_imports(source.read_text()))


def validation_scope(changed: list[str], *, setup: bool = False,
                     manual: bool = False) -> tuple[bool, list[str]]:
    """Select structural checks and fixtures from the current tool ownership."""
    if setup:
        return True, ['test_*.py']
    structural = manual or any(path.endswith('.lean') or path in CONFIG_INPUTS or client_input(path)
                               for path in changed)
    fixtures = set()
    owners = {
        'scripts/ci_targets.py': 'test_ci_targets.py',
        'scripts/test_ci_targets.py': 'test_ci_targets.py',
        'scripts/build.py': 'test_build.py',
        'scripts/test_build.py': 'test_build.py',
        'scripts/build_client.py': 'test_build_client.py',
        'scripts/test_build_client.py': 'test_build_client.py',
        'scripts/cache.py': 'test_repository.py',
        'scripts/check_repository.py': 'test_repository.py',
        'scripts/test_repository.py': 'test_repository.py',
    }
    for path in changed:
        if path == 'scripts/library_sources.py' or (
                path.startswith('.github/') and path.endswith(('.yml', '.yaml', '.py', '.sh'))):
            structural = True
            fixtures.add('test_*.py')
        elif path in owners:
            fixtures.add(owners[path])
            if path == 'scripts/check_repository.py':
                structural = True
        elif path.startswith('scripts/') and path.endswith(('.py', '.sh')):
            structural = True
            fixtures.add('test_*.py')
    if 'test_*.py' in fixtures:
        return structural, ['test_*.py']
    return structural, sorted(fixtures)


def select_targets(root: Path, changed: list[str], *, full: bool = False,
                   manual: list[str] | None = None) -> list[str]:
    sources = source_modules(root)
    if manual is not None or full:
        targets = list(DEFAULTS) if manual is None else list(dict.fromkeys(manual))
        if not targets:
            raise ValueError('An explicit manual target list cannot be empty')
        missing = [name for name in targets if name not in sources]
        if missing:
            raise ValueError('Expected existing local Motivic/MotivicTest targets: ' + ', '.join(missing))
        return targets
    needs_defaults = any(path in CONFIG_INPUTS or (
            path.startswith('.github/') and path.endswith(('.yml', '.yaml', '.py', '.sh'))) or (
            path.startswith('scripts/') and path.endswith(('.py', '.sh')))
           for path in changed)
    defaults = set(select_targets(root, [], full=True)) if needs_defaults else set()
    if any(client_input(path) for path in changed):
        defaults.add('Motivic')
    selected = {module_name(path) for path in changed if path.endswith('.lean')
                and module_name(path) in sources}
    if not selected:
        return sorted(defaults)
    texts = {name: path.read_text() for name, path in sources.items()}
    public = {name for name, path in sources.items()
              if name in DEFAULTS or name.startswith('MotivicTest.')
              or path.with_suffix('').is_dir()
              or is_import_surface(texts[name])}
    reverse = {}
    for name, path in sources.items():
        for imported in lean_imports(texts[name]):
            if imported in sources:
                reverse.setdefault(imported, set()).add(name)
    affected, pending = set(selected), list(selected)
    while pending:
        name = pending.pop()
        for consumer in reverse.get(name, set()):
            if consumer not in affected:
                affected.add(consumer)
                pending.append(consumer)
    return sorted(defaults | selected | (affected & public))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--event', default=os.environ.get('EVENT', 'push'))
    parser.add_argument('--base', default=os.environ.get('BASE', ''))
    parser.add_argument('--manual-targets', default=os.environ.get('MANUAL_TARGETS', ''))
    parser.add_argument('--github-output', type=Path)
    args = parser.parse_args()
    root = args.root.resolve()
    try:
        first_push = args.event != 'workflow_dispatch' and (not args.base or set(args.base) == {'0'})
        manual = args.manual_targets.split() if args.event == 'workflow_dispatch' and args.manual_targets.strip() else None
        full = first_push or args.event == 'workflow_dispatch'
        changed = [] if full else subprocess.check_output(
            ['git', 'diff', '--name-only', '-z', args.base, 'HEAD'], cwd=root).decode().rstrip('\0').split('\0')
        targets = select_targets(root, changed, full=full, manual=manual)
        setup = first_push or (args.event == 'workflow_dispatch'
                               and (manual is None or tuple(manual) == DEFAULTS))
        client = select_client(root, changed, targets)
        structural, tests = validation_scope(changed, setup=setup,
                                              manual=args.event == 'workflow_dispatch')
        print(' '.join(targets))
        if args.github_output:
            with args.github_output.open('a') as output:
                output.write('lean=' + str(bool(targets)).lower() + '\n')
                output.write('targets=' + ' '.join(targets) + '\n')
                output.write('client=' + str(client).lower() + '\n')
                output.write('structural=' + str(structural).lower() + '\n')
                output.write('tool_tests=' + ' '.join(tests) + '\n')
    except (OSError, UnicodeError, ValueError, subprocess.CalledProcessError) as error:
        print(f'CI target selection failed: {error}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
