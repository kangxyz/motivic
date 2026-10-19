#!/usr/bin/env python3
"""Select incremental validation from an explicit Git comparison or target list."""
# Authors: kangxyz
import argparse
import base64
import gzip
import hashlib
import json
import os
import re
from pathlib import Path
import subprocess
import sys
import tomllib

from library_sources import lean_imports, module_name, source_modules

ROOT = Path(__file__).resolve().parents[1]
DEFAULTS = ('Motivic', 'MotivicTest')
CONFIG_INPUTS = {'lakefile.toml', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain'}
CLIENT = 'examples/downstream/'
DEPENDENCY_SCOPE = '.github/dependency-scope.json'


def dependency_scope(root: Path, base: str) -> tuple[list[str], str]:
    """Validate the reviewed Aglib transition against both configuration snapshots."""
    def reject(message):
        raise ValueError(f'{DEPENDENCY_SCOPE}: {message}; review the exact pin transition and local targets')

    def keys(value, expected):
        return isinstance(value, dict) and set(value) == set(expected)

    try:
        raw = (root / DEPENDENCY_SCOPE).read_bytes()
        record = json.loads(raw)
    except (OSError, ValueError) as error:
        reject(f'missing or malformed reviewed dependency scope ({error})')
    if not keys(record, {'version', 'dependency', 'before', 'after', 'targets'}) or type(record['version']) is not int or record['version'] != 1:
        reject('expected the exact version 1 schema')
    dependency = record['dependency']
    if not keys(dependency, {'name', 'before', 'after'}) or dependency['name'] != 'Aglib':
        reject('expected an Aglib revision pair')
    if any(not isinstance(dependency[side], str) or not re.fullmatch(r'[0-9a-f]{40}', dependency[side])
           for side in ('before', 'after')) or dependency['before'] == dependency['after']:
        reject('expected distinct exact Aglib revisions')
    for side in ('before', 'after'):
        expected = record[side]
        if not keys(expected, CONFIG_INPUTS) or any(
                value is not None and (not isinstance(value, str) or not re.fullmatch(r'[0-9a-f]{64}', value))
                for value in expected.values()):
            reject(f'{side} must contain every configuration path with a SHA256 or null')
        snapshot = {}
        for path in sorted(CONFIG_INPUTS):
            if side == 'before':
                exists = subprocess.run(['git', 'cat-file', '-e', f'{base}:{path}'], cwd=root,
                                        capture_output=True)
                content = (subprocess.check_output(['git', 'show', f'{base}:{path}'], cwd=root)
                           if exists.returncode == 0 else None)
            else:
                content = (root / path).read_bytes() if (root / path).exists() else None
            actual = hashlib.sha256(content).hexdigest() if content is not None else None
            if expected[path] != actual:
                reject(f'stale or unexpected {side} configuration: {path}')
            snapshot[path] = content
        try:
            config = tomllib.loads(snapshot['lakefile.toml'].decode())
            manifest = json.loads(snapshot['lake-manifest.json'])
            configured = [item['rev'] for item in config['require'] if item.get('name') == 'Aglib']
            resolved = [item['rev'] for item in manifest['packages'] if item.get('name') == 'Aglib']
        except (AttributeError, KeyError, TypeError, ValueError, UnicodeError) as error:
            reject(f'unreadable {side} Aglib pin ({error})')
        if configured != [dependency[side]] or resolved != [dependency[side]]:
            reject(f'{side} Aglib revision disagrees with lakefile/manifest')
    targets = record['targets']
    if not isinstance(targets, list) or not targets or any(not isinstance(name, str) for name in targets):
        reject('targets must be a nonempty list of existing local modules')
    if len(set(targets)) != len(targets) or set(targets) - source_modules(root).keys():
        reject('targets must be unique existing local modules')
    return targets, hashlib.sha256(raw).hexdigest()


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
    """Static checks need no toolchain; fixtures follow current tool ownership."""
    if setup:
        return True, ['test_*.py']
    fixtures = set()
    owners = {
        'ci_targets': 'test_ci_targets.py', 'validate': 'test_validate.py',
        'lint_style': 'test_validate.py', 'lint_declarations': 'test_validate.py',
        'build': 'test_build.py', 'build_modules': 'test_build.py',
        'build_client': 'test_build_client.py',
        'cache': 'test_repository.py', 'cache_bootstrap': 'test_repository.py',
        'check_repository': 'test_repository.py',
        'generate_imports': 'test_generate_imports.py',
        'repository': 'test_repository.py',
    }
    for path in changed:
        if path == 'scripts/library_sources.py' or (
                path.startswith('.github/') and path.endswith(('.yml', '.yaml', '.py', '.sh'))):
            fixtures.add('test_*.py')
        elif path.startswith('scripts/') and path.endswith(('.py', '.sh')):
            stem = Path(path).stem.removeprefix('test_')
            fixtures.add(owners.get(stem, 'test_*.py'))
            if stem == 'check_repository':
                fixtures.add('test_generate_imports.py')
            if stem in {'ci_targets', 'build', 'build_modules', 'build_client', 'cache',
                        'cache_bootstrap'}:
                fixtures.add('test_validate.py')
    return True, ['test_*.py'] if 'test_*.py' in fixtures else sorted(fixtures)


def graph(root: Path) -> tuple[dict, dict]:
    sources = source_modules(root)
    imports = {name: lean_imports(path.read_text()) for name, path in sources.items()}
    return sources, imports


def select_targets(root: Path, changed: list[str], *, full: bool = False,
                   manual: list[str] | None = None, initial: bool = False) -> list[str]:
    sources, imports = graph(root)
    if full:
        return sorted(sources)
    if any(path in CONFIG_INPUTS for path in changed) and manual is None and not initial:
        raise ValueError('Changed dependency/toolchain configuration requires explicit targets or --full; '
                         'recover matching caches and identify the affected scope first')
    selected = set(manual or [])
    if manual is not None:
        if not manual:
            raise ValueError('An explicit manual target list cannot be empty')
        missing = selected - sources.keys()
        if missing:
            raise ValueError('Expected existing local Motivic/MotivicTest targets: ' + ', '.join(sorted(missing)))
    # Keep deleted/renamed names as graph seeds, but never send absent sources to Lake.
    selected.update(module_name(path) for path in changed if path.endswith('.lean')
                    and (path in {'Motivic.lean', 'MotivicTest.lean'}
                         or path.startswith(('Motivic/', 'MotivicTest/'))))
    required = set()
    if any(client_input(path) for path in changed):
        source = root / CLIENT / 'MotivicClient.lean'
        if source.is_file():
            required.update(name for name in lean_imports(source.read_text()) if name in sources)
    reverse = {}
    for name, imported in imports.items():
        for dependency in imported:
            reverse.setdefault(dependency, set()).add(name)
    affected, pending = set(selected), list(selected)
    while pending:
        for consumer in reverse.get(pending.pop(), set()):
            if consumer not in affected:
                affected.add(consumer)
                pending.append(consumer)
    return sorted((affected | required) & sources.keys())


def make_plan(root: Path, changed: list[str], *, full: bool = False,
              manual: list[str] | None = None, initial: bool = False,
              dependency_upgrade: bool = False) -> dict:
    targets = select_targets(root, changed, full=full, manual=manual, initial=initial)
    client = select_client(root, changed, targets)
    sources, imports = graph(root)
    changed_modules = {module_name(path) for path in changed if path.endswith('.lean')}
    seeds = set(targets) if full else changed_modules | set(manual or [])
    if any(client_input(path) for path in changed):
        source = root / CLIENT / 'MotivicClient.lean'
        if source.is_file():
            seeds.update(name for name in lean_imports(source.read_text()) if name in sources)
    providers = {name for name in seeds if name in sources
                 and name.split('.')[0] == 'Motivic'}
    # Unchanged dependency-affected tests do not make unrelated imports changed providers.
    prerequisite_seeds = changed_modules if dependency_upgrade else seeds
    pending = [name for name in prerequisite_seeds
               if name in sources and name.split('.')[0] == 'MotivicTest']
    seen = set(pending)
    while pending:
        for name in imports.get(pending.pop(), []):
            if name in sources and name not in seen:
                seen.add(name)
                if name.split('.')[0] == 'Motivic':
                    providers.add(name)
                else:
                    pending.append(name)
    targets = sorted(set(targets) | providers)
    structural, tests = validation_scope(changed, setup=full, manual=manual is not None)
    lint = sorted((providers | (seeds & sources.keys())) & set(targets))
    return dict(targets=targets, providers=sorted(providers), lint=lint,
                client=client, structural=structural,
                tool_tests=tests, full=full)


def comparison_base(root: Path, base: str, head: str, default_branch: str = '') -> str:
    """Resolve absent push history from available Git evidence, without broad fallback."""
    if base and set(base) != {'0'}:
        return base
    parents = subprocess.check_output(['git', 'rev-list', '--parents', '-n', '1', head], cwd=root).split()
    if len(parents) == 1:
        # Shallow traversal can hide real parents; inspect the commit header itself.
        header = subprocess.check_output(['git', 'cat-file', '-p', head], cwd=root).split(b'\n\n', 1)[0]
        if not any(line.startswith(b'parent ') for line in header.splitlines()):
            return '--root'
        raise ValueError('Git history is shallow; fetch the missing history before selecting affected checks')
    reference = 'refs/remotes/origin/' + default_branch if default_branch else ''
    if not reference:
        result = subprocess.run(['git', 'symbolic-ref', '-q', 'refs/remotes/origin/HEAD'],
                                cwd=root, capture_output=True, text=True)
        if result.returncode == 0:
            reference = result.stdout.strip()
    if reference:
        result = subprocess.run(['git', 'merge-base', head, reference], cwd=root,
                                capture_output=True, text=True)
        if result.returncode == 0:
            return result.stdout.strip()
    raise ValueError('No trustworthy Git comparison base is available: fetch the default-branch history '
                     'and set --default-branch, supply --base, select explicit targets, or opt in with --full')


def changed_paths(root: Path, base: str, head: str) -> list[str]:
    def names(argv):
        return subprocess.check_output(['git', *argv], cwd=root).decode().rstrip('\0').split('\0')
    # --no-renames retains both the removed name and the new name as graph seeds.
    paths = (names(['diff-tree', '--root', '--no-commit-id', '--no-renames', '--name-only', '-r', '-z', head])
             if base == '--root' else
             names(['diff', '--no-renames', '--name-only', '-z', base, head, '--']))
    paths += names(['diff', '--no-renames', '--name-only', '-z', 'HEAD', '--'])
    paths += names(['ls-files', '--others', '--exclude-standard', '-z'])
    return sorted(set(paths) - {''})


def encode_targets(targets: list[str]) -> str:
    payload = ('\n'.join(targets) + ('\n' if targets else '')).encode('utf-8')
    return base64.b64encode(gzip.compress(payload, mtime=0)).decode('ascii')


def arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--event', default=os.environ.get('EVENT', 'push'))
    parser.add_argument('--base', default=os.environ.get('BASE', ''))
    parser.add_argument('--default-branch', default=os.environ.get('DEFAULT_BRANCH', ''),
                        help='trusted default branch for a missing push base; use its fetched origin ref')
    parser.add_argument('--head', default=os.environ.get('HEAD_SHA', 'HEAD'))
    parser.add_argument('--full', action='store_true', default=os.environ.get('FULL', '').lower() == 'true',
                        help='explicitly select every existing local module')
    parser.add_argument('--manual-targets', default=os.environ.get('MANUAL_TARGETS', ''))


def from_arguments(args) -> dict:
    root = args.root.resolve()
    manual = args.manual_targets.split() if args.manual_targets.strip() else None
    base = args.base
    explicit = args.full or (manual is not None and (not base or set(base) == {'0'}))
    if not explicit:
        base = comparison_base(root, base, args.head, args.default_branch)
    changed = [] if explicit else changed_paths(root, base, args.head)
    if args.head != 'HEAD':
        expected = subprocess.check_output(['git', 'rev-parse', args.head], cwd=root).strip()
        actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root).strip()
        if expected != actual:
            raise ValueError('--head must identify the checked-out source; check out that revision first')
    scope_digest = None
    if not args.full and manual is None and base != '--root' and CONFIG_INPUTS.intersection(changed):
        manual, scope_digest = dependency_scope(root, base)
    plan = make_plan(root, changed, full=args.full, manual=manual, initial=base == '--root',
                     dependency_upgrade=scope_digest is not None)
    if scope_digest is not None:
        plan['dependency_scope_sha256'] = scope_digest
    plan['basis'] = dict(event=args.event, base=args.base, head=args.head, default_branch=args.default_branch,
                         full=args.full, manual_targets=args.manual_targets)
    return plan


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    arguments(parser)
    parser.add_argument('--github-output', type=Path)
    parser.add_argument('--plan', type=Path, help='write the exact local/CI validation plan as JSON')
    args = parser.parse_args()
    try:
        plan = from_arguments(args)
        targets = plan['targets']
        print(' '.join(targets))
        if args.plan:
            args.plan.write_text(json.dumps(plan, indent=2) + '\n')
        if args.github_output:
            with args.github_output.open('a') as output:
                for name, value in dict(lean=str(bool(targets) or plan['client']).lower(),
                        targets=' '.join(targets), targets_gzip_base64=encode_targets(targets),
                        plan_gzip_base64=base64.b64encode(gzip.compress(json.dumps(plan).encode(), mtime=0)).decode(),
                        client=str(plan['client']).lower(), structural=str(plan['structural']).lower(),
                        tool_tests=' '.join(plan['tool_tests'])).items():
                    output.write(name + '=' + value + '\n')
    except (OSError, UnicodeError, ValueError, subprocess.CalledProcessError) as error:
        print(f'CI target selection failed: {error}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
