#!/usr/bin/env python3
# Authors: kangxyz
"""Motivic selection and check policy for the independently pinned Lean CI core.

The existing per-origin Batteries predicate is deliberately retained. A shared
Lean environment batch requires a separate accepted coverage decision.
"""
import argparse
import importlib
import os
from pathlib import Path
import re
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))

from ci_targets import CONFIG_INPUTS, ROOT, from_arguments, graph, make_plan
from library_sources import ROOTS, lean_imports, source_modules

POLICY = ('scripts/shared_workflow.py', 'scripts/ci_policy.py', 'scripts/validate.py', 'scripts/ci_targets.py',
          'scripts/library_sources.py', 'scripts/check_repository.py',
          'scripts/lint_declarations.py', 'scripts/lint_style.py',
          'scripts/cache.py', 'scripts/cache_bootstrap.py',
          '.github/dependency-scope.json')
DRIVERS = ('.lake/packages/batteries/scripts/runLinter.lean',
           '.lake/packages/mathlib/scripts/lint-style.lean')
# This migration has no historical complete native witness. Explicit cutover
# and repair successors enroll the complete local library.
INITIAL_PARENT = '0fcc528c48128a37a04f3a6db8b4833cedb4d891'
INITIAL_PATHS = frozenset({'.github/workflows/ci.yml', 'scripts/shared_workflow.py',
    'scripts/ci_policy.py', 'scripts/test_hosted_ci.py', 'scripts/test_validate.py',
    'scripts/test_ci_targets.py', 'scripts/test_build_client.py',
    'docs/DEVELOPMENT.md', 'scripts/README.md'})
# The first complete enrollment failed declaration lint. Its single repair
# successor may retry complete enrollment; API failure never selects this mode.
REPAIR_PARENT = 'c793b96eb87eee540e665058e83e5f05d5c95683'
# The integrated repair still has no complete hosted baseline. Its explicit
# direct follow-up uses the same bounded repair admission and complete scope.
FOLLOWUP_PARENT = 'cc5c5d57e05a51ec7b1e7d6994646b306059130e'
REPAIR_TOOL_PATHS = frozenset({*INITIAL_PATHS, *POLICY,
    'scripts/build.py', 'scripts/build_modules.py', 'scripts/generate_imports.py',
    'scripts/test_build.py', 'scripts/test_declaration_batch.py', 'scripts/test_repository.py',
    'scripts/test_generate_imports.py'}) - CONFIG_INPUTS - {'.github/dependency-scope.json'}


def repair_path(path):
    """Admit only the assigned mathematical/documentation and exact CI owners."""
    return (path in REPAIR_TOOL_PATHS
            or path in {'Motivic.lean', 'MotivicTest.lean', 'README.md', 'AGENTS.md', 'CONTRIBUTING.md'}
            or (path.startswith(('Motivic/', 'MotivicTest/')) and path.endswith(('.lean', '.md')))
            or (path.startswith('docs/') and path.endswith('.md')))


def enrollment_parent(root, head):
    """Return only an explicitly admitted direct parent, never a verified base."""
    from lean_ci.github import commit, git
    head = commit(root, head)
    header = git(root, 'cat-file', '-p', head).split('\n\n', 1)[0]
    parents = [line.removeprefix('parent ') for line in header.splitlines()
               if line.startswith('parent ')]
    if len(parents) != 1 or parents[0] not in {INITIAL_PARENT, REPAIR_PARENT, FOLLOWUP_PARENT}:
        return None
    parent = parents[0]
    # Preserve filename bytes; whitespace lookalikes are not admitted owners.
    raw_paths = set(subprocess.check_output(['git', 'diff', '--no-renames', '--name-only', '-z',
                    parent, head, '--'], cwd=root).split(b'\0')) - {b''}
    if parent == INITIAL_PARENT:
        return parent if raw_paths and raw_paths <= {p.encode() for p in INITIAL_PATHS} else None
    try:
        paths = {path.decode('utf-8') for path in raw_paths}
    except UnicodeError:
        return None
    deleted = set(subprocess.check_output(['git', 'diff', '--no-renames', '--diff-filter=D',
                  '--name-only', '-z', parent, head, '--'], cwd=root).split(b'\0')) - {b''}
    if any(path.endswith(b'.lean') for path in deleted):
        return None
    # Configuration changes, unrecognized owners and empty retries fail closed.
    # Existing source enrollment cannot shrink through deletion. The path guard
    # also protects absent lakefile.lean and the dependency-scope record.
    return parent if paths and all(repair_path(path) for path in paths) else None


def initial_identity(root, head):
    """Recognize explicit cutover/recovery identity without API fallback."""
    return enrollment_parent(root, head) is not None


def initial_baseline(root, repository, default_branch, head):
    parent = enrollment_parent(root, head)
    if parent is None:
        raise ValueError('Initial enrollment requires the exact cutover or admitted repair successor')
    if repository != 'kangxyz/motivic' or default_branch != 'main':
        raise ValueError('Initial enrollment requires the owning repository/default branch')
    return dict(kind='initial-enrollment', head=head, repository=repository,
                default_branch=default_branch, parent=parent,
                selection_reason=('Explicit repair of failed complete enrollment; no historical verified base'
                                  if parent in {REPAIR_PARENT, FOLLOWUP_PARENT} else
                                  'One-time complete local enrollment; no historical verified base'))


def hosted_scope(root, baseline):
    if baseline.get('kind') == 'initial-enrollment':
        # Explicitly enumerate every local module, including leaves outside the
        # curated facades. Keep the ordinary exact-origin declaration predicate.
        scope = make_plan(Path(root), [], manual=sorted(source_modules(root)))
        scope.update(kind='initial-enrollment', tool_tests=['test_*.py'])
    else:
        scope = selection(root, baseline['base'], default_branch=baseline['default_branch'])
    return dict(scope, native=bool(scope['targets']))


def hosted_protocol(root, head, protocol=None):
    """Require exact reviewed current workflow and supporting recipe identities."""
    from ci_policy import PROTOCOL, TOOLING_REVISION
    from lean_ci.github import git_file, reviewed_recipe, workflow_kind
    protocol = protocol or PROTOCOL
    if (os.environ.get('MOTIVIC_TOOLING_REVISION') != TOOLING_REVISION
            or workflow_kind(git_file(root, head, protocol.workflow_path), protocol) != 'core'
            or not reviewed_recipe(root, head, 'core', protocol)):
        raise ValueError('Hosted workflow, owner recipe or independent tooling pin is not reviewed')
    return protocol


def shared_api():
    """Load only an explicit independently pinned checkout, never ambient siblings."""
    location = os.environ.get('MOTIVIC_TOOLING_ROOT')
    revision = os.environ.get('MOTIVIC_TOOLING_REVISION', '')
    if not location or re.fullmatch('[0-9a-f]{40}', revision) is None:
        raise ValueError('Set MOTIVIC_TOOLING_ROOT and MOTIVIC_TOOLING_REVISION to an independently '
                         'pinned shared-tooling checkout; mathematical dependency pins are unchanged')
    tooling = Path(location).resolve(strict=True)
    def repository_bytes(*arguments):
        try:
            return subprocess.check_output(['git', *arguments], cwd=tooling, stderr=subprocess.PIPE)
        except subprocess.SubprocessError as error:
            raise ValueError('Pinned shared tooling Git source is unavailable; restore the reviewed checkout') from error
    actual = repository_bytes('rev-parse', 'HEAD').decode().strip()
    if actual != revision:
        raise ValueError('Shared tooling HEAD differs from MOTIVIC_TOOLING_REVISION')
    package = tooling / 'ci/lean_ci'
    paths = sorted(package.glob('*.py'))
    if not paths or any(not (package / name).is_file() for name in ('recipe.py', 'local.py', 'batch.py')):
        raise ValueError('Pinned tooling lacks the shared batch/local-check/recipe API; adopt the reviewed common tooling commit')
    expected = {path for path in repository_bytes('ls-tree', '-r', '--name-only', revision, '--',
                                                'ci/lean_ci').decode().splitlines() if path.endswith('.py')}
    if {path.relative_to(tooling).as_posix() for path in paths} != expected:
        raise ValueError('Shared tooling package enrollment differs from its pinned revision')
    for path in paths:
        committed = repository_bytes('show', revision + ':' + path.relative_to(tooling).as_posix())
        if committed != path.read_bytes():
            raise ValueError('Shared tooling source differs from its pinned revision: ' + path.name)
    loaded = sys.modules.get('lean_ci')
    if loaded is not None and Path(loaded.__file__).resolve().parent != package:
        raise ValueError('An ambient lean_ci package was loaded before the pinned shared tooling')
    sys.path.insert(0, str(tooling / 'ci'))
    return importlib.import_module('lean_ci')


def local_inputs(root, requested_base=None, targets=()):
    """Enroll selection candidates before reading the import graph or policy.

    All local source bytes participate in reverse-consumer selection. Absent
    facades/configurations and directory candidates protect additions/shadows.
    Ignored dependency/runtime inputs are observed only after deterministic setup.
    """
    root = Path(root)
    paths = set(POLICY) | set(CONFIG_INPUTS)
    paths.update(('Motivic.lean', 'MotivicTest.lean', 'Motivic', 'MotivicTest',
                  'scripts', '.github', '.github/workflows'))
    for directory in ('Motivic', 'MotivicTest', 'scripts', '.github'):
        base = root / directory
        for path in base.rglob('*'):
            relative = path.relative_to(root)
            if '.lake' in relative.parts or '__pycache__' in relative.parts:
                continue
            if path.is_dir() or path.suffix in {'.lean', '.py', '.sh', '.yml', '.yaml', '.json'}:
                paths.add(relative.as_posix())
    return [({'path': path, 'exclude': ['.lake', '__pycache__']} if (root / path).is_dir() else path)
            for path in sorted(paths)]


def selection(root, requested_base=None, targets=(), *, full=False, default_branch=''):
    args = argparse.Namespace(root=Path(root), event='local', base=requested_base or '',
                              head='HEAD', default_branch=default_branch, full=full,
                              manual_targets=' '.join(targets))
    return from_arguments(args)


def checked_scope(root, scope):
    if scope.get('client') is not False:
        raise ValueError('Separate client diagnostics are outside incremental in-package validation')
    sources = source_modules(root)
    for key in ('targets', 'providers', 'lint'):
        names = scope[key]
        if (not isinstance(names, list) or len(set(names)) != len(names)
                or any(name not in sources for name in names)):
            raise ValueError('Validation plan requires unique existing local targets')
    if not set(scope['providers']) <= set(scope['targets']) or not set(scope['lint']) <= set(scope['targets']):
        raise ValueError('Provider/lint targets must be selected build targets')


def declaration_check(root, names, label, full):
    if not names:
        return []
    if full:
        return [dict(id=label + '/declarations', kind='check',
                     command=['lake', 'env', 'lean', '--run', DRIVERS[0], '--no-build', *names],
                     check_kind='declaration-native-package', modules=names, capped=True,
                     environment_boundary={'mode': 'separate-import-environment-per-origin',
                         'origins': names, 'declarations': 'native-package-prefix'})]
    from lean_ci.resources import remote_profile
    profile = remote_profile(runtime_environment(), resource_config())
    batch = {'id': label + '/declarations', 'jobs': min(8, profile['jobs']) if profile else 1,
             'read_only': True, 'single_process': True}
    command = [sys.executable, str(root / 'scripts/lint_declarations.py'),
               '--root', str(root), '--no-build']
    # The unchanged checker still imports one exact origin in its own process.
    # Individual bindings/progress retain valid peers after failure or interruption.
    return [dict(id=label + '/declarations/' + origin, kind='check',
                 command=[*command, origin], check_kind='declaration-exact-origin',
                 modules=[origin], capped=True, check_batch=dict(batch),
                 environment_boundary={'mode': 'separate-import-environment-per-origin',
                     'origins': [origin], 'declarations': 'exact-defining-origin'})
            for origin in names]


def recipe(root, scope, phase, directory, *, skip_static=False, skip_cache=False, export=False):
    from lean_ci.recipe import native_recipe
    root, directory = Path(root).resolve(), Path(directory).resolve()
    checked_scope(root, scope)
    providers, selected = scope['providers'], scope['targets']
    consumers = [name for name in selected if name not in providers]
    static = []
    def task(label, command, **extra):
        return dict(id=label, kind='process', command=list(map(str, command)), **extra)
    if not skip_static:
        if scope['structural']:
            static.append(task('source/structure', [sys.executable, root / 'scripts/check_repository.py', '--root', root]))
        for pattern in scope['tool_tests']:
            static.append(task('source/fixtures/' + pattern,
                [sys.executable, '-m', 'unittest', 'discover', '-s', root / 'scripts', '-p', pattern]))
    prepare = []
    if selected:
        if not skip_cache:
            prepare.append(task('prepare/cache', [sys.executable, root / 'scripts/cache.py', '--root', root,
                '--resolve-deps', '--lint-runtime', *selected], capped=True, establishes_inputs=True, established_paths=list(DRIVERS)))
        prepare.append(task('prepare/declaration-runtime',
            ['lake', '--rehash', 'build', '+Batteries.Tactic.Lint'], capped=True, establishes_inputs=True))
    style = []
    if scope['lint']:
        style.append(dict(id='selected/style', kind='check', check_kind='style-exact-source',
            command=[sys.executable, str(root / 'scripts/lint_style.py'), '--root', str(root), *scope['lint']],
            modules=[], source_modules=scope['lint'], capped=True,
            environment_boundary={'mode': 'pinned-style-driver-exact-sources', 'sources': scope['lint']}))
    provider = (dict(id='providers', modules=providers,
                    checks=declaration_check(root, providers, 'providers', scope['full'])) if providers else None)
    workspace = dict(id='consumers', modules=consumers, before=style,
                     checks=declaration_check(root, consumers, 'affected-consumers', scope['full']))
    exports = ([name for name, modules in (('providers', providers), ('consumers', consumers)) if modules]
               if export else [])
    return native_recipe(root, directory, source_checks=static, prepare=prepare,
                         provider_gate=provider, root_workspace=workspace,
                         exports=exports, phase=phase)


def _native_source_graph(root, observations):
    """Memoize pure graph parsing inside its whole-source observation lifetime."""
    if observations is None:
        return graph(root)
    from lean_ci.state import InputDrift
    whole = getattr(observations, 'whole', observations)
    whole.assert_stable()
    cache = getattr(whole, '_motivic_source_graphs', None)
    if cache is None:
        cache = whole._motivic_source_graphs = {}
    key = root.resolve()
    if key not in cache:
        excluded = ('.lake', '.git', '__pycache__')
        # Root enrolls the optional facades and source prefixes. Descendant
        # inventories stay inside the actual source prefixes, never parents.
        whole.observe_directory(root, excluded=excluded)
        for prefix in ROOTS:
            for directory, children, _ in os.walk(root / prefix):
                # source_modules includes ignored-name subdirectories inside
                # source prefixes; guard that same enrollment domain exactly.
                whole.observe_directory(Path(directory))
        sources = source_modules(root)
        for path in sources.values():
            whole.hash_file(path)
        snapshot = graph(root)
        if snapshot[0] != sources:
            raise InputDrift('Source enrollment changed while reading the native graph')
        whole.assert_stable()
        cache[key] = (root, snapshot)
    original, (sources, imports) = cache[key]
    whole.assert_stable()
    if original != root:
        sources = {name: root / path.relative_to(original) for name, path in sources.items()}
    return sources, imports


def binding(root, task, toolchain, reflection=None, observations=None):
    from lean_ci.state import check_binding, file_hash
    root = Path(root)
    style = task['check_kind'] == 'style-exact-source'
    names = task.get('source_modules', []) if style else task.get('modules', [])
    policy = [*POLICY, *CONFIG_INPUTS, *DRIVERS]
    if style:
        # Style reads these source files before the consumer graph is built.
        # Subject artifacts are neither prerequisites nor inputs to its predicate.
        sources = source_modules(root)
        raw = [str(sources[name].relative_to(root)) for name in names]
        native_names = []
        tooling = Path(os.environ.get('MOTIVIC_TOOLING_ROOT', root / '.lake/packages/Aglib')).resolve()
        # lint_style.runtime loads this exact helper. Its Python support import
        # resolves to the already loaded Motivic library_sources.py in POLICY.
        policy.append(str(tooling / 'scripts/run_style_linter.py'))
        # These optional sources are compiled only into the temporary runtime
        # overlay when their cached artifacts are absent. Runtime reflection
        # covers available checker imports, never the selected subject modules.
        support_sources = ('.lake/packages/Cli/Cli/Basic.lean',
                           '.lake/packages/importGraph/ImportGraph/Imports/FromSource.lean')
        policy.extend(support_sources)
        policy.extend(('nolints-style.txt', 'scripts/nolints-style.txt'))
        roots = ['Lean', 'Lake']
        for path in (DRIVERS[1], *support_sources):
            if (root / path).is_file():
                roots.extend(lean_imports((root / path).read_text()))
    else:
        # Declaration checks consume compiled subject environments and their
        # local source dependencies; retain the existing native binding there.
        sources, imports = _native_source_graph(root, observations)
        pending, closure = list(names), set()
        while pending:
            name = pending.pop()
            if name in closure:
                continue
            closure.add(name)
            pending.extend(n for n in imports.get(name, ()) if n in sources)
        raw = [str(sources[name].relative_to(root)) for name in closure if name in sources]
        native_names = names
        roots = [*names, 'Lean', 'Lake']
        if (root / DRIVERS[0]).is_file():
            roots.extend(lean_imports((root / DRIVERS[0]).read_text()))
    value = check_binding(root, task['check_kind'], native_names, task['command'], policy,
                          raw_paths=raw, toolchain=toolchain,
                          hash_file=observations.hash_file if observations else file_hash)
    # Retain semantic selection while explicitly leaving style's native subject
    # map empty. Unsupported checker-runtime reflection disables reuse honestly.
    value['modules'] = sorted(set(names))
    value['reflective_imports'] = reflection.closure(roots) if reflection else None
    value['environment_boundary'] = task['environment_boundary']
    return value


class MotivicAdapter:
    def __init__(self, *, full=False, default_branch='', expected_plan=None,
                 skip_static=False, skip_cache=False, export=False, protocol=None):
        self.full, self.default_branch = full, default_branch
        self.expected_plan = expected_plan
        self.skip_static, self.skip_cache, self.export = skip_static, skip_cache, export
        self.protocol = protocol

    local_inputs = staticmethod(local_inputs)
    binding = staticmethod(binding)

    def select_scope(self, root, requested_base=None, targets=(), source_basis=None):
        scope = selection(root, requested_base, targets, full=self.full, default_branch=self.default_branch)
        if self.expected_plan is not None and scope != self.expected_plan:
            raise ValueError('Validation selection changed since this plan; select the current affected scope again')
        return {'scope': scope}

    def validate_local(self, root, plan):
        scope = plan['scope']
        basis = scope['basis']
        expected = selection(root, basis['base'], basis['manual_targets'].split(),
                             full=basis['full'], default_branch=basis['default_branch'])
        if expected != scope:
            raise ValueError('Selected local source scope drifted during validation')
        if scope['targets']:
            if not (Path(root) / '.lake').is_dir():
                raise ValueError('Prepare this checkout\'s ignored .lake directory before shared final checking; '
                                 'absent configuration candidates remain under strict temporal observation')

    def tasks(self, root, plan, phase, directory):
        return recipe(root, plan['scope'], phase, directory, skip_static=self.skip_static,
                      skip_cache=self.skip_cache, export=self.export or phase == 'native')

    def plan(self, root, repository, default_branch, head, requested_base=None, api=None):
        protocol = hosted_protocol(root, head, self.protocol)
        if initial_identity(root, head):
            if requested_base:
                raise ValueError('Initial enrollment cannot accept a historical comparison base')
            baseline = initial_baseline(root, repository, default_branch, head)
        else:
            baseline = admitted_baseline(root, repository, default_branch, head, requested_base,
                                         api=api, protocol=protocol)
        return {'baseline': baseline, 'scope': hosted_scope(root, baseline),
                'tooling_revision': os.environ['MOTIVIC_TOOLING_REVISION']}

    def required_phases(self, root, plan):
        return ['source', 'native'] if plan['scope']['targets'] else ['source']

    def validate_plan(self, root, plan):
        from lean_ci.github import ancestor
        hosted_protocol(root, plan['head'], self.protocol)
        if plan['tooling_revision'] != os.environ.get('MOTIVIC_TOOLING_REVISION'):
            raise ValueError('Independent shared tooling pin drifted')
        baseline, scope = plan['baseline'], plan['scope']
        if baseline.get('kind') == 'initial-enrollment':
            if (baseline != initial_baseline(root, plan['repository'], baseline['default_branch'], plan['head'])
                    or scope != hosted_scope(root, baseline)):
                raise ValueError('Initial enrollment identity or complete local scope drifted')
            return
        if initial_identity(root, plan['head']):
            raise ValueError('The exact initial cutover requires initial-enrollment mode')
        if (baseline['head'] != plan['head'] or baseline['repository'] != plan['repository']
                or not ancestor(root, baseline['base'], baseline['verified_base'])
                or not ancestor(root, baseline['verified_base'], plan['head'])
                or scope != hosted_scope(root, baseline)):
            raise ValueError('CI selection advanced past its accepted complete baseline or drifted')


def admitted_baseline(root, repository, default_branch, head, requested_base=None, *, api=None, protocol=None):
    """Use the existing reviewed evidence interface; no previous-push fallback."""
    from ci_policy import PROTOCOL
    from lean_ci.github import select
    return select(root, repository, default_branch, head, requested_base, api,
                  protocol=protocol or PROTOCOL)


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


def _application(root, package_cwd, **options):
    from lean_ci.engine import Application
    from lean_ci.runtime import NativeRuntime
    runtime = NativeRuntime(package_cwd, resource_config(), runtime_environment())
    return Application(root, MotivicAdapter(**options), runtime, package_cwd=package_cwd)


def create_application(root, **options):
    shared_api()
    return _application(root, root, **options)


def create_native_application(root, package_cwd, source_mapping):
    """Factory for the frozen entry after SOURCE/core/tooling-file admission.

    The common frozen entry verifies the loaded core and exact helper files
    before calling this factory. A transported workspace need not contain Git
    metadata. Ordinary local/CI callers retain create_application's pin guards.
    """
    root, package_cwd = Path(root).resolve(), Path(package_cwd).resolve()
    if root != package_cwd or not isinstance(source_mapping, dict) or source_mapping:
        raise ValueError('Motivic native transport requires root == package_cwd and source_mapping={}')
    return _application(root, package_cwd)


def main():
    if len(sys.argv) > 1 and sys.argv[1] in ('plan', 'source', 'native', 'finalize'):
        # The same Application owns local, frozen and hosted task execution.
        # The common CLI enforces clean committed source and external state.
        sys.dont_write_bytecode = True
        shared_api()
        from lean_ci.cli import main as ci_main
        return ci_main([*sys.argv[1:], '--root', str(ROOT),
                        '--adapter', 'scripts/shared_workflow.py'])
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('operation', choices=['prepare-client'])
    parser.add_argument('--root', type=Path, default=ROOT)
    args = parser.parse_args()
    from build_client import prepare
    prepare(args.root.resolve())
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
