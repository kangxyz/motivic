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

from ci_targets import CONFIG_INPUTS, ROOT, from_arguments, graph
from library_sources import lean_imports, source_modules

POLICY = ('scripts/shared_workflow.py', 'scripts/validate.py', 'scripts/ci_targets.py',
          'scripts/library_sources.py', 'scripts/check_repository.py',
          'scripts/lint_declarations.py', 'scripts/lint_style.py',
          'scripts/build_client.py', 'scripts/cache.py', 'scripts/cache_bootstrap.py',
          '.github/dependency-scope.json')
DRIVERS = ('.lake/packages/batteries/scripts/runLinter.lean',
           '.lake/packages/mathlib/scripts/lint-style.lean')
CLIENT = 'examples/downstream'
GENERATED_MANIFEST = CLIENT + '/lake-manifest.json'
# No inspected hosted witness closes the current unfinished Motivic upgrade.
# The owner may admit an actual scoped/transitive coverage witness here after
# mathematical delivery, using the shared EvidenceProtocol and exact attempts.
BASELINE_PROTOCOL = None
LEGACY_ATTEMPTS = frozenset()  # (source SHA, run id, attempt), when required by review


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
    if not paths or not (package / 'recipe.py').is_file() or not (package / 'local.py').is_file():
        raise ValueError('Pinned tooling lacks the shared local-check/recipe API; adopt the reviewed common tooling commit')
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
                  'scripts', '.github', '.github/workflows', CLIENT,
                  CLIENT + '/lakefile.toml', CLIENT + '/lakefile.lean', CLIENT + '/lean-toolchain'))
    for directory in ('Motivic', 'MotivicTest', 'scripts', '.github', CLIENT):
        base = root / directory
        for path in base.rglob('*'):
            relative = path.relative_to(root)
            if '.lake' in relative.parts or '__pycache__' in relative.parts:
                continue
            if path.is_dir() or path.suffix in {'.lean', '.py', '.sh', '.yml', '.yaml', '.json'}:
                # The inherited ignored client manifest is established by setup.
                if relative.as_posix() != GENERATED_MANIFEST:
                    paths.add(relative.as_posix())
    return [({'path': path, 'exclude': ['.lake', '__pycache__']} if (root / path).is_dir() else path)
            for path in sorted(paths)]


def selection(root, requested_base=None, targets=(), *, full=False, default_branch=''):
    args = argparse.Namespace(root=Path(root), event='local', base=requested_base or '',
                              head='HEAD', default_branch=default_branch, full=full,
                              manual_targets=' '.join(targets))
    return from_arguments(args)


def checked_scope(root, scope):
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
    command = (['lake', 'env', 'lean', '--run', DRIVERS[0], '--no-build', *names] if full else
               [sys.executable, str(root / 'scripts/lint_declarations.py'), '--root', str(root), '--no-build', *names])
    return [dict(id=label + '/declarations', kind='check', command=command,
                 check_kind='declaration-native-package' if full else 'declaration-exact-origin',
                 modules=names, capped=True,
                 environment_boundary={'mode': 'separate-import-environment-per-origin', 'origins': names,
                     'declarations': 'native-package-prefix' if full else 'exact-defining-origin'})]


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
    clients = []
    if scope['client']:
        clients.append(dict(id='client', cwd=CLIENT, modules=['MotivicClient'], before=[task(
            'prepare/client', [sys.executable, root / 'scripts/shared_workflow.py', 'prepare-client', '--root', root],
            cwd=str(root), establishes_inputs=True, established_paths=[GENERATED_MANIFEST])]))
    exports = ([name for name, modules in (('providers', providers), ('consumers', consumers)) if modules]
               if export else [])
    return native_recipe(root, directory, source_checks=static, prepare=prepare,
                         provider_gate=provider, root_workspace=workspace, clients=clients,
                         exports=exports, phase=phase)


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
        sources, imports = graph(root)
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
        if scope['targets'] or scope['client']:
            if not (Path(root) / '.lake').is_dir():
                raise ValueError('Prepare this checkout\'s ignored .lake directory before shared final checking; '
                                 'absent configuration candidates remain under strict temporal observation')
        if scope['client'] and (not (Path(root) / CLIENT / '.lake').is_dir()
                                or not (Path(root) / GENERATED_MANIFEST).is_file()):
            raise ValueError('Prepare the ignored client directories/manifest before shared final checking: '
                             'python3 scripts/shared_workflow.py prepare-client')

    def tasks(self, root, plan, phase, directory):
        return recipe(root, plan['scope'], phase, directory, skip_static=self.skip_static,
                      skip_cache=self.skip_cache, export=self.export or phase == 'native')

    def plan(self, root, repository, default_branch, head, requested_base=None, api=None):
        baseline = admitted_baseline(root, repository, default_branch, head, requested_base,
                                     api=api, protocol=self.protocol)
        scope = selection(root, baseline['base'], full=self.full, default_branch=default_branch)
        return {'baseline': baseline, 'scope': scope}

    def required_phases(self, root, plan):
        return ['source', 'native'] if plan['scope']['targets'] or plan['scope']['client'] else ['source']

    def validate_plan(self, root, plan):
        from lean_ci.github import ancestor
        baseline, scope = plan['baseline'], plan['scope']
        if (baseline['head'] != plan['head'] or baseline['repository'] != plan['repository']
                or not ancestor(root, baseline['base'], baseline['verified_base'])
                or not ancestor(root, baseline['verified_base'], plan['head'])
                or scope != selection(root, baseline['base'], full=self.full,
                                      default_branch=baseline['default_branch'])):
            raise ValueError('CI selection advanced past its accepted complete baseline or drifted')


def admitted_baseline(root, repository, default_branch, head, requested_base=None, *, api=None, protocol=None):
    """Use the existing reviewed evidence interface; no previous-push fallback."""
    from lean_ci.github import BaselineError, GitHubAPI, select
    protocol = protocol or BASELINE_PROTOCOL
    if protocol is None:
        raise BaselineError('Motivic shared CI cutover has no admitted native baseline covering the '
            'unfinished upgrade. Recover an owner-reviewed hosted witness and configure the existing '
            'EvidenceProtocol. Two-facade smoke, excluded optional failures and root/test-only bootstrap '
            'runs do not close that range; event.before is not a fallback.')
    actual_api = api or GitHubAPI(repository)
    class AdmittedRuns:
        def get(self, *args, **kwargs):
            return actual_api.get(*args, **kwargs)
        def pages(self, path, key, **query):
            for run in actual_api.pages(path, key, **query):
                if (key == 'workflow_runs' and LEGACY_ATTEMPTS
                        and run.get('head_sha') in (protocol.legacy_heads or ())
                        and (run.get('head_sha'), run.get('id'), run.get('run_attempt')) not in LEGACY_ATTEMPTS):
                    continue
                yield run
    return select(root, repository, default_branch, head, requested_base, AdmittedRuns(), protocol=protocol)


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
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('operation', choices=['prepare-client'])
    parser.add_argument('--root', type=Path, default=ROOT)
    args = parser.parse_args()
    from build_client import prepare
    prepare(args.root.resolve())
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
