#!/usr/bin/env python3
# Authors: kangxyz
"""Adapt published Aglib's isolated pinned style runtime to explicit local targets.

Runtime mechanics reuse scripts/run_style_linter.py at published Aglib revision
c9863095f90b8bd312af807dbf0e378df82403b5 (Apache-2.0). No Aglib source is edited.
"""
import argparse
import importlib.util
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from library_sources import module_path, source_modules

ROOT = Path(__file__).resolve().parents[1]
DRIVER_SHA256 = 'dbee84c9deac55f83df09beb99eed61bb2df049ca7c3e7e485419902c7a19396'
IMPORT_ENUMERATION = '''  -- Get all the imports, but only those in the same package.
  let pkgs := originModules.map (·.components.head!)
  Lean.initSearchPath (← Lean.findSysroot)
  let searchPath ← Lean.getSrcSearchPath
  let allModuleNames ← originModules.flatMapM fun mod => do
    let some file ← searchPath.findWithExt "lean" mod
      | throw <| IO.userError s!"could not find module with name {mod}"
    let imports := (← file.parseImports').filterInit.imports.map (·.module)
    pure <| imports.filter (·.components.head! ∈ pkgs)
'''
EXACT_ENUMERATION = '''  -- The adapter's explicit arguments are the exact selected source files.
  Lean.initSearchPath (← Lean.findSysroot)
  let allModuleNames := originModules
'''


def adapt_driver(source: bytes) -> str:
    """Change only pinned source enumeration; retain every enabled native check."""
    if hashlib.sha256(source).hexdigest() != DRIVER_SHA256:
        raise ValueError('Mathlib style driver differs from the reviewed pinned source; review its selection interface')
    text = source.decode('utf-8')
    if text.count(IMPORT_ENUMERATION) != 1:
        raise ValueError('Expected exactly one pinned style-source enumeration')
    return text.replace(IMPORT_ENUMERATION, EXACT_ENUMERATION)


def runtime(tooling: Path):
    path = tooling / 'scripts/run_style_linter.py'
    spec = importlib.util.spec_from_file_location('motivic_pinned_style_runtime', path)
    if spec is None or spec.loader is None:
        raise ValueError(f'Missing published style runtime: {path}')
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    return helper


def run(root: Path, targets: list[str], helper) -> int:
    environment = helper.lake_environment(root)
    located_lean = environment.pop('lean')
    # The published helper's locator may see Lake's real bin before the guard.
    lean = os.environ.get('LEAN') or located_lean
    prefix = subprocess.run([lean, '--print-prefix'], cwd=root, capture_output=True,
                            text=True, check=True).stdout.strip()
    plan = helper.plan_runtime(root, Path(prefix))
    if plan['missing_prerequisites']:
        raise ValueError('Missing cached style-runtime prerequisites: ' + ', '.join(plan['missing_prerequisites']))
    adapted = adapt_driver(Path(plan['driver']).read_bytes())
    with tempfile.TemporaryDirectory(prefix='motivic-style-runtime-') as directory:
        overlay = Path(directory)
        helper.seed_cached_namespaces(overlay, plan)
        env = dict(os.environ, **environment)
        env['LEAN_PATH'] = str(overlay) + os.pathsep + environment['LEAN_PATH']
        for entry in plan['isolated_compile_modules']:
            relative = module_path(entry['module'])
            output = overlay / relative.with_suffix('.olean')
            if output.exists() or output.is_symlink():
                raise ValueError('Optional output would overwrite a cached artifact: ' + str(output))
            output.parent.mkdir(parents=True, exist_ok=True)
            code = subprocess.run([lean, '-o', str(output), relative.as_posix()],
                                  cwd=entry['package_root'], env=env).returncode
            if code:
                return code
        driver = overlay / 'MotivicStyleDriver.lean'
        driver.write_text(adapted)
        code = subprocess.run([lean, '-o', str(driver.with_suffix('.olean')), driver.name],
                              cwd=overlay, env=env).returncode
        if code:
            return code
        shim = overlay / 'RunStyle.lean'
        shim.write_text('import MotivicStyleDriver\n')
        return subprocess.run([lean, '--load-dynlib', plan['lake_shared_library'],
                               '--run', str(shim), *dict.fromkeys(targets)],
                              cwd=root, env=env).returncode



def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--check-prerequisites', action='store_true')
    parser.add_argument('--sysroot', type=Path)
    parser.add_argument('targets', nargs='*')
    args = parser.parse_args()
    root = args.root.resolve()
    try:
        helper = runtime(Path(os.environ.get('MOTIVIC_TOOLING_ROOT', root / '.lake/packages/Aglib')))
        if args.check_prerequisites:
            if args.sysroot is None:
                parser.error('--check-prerequisites requires --sysroot')
            plan = helper.plan_runtime(root, args.sysroot)
            print(json.dumps(plan, indent=2))
            return int(bool(plan['missing_prerequisites']))
        if args.sysroot is not None:
            parser.error('--sysroot is only used with --check-prerequisites')
        sources = source_modules(root)
        if not args.targets or any(name not in sources for name in args.targets):
            raise ValueError('Style checks require explicit existing local module targets')
        return run(root, args.targets, helper)
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        print(f'Focused style check failed: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
