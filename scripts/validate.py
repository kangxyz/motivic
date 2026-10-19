#!/usr/bin/env python3
# Authors: kangxyz
"""Run the selected final checks, providers before dependent tests and clients."""
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess
import sys

from ci_targets import arguments, from_arguments
from library_sources import source_modules

ROOT = Path(__file__).resolve().parents[1]


def commands(root: Path, plan: dict, receipts: Path, *, skip_static: bool = False,
             skip_cache: bool = False, outputs: Path | None = None,
             tooling: Path | None = None) -> list[list[str]]:
    """Pure command planning; neither readiness nor export can invoke a compiler."""
    sources = source_modules(root)
    targets, providers, lint = (plan[name] for name in ('targets', 'providers', 'lint'))
    for group in (targets, providers, lint):
        if not isinstance(group, list) or any(name not in sources for name in group):
            raise ValueError('Validation plan requires existing local targets')
    if not set(providers) <= set(targets) or not set(lint) <= set(targets):
        raise ValueError('Provider/lint targets must be selected build targets')
    result = []
    def script(name, *args):
        return [sys.executable, str(ROOT / 'scripts' / name), '--root', str(root), *map(str, args)]
    if not skip_static:
        if plan['structural']:
            result.append(script('check_repository.py'))
        for pattern in plan['tool_tests']:
            result.append([sys.executable, '-m', 'unittest', 'discover', '-s', str(ROOT / 'scripts'), '-p', pattern])
    if not targets and not plan['client']:
        return result
    if targets and not skip_cache:
        result.append(script('cache.py', '--guarded', '--resolve-deps', '--lint-runtime', *targets))
    helper = (tooling or root / '.lake/packages/Aglib') / 'scripts/resource_guard.py'
    def guarded(name, *args):
        return [sys.executable, str(helper), '--capped-toolchain', '--receipt',
                str(receipts / (name + '.json')), '--', *map(str, args)]
    def declaration_lint(names, phase):
        if not names:
            return
        if plan['full']:
            result.append(guarded(phase + '-declarations', 'lake', 'env', 'lean', '--run',
                '.lake/packages/batteries/scripts/runLinter.lean', '--no-build', *names))
        else:
            result.append(guarded(phase + '-declarations',
                *script('lint_declarations.py', '--no-build', *names)))
    if targets:
        # This is explicit tooling preparation, not a readiness probe or proof replay.
        result.append(guarded('declaration-runtime', 'lake', '--rehash', 'build', '+Batteries.Tactic.Lint'))
    if providers:
        result.append(script('build.py', '--receipt-dir', receipts / 'providers', *providers))
        declaration_lint(providers, 'providers')
    if lint:
        # One exact isolated runtime covers all changed-file style checks before consumers.
        result.append(guarded('selected-style', *script('lint_style.py', *lint)))
    consumers = [name for name in targets if name not in providers]
    if consumers:
        result.append(script('build.py', '--receipt-dir', receipts / 'consumers', *consumers))
    # Changed imported environments can invalidate unchanged consumer declarations
    # (for example simpNF); reuse the provider lint already completed above.
    declaration_lint(consumers, 'affected-consumers')
    if plan['client']:
        result.append(script('build_client.py', '--receipt-dir', receipts / 'client'))
    if outputs is not None and targets:
        result.append(script('build.py', '--export-only', '--receipt-dir', receipts / 'export',
                             '--outputs', outputs, *targets))
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    arguments(parser)
    parser.add_argument('--plan', type=Path, help='consume the selector plan for this same source checkout')
    parser.add_argument('--receipt-dir', type=Path)
    parser.add_argument('--outputs', type=Path)
    parser.add_argument('--skip-static', action='store_true', help='reuse same-run static checks, as in CI')
    parser.add_argument('--skip-cache', action='store_true', help='reuse already restored matching caches')
    parser.add_argument('--list', action='store_true', help='print commands without running tools or writing receipts')
    args = parser.parse_args()
    root = args.root.resolve()
    try:
        plan = json.loads(args.plan.read_text()) if args.plan else from_arguments(args)
        if args.plan:
            basis = argparse.Namespace(root=root, **plan['basis'])
            if from_arguments(basis) != plan:
                raise ValueError('Validation selection changed since this plan; select the current affected scope again')
        receipts = args.receipt_dir or Path('.lake/verification') / ('final-' + datetime.now(timezone.utc).strftime('%Y%m%d-%H%M%S-%f'))
        if not receipts.is_absolute():
            receipts = root / receipts
        outputs = args.outputs
        if outputs is not None and not outputs.is_absolute():
            outputs = root / outputs
        tooling = os.environ.get('MOTIVIC_TOOLING_ROOT')
        selected = commands(root, plan, receipts, skip_static=args.skip_static,
                            skip_cache=args.skip_cache, outputs=outputs,
                            tooling=Path(tooling) if tooling else None)
        for argv in selected:
            print(json.dumps(argv), flush=True)
            if not args.list:
                receipts.mkdir(parents=True, exist_ok=True)
                code = subprocess.run(argv, cwd=root).returncode
                if code:
                    return code
        return 0
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as error:
        print(f'Selected validation failed: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
