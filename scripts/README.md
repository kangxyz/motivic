# Developer tools

Use Python 3.11 or newer from the package root. During proof iteration, compile
the exact changed leaf and handle its diagnostics. Final validation uses the
same native commands as CI and reuses compatible Lake artifacts and individual
command successes. Helper returns, commits and merges do not create a new check
cycle.

## Native final checks

Install the current shared `lean-incremental-ci` distribution or explicitly
select its tooling checkout independently of mathematical dependencies. The
checkout provides `scripts/lean_ci`. Install it with
`python3 -m pip install /path/to/aglib/scripts`, or set the checkout path below:

```sh
export MOTIVIC_TOOLING_ROOT=/absolute/path/to/aglib-tooling
export PYTHONPATH="$MOTIVIC_TOOLING_ROOT/scripts${PYTHONPATH:+:$PYTHONPATH}"
python3 scripts/validate.py --list
python3 scripts/validate.py --base BASE --head HEAD
```

`validate.py` forwards to `lean_ci.cli.main(['check', ...], root=PACKAGE,
production=('Motivic',), source_checks=...)`. `shared_workflow.py` retains only
installed/explicit tooling loading and existing resource/environment overrides;
it has no plan, phase, recipe, scheduler, source-hash allowlist or hosted API.
`MOTIVIC_TOOLING_REVISION` is not an executable-admission mechanism. Existing
older installed versions are not modified by a source migration.

Options belong to the shared CLI: `--root PACKAGE`, repeatable `--production
ROOT` and optional `--check-target TARGET`, `--base`, `--head`, `--full`,
`--source-only`, `--progress DIR`, `--state`/`--receipt-dir DIR`, `--outputs PATH`
and `--list`. A selected committed head must be checked out. Nonempty docs-only
differences request source checks without Lean; clean/no-change invocations run
native final checks. `--full` uses the same incremental native commands and does
not force rebuilding or add replay/client/audit layers. `--list` does not execute.
Use external state/progress/output paths.

The native sequence builds production with rehashing, prepares checker tools,
builds/tests `MotivicTest.+` through `lake test`, checks generated production
entries, runs Mathlib text style and native lint, and invokes the pinned upstream
production axiom auditor. Pass production roots explicitly. Native lint's module
arguments select builtin lint; the configured Batteries driver retains its
package declaration predicate. Mathlib text style checks the root's imported
sources. No checker source is patched or injected. The auditor loads production
module origins including private/generated declarations and checks their axiom
closure; it does not replay proofs or establish source correspondence.

Command reuse depends on actual source/native/checker bytes and the toolchain;
failed/partial or changed inputs cannot supply success. Native mappings from
`--outputs` are compilation/recovery data and are delivered without an export
build. They do not by themselves record lint or audit coverage.

## Source and import tools

`python3 scripts/check_repository.py` checks local imports/cycles, generated
thematic facades, production/test/client separation, reusable-candidate closure,
source tokens and accepted mathematical pins. It needs neither Lean nor shared
tooling, and does not prove external imports or mathematical statements.
`library_sources.py` retains its comment-aware parser and occupied source
inventory, adapted from Aglib `c9863095f90b8bd312af807dbf0e378df82403b5`,
Apache-2.0. `generate_imports.py` owns only existing thematic facades with its
exact generated marker; native `mathlib/mk_all` owns `Motivic.lean`. Test globs
replace generated Test umbrellas. Preserve contributor notices and manually
owned files.

## Focused compilation and cache recovery

```sh
python3 scripts/build.py Motivic.Transfers.Cohomology.Basic
python3 scripts/build.py --export-only --outputs /absolute/scratch/modules.jsonl Motivic.Cor
python3 scripts/cache.py --guarded --resolve-deps Motivic.Cor
```

`build.py` forwards semantic module names through `build_modules.py` to the
shared `lean_ci.build` API. Already-rendered `+MODULE` names are rejected by that
wrapper; direct Lake commands use `lake --rehash build +MODULE`. Export-only uses
`--no-build` and fails on missing outputs, without a compile fallback. The cache
helper follows only reachable Mathlib leaves and has an explicit guarded
bootstrap. Dependency resolution/cache acquisition are setup and recovery work,
not automatic preliminaries to a prepared proof loop. Mathematical pins remain
unchanged.

`MOTIVIC_BUILD_THREADS`, `MOTIVIC_LEAN_MEMORY_MB` and `MOTIVIC_RSS_LIMIT_MB` retain
precedence over Aglib aliases. Existing `R5_LEAN_REMOTE_PROFILE`/
`AGLIB_REMOTE_PROFILE` wrappers and their process/resource limits pass through
unchanged. No ordinary command creates another executor or a client acceptance
stage.

## Explicit client diagnostic and Python fixtures

`python3 scripts/build_client.py` is only for a specifically requested independent
client check. It inherits locked dependency metadata, shares this checkout's
package directory and keeps client outputs owned in its own `.lake/build`.
Routine validation does not call it. See the existing client README.

With the selected shared package on `PYTHONPATH`, run the existing bounded
Python fixtures with `python3 -m unittest discover -s scripts -p 'test_*.py'`.
They exercise thin-entry forwarding, source boundaries, import generation,
focused build/export and explicit client/cache ownership with stand-ins. Shared
native-command failure/reuse checks live in the common tooling package; these
fixtures invoke no full Lean library build and certify no mathematical result.
