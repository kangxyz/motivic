# Developer tools

Use Python 3.11 or newer from the package root. During proof iteration, compile
the exact changed leaf and handle its diagnostics. Final validation uses the
same native commands as CI and reuses compatible Lake artifacts and individual
command successes. Helper returns, commits and merges do not create a new check
cycle.

## Native final checks

Install the current shared `lean-incremental-ci` distribution or explicitly
select its tooling checkout independently of mathematical dependencies. The
checkout provides `scripts/lean_tools`. Install it with
`python3 -m pip install /path/to/aglib/scripts`, or set the checkout path below:

```sh
export MOTIVIC_TOOLING_ROOT=/absolute/path/to/aglib-tooling
export PYTHONPATH="$MOTIVIC_TOOLING_ROOT/scripts${PYTHONPATH:+:$PYTHONPATH}"
python3 scripts/validate.py --list
python3 scripts/validate.py --base BASE --head HEAD
```

`validate.py` forwards to the installed toolkit's `check` action. The toolkit
selects shared library configuration from the Lake package name.
All source, generation, build, cache and explicit client commands use the
shared operation modules; library differences are data in `lean_tools.library`.
Local scripts forward operation names and arguments. `MOTIVIC_TOOLING_REVISION` does not admit executable
code, and selecting tooling does not alter the mathematical dependency pins.

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
source tokens and accepted mathematical pins. It needs the shared Python toolkit, but no Lean runtime, and does not prove
external imports or mathematical statements. `lean_tools.source` owns the shared
project/client inventory and comment-aware Lean header grammar. `generate_imports.py` owns only existing thematic facades with its
exact generated marker; native `mathlib/mk_all` owns `Motivic.lean`. Test globs
replace generated Test umbrellas. Generated topic entries always contain
`set_option linter.style.longFile 0`, so source growth does not require a new
line allowance. Preserve contributor notices and manually owned files.

## Focused compilation and cache recovery

```sh
python3 scripts/build.py Motivic.Transfers.Cohomology.Basic
python3 scripts/build.py --export-only --outputs /absolute/scratch/modules.jsonl Motivic.Cor
python3 scripts/cache.py --guarded --resolve-deps Motivic.Cor
```

`build.py` forwards semantic module names directly to the common `build` action.
The shared selector renderer rejects already-rendered `+MODULE` names; direct Lake commands use `lake --rehash build +MODULE`. Export-only uses
`--no-build` and fails on missing outputs, without a compile fallback. The shared `lean_tools.cache`
helper follows only reachable Mathlib leaves and has an explicit guarded
bootstrap through `lean-tools run --bootstrap-cache`. Dependency resolution/cache acquisition are setup and recovery work,
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
Python fixtures from the tooling checkout with
`PYTHONPATH=scripts python3 -m unittest discover -s scripts/tests/motivic`.
They exercise thin-entry forwarding, source boundaries, import generation,
focused build/export and explicit client/cache ownership with stand-ins. Shared
native-command failure/reuse checks live in the common tooling package; these
fixtures invoke no full Lean library build and certify no mathematical result.
