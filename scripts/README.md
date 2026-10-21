# Focused developer tools

Use Python 3.11 or newer. Ordinary proof iteration uses scoped Lake module
builds and their configured diagnostics:

```sh
lake build +Motivic.Transfers.Cohomology.Basic
```

## Common CI

`.github/lean-ci.toml` declares this package's production and positive Test
libraries and the independent `examples/downstream` client. Historical Lean
snapshots in `docs/provenance` are declared reference material; they are not
current executable sources. The exact dependency transition assessment remains
in `.github/dependency-scope.json` as common policy data. The pinned reusable
workflow in `.github/workflows/ci.yml` supplies the common `lean_ci` CLI,
mandatory checks, execution, resource guards, cache transport and progress.
The tooling revision is independent of the mathematical Aglib dependency pin.
Select the tooling core pinned by that workflow for local execution, installing
its `ci/` package in the active Python environment. Do not load tooling from the
mathematical dependency checkout merely because its package name is Aglib.

At final validation, use a starting revision or exact selected module:

```sh
python3 -m lean_ci check --config .github/lean-ci.toml --root . \
  --requested-base BASE --progress /absolute/scratch/motivic-check-progress
python3 -m lean_ci check --config .github/lean-ci.toml --root . \
  --target Motivic.Transfers.Cohomology.Basic \
  --progress /absolute/scratch/motivic-check-progress
```

For missing native setup inputs, prepare only the selected scope:

```sh
python3 -m lean_ci prepare --config .github/lean-ci.toml --root . \
  --requested-base BASE --target Motivic.Transfers.Cohomology.Basic
```

`check` runs the selected source, provider, declaration, consumer, Test and client
obligations. For committed hosted phases, the same CLI exposes `plan`, `source`,
`native` and `finalize` with `--state`; `plan` also requires `--repository`
and an exact `--head`. Scoped `prepare` uses the same configuration and selection. `--outputs` requests checked native mappings. Finalization
aggregates completed coverage and exports selected artifacts without another
build. Use `python3 -m lean_ci --help` for phase arguments.

The common selector includes changed/deleted origins and consumers reached in
the old/new import graphs, with separate source-style scope. A changed Test
uses its actual production prerequisites. The independent client is selected
when its own inputs or reachable library inputs change. Common tooling changes receive tiny native runtime fixtures in the shared
package, without requesting a cold consumer facade graph or broad library build. Documentation-only changes do not request unrelated compilation.

Source checks cover local imports, cycles, production/Test/client isolation,
placeholder/unsafe tokens, layout, finite budgets and generated-facade enrollment.
`Motivic.Aglib` candidates can depend on external libraries and other candidates;
they cannot import ordinary `Motivic` host modules. These checks do not establish
external mathematical correctness or independent kernel certification.

Source style uses the pinned isolated runtime and selected source files; the
subject modules need no oleans merely to check their source text. Declaration
lint uses one canonical defining-origin environment per origin, with the common
runtime imported before the subject. Additional batch origins do not change
that environment. Compiled artifacts alone do not count as passed lint checks.

Matching per-origin/check progress survives later failures and repairs. A
missing verified baseline leaves the current uncovered obligation universe
pending; no per-commit enrollment whitelist is maintained. Partial completion
cannot publish a complete native baseline. Reuse compatible source/build/check
evidence and rerun only changed or failed obligations. No helper return, commit,
merge or new receipt starts another final-validation cycle.

The reusable workflow supplies runner resource limits and honors admitted
local/remote resource profiles; never enlarge a mathematical heartbeat
allowance to solve a runtime resource problem. Required library/Test checks and
client checks precede qualified publication. Pull requests cannot publish a
trusted producer cache.

## Mathematical source maintenance

Facade authoring uses the same shared implementation and declarative source
policy as CI:

```sh
python3 -m lean_ci imports --config .github/lean-ci.toml --root . --check
python3 -m lean_ci imports --config .github/lean-ci.toml --root . --write
```

Only exact leading ownership markers enroll existing topic facades. Curated
`Motivic.lean` and `MotivicTest.lean`, unmarked manual sources and absent facades
retain their owners. The historical marker spelling is preserved; it does not
require a local script. Common fixtures cover sorted descendants, headers,
manual ownership, prospective cycles and source/policy/HEAD drift. All proposed
products are checked before guarded atomic file replacement. Standard source
parsing and maintenance helpers are distributed once with `lean_ci`.
