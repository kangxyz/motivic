# Development

## Normal task

In a prepared checkout, keep a coherent proof and its compiler repair with one
author. Compile the changed leaf or actual interface consumer:

```sh
lake build +Motivic.Transfers.Cohomology.Basic
```

Keep compiler-integrated checks enabled. At the task's final validation, compare
with its starting revision through the common CLI:

```sh
python3 -m lean_ci check --config .github/lean-ci.toml --root . \
  --requested-base BASE --progress /absolute/scratch/motivic-check-progress
```

Use the independently pinned tooling core selected by the reusable workflow;
the [script guide](../scripts/README.md#common-ci) owns setup and phase commands.
Successful individual checks remain reusable after later failures when their
actual inputs still match. Compile a repaired Test directly with
`lake build +MotivicTest.OrdinaryCohomologyTransfers`, then check its affected
obligations. A helper return, internal commit or merge does not start a new
final-validation phase.

A prepared proof loop does not start by resolving dependencies, fetching caches,
extracting inventories or updating documentation. Select those operations only
for an actual missing input or changed interface.

## Environment and dependencies

Run commands from the repository root. `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json` pin Lean, Mathlib and Aglib. Use the elan `lake` selected
by this directory. Do not run `lake update` during ordinary proof work.
`lake resolve-deps` materializes the committed snapshot without choosing new
revisions. The common native phase prepares the selected dependency/cache and
checker-runtime inputs with common resource guards. For a missing setup input:

```sh
python3 -m lean_ci prepare --config .github/lean-ci.toml --root . \
  --requested-base BASE --target Motivic.Transfers.Cohomology.Basic
```

Recover compatible artifacts before compiling genuinely missing dependencies; never link another
checkout's mutable build tree.

General Milnor implementation work belongs in the independent Aglib checkout.
The public `Motivic.KTheory.MilnorK` and `.Norms` entries are import bridges;
change shared theory through Aglib's own focused route.

The reusable workflow pins its compatible tooling core independently of the
mathematical Aglib pin. Native artifacts and individual progress survive failed
runs. Cache misses permit selected-target builds; changed tooling, publication,
relocation or a missing receipt does not justify a clean rebuild.

## Verification by scope

All normal maintenance, review, integration and publication use incremental
checks. Compilation covers changed modules, missing required dependencies and
actual affected consumers. Source-style selection follows changed files or its
checker policy. Declaration, builtin and trust checks cover their selected
origins under fixed checker inputs. Positive Tests are elaborated as selected
Lake modules; the independent client is built in its own package.

The shared selector includes optional leaves outside the curated facades and
uses both old and new import edges for deletions or renames. Exact package paths
and roles are data in `.github/lean-ci.toml`; the library supplies no adapter,
callback or alternate check loop. Selected providers and their checks precede
affected consumers, Tests and client. Keep all applicable mandatory categories.
Independent lint and tests belong to final validation; after repairs rerun only
failed or newly affected obligations and retain matching successes.

For an exact final-check scope:

```sh
python3 -m lean_ci check --config .github/lean-ci.toml --root . \
  --target MotivicTest.OrdinaryCohomologyTransfers \
  --progress /absolute/scratch/motivic-check-progress
```

This Test checks graph/composition maps, ordinary group identity and standard
axiom dependencies. Select `MotivicTest.PublicAPI` or the independent client
when its interface is affected. Source token checks and declaration lint do not
replace an independent transitive axiom audit or kernel replay. Preserve
incremental LeanChecker for an explicitly assigned formal acceptance milestone.

The common phase API is `plan`, `source`, `native`, `finalize`, local `check`, and scoped `prepare`.
Source/preflight is independent of a long native execution. Finalization checks
required/reused coverage and exports the already selected artifacts without
recompiling them. An incomplete run saves matching individual progress but
cannot become a complete verified baseline or qualified public cache.

Initialization reconciles the current obligation universe with compatible
inherited coverage and per-check successes. Uncovered obligations remain pending
across repairs; no parent-commit whitelist or prior-push reset defines coverage.
A new canonical declaration-lint predicate is checked afresh where no compatible
result exists. Existing compilation artifacts may still be reused by Lake.
Configuration alone does not claim completed native initialization.

The normal `Motivic` and `MotivicTest` entries remain curated. Ordinary proof
iteration uses `lake build +MODULE`, never an unqualified library build merely
to prepare lint. Whole-library rebuild/replay requires an explicit request for
that scope or diagnosed untrustworthy artifacts without matching usable cache.
Historical logs retain their identified source and input basis.

## Public client

`examples/downstream` is a separate Lake package requiring this repository by
relative path. Its `Motivic` import checks the public correspondence category
and canonical Milnor degree-zero equivalence. Common CI prepares its locked
inherited dependencies and keeps its build outputs in the client's own
`.lake/build`. Client source/configuration changes and affected imports select
the client after provider checks. Its failure blocks qualified publication.

To select its library interface explicitly:

```sh
python3 -m lean_ci check --config .github/lean-ci.toml --root . \
  --target Motivic --progress /absolute/scratch/motivic-check-progress
```

Publication reuses the checked selected outputs. For distribution, replace the
relative dependency with the repository URL and an exact reviewed commit.

## Source and contribution conventions

Use Mathlib style, `module`, precise `public import`, and exposed public
sections for implementation interfaces. Keep `autoImplicit = false`, warning
errors and the standard heartbeat default. A necessary finite local budget
exception belongs to the individual declaration with an explanation; do not
raise the package budget or use unlimited heartbeats.

Use `Authors: kangxyz` for code authored by this project owner. Preserve
concrete original authors and source attribution when adapting external code;
credit other contributors by their actual names. Generic new theory intended for Aglib belongs in `Motivic/Aglib/`, mirroring
the intended upstream subject and using native declaration namespaces. Its
dependency closure contains only Mathlib, Aglib and designated general
candidates. Record the intended upstream module, exact hypotheses and current
consumer in each candidate module; update the occupied family guide. Keep
motivic applications and adapters outside the candidate tree. General curve,
line-bundle, frame and pencil theorems with full general interfaces remain
candidates. Before admission, search both pinned dependencies and local
candidates for the actual object and map.

Candidates are ordinary production modules under the same enrollment, lint,
axiom and incremental-build rules. They are maintained proofs, not scratch or
claims of upstream acceptance. Resolve a host dependency by extracting its
general prerequisite first; do not waive the closure rule because a module
already compiles. Coordinate one implementation owner across downstream
libraries. When an accepted upstream revision is pinned, retarget consumers
and remove the local implementation in the same change, preserving native
names and avoiding duplicate copies or default compatibility facades. Follow
the [shared candidate policy](https://github.com/kangxyz/aglib/blob/main/docs/DEVELOPMENT.md#downstream-candidates-for-aglib).
See [contribution guidance](../CONTRIBUTING.md).

## Documentation ownership

Keep central `docs/` pages as concise summaries, indexes and package-wide
conventions. Mathematical definitions, complete hypotheses, universes, signs,
API examples and remaining theorem inputs belong in the owning source-family
README or an existing child document. Update that owner and its central link
when the interface changes; avoid duplicating detailed mathematical prose.
