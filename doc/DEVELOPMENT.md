# Development

## Environment and dependencies

Run commands from the repository root. `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json` pin Lean, Mathlib and Aglib. Use the elan `lake` selected
by this directory. Do not run `lake update` during ordinary proof work.
`lake resolve-deps` materializes the committed dependency snapshot without
choosing new revisions.

For a selected target, fetch its reachable Mathlib cache and build incrementally:

```sh
lake resolve-deps
python3 scripts/cache.py --guarded --resolve-deps Motivic.KTheory.MilnorK.Basic
python3 scripts/build.py Motivic.KTheory.MilnorK.Basic
```

General Milnor implementation work belongs in the independent Aglib checkout.
The `Motivic.KTheory.MilnorK*` paths are import compatibility leaves; use
Aglib's focused build and cache route when changing the shared theory.


The build wrapper uses Aglib's pinned serial/resource-capped driver with this
repository as the root. Exact commands and CLI options are available with
`--help`. Receipts and writable outputs stay under this checkout's `.lake/`.
Never symlink another checkout's mutable build tree into this one.

Lake native artifact caching is enabled, including restoration of conventional
build files. It preserves compatible work across checkouts; a current rehashed
build decides reuse. The CI workflow uses separately pinned Aglib tooling to
restore compatible public dependency artifacts without changing mathematical
pins. Cache misses fall back to ordinary selected-target builds. On a successful main-branch push, a separate guarded export includes the core
roots and selected changed targets. The canonical shared action stages native
mappings; a separate release job publishes the exact same-run artifact with
repository write permission. Build jobs and pull requests remain read-only.
A configured producer is not a claim that its first remote release succeeded.

## Verification by scope

All normal workflows must use incremental checks, including maintenance, review,
merge, integration and publication. During development, compile changed leaves
and needed affected consumers and handle their diagnostics:

```sh
python3 scripts/build.py Motivic.Transfers.SheafCohomologyWithTransfers
```

Incremental validation covers all applicable categories, not compilation alone:

| Category | Incremental coverage |
|---|---|
| Compilation | Changed modules, genuinely missing required dependencies, and needed affected consumers |
| Lint | Compiler-integrated lint plus applicable declaration and text/style checks for changed modules or files |
| Tests and clients | Affected `MotivicTest` regression/property modules and meaningful public/downstream client tests; affected tooling tests when tools change |
| Source and structure | Affected import/enrollment, layout, pin, option, heartbeat and other source-policy checks |
| Trust boundary | Axiom/input checks whose premises or coverage changed, reusing compatible unchanged evidence |

Keep compiler-integrated checks enabled during development. Run independent
lint and tests only in the task's final validation before delivery, covering its
applicable categories with compatible retained evidence and focused new checks.
A helper return, internal commit or merge does not start that phase. Compilation
covers only the lint or tests it actually runs. After final-check repairs, rerun
only failed or newly affected checks. Unchanged behavior needs no new tests;
documentation-only changes use applicable source/link checks and changed examples.

For a transfer-interface change, a relevant final test is:

```sh
python3 scripts/build.py MotivicTest.OrdinaryCohomologyTransfers
```

This consumer checks actual graph/composition maps, original ordinary group
identity and standard-axiom dependencies. Select `MotivicTest.PublicAPI` or the
independent client below when its public-import interface is affected.

The repository-wide structural diagnostic `python3 scripts/check_repository.py`
verifies names, pins, imports, cycles and forbidden proof placeholders. Select
it for an actual structural question; it is not a per-edit or merge gate and
does not supply kernel validation or request a library build. Report the scope
actually covered by a selected checker.

Build changed leaves and needed affected consumers. Preserve compatible source
and trust evidence and match dependency identities before reuse. Do not delete
caches or rebuild the whole library merely for publication, relocation, a new
receipt, or a changed pin. A missing artifact first calls for a matching cache;
compile genuinely missing required dependencies when no matching cache exists.
Whole-library rebuilding or full dependency replay belongs only to an explicit
request for that exact scope or exceptional recovery from diagnosed incompatible,
corrupt or untrustworthy artifacts in that closure with no usable matching cache.
Keep recovery inside the actual invalidated owned scope. Complete publication
coverage may combine compatible existing evidence and new affected-scope checks;
it does not require reexecuting unchanged checks. Historical successful logs
remain historical; file existence alone is not a stale-source build check.

The normal package targets `Motivic` and `MotivicTest` select curated core and
public consumers. They do not build all retained research leaves. CI declares
its selected targets in `.github/workflows/ci.yml`; manual runs can select a
specific target. A configured workflow is not evidence that it passed.

## Public client

`examples/downstream` is a separate Lake package requiring this repository by
relative path. Its source imports only a public facade and checks an original
mathematical interface. Resolve its committed upstream pins before building.
For a consumer changing to a Git dependency, pin a reviewed repository commit
rather than a moving branch.

## Source and contribution conventions

Use Mathlib style, `module`, precise `public import`, and exposed public
sections for implementation interfaces. Keep `autoImplicit = false`, warning
errors and the standard heartbeat default. A necessary finite local budget
exception belongs to the individual declaration with an explanation; do not
raise the package budget or use unlimited heartbeats.

Use `Authors: kangxyz` for code authored by this project owner. Preserve
concrete original authors and source attribution when adapting external code;
credit other contributors by their actual names. Generic new theory belongs with its
native object and the lowest useful dependency owner. A future upstream
promotion must reconcile candidate dependencies and competing declarations.
See [contribution guidance](../CONTRIBUTING.md).
