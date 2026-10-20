# Development

## Normal task

In a prepared checkout, keep a coherent proof and its compiler repair with one
author. Compile the changed leaf or actual interface consumer:

```sh
python3 scripts/build.py Motivic.Transfers.Cohomology.Basic
```

At the task's final validation, run the selected provider/lint/consumer checks
once, comparing with its starting revision (omit `--head` for working changes):

```sh
python3 scripts/validate.py --base BASE
```

Final checks use the independently pinned shared `lean_ci` recipe and executor.
Set `MOTIVIC_TOOLING_ROOT` and its exact reviewed `MOTIVIC_TOOLING_REVISION`; the
[script guide](../scripts/README.md) owns tooling admission and command details.
Use an external `--progress` directory to retain compatible individual checks
across final-check attempts. After a late failure, repair the failed category
and retain compatible earlier results. For example, a repaired test can be compiled directly
with `python3 scripts/build.py MotivicTest.OrdinaryCohomologyTransfers`; finish
that changed source's applicable lint without restarting unchanged provider
checks. The [script guide](../scripts/README.md) owns direct lint/client commands.
Source/option changes still invalidate their actual dependent coverage.

Use the environment/cache reference below only for a missing dependency or a
changed setup. A prepared proof loop does not start by resolving dependencies,
fetching caches, extracting inventories or updating documentation. Documentation
and tooling work select their own affected checks under [verification](#verification-by-scope).

## Environment and dependencies

Run commands from the repository root. `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json` pin Lean, Mathlib and Aglib. Use the elan `lake` selected
by this directory. Do not run `lake update` during ordinary proof work.
`lake resolve-deps` materializes the committed dependency snapshot without
choosing new revisions.

For a selected target, fetch its reachable Mathlib cache and build incrementally:

```sh
lake resolve-deps
python3 scripts/cache.py --guarded --resolve-deps Motivic.Cor
python3 scripts/build.py Motivic.Cor
```

General Milnor implementation work belongs in the independent Aglib checkout.
The two public `Motivic.KTheory.MilnorK` and `.Norms` entries are import bridges; use
Aglib's focused build and cache route when changing the shared theory.


The build wrapper uses the independently pinned shared resource-capped build
helper with bare module names and explicit Lake module selection. Exact commands and CLI options are available with
`--help`. Direct-build receipts may stay under this checkout's `.lake/`; shared final-check
state, progress and delivered mappings use external directories.
Never symlink another checkout's mutable build tree into this one.

Lake native artifact caching is enabled, including restoration of conventional
build files. It preserves compatible work across checkouts; a current rehashed
build decides reuse. The CI workflow uses separately pinned Aglib tooling to
restore compatible public dependency artifacts without changing mathematical
pins. Cache misses permit only ordinary selected-target builds. The hosted cutover remains pending a reviewed common tooling commit and native
baseline covering the unfinished upgrade. In the shared candidate, mapping
export reuses the original selected build outputs after all checks succeed.
A missing export artifact fails delivery without compiling an extra closure. The canonical shared action stages native
mappings; a separate release job publishes the exact same-run artifact with
repository write permission. Build jobs and pull requests remain read-only.
A configured producer is not a claim that its first remote release succeeded.

## Verification by scope

All normal workflows must use incremental checks, including maintenance, review,
merge, integration and publication. During development, compile changed leaves
and needed affected consumers and handle their diagnostics:

```sh
python3 scripts/build.py Motivic.Transfers.Cohomology.Basic
```

Incremental validation covers all applicable categories, not compilation alone:

| Category | Incremental coverage |
|---|---|
| Compilation | Changed modules, genuinely missing required dependencies, and needed affected consumers |
| Lint | Compiler-integrated lint, declaration checks for affected defining origins, and text/style checks for selected source files |
| Tests and clients | Affected `MotivicTest` regression/property modules and meaningful public/downstream client tests; affected tooling tests when tools change |
| Source and structure | Affected import/enrollment, layout, pin, option, heartbeat and other source-policy checks |
| Trust boundary | Axiom/input checks whose premises or coverage changed, reusing compatible unchanged evidence |

Keep compiler-integrated checks enabled during development. Run independent
lint and tests only in the task's final validation before delivery, covering its
applicable categories with compatible retained evidence and focused new checks.
A helper return, internal commit or merge does not start that phase. Compilation
covers only the lint or tests it actually runs. After final-check repairs, rerun
only failed or newly affected checks. Unchanged behavior needs no new tests;
documentation-only changes use static source/link checks and changed examples.

For the final phase, the shared adapter uses the existing affected-scope selector:

```sh
python3 scripts/validate.py --base BASE --head HEAD --list
python3 scripts/validate.py --base BASE --head HEAD
```

Use a comparison identifying the current checkout; staged, unstaged and
untracked edits are included. Alternatively pass explicit `--manual-targets`
(existing local modules); `--full` is an opt-in diagnostic over all occupied
modules. Local missing bases use a trusted fetched default-branch merge-base or a true
initial root diff; unresolvable bases fail actionably. Shared committed CI uses
the reviewed `EvidenceProtocol` and cannot fall back to `event.before` or a
previous push. There is no admitted historical complete native Motivic baseline.
The one-time cutover is explicit: only a commit with exactly one parent,
`33af37716ce796f9863dbc33a5b9bfbb2cfab7d6`, and a nonempty diff confined to the
enumerated CI-owned paths in `scripts/shared_workflow.py` may use
`initial-enrollment`. That plan has no historical `verified_base`; it enrolls
every local production module, every local test (including orphan leaves outside
the facades), and the existing independent client. Production providers precede
the remaining tests and client, retaining the ordinary exact-origin declaration
and selected-source style predicates. All tooling fixtures run at enrollment.
Only the successful native phase plus finalization can supply the first future
baseline. Every later head requires a genuinely verified native ancestor;
missing or skipped native/finalizer evidence cannot trigger enrollment.
Pin changes and manual dispatch have no full fallback.
Pin changes require explicit affected scope and matching caches. An Aglib upgrade
can commit the reviewed configuration hashes and local seeds in
`.github/dependency-scope.json`; the [script guide](../scripts/README.md) defines
the checked format used by automatic CI. Documentation-only changes run static
checks without installing Lean. Execution-script and CI-workflow changes run affected
tooling fixtures and, when no native scope is already selected, compile and
declaration/style-lint the exact curated `Motivic` and `MotivicTest` facade
modules and check the independent client. This smoke uses module selectors,
without whole-library expansion or unchanged test-prerequisite expansion.
Existing Lean, pin-upgrade and manual native scopes remain exact; tool changes
do not add extra roots to those selections. Pure Python fixture changes retain
their affected fixture checks without native smoke.
The final route compiles and declaration/style-lints providers before expensive
affected consumers, tests and clients. It also declaration-lints the remaining
affected origins after their builds; text/style selection has its own narrower
file scope. Test-only edits retain their direct
production prerequisite checks. Linter runtime setup selects only its actual tooling prerequisites, with
separate guarded receipts; missing remaining prerequisites fail closed.
Before native final checking, prepare ignored root `.lake` inputs and, for a
selected client, run `python3 scripts/shared_workflow.py prepare-client`. This
precedes the source snapshot and preserves strict absent-config observations.
Batteries declaration checks still use separate environments per origin; no
union-environment batch or equivalence is claimed. See
[tool commands](../scripts/README.md) for source boundaries and scoped export.

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
public consumers. They do not build all retained research leaves. CI uses the affected import graph; required roots remain selected when actually
changed or reached as consumers. Manual runs require a Git base, explicit
targets, or the explicit full diagnostic. A configured workflow is not evidence that it passed.

## Public client

`examples/downstream` is a separate Lake package requiring this repository by
relative path. Its `Motivic` import checks the public correspondence category
and the canonical Milnor degree-zero equivalence. After the guarded public
build, compile the independent package with the same pinned dependencies:

```sh
python3 scripts/build.py Motivic
python3 scripts/build_client.py
```

The client helper prepares an inherited manifest, shares this checkout's canonical
package directory, and keeps its build outputs in the client's own `.lake/build`.
It uses the same resource caps and rehashed native cache checks as the library
build; it does not link another checkout's mutable outputs. CI and local final validation check it after provider checks and selected public
builds when client source/configuration or its public import is affected.
Publication reuses those checks and exact selected outputs; it adds no client
or core-root replay. An affected client failure blocks publication. For a consumer changing to a
Git dependency, pin a reviewed repository commit rather than a moving branch.

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
the [shared candidate policy](https://github.com/kangxyz/aglib/blob/main/doc/DEVELOPMENT.md#downstream-candidates-for-aglib).
See [contribution guidance](../CONTRIBUTING.md).

## Documentation ownership

Keep central `docs/` pages as concise summaries, indexes and package-wide
conventions. Mathematical definitions, complete hypotheses, universes, signs,
API examples and remaining theorem inputs belong in the owning source-family
README or an existing child document. Update that owner and its central link
when the interface changes; avoid duplicating detailed mathematical prose.
