# Development

## Mathematical trust

Closed results require source correspondence, complete hypotheses and foundation
inputs, no transitive `sorry`, and axiom dependencies limited to `propext`,
`Classical.choice` and `Quot.sound`. Compilation, lint and a cache hit do not prove
correspondence with the intended mathematics. Native final validation uses the
same pinned upstream production axiom auditor as CI; it loads built module
origins and does not replay proofs. Preserve dependency boundaries, source and
toolchain identity, compatible audit evidence and independent mathematical
review/writing acceptance. Conditional theorems retain their premises.

## Normal task

Keep a coherent proof and compiler repair with one author in the prepared
workspace. Build the changed leaf or actual interface consumer:

```sh
python3 scripts/build.py Motivic.Transfers.Cohomology.Basic
```

At final validation use the shared native commands already used by public CI:

```sh
python3 scripts/validate.py
python3 scripts/validate.py --base BASE --head HEAD
python3 scripts/validate.py --progress /absolute/scratch/check-progress
```

The thin entry calls the toolkit `check` action. The Lake package name selects
`lean_ci.motivic.options`, including production root `Motivic` and the repository
source checker. Source policy, import generation and focused build/cache/client
helpers live in the installable toolkit. Install the current shared package or select
an explicit tooling checkout with `MOTIVIC_TOOLING_ROOT` (or
`LEAN_CI_TOOLING_ROOT`). The tooling checkout provides `scripts/lean_ci` and is
installed from `scripts/pyproject.toml`. Its executable is independent of
mathematical Lake pins. No whole-package Git fingerprint, injected checker,
GitHub baseline,
committed-phase protocol or frozen plan is required. The
[script guide](../scripts/README.md) owns exact command options.

## Environment and dependencies

The package's `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` pin Lean,
Mathlib and Aglib. Do not run `lake update` during ordinary proof work.
`lake resolve-deps` materializes the committed dependency snapshot without
choosing new revisions. A prepared proof loop does not start with cache fetching,
inventories or dependency initialization. For genuinely missing inputs:

```sh
lake resolve-deps
python3 scripts/cache.py --guarded --resolve-deps Motivic.Cor
python3 scripts/build.py Motivic.Cor
```

The explicit cache helper follows reachable local/Aglib imports to Mathlib
leaves. Its guarded bootstrap retains process/RSS/native compiler caps. Direct
builds use the existing shared module builder and resource profile; no second
executor is maintained here. Never link another checkout's mutable build tree.
Native Lake artifact caching and rehashed builds reuse compatible outputs. A
missing cache or receipt does not itself assign a clean or blanket rebuild.
General Milnor implementations live in Aglib; the two public
`Motivic.KTheory.MilnorK` and `.Norms` entries remain import bridges.

## Verification by scope

During proof iteration use explicit `+MODULE` builds or `scripts/build.py`.
Final validation builds the production `Motivic` library incrementally, prepares
native checker tools and runs `lake test`, `mathlib/mk_all --lib Motivic --check`,
Mathlib text style, `lake --no-build lint Motivic -- --trace` and the upstream
production axiom audit. The configured `MotivicTest.+` globs discover in-package
tests; no Test umbrella is generated. The library test driver accepts no module
arguments. Positive/negative compile-time assertions run in the ordinary test
graph without a separate replay invocation.

A nonempty docs-only comparison runs the repository source checks without Lean
or cache preparation. A clean/no-change invocation still requests native final
checks. `--source-only` is explicit static coverage; `--list` displays commands
without executing them. `--full` uses the same native graph and predicates,
without forced rebuilding, clients, kernel replay or an extra acceptance chain.
Routine checking never prepares or builds the independent downstream client.

Use external `--state`/`--receipt-dir` and `--progress` paths. Reuse binds each
successful command to actual source/native/checker inputs and toolchain; retain
valid successes after a later failure and rerun changed or missing coverage.
`--outputs PATH` delivers mappings from the successful native build without a
second compilation; mappings describe compilation, not proof correspondence or
a check pass. Full/partial outputs retain their actual coverage.

The repository source checker preserves import existence/cycles, production/test
and candidate boundaries, thematic facade ownership, tokens and mathematical
pins. Mathlib owns production-root generation. The native text driver scans the
production root's imports; there is no custom exact-source injection. The
upstream auditor retains its defining-module-origin selection and allowed axioms;
it imports production only, excluding separate deliberate negative Test fixtures.
Public CI continues to use its pinned Build/Test/Publish workflow, with caches
saved on failure and publication gated by all required checks.

## Public client

`examples/downstream` is a separate Lake package requiring this repository by
relative path. Its `Motivic` import checks the public correspondence category
and the canonical Milnor degree-zero equivalence. For an explicitly requested
client diagnostic, compile it with the same pinned dependencies:

```sh
python3 scripts/build.py Motivic
python3 scripts/build_client.py
```

The client helper prepares an inherited manifest, shares this checkout's canonical
package directory, and keeps its build outputs in the client's own `.lake/build`.
It uses the same resource caps and rehashed native cache checks as the library
build; it does not link another checkout's mutable outputs. This is a standalone
diagnostic for a specific client-check request. Routine validation, `--full`,
merge, publication and adoption do not select or prepare this client.
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
