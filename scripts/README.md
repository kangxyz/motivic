# Focused developer tools

Use Python 3.11 or newer from the repository root. During development, use
incremental compilation and its integrated diagnostics. Independent lint and
tests, including applicable tooling tests below, belong only to the current
task's final validation before delivery. Helper returns, internal commits and
merges do not trigger them; preserve compatible results and rerun only failures
or newly affected checks after repairs.

The source checker does not
invoke Lean, modify source, resolve dependencies or validate external proofs:

```sh
python3 scripts/check_repository.py
python3 -m unittest discover -s scripts -p 'test_*.py'
```

`library_sources.py` inventories occupied `Motivic` and `MotivicTest` sources and
provides the comment-aware Lean import parser adapted from Aglib at revision
`c9863095f90b8bd312af807dbf0e378df82403b5` under Apache-2.0.
`check_repository.py` checks local import existence, actual import cycles,
production/test isolation, retired source roots, proof-placeholder and unsafe
tokens, package/test identities and exact accepted dependency pins. It separately
checks `examples/downstream` in the client's module namespace: imports may use
production and dependencies, production cannot import the client, and client
placeholders and missing local imports are rejected. The reported source count
distinguishes project and downstream files. It does not
require a candidate-only dependency layer. External roots are allowlisted;
external module existence and elaboration require resolved dependencies and a
focused Lean build.

`cache.py` requires explicit existing local module targets. It follows their
imports through local source and the pinned Aglib source to collect only
reachable Mathlib cache roots. It never sends Aglib modules to Mathlib's cache
and rejects an unscoped `Mathlib` import. `--list` prints the selection without
running Lake; `--resolve-deps` resolves the existing manifest before fetching:

```sh
python3 scripts/cache.py --resolve-deps Motivic.Cor
python3 scripts/cache.py --list Motivic.Cor
```

`--guarded` applies the reviewed Aglib resource guard and writes a private cache
receipt. CI uses this mode with its separate tooling checkout and memory limits.

`build.py` requires explicit targets, always requests native `--rehash`
validation, and invokes Aglib's `scripts/build_serial.py --root` with private
verification receipts. Its default helper comes from the pinned dependency;
`MOTIVIC_TOOLING_ROOT` selects a separately reviewed Aglib tooling checkout.
The wrapper never deletes artifacts or accepts artifact presence as proof of
cache validity. It retains the upstream driver's owned-process resource guard:

```sh
python3 scripts/build.py Motivic.Cor
python3 scripts/build.py --receipt-dir .lake/verification/my-change Motivic.Transfers
```

Optional `--outputs FILE` forwards native Lake input-to-output mapping export to
the same guarded incremental build. It preserves ordinary target selection and
cached-build behavior; a relative output path is resolved from the package root.

`MOTIVIC_BUILD_THREADS`, `MOTIVIC_LEAN_MEMORY_MB` and `MOTIVIC_RSS_LIMIT_MB`
map to the upstream driver's corresponding `AGLIB_*` settings. Existing upstream
settings remain available when no Motivic override is supplied. Keep shared
Lean build outputs serialized; dependency build trees must belong to this
checkout. The build command may compile the selected target's genuinely
missing dependency closure, so obtain matching caches first and investigate
unexpected broad work.

`test_repository.py` supplies boundary fixtures for actual cycles, candidate
imports, test/client leaks, comment/string masking, cache reachability and pin drift.
`test_ci_targets.py` checks optional-leaf coverage, import-only optional facades
without same-named directories, affected public consumers,
docs-only selection, first pushes and explicit manual targets.
No test here claims mathematical or kernel acceptance.

CI selects affected checks before running them. Lean/pin/import changes select
the structural source check; documentation-only changes run no Lean or tool
fixtures. Python fixture ownership is explicit: selector changes run selector
fixtures, build-wrapper changes run build fixtures, cache/checker changes run
repository fixtures, and shared-parser changes run all current fixtures. First
setup, default manual acceptance, changed workflow wiring and unknown new tools
select the safe full source/tool scope. Explicit manual targets check structure
without replaying unchanged tool fixtures. Compatible unchanged check evidence
remains reusable; helper returns and internal commits or merges do not trigger
reruns. Independent tool fixtures run at the final task/CI acceptance boundary.

`ci_targets.py` selects each
existing changed local Lean module, including optional leaves outside curated
roots. Reverse import reachability adds affected public directory facades,
comment-aware import-only facades regardless of directory layout, and
production/test roots and all reachable `MotivicTest` consumers, including
modules with declarations and axiom audits. Unrelated roots and tests are omitted;
subject names require no manual public-facade list.
First pushes, dependency/toolchain pins, tooling/workflow changes and default
manual dispatch select `Motivic MotivicTest`. Simultaneously changed Lean leaves
and their affected consumers remain selected alongside those roots. An explicit
manual selection must name existing local modules. Documentation-only changes avoid the Lean job.
Client Lean/config changes select the `Motivic` public root and independent
client acceptance; changes reaching the client's public import select it too.
PR/manual runs keep unrelated optional leaves outside client acceptance;
documentation-only changes do not select the Lean job.
`python3 scripts/build_client.py` prepares the inherited locked manifest and
runs the same guarded `--rehash` driver on `MotivicClient`. Its package-directory
link points only to this checkout's canonical dependency cache; its writable
outputs remain in `examples/downstream/.lake/build`. Existing foreign package
links or shared build-output links are rejected without deleting user work.
PR/manual runs check the client after the selected public build when it is
affected. Every main-branch native-cache producer checks it after the already
required guarded core export and before cache staging, even for optional-only
changes. A failure blocks publication. The client reuses the same job's validated
public outputs and matching dependency caches. CI restores matching
Mathlib dependencies, public Aglib native artifacts and incremental outputs;
it saves partial progress. Native cache transport tooling has its own reviewed
pin, independent of the mathematical Aglib revision. The selected build also
exports native mappings. Before publishing on a main-branch push, a separate
guarded export selects `Motivic`, `MotivicTest` and the changed targets together,
so an optional-leaf change retains reusable core coverage in its producer asset.
The shared helper's rehashed no-build probe reuses matching outputs; a miss may
compile only the genuinely missing required core/selected closure. This is a
specific cache consumer, not a request to build every retained leaf or replay
the whole library. After a successful export, the shared action stages those
mappings with the actual source/compiler provenance and uploads a
same-run artifact. Only the separate `publish-cache` job receives repository
write permission; after the build job succeeds it releases that exact artifact
as an immutable `cache-<producer SHA>` prerelease asset. Pull requests and manual
dispatch do not publish. Upload and `gh`-based same-run download remain in the
pinned shared implementation. A configured workflow is not evidence of a
successful hosted build, upload or release.

`test_build.py` exercises existing calls and optional mapping-export forwarding
against a temporary stand-in helper without invoking Lean or touching caches.
