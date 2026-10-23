# Lean compilation performance

This guide records reusable repairs from the 2026-10-21 sheafification
integration. Measurements below are successful Lake module jobs on
`lean-build-cqa1`, using Lean 4.34.1, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` and Aglib
`52e09db47998f139064acf48a2d3a64494d0dd9a`.
The native build admitted eight jobs with four Lean threads each, a 12800 MiB
frontend limit and the ordinary 200000-heartbeat budget. These are observations
from incremental runs with different active dependency jobs, not a controlled
whole-library benchmark. A cached job supplies no fresh timing.

## Repair workflow

For serious compilation trouble, consult the relevant findings here before
further experiments or budget changes. When they do not cover the failure, use
the shared [reference-search method](https://github.com/kangxyz/aglib/blob/main/docs/PERFORMANCE.md#repair-workflow):
search the corresponding GitHub issues, PRs, discussions and official documents
by diagnostic, public symbol and version, then check the pinned source and
applicability of the proposed repair.

After a fix passes its relevant incremental check, add the reusable lesson here:
symptom, affected declarations and versions/conditions, effective change,
existing validation evidence, source links and remaining limits. Separate
observations from a proposed cause. Reuse existing measurements and compatible
checks; this adds no per-edit diary, mandatory benchmark or acceptance cycle.

## Generated import entries

A fixed line allowance on an import-only entry can expire as the source graph
grows; see the [Aglib failure and pinned-linter reproduction](https://github.com/kangxyz/aglib/blob/main/docs/PERFORMANCE.md#generated-import-entries-and-file-length-limits).
The existing opt-in topic generator now writes `set_option linter.style.longFile 0`
for every generated entry. Fixtures cover new and growing topics, repeated
refresh and preservation of native roots and manually owned files. No current
Motivic topic is enrolled; native defaults and CI commands are unchanged.

## Observed module costs

Module names in the first four rows have prefix
`Motivic.Transfers.Presheaf.Actions.Norm.NativeRefinement`.
The last two are in `Motivic.Cohomology.A1.Sheafification`.

| Module | Before, seconds | After, seconds | Interpretation |
| --- | ---: | ---: | --- |
| `NativeOriginalRefinedSource` | 1845 | 96–97 | Native ring and scheme helpers before site specialization |
| `NativeOriginalRefinedPuncture` | 4325 | 555 | Shared restricted maps and an arrow over the actual target object |
| `OriginalHistoryLine` | 643 | 51 | Generic endpoint equalities and one abstract history context |
| `OriginalHistoryRestrictions` | 385 | 5.8 | Shared context instead of repeated concrete history reconstruction |
| `OriginalHistoryLifting` | 42 | 36 | Supplier conversion is checked over abstract history data |
| `WholeCylinderLifting` | 135 | 141 | Concrete producer passes the original rich suppliers directly |

The extracted `NativeOriginalRefinedCover` compiled in 67 seconds; no matching
successful baseline measurement is recorded. `OriginalHistoryMiddleRelations`
compiled in 4.6 seconds in the final affected build after its proof was moved
to the abstract native input.
Module times must not be summed into a whole-build speedup: dependency jobs can
overlap, and extraction moves work into new modules. The final constructor is
close to its original 135-second cost; no improvement over that baseline is
claimed. Its first context-based version had regressed to 300 seconds. Moving
the complete supplier conversion to the abstract lifting producer reduced that
observation to 141 seconds. The first context version reported 109 seconds for
Line, 8.5 for Restrictions and 31 for HistoryLifting; the table records the final
affected build, with its changed dependencies and allocation of work.

Two earlier constructor variants did not resolve that regression. Explicitly
constructing the inherited parent records took 294 seconds, close to the
300-second observation. Selecting the two nonempty section witnesses in a
separate abstract context constructor took 319 seconds. Neither variant is
retained. These observations do not support claiming that either rearrangement
reduced the remaining cost. The retained repair moves supplier conversion into
the abstract producer rather than just rearranging the final record literal.

## Prove over abstract objects, then specialize

The expensive concrete terms combine nested coefficient restrictions, global
section rings, polynomial lines, smooth-site structures and their instance
proofs. Passing those terms into every inference and equality comparison caused
large repeated conversion obligations. The successful encoding changes suggest
conversion at these boundaries was significant; these module measurements alone
do not separate elaboration, instance search and kernel checking costs.

[NativeCover](../Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/AffineLine/NativeCover.lean)
proves affineness, étaleness and restriction squares over `R : CommRingCat` and
literal scheme maps. `affineEtaleOverArrow` receives the actual target site
object. This avoids reconstructing an extensionally identical target with
different structure or instance expressions. The application modules then
specialize those helpers once. The underlying-arrow equalities remain `rfl`.
[OriginalNativeCover](../Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Nisnevich/OriginalNativeCover.lean)
proves field lifting for abstract actual arrows with explicit underlying-map
equalities before receiving the original representatives.

[LocalizationHistory](../Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/AffineLine/LocalizationHistory.lean)
proves the native line and source endpoint equalities over the existing abstract
localization witnesses. The application-level
[OriginalHistory](../Motivic/Transfers/Presheaf/Actions/Norm/NativeRefinement/OriginalHistory.lean)
packages geometry, localization choices and witnesses in `OriginalHistoryContext`.
Line and restriction adapters consume that one context. The generic history's
`SourceSections` and `TargetSections` name the unchanged rich supplier predicates.
The lifting producer converts those suppliers to witnesses over an abstract
`OriginalHistoryData`, then constructs its context. `WholeCylinderLifting` passes
its original suppliers to that producer without unpacking the witness records
in the concrete geometric context. The raw
action-difference proof is checked over `NativeOriginalMiddleInput` with an
explicit source equality; its history specialization discharges that equality
by `rfl`. The shared context avoids repeating long parameter lists and building
the same concrete native input in each wrapper.

The original maps, chosen witnesses, E3 correction sign, coefficient universe
`u + 1` and public theorem hypotheses are retained. General localization APIs
remain maintained; superseded concrete wrappers are preserved as
[non-imported recovery copies](provenance/hi-presheaf-sheafification-20261020/history-before-abstraction/README.md).
Abstraction is useful when it reduces repeated conversion; the intermediate
constructor regression shows that packaging alone does not guarantee a faster
consumer.

The targeted diagnostic of the 300-second version reported an elaboration
interval of 314.34 seconds before a `whnf` timeout at 200000 heartbeats. Its
partial counters included 555 unfolds of `OriginalHistorySeedData.toSeed`,
8291 of `toOriginalRepresentativeGeometry` and 6974 of
`toOriginalHistorySeedData`, alongside repeated scheme and structure-sheaf
projections. This suggested moving the complete supplier-to-witness conversion
across the abstraction boundary. The diagnostic did not complete a kernel check
and supplies no successful build or per-constant timing. Its additional
diagnostic output and single-file setup make its 563.50-second total unsuitable
as an ordinary module benchmark. The retained repair passed a normal native
build with the unchanged 200000-heartbeat budget.

## Reuse the build environment

Use an ordinary incremental Lake build for changed providers and their actual
consumers, with a bounded batch of independent jobs. Preserve compatible
artifacts in the managed remote workspace. A serialized dependency chain cannot
use all compiler slots; increasing concurrency does not reduce one declaration's
conversion cost.

Run final package tests in the same native build batch. For declaration lint,
import the production umbrella once per configured linter framework and select
declarations in that shared environment. Starting a fresh import environment for
every origin repeats the expensive transitive import work. Generated-entry and
text-style scripts need their actual tool dependencies prepared once; a missing
tool artifact calls for that dependency, not a clean library rebuild. Reuse
successful checks after a repair and rerun only changed inputs, failures and
coverage gaps. Extra replay and downstream builds are separate requested work.

Prefer a compatible compiled checker executable when it is already available.
The pinned Mathlib text-style driver contains an initialization declaration:
directly interpreting its source with `lean --run` spent several minutes
elaborating it and then failed with `cannot evaluate [init] declaration ... in
the same module`. This was a checker-launch failure, not a reported source-style
failure. Its native `mathlib/lint-style` executable, or the packaged runtime
that first compiles the driver and runs an importing shim, handles that boundary.
Read-only tool reuse must match the Lean version, Mathlib revision and exact
driver source; a neighboring library's mathematical artifacts are not substitutes
for this library's compiled subjects.

For a warranted single-file diagnosis, `lake lean path/to/File.lean --
-Dtrace.profiler=true -Dtrace.profiler.threshold=100 -o /fresh/File.olean` builds
only missing imports and supplies Lake's file context. Do not assume a previous
build's temporary `.setup.json` remains on disk. Keep diagnostic outputs outside
the maintained source and distinguish a profiled run from the ordinary module
timings above.

## Source and log evidence

The retained receipts and `build.log` files are under
`/private/tmp/r5-investigations/motivic-ci-latest-20261021/root/`, with remote
copies under `/root/autodl-tmp/lean-build/logs/`. The table reuses these existing
measurements; no additional benchmark runs were requested for this guide.

| Run suffix after `remote-` | Source content SHA-256 | Scope |
| --- | --- | --- |
| `7d6f481b8525470286fd6ddc61abb8d6` | `22ccedfef9a95161496a180d8eeb46d9554f8596b681c6561e5f5c6137d06915` | Source/puncture baseline jobs passed; the enclosing run was later stopped |
| `b2bec531bd8d48d7b1bf439044ae5fbb` | `e0fdb0e38b13460d233ee2dee0ed55a1c427b13c6f72a2e394f9d57c33e31255` | Source job passed in 97 seconds; the enclosing run later timed out |
| `f4e45397b5f848cfbed7799758a01637` | `a13e07c7dcf9465c0f5525d892e21d25fa3d78e4770bce317b84e93098005863` | Source job passed in 96 seconds; the enclosing run was later stopped |
| `4a2c5ba14f864f48ae9abf37d50893f0` | `a09da017b566d807cde9c5359434e72b53f127d1e713dd612ef040f75739e67e` | Selected puncture and cover passed |
| `b38006877ae840e7bc8824c16bee9f72` | `a09da017b566d807cde9c5359434e72b53f127d1e713dd612ef040f75739e67e` | Pre-history-refactor library and package tests passed; history baseline times |
| `437211be4722480796277767eed3fe56` | `1599c245b700b5b7d675d6d21f6d4bf231507e867883ba372b21ea393add8a9e` | Rewritten line/restriction jobs passed; a separate draft middle proof failed |
| `6736b4a518924c80a4c64287b14eb302` | `75bc5aa1e6d41c66dfd69123c4ca457c478e38bedf57bd1849dc3b8e27ac047d` | Repaired middle relations and both lifting consumers passed |
| `52b2c5b89ae24fa28cffd6f5ba4b63da` | `550d67a4fafa3fea72646a88420ad52acf36f817e8dcc73269d51db29e22ae06` | Parent-record constructor variant passed in 294 seconds; not retained |
| `e54ab7cb8cc24d0e98116273a0160eb3` | `b7efba89a37d59701de2d6862008f8ed20952b0a3a95f0e826d0be2e93f81d49` | Witness-choice variant passed in 319 seconds and package tests passed; not retained |
| `84428111c0744095901a65dd5125e7ad` | `75bc5aa1e6d41c66dfd69123c4ca457c478e38bedf57bd1849dc3b8e27ac047d` | Native text style passed; separate diagnostic timed out and is not acceptance evidence |
| `95df3fc6263f42f3b1d78b428daa2120` | `395417e19b32e9ec4e4b7b68a60bc01a16ed44ea9d56c4b8d7a5b9681e3ad237` | Retained supplier abstraction: Line 51, Restrictions 5.8, HistoryLifting 36 and WholeCylinderLifting 141 seconds; affected build passed |
| `fede19f54895450987a8a984342dfe57` | `395417e19b32e9ec4e4b7b68a60bc01a16ed44ea9d56c4b8d7a5b9681e3ad237` | Final incremental library/package tests, generated entry, native text style, shared declaration lint and builtin lint all passed |

The history baseline is preserved with per-file hashes in the recovery-copy
index. The [integration record](provenance/hi-presheaf-sheafification-20261020/README.md#abstract-history-refactor)
owns final check status. A successful individual module in an interrupted or
failed enclosing run is not a successful whole-run or CI result.
