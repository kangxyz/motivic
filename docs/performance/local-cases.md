# Motivic performance cases

Return to the [performance lookup](../PERFORMANCE.md).
Common methods live in Aglib's
[conversion boundaries](https://github.com/kangxyz/aglib/blob/main/docs/performance/conversion-boundaries.md)
and [shared constructions](https://github.com/kangxyz/aglib/blob/main/docs/performance/shared-constructions.md).
The following integration observations used Lean 4.34.1, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, Aglib
`52e09db47998f139064acf48a2d3a64494d0dd9a`, the ordinary 200,000-heartbeat
budget and a 12,800 MiB frontend cap. Their historical job/thread settings are
measurement conditions, not current resource prescriptions.

## History context and complete supplier conversion

The expensive terms combined coefficient restrictions, section rings,
polynomial lines, smooth-site structures and their instance proofs. The
retained repair proved generic geometry over actual ring/scheme maps, supplied
the actual target site object, and specialized the comparisons once.

[NativeCover](../../Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/AffineLine/NativeCover.lean)
keeps literal scheme maps in the affineness, étaleness and restriction-square
proofs. `affineEtaleOverArrow` receives the actual target object.
[OriginalNativeCover](../../Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Nisnevich/OriginalNativeCover.lean)
retains the field-lifting arrows and their explicit underlying-map equations.

[LocalizationHistory](../../Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/AffineLine/LocalizationHistory.lean)
proves the endpoint equations over abstract original localization witnesses.
[OriginalHistory](../../Motivic/Transfers/Presheaf/Actions/Norm/NativeRefinement/OriginalHistory.lean)
packages those same choices and suppliers in a shared context. The lifting
producer converts rich suppliers into witnesses over abstract history data
before constructing that context. Its concrete consumer passes the original
suppliers directly rather than unpacking and reconstructing them.

### Observed module costs

The first four modules have prefix
`Motivic.Transfers.Presheaf.Actions.Norm.NativeRefinement`;
the last two are in `Motivic.Cohomology.A1.Sheafification`.

| Module | Before (s) | After (s) | Interpretation |
| --- | ---: | ---: | --- |
| `NativeOriginalRefinedSource` | 1845 | 96–97 | Native ring/scheme helpers before site specialization |
| `NativeOriginalRefinedPuncture` | 4325 | 555 | Shared restricted maps and the actual target object |
| `OriginalHistoryLine` | 643 | 51 | Generic endpoint equations and one abstract history context |
| `OriginalHistoryRestrictions` | 385 | 5.8 | Shared context avoids reconstructing concrete history |
| `OriginalHistoryLifting` | 42 | 36 | Supplier conversion over abstract history data |
| `WholeCylinderLifting` | 135 | 141 | Original rich suppliers passed directly |

These are successful incremental module-job observations with different active
dependencies, not controlled whole-library benchmarks. Module durations cannot
be added into a whole-build saving; extraction moved work to new providers.

The important counterexample is the constructor itself. Its first context
version took 300 seconds, explicit inherited records 294, and a separate witness
choice constructor 319. Moving the complete supplier-to-witness conversion into
the abstract producer led to 141 seconds. That does not improve the original
135-second observation. Packaging the same expensive specialization differently
had not solved it.

A separate diagnostic of the 300-second candidate timed out after a reported
314.34-second elaboration interval and showed repeated structure projections.
It did not complete a kernel check. Instrumentation and single-file setup make
its 563.50-second total unsuitable as an ordinary module benchmark. The retained
repair passed normal native compilation at the ordinary budget.

The original maps, chosen witnesses, E3 correction sign, coefficient universe
`u + 1` and public hypotheses were retained.
[Historical recovery copies](../provenance/hi-presheaf-sheafification-20261020/history-before-abstraction/README.md)
and the [integration record](../provenance/hi-presheaf-sheafification-20261020/README.md#abstract-history-refactor)
own source identity and final integration scope.

## Cached command-lint coverage

The [2026-10-24 failure](https://github.com/kangxyz/motivic/actions/runs/39996085343/job/120559858728)
reported malformed copyright headers after cache restoration caused modules
to compile again. Earlier cached outputs and separate text-style success did
not establish coverage of the enabled header command linter.

The repair completed 190 production headers without changing mathematical
bodies or concrete upstream credits. One shared Lean environment ran the
[pinned header predicate](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Tactic/Linter/Header.lean);
all 2,414 production leaf headers passed that predicate. This is that source
predicate's coverage, not replacement evidence for compilation, declaration lint
or axiom checks. It illustrates batching a cheap source repair while retaining
compatible artifacts.

## Compiled checker startup

Interpreting the pinned Mathlib text-style source with `lean --run` spent
minutes elaborating it and failed with
`cannot evaluate [init] declaration ... in the same module`.
This was a checker-launch failure, not a style finding. Its matching compiled
`mathlib/lint-style` executable handled the boundary.

A reused checker must match its actual compiler, dependency revision and driver
source. A missing tool artifact calls for that matching dependency, not a clean
library rebuild. Current invocation belongs to [the script guide](../../scripts/README.md).
The [shared build/check topic](https://github.com/kangxyz/aglib/blob/main/docs/performance/build-and-check-costs.md)
owns the common lesson; there is no additional checker or client stage here.

## Existing source and run evidence

The following table is retained from the
[fixed original guide](https://github.com/kangxyz/motivic/blob/be8e17f5286874bd44942f796b96860b4b924993/docs/PERFORMANCE.md#source-and-log-evidence).
Its receipts/logs were reported under
`/private/tmp/r5-investigations/motivic-ci-latest-20261021/root/` and
`/root/autodl-tmp/lean-build/logs/`; their present availability has not been
rechecked. No new experiment was run to prepare these notes.

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

A successful module in an interrupted or failed run retains only its original
scope. The linked provenance owners distinguish the source variants and final
integration; the table does not confer mathematical status or a whole-CI pass.
