# Verification scope

This bootstrap preserves the supplied mathematical implementation and changes
package organization, public import selection, test-root names and developer
tooling. It does not assign a new mathematical proof status.

The bootstrap observations below apply to initial repository commit `04569be`.
Later source changes and their selected coverage are recorded separately below.

## Initial bootstrap source and integration checks

- All 1,665 original production Lean bodies are preserved. Generic author
  labels were normalized to `kangxyz`; bytes after each first license/author
  comment are unchanged. Concrete upstream authors remain credited.
- All 1,022 migrated test leaves match the specified mechanical `Tests` and
  `MotivicTests` to `MotivicTest` substitution, plus author metadata. Original native object namespaces
  remain intact; one new public consumer is added.
- `python3 scripts/check_repository.py` passes for 2,698 project/client sources:
  import existence, actual cycles, source isolation, forbidden proof tokens,
  package names and pinned dependency consistency.
- There is compatible coverage of 21 tooling fixtures. The final selector
  changes passed seven graph/target tests, and the affected CI check-selection
  changes passed seven `ValidationScopeTests`. Six unchanged repository fixtures
  and one unchanged build-argument fixture reuse their previous success; no
  whole-suite rerun was triggered by helper returns or metadata edits.
- Independent read-only engineering/API review found no remaining actionable
  findings after the client field argument and stale family guidance were fixed.
  This was not independent mathematical proof review.
- Newly authored staged files pass Git whitespace checks. Original imported
  whitespace is preserved with its source bytes rather than silently changing
  historical source identities.

## Initial bootstrap native compilation

The local compiler is Lean 4.34.1, `arm64-apple-darwin24.6.0`, commit
`5045d0056413266e57c625dcd7c365b10e377c52`. Mathlib and Aglib retain the exact
committed pins. Checkout-owned dependency/build outputs and current rehashed
Lake traces determine cache compatibility.

| Selected check | Status |
| --- | --- |
| `python3 scripts/build.py Motivic.KTheory.MilnorK.Basic` | Passed |
| `python3 scripts/build.py Motivic.Transfers MotivicTest.OrdinaryCohomologyTransfers` | Passed, including transitive standard-foundations audit |
| Production `Motivic` entry | Passed in the combined core run |
| `python3 scripts/build.py MotivicTest.PublicAPI MotivicTest` | Passed after two test-only topology namespace qualifications |
| Separate `examples/downstream` client | Passed; only the client module compiled |

The transfer/consumer run reused matching dependencies and compiled its selected
missing local closure in 2,323 seconds, with peak group RSS 7.39 GiB and no
resource-guard failure. The final core is 651 local modules; together with its
selected test consumers the combined closure is 654 modules. No optional norm,
diagonal or weight-one replay was added.

The initial combined core command returned exit one only because the new public
consumer omitted two `Motivic` namespace qualifiers. The production root had
already succeeded. After correction, only the failed consumer and its test
entry were rebuilt successfully. The independent client ran in an isolated
scratch package with unchanged Lean source, an absolute local package path and
matching checkout-owned dependency artifacts. It required no downloads.

Compilation completed before the final author-header normalization. That later
change modifies comments only: every Lean body after its first header is exact,
and Python ASTs are unchanged. The applicable compilation/trust evidence is
retained; the author edits are not represented as fresh raw-byte compilation
certificates. Historical source hashes and current author-header hashes are
separately identified in the provenance index. No metadata-only proof replay
was requested.

The guarded build uses one active compiler with a finite memory cap; native
threads do not change mathematical heartbeats or admitted axioms. Build records
are private outputs under `.lake/verification`, outside version control.

## Boundaries

The selected native targets do not cover every retained research leaf. Optional
norm, diagonal and weight-one computation endpoints retain their exact imported
Linux source/check evidence; no fresh whole-library replay is claimed.
[Historical records](provenance/README.md) identify their source hashes and
compiler separately. Source scans, caches and successful conditional theorems
do not discharge explicit premises. Strict A1 invariance remains open.

The hosted workflow is configured to check actual changed leaves and affected
public consumers, with `Motivic` and `MotivicTest` on initial setup or pin/tooling
changes. The producer exports current core and selected-target native mappings on a
successful main push and releases the same-run staged artifact from a separate
write-permission job. Configuration alone does not claim a successful GitHub
Actions run or a published cache release.

## Affine-line positive-vanishing milestone

Source archive SHA256:
`3f5e1eed50f393d1345c753582fd25a4850cf7084befcbca6414a4472fb000c9`.
The source delta from the first archive adds 184 production and 65 test leaves,
changes four production and two test leaves, and deletes none. Toolchain,
mathematical dependency pins, curated default entries and native-cache transport
are unchanged. Their applicable existing evidence is reused. The new optional
entry is `Motivic.Cohomology.AffineLine`.

CI target selection now includes declaration-containing `MotivicTest` consumers
reachable from changed modules. Mixed tool/configuration and Lean edits retain
changed optional leaves alongside required default roots. The nine affected
`TargetSelectionTests` passed, including two new regressions for these cases.
The unchanged check-scope fixtures and other tooling results are retained.

Independent ordinary mathematical/source review accepted the two exact endpoint
statements and their original cohomology objects: `H^(n+2)` vanishes for arbitrary
ordinary abelian coefficients on the big smooth Nisnevich site over any field;
`H^(n+1)` vanishes for homotopy-invariant sheaves with transfers. Coefficient
universe and ordinary `HasExt` remain explicit. Review covered all 13 changed
local modules in the higher-vanishing closure and traced supporting unchanged
interfaces; the entire existing H1 closure has no changed modules. This is an
ordinary result-specific review, not an established-status assignment.

The [delta provenance](provenance/positive-vanishing-20261017/README.md) records
253 matching supplied strict Linux checks for 255 added/changed leaves. Two
new leaves lack supplied check logs and are explicitly identified there.
These source records are separate from selected current native checks.

The protected previously validated core has no implementation changes or
affected consumers in this source delta. Lake's raw hashes differ after the
previous author-header normalization; old traces remain untouched. Selected
native compilation used an explicit bound baseline and current-source artifact
overlay. It does not constitute a successful current-source rehashed Lake build.

The higher-vanishing endpoint and its 32-module extension compiled successfully.
Current native checks also covered the two statement-preserving repairs to
unlogged helpers, the changed polynomial transcendence-degree module, both
finite-etale colimit modules and their standard-foundations consumer. The
651-module core was retained; 436 baseline modules in the selected closure were
bound to their controlled outputs and author-header-only source equivalence.

The full all-positive native entry was not completed locally. At the scope
review, all 180 remaining original mathematical leaves (179 older prerequisites
and the new `RankZero` module) had matching successful supplied Linux logs. The
original terminal consumer also had a matching standard-foundations audit.
Those records and the independent endpoint review were retained rather than
continuing the long native H1 replay. The new import-only facade and its migrated
consumer have structural/selection coverage; their full current-byte build is
left to the push CI.

One stopped prerequisite probe,
`Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.PullbackSections`, failed to
find three public identifiers present in pinned `GlobalSections` source. Its
fallback cached dependency had no source/compiler/options binding and differed
from a same-source producer artifact. This is evidence of an imported-cache/API
mismatch, not a verdict that the pinned source is broken. The controlled local
successes retain their external-artifact basis; no fresh whole-pinned-graph
certificate is claimed. CI uses native `--rehash` to compare current inputs.
The failed diagnostic is retained separately from successful leaf results.

The structural checker passed for 2,948 Lean sources (2,947 project and one
downstream). All 256 delta/facade files passed exact-file text/style lint after
one trailing space was removed; affected files were checked separately after
repairs. Six selected compiled production modules passed 15 declaration linters
each, with the explicit domain-API exception recorded in the provenance index.
The [fixed native-check record](provenance/positive-vanishing-20261017/NATIVE-CHECKS.json)
stores exact current source/output identities, successful receipt hashes, retained
evidence conditions and the stopped diagnostic. The initial bootstrap
[CI run](https://github.com/kangxyz/motivic/actions/runs/39045875580) succeeded,
including cache publication; the subsequent merge run is not asserted here.

General small-site coefficient comparison, generic-cylinder continuity and
strict A1 invariance on arbitrary smooth schemes remain outside this milestone.

## Affine generic detection and relative-line generic base

The next archive has SHA256
`972401892b0b3753d3b3538cdfdb37a6b9ac72991b5c176dfd78219b249267c7`.
The raw delta adds 158 production and 21 test leaves and changes two helpers.
There are 175 matching successful incoming Linux logs for 181 delta sources.
The maintained admission is 153 new production leaves and 20 tests, plus two
optional public facades. Exactly six unlogged sources are preserved unchanged
under the [provenance archive](provenance/generic-detection-20261017/README.md),
outside production/test discovery. They form their complete reverse dependency
closure; no admitted consumer or either primary endpoint depends on them.

The two already-repaired helper implementations are retained. Their statements
match incoming source, but current proofs use their previous bounded native
checks; incoming logs are not relabeled as checks of those different bytes.
Toolchain, dependency pins, default imports and tooling are unchanged. Matching
prior evidence is retained, including affected-test selection fixtures.

Independent ordinary review accepted both exact primary endpoints. Affine
local-zero detection requires an infinite field, smooth domain and HI presheaf
with transfers. It uses the original nonempty open, section, inclusion graph
and coefficient universe; no sheaf, presentation or closed-point hypothesis is
supplied. The review covered all 51 new/changed imports, dimension-zero and
positive-dimensional branches, full prescribed schemes and the Jacobson passage
from closed-point neighborhoods to an all-point open cover. It does not infer
global zero for arbitrary presheaves.

The relative-line endpoint, over any field and smooth domain base, gives
classwise eventual vanishing of original ordinary `H^(n+2)` after the stated
base restrictions, with the whole line retained. Its review covered all 23 new
production dependencies, the direct Ext consumer and unchanged interfaces.
The original ordinary coefficient universe and `HasExt` remain explicit. No
fraction-field coefficient object or cohomological continuity is substituted.
The generic-fiber dimension bound is not imposed on the total space. Both
ordinary reviews retain matching individual source/log coverage and the original
standard-foundations audits; neither assigns established status.

Current structural checks passed for 3,123 Lean sources. All 175 new maintained
sources/facades passed exact-file text/style lint after a one-file whitespace
correction; the unaffected results were retained. Three new Mathlib-only leaves
were selected for native checks. Their actual module names are
`Motivic.Topology.JacobsonOpenCover`, `Motivic.Aglib.Topology.GenericComponentOpens`
and `Motivic.Aglib.AlgebraicGeometry.AffineOpenComplementIdeal`; all compiled and
passed 15 declaration linters each, with no exceptions or findings. No dependency
builds were needed. The [fixed check record](provenance/generic-detection-20261017/CHECKS.json)
stores source/output identities and guarded receipts. These are the actual native
checks; neither full new endpoint was replayed locally. Their matching Linux
records and ordinary source reviews remain the evidence for the larger closures.

The real import-graph selection includes all 175 maintained changed Lean modules
and excludes all six archival sources. Changing either new facade alone selects
its terminal test as well. Existing target-selector fixtures remain applicable;
unchanged tools were not retested. The public facade/test projections are
selected for the push CI.

The previous `04dba9f` [CI run](https://github.com/kangxyz/motivic/actions/runs/39052789364)
had successful source/tool checks and an active Lean build when inspected. All
three prior cache entries were actually accessed in its restore windows, about
1.52 GB dependencies, 983 MB native artifacts and 107 MB project outputs. The
completed bootstrap run imported pinned Aglib artifacts, built no Aglib/Mathlib
source modules and reported a native export cache hit. The
[cache observation](provenance/generic-detection-20261017/CI-CACHE-CHECK.json)
distinguishes those facts from unverified per-module reuse or final success of
the active/new run. No cache repair or healthy-run restart was indicated.

Finite-field detection, nonintegral smooth targets, the final zero-sheaf consumer,
arbitrary-class generic-base H1, the all-positive generic rank-zero join and full
strict A1 invariance remain outside these entries.

## Hosted endpoint test correction

The [corrected hosted run](https://github.com/kangxyz/motivic/actions/runs/39072227872)
at [ff4ff6d](https://github.com/kangxyz/motivic/commit/ff4ff6d73b49e5ea6c05ab55f4e5665b249e3a9f)
passed source checks, Lean validation and public cache publication. The two
endpoint tests needed an explicit `end` for their anonymous noncomputable
sections before closing their test namespaces. Statements and proof bodies
were unchanged; earlier provenance hashes retain the pre-correction snapshots.

The completed log reports exactly two newly compiled proof modules, both
corrected tests, with both standard-foundations audits passing. Dependency,
native and project caches were restored from the previous failed run's saved
progress. Core/selected-target native export reported a cache hit with no
compilation needed. No cache deletion or production proof replay was required.
