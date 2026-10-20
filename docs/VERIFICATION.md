# Verification scope

> Current navigation: see the [documentation index](README.md) and
> [A1 guide](../Motivic/Cohomology/A1/README.md), including the
> [HI-presheaf sheafification interface](../Motivic/Cohomology/A1/Sheafification/README.md).
> Current guides retain `Motivic/Aglib` as maintained general-theory candidates
> and distinguish their native interfaces from host applications. This notice
> adds navigation only; the chronology below retains its original evidence basis.
> The sections below retain their identified source snapshots, historical paths,
> pins and validation limits. Source reorganization does not relabel those checks
> as validation of later bytes. Later interfaces supersede historical open
> frontiers only under their stated hypotheses and recorded evidence boundaries.

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
do not discharge explicit premises. The later infinite-perfect-field strict A1
entry below supersedes this initial open frontier under its exact hypotheses.

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

## Cartier boundary and genuine open direct image

Archive SHA256:
`5b3aaaf7cbb57d046c0c44e8e2f5cb3622cc6adc6e1d00c1ae5042ccf6c65aef`,
based on current main `97e291af`. The admitted source set is 53 new production
leaves, 13 tests and three updates. It is dependency-closed. The other 59 new
candidates and two incoming replacements are preserved as raw archival source;
the two corresponding current-base implementations remain unchanged. None of
the admitted callers uses the five extra unbound APIs in those replacements.
All six previously quarantined generic-detection inputs now have recorded
admission evidence, with their earlier archival bytes retained.

The [source index](provenance/cartier-boundary-rj-20261018/SOURCE-INDEX.json)
binds all 130 incoming source identities. Sixty-seven status-listed hashes match;
Cartier choice and its test have separate frozen-hash/stdout summaries, whose
referenced raw guard receipts are absent. The exact twelve-file Cartier bridge
has a successful graph-build guard and scoped text/source/audit summaries. Its
earlier cache probe exited three and is not counted as success. These are
identified archive records, not fresh executions against later projections.

Independent ordinary review accepted the actual quotient, coefficient/unit,
Cartier-chart, genuine inverse-image, point-fiber and Rj comparisons. It also
accepted moving the exact composed Rj theorem from the test into production,
with the literal test type retained as a public consumer and the new defining
module included in its scoped lint. The production hypothesis block and proof
block are byte-identical to the reviewed archive consumer.

The upstream ordinary review accepted any-field generic-base H1/all-positive
results for HI coefficients, infinite-field actual generic-model/sheafification
zero, current-degree conditional contraction-sheaf zero, canonical boundary Mono,
and the rank-zero cylinder join. Positive-rank reduction remains conditional.
Neither review assigns established status or discharges original EPI-P,
current-degree HI, the remaining marked restriction-Mono joins or strict A1.

Current source checks passed for 3,191 Lean sources. All 71 maintained changed
modules passed exact-file text/style lint. Two Mathlib-only foundations,
`SheafifyLocallyZero` and `ClosedFiberEtaleEqualization`, compiled and passed
15 default declaration linters each, with no exceptions or findings. Their
source/output/receipt hashes are in the [fixed check record](provenance/cartier-boundary-rj-20261018/CHECKS.json).
No dependency builds or local whole-endpoint replay occurred.

The actual CI selection covers 73 targets: the 71 changed modules and two
affected existing consumers. All 62 archival Lean/control paths are excluded.
The new facade selects its joint consumer on future isolated changes. Existing
tool fixtures are retained because tooling is unchanged. The adapted consumer's
current production theorem, exact-origin lint and transitive audit are selected
for hosted validation. The 20-line root README, pins, configuration, CI and
previous source/test repairs remain intact.

The [hosted Cartier run](https://github.com/kangxyz/motivic/actions/runs/39090562661)
for `48dd1e1` subsequently passed source checks, all selected Lean targets and
cache publication. The adapted public consumer passed its standard-foundations
audit and all 103 exact-origin declaration checks. Its completed log reports
74 production and 14 test modules freshly built, zero Aglib/Mathlib source
builds, and a native-export cache hit without compilation. This validates the
current public production/test projection against the pinned hosted environment.
The source Epi and current-degree HI assumptions remain explicit.

## Strict A1 invariance over infinite perfect fields

Archive SHA256:
`6e33d7d1c1417882b6686f76e6940b6092a9c9b6b6f6c548b062120de81eca54`,
based on `b368f696`. The admitted delta is 70 new production files, nine new
tests, five production updates and one test update. Eleven unbound new sources
remain outside production under the [source provenance](provenance/strict-a1-infinite-perfect-20261018/README.md).
Eighty-two admitted sources are byte-exact to the archive. Two helpers and their
covering-norm consumer use canonical Aglib imports and native `Module` names;
their mathematical statements, conditions and proofs are preserved modulo
those qualifications. The root README and curated default imports are unchanged.

Independent ordinary mathematical/source review accepted the actual original
ordinary Nisnevich cohomology projection isomorphism in every natural degree
for HI sheaves with transfers over an infinite perfect field. The public leaf is
`Motivic.Cohomology.A1.StrictInvariance`; ordinary `HasExt.{u+1}` and the original
coefficient universe remain explicit. The canonical presheaf boundary Epi,
marked H1 and positive restriction Monos, and lower-degree strong-induction
suppliers are supplied. No positive-HI or puncture-Mono theorem family remains
an external input to that final theorem. This is ordinary result-specific
review, not an established-status assignment.

All 85 admitted sources have matching supplied source-status and frozen-hash
evidence. The final five-file Linux scope includes successful production and
terminal consumer receipts and 50 exact-origin declaration checks. Two earlier
raw producer receipts are absent; they are not invented or relabeled as fresh
native checks. The successful downstream records and final source bindings are
retained separately. No whole new strict endpoint replay is claimed locally.

The two adapted helpers compiled against the current Aglib provider. Their nine
exact-origin declarations passed the standard-foundations audit and all 15
applicable declaration linters. The corrected `MotivicTest.CoveringNormLengths`
also compiled, reporting 11 declarations checked for lint and standard axioms,
and text/style success for itself and both helpers. The 85-file source delta
has exact-file text/style coverage. Source checks pass for 3,100 Lean sources,
and the six dependency/source-boundary fixtures pass after the exact Aglib pin
update. The [fixed check record](provenance/strict-a1-infinite-perfect-20261018/CHECKS.json)
separates current native checks from historical Linux evidence.

The later current Linux integration at `d05e037` compiled the strict-invariance
leaf and consumer, with all 50 exact-origin declarations and five-source
text/style checks passing. Its separate aggregate audit-name failure is recorded
in the Milnor integration section below.

All 43 source adaptations within the strict consumer closure already belong to
the Milnor migration's selected downstream validation scope. The two newly
adapted helpers are outside that closure. A separate full strict-closure replay
would duplicate that integration work. At this snapshot, finite-field descent
and the separate frame/standard-triple/norm/Picard program remained open;
higher-Chow and spectrum comparisons were separate.

## General Milnor K-theory upstream integration

The independent Aglib dependency is pinned to
`b11b71d11bf03cf231f0e06b947a7b63d4344a9e`. Its source correspondence records
273 moved implementation modules, one generic polynomial extraction and 170
moved tests. `MilnorK.K F n` is canonical; the tensor presentations live in
`MilnorK.K2.Group` and `MilnorK.K3.Group`. Motivic keeps its two actual endpoint
geometry applications and comparison interfaces. Old module paths are thin
imports, with the six existing native-alias adapters retained. Earlier source
identities remain recorded separately from the current authorship and
Apache-2.0 license headers.

Ordinary source/API correspondence review passed. The upstream selected
production, declaration/style checks, 147 affected tests, 23 retained unchanged
tests and standalone client passed. Its final hosted CI passed library and
client checks and published the matching native cache. The header-credit guard
and mixed-format test-umbrella regressions pass; legacy audit leaves keep their
original visibility and private-origin coverage.

Current native downstream validation compiled 342 modules and reused 279
controlled compatible geometry outputs, with 264 current Aglib providers and
168 reached foreign interfaces bound to actual artifacts. All three selected
production endpoints passed. Five direct consumers of symbols, naturality,
weight-two norms, prime induction and Koszul replacement also passed under the
actual test-package options. Compatible outputs survived every source repair;
no mathematical heartbeat bound changed.

[The integration check record](provenance/milnor-k-aglib-20261018/CHECKS.json)
identifies the exact endpoint/test sources, artifacts and successful guards.
It distinguishes controlled native overlays from a fresh rehashed Lake build
of the complete committed-pin package. No unbound Darwin artifact is adopted
to claim local completion.

The [hosted run at `50799e2`](https://github.com/kangxyz/motivic/actions/runs/39103086719)
built the public root and `MotivicTest.PublicAPI`, but failed on three optional
leaves: an open-transport theorem name collided with the upstream degree-transport
theorem; four categorical projectivity references resolved to module projectivity;
and a Milnor surjectivity definition exceeded the line-length limit. Its partial
caches were saved. The pinned Aglib asset imported successfully, with no fresh
Aglib or Mathlib compilation.

The [follow-up at `dd1f4ef`](https://github.com/kangxyz/motivic/actions/runs/39108109720)
passed the public roots, the 12,309-declaration standard-foundation audit and the
independent `MotivicClient`, then published its native cache. It reused the failed
run's project/native progress; only the audit and client modules compiled. That
selection does not certify repairs to the three optional failures, whose focused
validation is recorded separately.

The focused repairs rename the local open-equality theorem and its caller,
qualify categorical projectivity, and wrap the long signature. Nine current
native modules, including the existing Koszul/Tor and weight-two surjectivity
tests, passed. Fifteen declaration linters found no errors in the two repaired
defining modules (21 declarations and seven generated declarations). All four
changed sources passed pinned text/style checks.

The [repair run at `d05e037`](https://github.com/kangxyz/motivic/actions/runs/39113032519)
compiled all three repaired leaves. It also compiled `StrictInvariance` and
`MotivicTest.StrictA1Invariance`: 50 declarations passed the exact-origin
standard-foundation/declaration audit, and the five selected source files passed
pinned text/style checks. The run failed only in `MotivicTest.MotivicIntegration`,
where 43 canonical declarations were unavailable after their former test-import
paths moved upstream. Four precise public Aglib imports restore reachability of
their 25 defining modules. All 417 audit entries and all non-import source bytes
are preserved. Dependency, project and native progress were saved; no Aglib or
Mathlib module compiled. The aggregate audit was selected for cached hosted
acceptance after this import repair; this entry does not record its completion.

## Perfect-field strict invariance, 18 October 2026

The later archive adds the finite-field local-zero and canonical boundary-Epi
producers, their ordinary-cohomology induction assembly, and the general entry
`Motivic.Cohomology.A1.StrictInvariancePerfectField`. Its theorem
`Motivic.SheafWithTransfers.isStrictA1Invariant_of_perfect` gives the literal
ordinary Nisnevich projection isomorphism in every degree over every perfect
field. It retains HI, `SheafWithTransfers.{u+1}` and ordinary `HasExt.{u+1}`;
no cardinality or supplied D/E geometric-family premise remains.

Independent ordinary review accepted the finite original-presheaf Epi, the
arbitrary-coefficient-universe finite local-zero construction and the perfect-field
strict endpoint. The finite boundary theorem itself requires neither HasExt nor
sheafness. The existing infinite-field branch and its reviewed background are
retained. Other admitted supporting families keep their explicit local
principal-face conditions and supplied correction/frame witnesses. This
milestone inferred no global principal-A1, non-flat norm, Picard or general
HI-presheaf sheafification result.

The admitted delta contains 131 new production sources, 21 tests and one
Coherence proof factorization with unchanged public statements. All 153 sources
match the archive bytes and pass current pinned text/style checks. Current
source checks pass for 3,252 project/client sources. Eighteen independent source
candidates remain outside production, with their actual historical evidence
boundaries preserved.

[The source and check record](provenance/perfect-strict-20261018/README.md)
binds the archive, source hashes, unchanged pins and selected supplied Linux
receipts. Its final finite scope reports 322 exact-origin declarations over
19 sources; the perfect-field terminal reports four over two sources. Supplied
evidence and current checks are distinguished. At this snapshot, affected
compilation and consumers were selected for integration CI with matching caches;
this entry does not record their completion.

## Topic layout and support-sensitive original action, 19 October 2026

The [integration record](provenance/support-sensitive-action-20261018/README.md)
binds 264 intake destinations to the topic hierarchy described in
[architecture](ARCHITECTURE.md) and [naming](NAMING.md). Reusable general
candidates remain under `Motivic/Aglib/`. Detailed mathematics and interfaces
are documented in their owning source families.

Current validation covers the affected production closure, 919 defining origins
under 15 declaration linters, changed-source style checks, affected tests, the
independent client and compiled documentation examples. It combines fresh checks
with retained results whose actual inputs remain compatible. Test coverage
includes 956 affected modules and three unchanged prerequisites; other unchanged
tests retain their recorded evidence. Remote tests used matching production and
dependency caches.

At this snapshot, the arbitrary HI-presheaf sheafification corollary retained
its explicit whole-cylinder lifting input. The perfect-field strict-invariance
entry retained its HI transfer-sheaf, ordinary HasExt and coefficient-universe
hypotheses. The later unconditional presheaf entry is recorded below.

## Original normalization recovery, 19 October 2026

The [integration record](provenance/normalization-recovery-20261019/README.md)
maps the two archive snapshots to 94 new sources: 66 general candidates,
27 motivic implementations and one affected test. Existing Lean sources,
dependency pins and curated roots are unchanged. Mathematical interfaces and remaining inputs
are documented in the owning normalization, pencil, action and representative
guides linked from that record.

Compatible retained checks and focused new runs cover all 93 production origins:
compilation, 15 declaration linters and a standard-axiom audit of 1,455 public,
private and generated declarations. All 94 source files pass text/style checks.
The affected test compiles and introduces no declarations of its own. Structural
checks pass for 3,369 project/client sources; tooling coverage is 66 passing
fixtures and one optional skip.
The exact 94-target portable cache was exported and imported locally, passing
guarded no-build/rehash acceptance.

The original E5 action endpoints retain their sections, maps and signs. The E3
original-difference zero results and generic middle-difference lifting adapter
retain all their displayed premises. Expanded E3 action wrappers and the actual
common-witness master transport were deferred. At this snapshot, arbitrary
HI-presheaf sheafification and its strict A1 corollary remained open; the existing
perfect-field theorem for already-HI transfer sheaves was unchanged.

## Aglib dependency upgrade, 20 October 2026

Aglib is pinned to `52e09db47998f139064acf48a2d3a64494d0dd9a`.
Lean and Mathlib are unchanged. Lint repairs complete five docstrings, remove
redundant simp registrations and drop an unused `IsIntegrallyClosed` premise
from the finite-generic-fiber helper. A function-level rational-coordinate
identity factors the existing pointwise proof and preserves tuple simplification.
The [reviewed dependency scope](../.github/dependency-scope.json) binds the exact
before/after configuration snapshots and selects 1,263 affected modules:
942 production modules and 321 tests. Its 76 direct production providers are
checked before consumers; text/style checks cover the 80 direct local seeds.
Declaration lint still covers every affected defining origin.

Compatible retained fixtures and focused new tests give 78 passes and one
optional skip. The cache setup now includes the style driver's exact direct
Batteries prerequisites, including `Batteries.Data.String.Basic`; two new
fixtures cover acquisition and read-only selection. A further fixture checks
that cache export preserves explicit module selection for the root facades.

Structural checks, provider compilation and declaration lint, selected text/style
checks and the two changed-declaration axiom checks passed. The remaining
affected-consumer checks and independent client check are pending at this
upgrade's initial push.

## HI-presheaf sheafification, 20 October 2026

The [intake and recovery record](provenance/hi-presheaf-sheafification-20261020/README.md)
identifies the incoming archive based on `522c7256` and its integration onto
`c793b96`. Superseded proof experiments and historical evidence are preserved
in a separate recovery archive outside the production import graph; no supplied
file was deleted. Conditional lifting APIs remain maintained reusable interfaces.

The new source entry
`Motivic.Cohomology.A1.Sheafification.HomotopyInvariance` contains
`Motivic.PresheafWithTransfers.nisnevichSheafify_isA1Invariant`. It takes
`P : PresheafWithTransfers.{u + 1} k` over a field `k : Type u` and `P.IsA1Invariant`,
with no perfectness, target-HI or lifting premise. The whole-cylinder lifting
producer is constructed from those original inputs. The separate
`Motivic.Cohomology.A1.Sheafification.StrictInvariance` entry adds perfectness
and ordinary `HasExt.{u + 1}` on Nisnevich sheaves valued in
`AddCommGrpCat.{u + 1}`. Its strict-invariance conclusion retains the actual
ordinary cohomology projections in every natural degree. The
[family guide](../Motivic/Cohomology/A1/Sheafification/README.md) owns the exact
declarations, proof route and original-map conditions.

Independent ordinary mathematical review passed the central argument relative
to the accepted mathematical dependency snapshot at `c793b96`. It is not a new
review of the entire earlier perfect-field proof or a complete native CI
baseline. Current-pin native validation, transitive axiom auditing and scoped
replay remain in progress. Historical receipts do not claim completion of
those current checks, cache publication or hosted CI. Nonperfect
strict invariance, derived continuity, full canonical purity,
positive-characteristic diagonal, higher-Chow and spectrum comparisons retain
their separate boundaries.
