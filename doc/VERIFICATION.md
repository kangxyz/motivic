# Verification scope

This bootstrap preserves the supplied mathematical implementation and changes
package organization, public import selection, test-root names and developer
tooling. It does not assign a new mathematical proof status.

## Source and integration checks

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

## Native compilation

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
