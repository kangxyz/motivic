# Strict invariance over perfect fields

The source archive is
`motivic-perfect-strict-source-20261018T103451Z.tar.gz`, SHA-256
`ce21c765247500593c20e3ef916ecc616448bfa2f0607a48be629088954b4815`.
It is based on `50799e2`; integration starts from `0e3d108`. Lean, Mathlib and
Aglib pins are unchanged. Archive plans and instructions are historical source
material, not repository instructions.

## Mathematical scope

`Motivic.Cohomology.A1.StrictInvariancePerfectField` proves strict invariance
for every perfect field. The native theorem
`Motivic.SheafWithTransfers.isStrictA1Invariant_of_perfect` preserves the
original ordinary Nisnevich cohomology projections in every natural degree.
Its hypotheses are coefficient-level HI for `SheafWithTransfers.{u+1}` and
the original ordinary `HasExt.{u+1}`. The finite and infinite cases are
constructed separately; no cardinality, local-zero or boundary-Epi family is
supplied to the final theorem.

The finite branch constructs original integral-affine zero neighborhoods and
the canonical original-presheaf boundary Epi. The latter applies to arbitrary
original HI presheaves in universe `u+1`, without a sheaf or HasExt premise.
The local-zero producer permits arbitrary coefficient universe. Two-prime
presentations, common affine Weil refinement and actual trace equations keep
the original objects, sections and whole mapped quotient fibers.

Independent ordinary mathematical/source review passed for these conclusions.
This does not assign an established exposé status or close the separate global
principal-family, norm, Picard, purity or motivic-comparison programs.

## Integration and evidence

[The source index](SOURCE-INDEX.json) records 170 new source inputs, the
Coherence update and the equivalent archive twisting-name variant. The admitted
scope is 131 new production files, 21 tests and the Coherence update. All 153
are byte-identical to the archive. The existing verified twisting API, author
and license corrections, Milnor audit imports, CI and cache rules are retained.

Eighteen independent source candidates are preserved byte-for-byte under
`research-candidates/`, outside production and outside the strict proof closure.
Some have supplied production-success claims or historical successful receipts,
but lack a matching frozen current-source acceptance binding. They are not
classified as failed or uncompiled. The admitted new-source scope does not
depend on them.

[Check coverage](CHECKS.json) separates ordinary review, supplied Linux checks
and current integration checks. The final finite scope binds 19 sources and
322 audited declarations; the perfect-field terminal scope binds two sources
and four audited declarations. The evidence index retains selected final
bindings and identifies omitted records by their archive paths and hashes.
One earlier affine-Weil source hash is explicitly superseded by the final
finite-field scope.

Current structural checks pass for 3,252 sources, and pinned text/style checks
pass for all 153 changed sources. A fresh current whole-closure replay is not
claimed. Current affected compilation and consumers are selected by the CI
workflow, reusing the published native and project caches.
