# Cohomology

[The family entry](../Cohomology.lean) exports ordinary sheaf cohomology,
hypercohomology and relative cohomology with their original naturality, plus
[canonical motivic complexes](Motivic/README.md).

Ordinary cohomology is defined independently of transfer-category cohomology.
The [transfer endpoint](../Transfers/SheafCohomologyWithTransfers.lean) acts
on its original groups, restrictions and coefficient maps. Degree conventions,
coefficient universes and `HasExt` inputs stay explicit.

The optional [perfect-field strict-invariance entry](A1/StrictInvariancePerfectField.lean)
proves all-degree invariance of the original ordinary projections for HI transfer
sheaves over every perfect field. It retains ordinary `HasExt.{u+1}` and
coefficient universe `u + 1`. The [A1 guide](A1/README.md) records its finite and
infinite suppliers. Other geometric H1/descent leaves retain their individual
scopes; historical roadmaps live in [provenance](../../doc/provenance/README.md).

## Affine-line vanishing

The optional [AffineLine entry](AffineLine.lean) exposes
`Motivic.SheafCohomology.affineLine_H_add_two_eq_zero` for arbitrary ordinary
abelian coefficients on the original smooth Nisnevich site over any field,
and `affineLine_H_succ_eq_zero` for homotopy-invariant Nisnevich sheaves with
transfers. Both retain the ordinary `HasExt` and coefficient-universe inputs.
The cohomology groups and restriction maps remain the original ordinary ones.

The degree-one pencil theorem is the unchanged prerequisite for the positive
HI result; the higher-degree proof uses actual generic-open section lifting,
Artinian neighborhoods, relative Ext excision and finite closed overlap-support
deletion. The exact [milestone record](../../doc/provenance/positive-vanishing-20261017/README.md)
and [verification record](../../doc/VERIFICATION.md) distinguish archived checks,
source review and current checks. The perfect-field strict theorem has its own
entry and proof; general derived continuity remains separate. Arbitrary small-site coefficients
are not identified with arbitrary big-site coefficients by this entry.

## Generic neighborhoods

[Affine generic detection](A1/GenericDetection.lean) exports the original
`Motivic.PresheafWithTransfers.exists_zero_neighborhood_of_nonempty_open` and
`iSup_zero_opens_of_nonempty_open`. Over an infinite field, a section of an
A1-invariant presheaf with transfers on a smooth integral affine scheme that is
zero on an original nonempty open is zero on
affine neighborhoods covering every point. The original open need not be affine,
and the presheaf need not be a sheaf. The conclusion is local zero, without
asserting global vanishing for an arbitrary presheaf.

[Relative affine-line generic-base vanishing](AffineLine/GenericBase.lean)
retains arbitrary ordinary coefficients in degrees at least two. It now also
exports original generic-base H1 and all-positive results for HI Nisnevich
sheaves with transfers over any field. Each class is killed after the stated
two nonzero base localizations and an affine generic base open. The whole line
and original restriction maps remain; the open may depend on the class.

The generic-model detection leaves use actual model-open colimits. Over an
infinite field, they give genuine big transfer and literal small ordinary
sheafification-zero conclusions. They do not identify these sheafifications or
assert objectwise zero of an arbitrary original presheaf. The positive
contraction-sheaf zero result retains current-degree cohomology invariance.

The rank-zero cylinder join is available for HI sheaves with transfers in all
positive degrees over any field, with complete field-valued markings retained.
Positive-rank Cartier reduction retains coefficient HI, perfectness, lower-degree invariance,
lower-rank germ induction and the exact original marked restriction Mono.
Coefficient-section dense-open injectivity does not supply that cohomology Mono.

## Cartier boundary and open support

The optional [CartierBoundary entry](A1/CartierBoundary.lean) exports
`Motivic.SheafCohomology.higherDirectImage_isZero_of_original_epi`.
For an actual smooth Cartier complement over an infinite field, it proves
vanishing of the genuine positive right-derived open direct image. It retains
A1-invariance of `withTransfers k F (n+1)`, epimorphic original
`contractionToBoundary X` for every smooth `X`, ordinary `HasExt.{u+1}` and
coefficient universe `u+1`. Perfectness is not required once the smooth Cartier
pair is supplied. Quotient, small sheafification, genuine closed inverse image
and original punctured representatives remain the actual constructions.

The [source record](../../doc/provenance/cartier-boundary-rj-20261018/README.md)
distinguishes checked admissions from archived candidates. The later perfect-field
strict proof supplies its original Epi and marked restriction-Mono joins, including
finite-field local-zero and boundary constructions. The conditional Cartier
interface above keeps its stated hypotheses. Default imports are unchanged.
