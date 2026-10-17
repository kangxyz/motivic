# Cohomology

[The family entry](../Cohomology.lean) exports ordinary sheaf cohomology,
hypercohomology and relative cohomology with their original naturality, plus
[canonical motivic complexes](Motivic/README.md).

Ordinary cohomology is defined independently of transfer-category cohomology.
The [transfer endpoint](../Transfers/SheafCohomologyWithTransfers.lean) acts
on its original groups, restrictions and coefficient maps. Degree conventions,
coefficient universes and `HasExt` inputs stay explicit.

`A1/` and the geometric H1/descent leaves retain their individual scopes.
They do not supply general strict A1 invariance. The imported roadmap and
source-check evidence live in [provenance](../../doc/provenance/README.md).

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
source review and current checks. Generic-cylinder continuity and full strict
A1 invariance remain separate obligations. Arbitrary small-site coefficients
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
exports `Motivic.SheafCohomology.exists_relative_generic_base_h_add_two_zero`.
For any field, smooth domain base and original ordinary coefficient sheaf,
each degree-at-least-two class is killed after two nonzero base localizations
and restriction over an affine generic base open. The entire affine line and
original Ext restriction maps remain. The open may depend on the class.

The [source record](../../doc/provenance/generic-detection-20261017/README.md)
separates checked admissions from six unlogged archival leaves. Finite-field
generic detection, nonintegral smooth schemes, the final zero-sheaf consumer,
arbitrary-class generic-base H1 and the all-positive generic rank-zero join
remain outside these entries. The default cohomology entry is unchanged.
