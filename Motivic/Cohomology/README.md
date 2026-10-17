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
