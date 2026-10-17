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
