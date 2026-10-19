# General algebra and homological candidates

These candidates extend actual complexes, tensor products, module categories,
Tor and derived objects under native mathematical namespaces. Their closure
contains only Mathlib, Aglib and designated general candidates.

| Exact import | Interface and boundary |
| --- | --- |
| `Motivic.Aglib.Algebra.Homology.Koszul.RegularBlock.TorReduction` | Eliminate a proved regular leading block from actual Tor; preserve the remaining Koszul complex and exact scalar maps. |
| `Motivic.Aglib.Algebra.Homology.DerivedCategory.AdjunctionEdgeMap` | Adjunction/Ext edge maps on actual derived objects; subsequent window and injectivity leaves retain their bounds. |
| `Motivic.Aglib.Algebra.Category.ModuleCat.Tor.AmbientLocalLength` | Actual module-category Tor and ambient local-length comparisons. |
| `Motivic.Aglib.Algebra.Homology.CochainComplex.FiniteCoefficients.Basic` | Actual cone of multiplication, with original coefficient and Bockstein maps. |

Shared Koszul basics use canonical `ChainComplex.Koszul` in pinned Aglib.
Do not copy its objects or introduce a second core implementation. Higher
Koszul/Tor extensions consume those objects. Preserve degree indexing,
differentials, regular-sequence data, local length finiteness, independent
module universes and every displayed categorical assumption.

General diagonal/intersection support primitives belong to the
[geometry candidates](../AlgebraicGeometry/README.md). Actual correspondence
incidence and transfer actions are host consumers. A generic complex theorem
does not supply geometric acyclicity or a missing comparison premise.
`MotivicTest.KoszulTwoListReplacement` is an existing actual replacement consumer.
See [finite coefficients](Homology/CochainComplex/FiniteCoefficients/README.md)
and the [candidate policy](../README.md).
