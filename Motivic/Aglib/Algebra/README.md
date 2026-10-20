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
| `Motivic.Aglib.Algebra.Homology.SingularComplex.Basic` | Alternating-face chains of a presheaf on a cosimplicial object, in native `CategoryTheory.SingularComplex`. |
| `Motivic.Aglib.Algebra.Homology.SingularComplex.Presheaf` | The same construction as a complex of presheaves, retaining actual product restriction maps. |
| `Motivic.Aglib.Algebra.Homology.Sheafification.Basic` | Degreewise canonical sheafification of presheaf complexes, in native `CategoryTheory.Sheafification`, with `[HasSheafify J A]` and abelian coefficients. |

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
[SingularComplex.Indexing](Homology/SingularComplex/Indexing.lean) places chain
degree `r` in cochain degree `q - r`; its numerical comparison with Bloch's
`2q - i` convention is not a complex comparison theorem.
[SignedShift](Homology/SingularComplex/SignedShift.lean) gives the separate
signed comparison with weight-zero cochains shifted by `-q`, using
`(-1)^(q*r)` in chain degree `r`. Host singular and motivic complexes use
these generic constructions through their own
[source family](../../Transfers/SingularComplex/README.md).
See [finite coefficients](Homology/CochainComplex/FiniteCoefficients/README.md)
and the [candidate policy](../README.md).
