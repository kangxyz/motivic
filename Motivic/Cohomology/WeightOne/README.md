# Weight-one computations

| Exact import | Interface |
| --- | --- |
| `Motivic.Cohomology.WeightOne` | Focused weight-one entry |
| `Motivic.Cohomology.WeightOne.SheafComparison` | Original ordinary unit-sheaf comparison |
| `Motivic.Cohomology.WeightOne.Hypercohomology` | Original ordinary hypercohomology comparison |

This family compares the actual current weight-one motivic complex with the
ordinary Nisnevich unit sheaf shifted by `[-1]`. It supplies the quasi-isomorphism
and the resulting ordinary hypercohomology comparisons under their stated
conditions. These consume the
[Suslin–Voevodsky model](../SuslinVoevodsky/README.md); they do not replace its
complex or introduce a derived-with-transfers cohomology group.

Original unit, boundary, norm, restriction and coefficient maps remain part of
the interface. Finite-coefficient results use the
[current cone construction](../Coefficients/Finite/README.md), with its actual
Bockstein sign. Preserve the degree shift, coefficient universes, ordinary
`HasExt` and derived-category conditions displayed by each leaf.

Existing consumers include `MotivicTest.WeightOneHypercohomology`,
`MotivicTest.WeightOneSheafComparison` and
`MotivicTest.WeightOneFiniteCoefficients`. General Milnor symbols and norm
infrastructure are supplied by independent Aglib. A comparison to another model
or broader base scheme requires explicit maps and separate hypotheses.
