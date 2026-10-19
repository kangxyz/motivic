# The Suslin–Voevodsky model

| Exact import | Interface |
| --- | --- |
| `Motivic.Cohomology.SuslinVoevodsky.Complex` | Original motivic complex and functor |
| `Motivic.Cohomology.SuslinVoevodsky.Hypercohomology` | Original ordinary sheaf complex and integer-degree groups |

`Motivic.Cohomology.SuslinVoevodsky` is the focused facade for `Complex` and
`Hypercohomology`. The narrow legacy `Motivic.Cohomology.Motivic` entry
reexports this model and the finite-coefficient facade. New consumers use the
canonical entries.

The current model is the sheafified Suslin complex of the reduced torus.
`Motivic.motivicComplex k q` and `Motivic.motivicComplexFunctor k q` retain
complexes of transfer sheaves in coefficient universe `u+1` for a field
`k : Type u` and weight `q : ℕ`. No perfection or characteristic assumption is
part of these constructors. Singular chain degree `r` occupies cochain degree
`q-r`; preserve the original differential and shift signs.

`Motivic.motivicSheafComplex` is the underlying ordinary Nisnevich sheaf complex.
Its actual unbounded hypercohomology defines
`Motivic.motivicCohomology k p q X`, with `p : ℤ`, `q : ℕ` and a smooth-site
object `X`. `HasDerivedCategory.{w}` on ordinary Nisnevich sheaves remains
explicit; the group lies in `Type w`. The native smooth-site object is
`AlgebraicGeometry.Scheme.SmoothSite (Spec (.of k))`.
`Motivic.motivicCohomologyRestriction` is the original contravariant map along
an actual smooth-site morphism.

Lower [singular complexes](../../Transfers/SingularComplex/README.md),
transfer sheafification and
[general hypercohomology](../../Aglib/CategoryTheory/Sites/Hypercohomology/README.md)
precede these constructions. Derived finite coefficients have their
[separate coefficient owner](../Coefficients/Finite/README.md).
[Diagonal](../Diagonal/README.md), [weight one](../WeightOne/README.md) and
[weight two](../WeightTwo/README.md) are computations and comparisons of these
actual objects, retaining each theorem's field and derived-category conditions.

The existing `MotivicTest.DiagonalMilnorEquivalenceNaturality` and
`MotivicTest.WeightTwoMilnorNormComparison` consume original symbols, field
maps and norm comparisons. Preserve actual coefficient and shift maps when
extending a computation. A future higher-Chow, motives or spectrum model needs
its own construction and explicit comparison maps. Current constructors do
not imply these comparisons, broader-base theorems or positive-characteristic
diagonal equivalence. See [architecture](../../../docs/ARCHITECTURE.md).
