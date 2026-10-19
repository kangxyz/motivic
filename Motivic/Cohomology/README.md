# Motivic cohomology, invariance and computations

`Motivic.Cohomology` is the curated public cohomology entry. The actual current
model is the sheafified Suslin complex of the reduced torus, with original
ordinary Nisnevich hypercohomology. A module family does not introduce another
cohomology type or rename `Motivic.motivicComplex` and
`Motivic.motivicCohomology`.

| Family or exact entry | Objects and retained conditions |
| --- | --- |
| [Suslin–Voevodsky model](SuslinVoevodsky/README.md) | `Motivic.Cohomology.SuslinVoevodsky.Complex` and `.Hypercohomology`; field `k : Type u`, transfer coefficients `u+1`, integer cohomological degree, natural weight |
| [Finite coefficients](Coefficients/Finite/README.md) | Actual cone and original integral/Bockstein maps; `Motivic.Cohomology.Coefficients.Finite.Complex` |
| [A1 invariance](A1/README.md) | `Motivic.Cohomology.A1.StrictInvariance` for HI transfer sheaves over every perfect field, retaining ordinary `HasExt.{u+1}` |
| `Motivic.Cohomology.AffineLine` | Original ordinary higher vanishing and positive vanishing for HI transfer sheaves over arbitrary fields |
| `Motivic.Cohomology.AffineLine.GenericBase` | Classwise eventual vanishing on the original whole line over a smooth domain base; original restrictions and class-dependent base open |
| [Diagonal](Diagonal/README.md) | Original diagonal/Milnor comparison, retaining characteristic zero |
| [Weight one](WeightOne/README.md) | Original ordinary unit-sheaf quasi-isomorphism and hypercohomology comparisons |
| [Weight two](WeightTwo/README.md) | Implemented cycle, symbol and norm comparisons with each leaf's assumptions |

General unbounded derived Hom lives in
[hypercohomology candidates](../Aglib/CategoryTheory/Sites/Hypercohomology/README.md).
The existing large-universe Ext construction lives in
[large sheaf-cohomology candidates](../Aglib/CategoryTheory/Sites/SheafCohomology/Large/README.md),
with its explicit comparison to Mathlib's ordinary sheaf cohomology. General
relative cohomology and coefficient cones have their own candidate owners.
Their host applications preserve actual groups, restrictions, signs and maps.

Ordinary cohomology with transfers lives in
[Transfers/Cohomology](../Transfers/Cohomology/README.md). Exactness alone does
not imply the required acyclicity or comparison. General HI-presheaf
sheafification, nonperfect-field strict invariance, full canonical purity,
derived continuity, positive-characteristic diagonal and higher-Chow/motives/
spectrum comparisons retain separate proof obligations. See
[interfaces](../../docs/INTERFACES.md) for complete boundaries.
