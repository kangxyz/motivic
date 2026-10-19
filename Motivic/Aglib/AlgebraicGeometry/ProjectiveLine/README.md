# Relative projective-line charts, flatness and component dimension

These general interfaces use the native relative projective line
`ProjectiveSpace R (ULift.{u} (Fin 2))` and the actual two polynomial charts.
The [neighborhood guide](Neighborhood/README.md) retains original coefficient
squares, punctures and full boundaries.

## Flatness from the whole chart algebras

[Charts/FlatOfFreeCharts](Charts/FlatOfFreeCharts.lean) supplies
`AlgebraicGeometry.RelativeProjectiveLine.flat_of_free_chart_sections`.
For any commutative `R : Type u`, a scheme `C : Scheme.{u}` and an affine
morphism `f` to that relative projective line, it assumes that each whole
chart algebra `Γ(pullback f (chart R i), ⊤)` is free over `R[t]` through
the scalar map of `pullback.snd`. It concludes `Flat f`. Flatness is local on
the target, so the actual two-chart cover and canonical affine comparisons
apply without choosing another base, basis or normalization. The source may
be empty, disconnected or nonreduced; no positive rank is required.
The [coefficient-flatness consumer](../Normalization/README.md) applies this
to the original and final coefficient restrictions using their same witnesses.

## Dimension over a field

[Dimension/FiniteFlatComponents](Dimension/FiniteFlatComponents.lean) supplies
two interfaces in `AlgebraicGeometry.RelativeProjectiveLine`. For any field
`K : Type u` and finite `g : C ⟶ ProjectiveSpace K (ULift.{u} (Fin 2))`,
`topologicalKrullDim_le_one_of_isFinite` gives `topologicalKrullDim C ≤ 1`.
With `Flat g`,
`topologicalKrullDim_eq_one_of_mem_irreducibleComponents_of_finite_flat`
gives `topologicalKrullDim Z = 1` for every actual irreducible component `Z`.
No reducedness, connectedness, integral-source, nonempty-source or positive-rank
hypothesis is added; an empty source has no component to check.

The proof uses the literal inverse images of the two charts, presented by
their actual affine global sections. The native
`AlgebraicGeometry.FiniteSchemeNormBaseChange.sections_flat` transports a flat
affine map to flatness for its structural scalar map, including `ΓSpecIso`.
`AlgebraicGeometry.Scheme.topologicalKrullDim_le_of_openCover` transports the
upper bound through actual stalk maps, for any native open cover and bound
`n : WithBot ℕ∞`. The
[polynomial-algebra component theorem](../../RingTheory/KrullDimension/README.md)
supplies the affine lower bound. These are dimension statements; they neither
assert a smooth relative-dimension predicate nor identify a separate native
coefficient-fiber map. Intended upstream family:
`Aglib.AlgebraicGeometry.ProjectiveLine`.
