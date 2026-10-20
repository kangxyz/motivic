# Relative projective-line charts, flatness and component dimension

These general interfaces use the native relative projective line
`ProjectiveSpace R (ULift.{u} (Fin 2))` and the actual two polynomial charts.
The [neighborhood guide](Neighborhood/README.md) retains original coefficient
squares, punctures and full boundaries. The
[two-localization guide](BaseChange/README.md) records the literal nested
pullbacks, retained source and boundary transport.

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

## The coordinate map on a native fiber

[Fiber](Fiber.lean) defines
`AlgebraicGeometry.RelativeProjectiveLine.nativeFiberToProjectiveLine`.
For `R : Type u`, schemes `C S : Scheme.{u}`, the actual maps `q : C ⟶ S`
and `F : C ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))`, a specified affine-base
isomorphism `e : S ≅ Spec R`, and the exact equation `F ≫ toSpec = q ≫ e.hom`,
its source is literally `q.fiber s` and its target is the projective line
over `S.residueField s`. The coefficient hom is recovered from the native
residue-field arrow composed with `e.hom`, not supplied independently.

The two structural equations and the Cartesian square retain the original
fiber inclusion and projection. The finite and flat instances are actual
base changes of the corresponding properties of `F`. The square helpers
`residueProjectiveSquare` and `fiberProjectionSquare` expose the two native
base-change comparisons. No nonempty, reduced, connected, smooth, or
positive-rank premise is added. This leaf does not assert fiber dimension.
Its component-dimension consumer below applies to the first and final
normalization coefficient restrictions on the same chosen opens and
whole-chart witnesses.

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

## Component dimension of the actual native fibers

[Dimension/FiberComponents](Dimension/FiberComponents.lean) supplies
`AlgebraicGeometry.RelativeProjectiveLine.topologicalKrullDim_eq_one_of_mem_nativeFiberComponents`.
For the same commutative `R`, schemes `C S`, maps `q` and `F`, base
isomorphism `e`, and structural equation used by `Fiber`, it assumes
`IsFinite F` and `Flat F`. For each `s : S` and each actual irreducible
component `Z` of `q.fiber s`, it concludes `topologicalKrullDim Z = 1`.
The proof applies the field theorem to the canonical map on that literal
fiber over `S.residueField s`. It does not replace the base point or fiber,
or assume that a fiber is nonempty.

The [same-coefficient consumer](../Normalization/README.md) supplies both
first and final compactification projections using their original free
charts. These componentwise results are not a smooth relative-dimension
assertion. Their fixed-witness geometric conjunction has the
[normalization owner](../Normalization/README.md).

## Whole boundary factors after the same two localizations

[BaseChange/TwoLocalizationBoundaryFactors](BaseChange/TwoLocalizationBoundaryFactors.lean)
extends the existing `AlgebraicGeometry.RelativeProjectiveLine.TwoLocalizations`
layout without choosing another localization, boundary, or ambient. For
`R : Type u`, fixed `r : R`, fixed `s : Localization.Away r`,
`F : C ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))`, and `b : B ⟶ C`,
`firstBoundaryMap` is the literal lift from the pullback of `b ≫ F` to
the first source pullback. `boundary` is its pullback along `sourceFirstMap`,
exactly as in the full-boundary affine-ambient supplier.

`boundarySquare` proves that `boundaryOriginalMap` and `boundaryMap` form a
Cartesian square over `b` and the unchanged composite `sourceMap`. It uses
native pullback cancellation and pasting, not an assumed global comparison
isomorphism. Given an actual factor `a : E ⟶ B` with `a ≫ b = e`,
`boundaryFactor` maps the whole scheme `pullback e sourceMap` into that nested
boundary. `boundaryFactor_map` and `boundaryFactor_original` retain both
projection triangles.

For `b = coprod.desc d z`,
`coproductBoundary_factors_through_ambient` takes the already supplied open
`U` and its existing full-boundary factor. The two coproduct injections give
maps from literally `pullback d sourceMap` and `pullback z sourceMap` into
that same `U`, each composing with `U.ι` to its original pullback projection.
The theorem needs no nonzero-element, finite, flat, closed, affine, or
nonempty-source premise. In the normalization application, `d` is the same
nonreduced thickened boundary and `z` is the actual marked section composite.
Affineness of the already supplied ambient remains the supplier's evidence;
this leaf proves the full scheme factorizations, not a replacement support
or a standard-triple splitting.
