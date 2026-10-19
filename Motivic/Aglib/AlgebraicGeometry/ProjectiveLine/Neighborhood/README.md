# Actual projective-line neighborhoods

These interfaces use `AlgebraicGeometry.RelativeProjectiveLine`, with
`R : Type u`, `[CommRing R]` and projective coordinates `ULift.{u} (Fin 2)`.

[Target/AffineSpecSquare](Target/AffineSpecSquare.lean) defines
`nativeAffineBaseRestriction R b := Y.isoSpec.inv ≫ b` for affine `Y`
and `b : Y ⟶ Spec R`, and its literal polynomial line restriction.
`nativeAffineSpecSquare` gives their Cartesian square with the two original
polynomial projections. The
[smooth-site cylinder construction](../../Sites/Smooth/README.md) pastes these
squares while retaining all coefficient restrictions as composites.

[Source/NativePunctureTransport](Source/NativePunctureTransport.lean) works
with an affine coefficient open `O` and an arbitrary original map
`a : A ⟶ Spec R[t]`. `sourceWholeCoverIso` removes the redundant intersection
with the entire original line; `sourceWholeCoverIso_native` preserves the
original native map. `nativePunctureTransport` identifies the original target
retained scheme with that same native puncture, and
`nativePunctureTransport_chart` identifies their literal projective-chart
composites. It does not choose a new open or section.

[Boundary/NormNonempty](Boundary/NormNonempty.lean) proves
`neighborhoodBoundary_toSpec_surjective` for every original line open `V`.
The opposite-chart zero gives a point of the actual full neighborhood boundary
over each coefficient point. `normFullBoundarySource_nonempty` consequently
requires only a nonempty parameter scheme `A` and its map to `Spec R`; the
infinity component already makes the coproduct of infinity and marked
pullbacks nonempty. No nonempty marked fiber or reducedness condition is
added. This is the boundary used by the
[original principal-action interfaces](../../../../Transfers/Presheaf/Actions/README.md).
