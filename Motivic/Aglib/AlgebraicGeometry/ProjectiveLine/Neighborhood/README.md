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

[Source/NativeSmooth](Source/NativeSmooth.lean) proves relative smooth dimension
one for the literal native restriction of any original open affine-line map,
followed by chart zero and the structure map over the same affine coefficient
open. It requires no affine or nonempty source hypothesis.

[Target/NativeRetainedProduct](Target/NativeRetainedProduct.lean) proves openness
of the literal retained-product inclusion using the original retained map
`targetNativeRetained R V (a ≫ chart R 0)`. It specializes the existing Cartesian
openness API; it does not replace that retained map by a smaller parameter open.
Both leaves are independently selectable general geometry. Their interfaces
retain the original coefficient maps and supplied neighborhoods; source presence
does not extend the accepted scope of the host sheafification chain.
