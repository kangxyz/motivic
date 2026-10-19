# Boundary sections through an open factor

[BoundarySections](BoundarySections.lean) provides
`AlgebraicGeometry.Scheme.Hom.appTop_eq_one_of_open_factor`. For schemes
`E,T : Scheme.{u}`, a morphism `b : E ⟶ T`, an open `V`, a section
`r : Γ(T,V)` and an actual factor `β : E ⟶ V.toScheme` satisfying
`β ≫ V.ι = b`, the hypothesis `b.app V r = 1` gives
`β.appTop (V.topIso.inv r) = 1`.
The equality concerns the full inverse-image open and its scheme structure;
no reducedness, nonemptiness, affineness or integral-target premise is used.

The [native correction principal-action consumer](../../../../Transfers/Presheaf/Actions/Pencils/NativeCorrectionNormAction.lean)
uses this to pass the normalized full-boundary equation into global sections
of the same factor. The theorem supplies no boundary-value hypothesis itself.
Intended upstream module: `Aglib.AlgebraicGeometry.Morphisms.OpenImmersion.BoundarySections`.
