# Finite-boundary twists

[Field](Field.lean) works over any field `k`. For `g : Z ⟶ ProjectiveSpace k ι`
with finite composite `g ≫ toSpec k ι`, it chooses one unit trivialization of the
restriction of O(1) to the whole finite boundary `Z`. Its nonnegative tensor
powers give `fieldBoundaryTwistIso`.

For an arbitrary `h : W ⟶ Z`, `fieldBoundaryTwistBaseChangeIso` pulls this same
chosen trivialization to `W`. It uses the actual pullback-composition comparison,
the pullback of the chosen isomorphism and `pullbackUnitIso h`.
`fieldBoundaryTwistBaseChangeSection` is the inverse isomorphism applied to the
unit section. Its coefficient is one on all of `W`, and the corresponding map
from the structure sheaf is an isomorphism. Both constructions use all of `W`.

The legacy names `fieldBoundaryTwistIso_baseChange` and
`fieldBoundaryTwistSection_baseChange` remain deprecated transparent aliases.
The coefficient and isomorphism theorems retain their existing names.

[FieldRelative](FieldRelative.lean) compares these units with the actual
relative projective twist, retaining the caller's coefficient-map square.
These are general algebraic-geometry candidates in the native
`AlgebraicGeometry.Scheme.CoherentGraph` namespace.
