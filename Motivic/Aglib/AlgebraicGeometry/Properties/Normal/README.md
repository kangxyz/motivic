# Normality along actual scheme morphisms

[OpenImmersion](OpenImmersion.lean), imported as
`Motivic.Aglib.AlgebraicGeometry.Properties.Normal.OpenImmersion`, extends
`Scheme.NormalStalks` from pinned `Aglib.AlgebraicGeometry.Properties.Normal.Basic`.
Its intended upstream owner is `Aglib.AlgebraicGeometry.Properties.Normal.OpenImmersion`.

`AlgebraicGeometry.Scheme.NormalStalks.of_isOpenImmersion` takes native schemes
`X Y : Scheme.{u}`, `hX : NormalStalks X`, and an open immersion `f : Y ⟶ X`.
It returns `NormalStalks Y` through the actual `f.stalkMap` isomorphisms.
There is no nonempty, connected, Noetherian, or whole-scheme integrality premise.
The underlying normality predicate requires both the domain and integral-closedness
conditions on every actual stalk.

The current consumer is
[the relative affine-line compactification normality leaf](../../Normalization/Compactification/RelativeAffineLine/NormalStalks.lean).
Existing `Scheme/NormalStalks.lean` providers remain unchanged.
