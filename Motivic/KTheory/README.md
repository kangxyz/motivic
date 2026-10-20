# Milnor import compatibility

General Milnor K-theory is maintained by independent
[Aglib](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/KTheory/MilnorK/README.md)
at the revision pinned in this package's manifest.
Motivic retains exactly two public Milnor import bridges:

| Import | Canonical upstream entry |
| --- | --- |
| `Motivic.KTheory.MilnorK` | `Aglib.KTheory.MilnorK` |
| `Motivic.KTheory.MilnorK.Norms` | `Aglib.KTheory.MilnorK.Norms` |

New implementations use exact Aglib lower imports. The actual group is
`MilnorK.K F n`; its low-degree tensor presentations are `MilnorK.K2.Group F`
and `MilnorK.K3.Group F`, connected by `twoEquiv` and `threeEquiv`. Norm towers
retain characteristic-zero, finite-dimensional and scalar-tower hypotheses.

[Diagonal](../Cohomology/Diagonal/README.md) and
[weight-two comparisons](../Cohomology/WeightTwo/README.md) consume the original
symbols, geometric endpoint maps and canonical upstream groups. General
[curve and frame prerequisites](../Aglib/AlgebraicGeometry/RelativeCurve/README.md)
have their candidate owners; motivic applications remain host constructions.
There is no parallel local general Milnor implementation. See the
[bridge guide](MilnorK/README.md) and
[interfaces](../../docs/INTERFACES.md) for retained boundaries.
