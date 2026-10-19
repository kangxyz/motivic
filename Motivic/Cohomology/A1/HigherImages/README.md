# Higher-image and Cartier boundaries

`Motivic.Cohomology.A1.CartierBoundary` exposes genuine positive `Rj_*`
vanishing for a supplied smooth Cartier complement over an infinite field.
It retains current-degree original cohomology HI and the original
contraction-to-boundary Epi for every smooth object. Ordinary
`HasExt.{u+1}`, coefficients in universe `u+1`, a locally rank-one actual ideal
and equality with the actual complement remain explicit.

The [boundary family](../Boundary/README.md) contains proved original-presheaf
Epi suppliers, but the retained Cartier theorem's inputs stay in its statement.
Coefficient-section dense-open Mono is a different map. Conditional rank
reductions retain their exact hypotheses; supplying a smooth Cartier pair does
not automatically establish every marked Mono or full canonical purity.

This family consumes original ordinary cohomology and genuine sheaf
inverse/direct images. A replacement Ext object or exact forgetful functor
alone does not establish its acyclicity or comparison. See the
[site guide](../../../Aglib/AlgebraicGeometry/Sites/README.md),
[ordinary transfer guide](../../../Transfers/Cohomology/README.md) and
[A1 guide](../README.md) for the separate endpoint boundaries.
