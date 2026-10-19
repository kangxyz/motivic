# Canonical contraction-to-boundary maps

This family retains the actual original-presheaf contraction-to-boundary
morphism. Coefficient-section dense-open Mono is a different morphism.
Sheaf cokernels are genuine sheaf colimits, not asserted to be objectwise
cokernels. Use the original maps and their comparison proofs.

| Exact import | Interface and conditions |
| --- | --- |
| `Motivic.Cohomology.A1.Boundary.Presheaf.Contraction.Epi` | The genuine Epi for original HI presheaves with transfers over infinite fields |
| `Motivic.Cohomology.A1.Boundary.Presheaf.FiniteFieldEpi` | The genuine Epi over finite fields for arbitrary original HI `PresheafWithTransfers.{u+1}`; no `HasExt`, transfer-sheaf or supplied geometry-family premise |

The transfer-presheaf application interfaces retain the host namespace
`Motivic.FiniteEtaleSite.OriginalPresheaf`:
`contractionToBoundary_epi` supplies the infinite-field branch and
`contractionToBoundary_epi_of_finite` supplies the finite-field branch.
The generic site object itself is
`AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType`. General site geometry remains in the
[candidate site family](../../../Aglib/AlgebraicGeometry/Sites/README.md);
HI transfer specialization stays host.

[Perfect-field strict invariance](../README.md) combines both cardinalities,
actual local-zero suppliers and lower-degree induction over all HI
coefficients, including their actual contractions. Its puncture-Mono family
is constructed. Earlier conditional rank interfaces retain their own inputs.
The [Cartier higher-image theorem](../HigherImages/README.md) continues to state
its original current-degree HI and boundary-Epi assumptions.
