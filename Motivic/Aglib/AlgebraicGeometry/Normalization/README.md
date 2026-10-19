# Normalization and retained compactification charts

These occupied candidates keep the normalization of the original cover,
its actual retained opens and one common coefficient refinement. They are
general scheme geometry; motivic actions consume them downstream.

| Exact import | Interface and retained boundary |
| --- | --- |
| `Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.NormalizedBoundaryChoice` | One normalized thickened boundary for the given original cover, retaining residual and inverse-infinity maps. |
| `Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.Diagrams.OriginalAffineRefinement` | Native coordinate identification with the original coefficient-map domains unchanged. |
| `Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.RetainedUnitDomain` | Factorization of the whole inverse boundary through the original functional unit open. |
| `Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.RetainedTargetChartFrame` | The same target extension frame on the literal inverse retained graph chart. |
| `Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.RetainedMarkedChartProjection` | Marked projection from the actual Cartesian chart and selected inverse-frame factorization. |

The common generic coefficient open is chosen once, followed by one actual
thickened boundary. Scheme-level factors retain nilpotents. A unit-domain range
factorization does not replace the stronger full scheme factors needed for
boundary values or norm equations. The marked projection is derived from the
actual square, rather than supplied as an unrelated scalar normalization.

Generic finite norm and whole-fiber ratio interfaces have the
[finite-morphism owner](../Morphisms/Finite/README.md). Their finite sources
need not be integral; their target and local-free hypotheses remain explicit.
The original source and target frames are preserved through the
[relative-curve data](../RelativeCurve/README.md) and
[invertible-module comparisons](../Modules/Invertible/README.md).

Each interface retains its stated cover, flatness, regularity and boundary
conditions. Intended upstream owner: `Aglib.AlgebraicGeometry.Normalization`.
