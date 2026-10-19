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

## A normalization and section choice on the original overlap

[Compactification/RelativeAffineLine/OriginalSectionChoice](Compactification/RelativeAffineLine/OriginalSectionChoice.lean)
works in `AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification`.
For a commutative normal Noetherian domain `R : Type u`, an affine source
`Y`, an étale quasi-compact separated `p : Y ⟶ Spec R[t]`, a closed marked
scheme finite over `Spec R`, its section through `p`, and an affine open
puncture with exact marked complement and Cartesian marked square,
`exists_normalizedOriginalSectionChoice` constructs
`NormalizedOriginalSectionChoice`. This proposition records one nonzero
localization element, whole finite free projective charts, one affine generic
coefficient open, one closed thickened complement, and actual factors of the
old infinity, residual marked fiber and inverse infinity into it. It then
supplies one simultaneous source/target section choice on the fixed overlap
and puncture. Those sections are conclusions of the constructor.

[CoefficientFreeCharts](Compactification/RelativeAffineLine/CoefficientFreeCharts.lean)
transports the entire free chart algebras through the original and final
coefficient localizations, preserving the literal scalar maps.
[CoefficientNormalDomain](Compactification/RelativeAffineLine/CoefficientNormalDomain.lean)
proves `originalCoefficientRing_properties` and
`finalCoefficientRing_properties`: the displayed affine coefficient opens
have domain, integrally closed and Noetherian section rings when they retain
the specified points. The retained points supply nonemptiness without another
coefficient shrink.

[NativeComplement](Compactification/RelativeAffineLine/NativeComplement.lean)
transports the exact original marked-complement identity to the native
puncture. [RestrictedSourceInclusion](Compactification/RelativeAffineLine/RestrictedSourceInclusion.lean)
defines `finalOriginalSource`, its original compactification inclusion and
stalk isomorphism through the two actual coefficient restrictions. This is
the source used by the
[pencil component and normalized-unit constructors](../RelativeCurve/Pencils/README.md),
including when it is empty. The
[representative consumer](../../../Transfers/Presheaf/Sheafification/README.md)
binds this same normalization and section choice to the original sections of
the sheafification image. A normalization record alone does not supply the
whole-cylinder lift or the later common-witness action assembly.

## Flatness on the same coefficient opens

[CoefficientFlat](Compactification/RelativeAffineLine/CoefficientFlat.lean)
supplies `originalCoefficient_projectiveMap_flat` and
`finalCoefficient_projectiveMap_flat` in
`AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification`.
For a commutative `R : Type u`, finite projective-line map `f`, a fixed
`r : R`, an affine open `O ≤ D(r)` and the original free chart witnesses
over `Localization.Away r`, these prove flatness of the literal first
coefficient map and its restriction to the already selected affine final
open `V`. These two assertions require neither a new coefficient choice nor
an additional domain, nonzero-`r` or positive-rank premise. They apply the
[whole-chart flatness theorem](../ProjectiveLine/README.md); they assert no
fiber comparison or complete standard-triple structure.

## Affine ambients for the full thickened boundaries

[ThickenedBoundaryAffineAmbients](Compactification/RelativeAffineLine/ThickenedBoundaryAffineAmbients.lean)
defines `AlgebraicGeometry.ProjectiveSpace.SourceTargetFullBoundaryAffineAmbients`.
It records two successive nonzero coefficient localizations and actual affine
source/target opens containing the entire pulled-back boundary schemes, with
literal factorization equations. The boundaries retain their nilpotents.

For a normal Noetherian coefficient domain, an étale quasi-compact separated
source over `Spec R[t]`, a closed marked scheme finite over `Spec R`, its
original section and Cartesian marked square,
`exists_originalThickenedBoundaryAffineAmbients` constructs
`OriginalThickenedBoundaryAffineAmbients`. This retains the original free
charts, generic coefficient open, closed thickened complement and residual /
inverse-infinity factors, then adds both affine ambients. It works before
any simultaneous section choice and assumes no nonempty source or positive
rank. The resulting affine-ambient evidence does not itself supply the
later common-witness action or whole-cylinder assembly.
