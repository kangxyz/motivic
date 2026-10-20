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

## One original localization history and native input

[OriginalLocalizationHistory](Compactification/RelativeAffineLine/OriginalLocalizationHistory.lean)
works in `AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification`.
`OriginalLocalizationSeed` retains a normal Noetherian coefficient domain,
the original affine étale quasi-compact separated source, affine open puncture,
closed marked complement finite over the coefficient base, and its section and
Cartesian marked square. `OriginalLocalizationHistory` fixes the same two
affine coefficient opens and original square equations. Its boundary, source
and target witness interfaces retain the full thickened boundary, free charts
and actual original sections; packaging them does not make another choice.

[NativeOriginalMiddleInput](Compactification/RelativeAffineLine/NativeOriginalMiddleInput.lean)
owns the native geometric input, its single `toInput` specialization, and the
original `aSite` and `delta` maps.
[OriginalLocalizationInput](Compactification/RelativeAffineLine/OriginalLocalizationInput.lean)
provides `SourceWitnesses.toNative` using the same history and witnesses.
`SourceWitnesses.toNativeAncestry` retains the literal two source and puncture
open inclusions and one common coefficient-line composite, with both coordinate
squares proved for that composite. These are general geometric interfaces;
transfer actions and the final sheafification theorem belong to their host
consumers, not to this package.

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

The generic predicate
[`AlgebraicGeometry.ProjectiveSpace.SourceTargetFullBoundaryAffineAmbients`](../ProjectiveSpace/Boundary/SourceTargetFullAffineAmbients.lean)
records two successive nonzero coefficient localizations and actual affine
source/target opens containing the entire pulled-back boundary schemes, with
literal factorization equations. The boundaries retain their nilpotents.

[FixedThickenedBoundaryAffineAmbients](Compactification/RelativeAffineLine/FixedThickenedBoundaryAffineAmbients.lean)
supplies `fixedThickenedBoundary_fullBoundary_affineAmbients`. It takes the
original normal Noetherian domain, étale quasi-compact separated cover, closed
finite marked scheme, section and Cartesian marked square, together with an
already supplied affine coefficient open `O`, a point of `O`, and a whole
closed boundary `d'` finite over that coefficient base and disjoint from the
actual marked section. It derives closedness and finite projection of the
source and target full coproduct boundaries, then invokes the lower
source/target affine-ambient supplier. It chooses no finite/free restriction,
normalization, thickening, factor, section, or frame again.

The supplied point proves that `Γ(O)` is a domain; it is not asserted to
survive the subsequent localizations. Both returned elements are nonzero,
so the composite coefficient open is nonempty. Its intersection with another
already chosen nonempty coefficient open is nonempty by irreducibility.
Transport of previously chosen factors and free-chart witnesses through the
literal nested pullbacks remains a separate obligation.

[ThickenedBoundaryAffineAmbients](Compactification/RelativeAffineLine/ThickenedBoundaryAffineAmbients.lean)
delegates its geometric tail to this fixed-witness theorem.

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

## Native fiber dimension on the same coefficient opens

[CoefficientFiberDimension](Compactification/RelativeAffineLine/CoefficientFiberDimension.lean)
supplies `originalCoefficient_fiber_component_dimension` and
`finalCoefficient_fiber_component_dimension` in
`AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification`.
They retain the exact hypotheses of `CoefficientFlat`: a commutative
`R : Type u`, a finite projective-line map `f`, the fixed `r`, affine open
`O ≤ D(r)`, and the whole localized free-chart witnesses. The final theorem
uses the already selected affine open `V` of `Spec Γ(O.toScheme, ⊤)`.

For the first map, the structural projection is literally
`pullback.fst O.ι (f ≫ ProjectiveSpace.toSpec R (ULift (Fin 2)))`. For the
final map it is `pullback.fst V.ι (F ≫ ProjectiveSpace.toSpec Γ(O.toScheme, ⊤)
(ULift (Fin 2)))`, where `F := boundaryBaseProjectiveMap R (ULift (Fin 2)) f O`.
For any base point and any actual irreducible component `Z` of the native
fiber of either projection, the conclusion is `topologicalKrullDim Z = 1`.
The [projective-line fiber theorem](../ProjectiveLine/README.md) uses the
actual residue field and the original structural equations.

No coefficient open, normalization, thickened boundary, or section is
chosen again. No nonempty, connected, reduced, smooth, or positive-rank
source premise is added. Empty fibers have no irreducible component to
check. With `f := toProjectiveLine R p`, the original `projection R p` is
the same displayed composite by its definition. These theorems do not
assemble retained smoothness, properness, normality, the full affine boundary,
or the chosen splitting into a complete standard triple.

## Normal stalks on the same compactification restrictions

[NormalStalks](Compactification/RelativeAffineLine/NormalStalks.lean) supplies
`compactification_normalStalks`, `originalCoefficient_normalStalks`, and
`finalCoefficient_normalStalks` in
`AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification`.
For a commutative normal Noetherian domain `R : Type u` and an étale,
quasi-compact `p : Y ⟶ Spec R[t]`, the actual constructed compactification
has `Scheme.NormalStalks`. This means every actual stalk is an integrally
closed domain; it does not assert that the whole source is integral.
The stalk theorem does not require source separatedness or nonemptiness.

The first restriction is literally `pullback O.ι (projection R p)`, with
arbitrary coefficient open `O`. For affine `O`, put
`F := boundaryBaseProjectiveMap R (ULift (Fin 2)) (toProjectiveLine R p) O`.
The final restriction is literally `pullback V.ι (F ≫ toSpec Γ(O.toScheme, ⊤) _)`,
with arbitrary already selected open `V` of `Spec Γ(O.toScheme, ⊤)`.
No affine `V`, generic point, free-chart witness, or new coefficient choice is
needed for these normality statements.

The proofs use the original `EtaleCompactification.genericCover` and the
[normality inheritance extension](../Properties/Normal/README.md) along the
actual open-immersion projections. They do not re-normalize, infer normality
of residue-field fibers, or assemble a complete standard triple.

## Standard-triple geometry on one twice-localized witness

[TwoLocalizationStandardTripleGeometry](Compactification/RelativeAffineLine/TwoLocalizationStandardTripleGeometry.lean)
supplies `twoLocalization_standardTriple_geometry`. The native literal layout
is described in the [two-localization guide](../ProjectiveLine/BaseChange/README.md).
The theorem takes the original normal Noetherian domain, separated quasi-compact
étale affine-line map, full closed finite marked scheme and its Cartesian
section square. It retains the same affine coefficient open `O`, a point of
`O`, original free-chart witnesses, two nonzero localization elements, original
closed finite boundary `d`, and its full complementary-range identity. It then
consumes the exact already selected affine open `U` and the whole nested
coproduct-boundary factor through `U`.

On that ONE literal final compactification, the conclusion gives:

- a finite flat map to the final projective line and a proper flat base
  projection whose native fiber components all have dimension one;
- normal total-space stalks and a nonempty affine coefficient base;
- a smooth base over the supplied field, using the original `[Smooth t]`;
- the literal retained open, smooth of relative dimension one, smooth over the
  field, and quasi-affine via the affine projection to the original source;
- the two direct full boundary pullbacks, each closed and finite over the base,
  with the original boundary exactly complementary to the retained open and
  disjoint from the marked boundary;
- factorizations of BOTH full boundaries through the SAME affine open `U`.

Closedness and finiteness of the original source marking are derived from its
Cartesian square, the finite target marking, and the actual compactification;
they are not new final-property premises. The original complement identity
must be retained from the same thickened-boundary witness: the affine-ambient
supplier alone does not imply it. The final boundaries keep their nilpotents.
Only the base is proved nonempty; an empty source is permitted and its
fiber-component assertion is vacuous. The original chosen point is not claimed
to survive either localization.

Supplied historical records report selected production compilation on
2026-10-19 for the structure-map flatness, generic boundary geometry and
conjunction providers. Current-pin integration coverage is recorded in the
[sheafification provenance](../../../../docs/provenance/hi-presheaf-sheafification-20261020/README.md).
This is a deterministic fixed-witness theorem, not a repeated existential
construction. Marked-product frame specialization and its joint packaging with
these same witnesses remain distinct from the non-frame geometric theorem.
