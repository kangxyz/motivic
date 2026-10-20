# Original section choices, norm diagrams and normalized units

## Simultaneous original sections and parameter diagrams

[Common/OriginalOverlapSectionChoice](Common/OriginalOverlapSectionChoice.lean)
defines `OriginalOverlapCommonSections` in
`AlgebraicGeometry.Scheme.RelativeCurvePencil`.
`exists_originalOverlap_common_boundary_sections` chooses one affine coefficient
open containing the prescribed point inside the prescribed open, together with
source `NativeSourceBoundarySections` and target `NativeTargetBoundarySections`.
It retains the original étale overlap, affine puncture, finite projective map,
Cartesian marked square, exact complements and finite thickened boundary.
The normalization constructor that supplies this fixed geometry is documented
in the [normalization guide](../../Normalization/README.md).

[Data/OriginalMiddleInput](Data/OriginalMiddleInput.lean) owns
`AlgebraicGeometry.Scheme.RelativeCurvePencil.OriginalMiddleInput`: the complete
original schemes, maps, `BoundarySectionData` and target sections, with five
smooth sites and their `pSite`, `wSite` and `uSite` maps. It contains no transfer
action or lifting conclusion.
[Correction/OriginalTargetSectionWitnesses](Correction/OriginalTargetSectionWitnesses.lean)
owns `OriginalTargetSectionWitnesses` in
`AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification`.
Its eight fields retain the original line bundle, section pair, finite-flat
divisors, full-boundary frame equation and both units.
`nonempty_originalTargetSectionWitnesses` packages the existing target supplier
without choosing a second pair. The general consumers are
`NativeOriginalMiddleInput` and `OriginalLocalizationHistory` in the
[normalization family](../../Normalization/README.md).

[Norm/OriginalRetainedNormMaps](Norm/OriginalRetainedNormMaps.lean)
uses the native `Scheme.Hom.normProductMap` for the finite map on the second
factor. Its retained-source/target square commutes; it is not declared Cartesian
merely from that commutation. [OriginalNormParameterChart](Norm/OriginalNormParameterChart.lean)
constructs the separate genuine first-parameter Cartesian square and
`normProductParameterChartIso`, preserving the original whole finite source
and scalar map. [OriginalNormParameterGenericRatio](Norm/OriginalNormParameterGenericRatio.lean)
and [OriginalNormParameterTargetMap](Norm/OriginalNormParameterTargetMap.lean)
identify the original ratio norms and target composites in these presentations.
[OriginalPairNormDiagram](Norm/OriginalPairNormDiagram.lean) indexes the
source finite leg and target identity leg by `Fin 2`;
[OriginalPairNormSectionData](Norm/OriginalPairNormSectionData.lean)
projects the same `BoundarySectionData` and target pair into that dependent
family. [OriginalPairNormBoundaryUnits](Norm/OriginalPairNormBoundaryUnits.lean)
retains its infinity units and covers. These are scheme/section interfaces;
finite correspondences enter in the host action family.

## Regularity and the uniquely determined graph-association unit

[Boundary/SectionPairNormUnit](Boundary/SectionPairNormUnit.lean)
extends the stable `SectionPairNormIdeal` provider in the native namespace
`AlgebraicGeometry.Scheme.RelativeCurvePencil`.
`sectionPairTargetFrameOnChart_scalar_regular` proves `IsSMulRegular Γ(W,⊤)`
for the transported original target graph coefficient. Its context retains a
separated `π`, the target open smooth relative curve `jA`, flat retained map
`p`, the actual retained-map equation, target line bundle and numerator/pole,
their displayed local-unit conditions on `vA`, and the lift equation `hl`.
It additionally requires that the actual chart `w` is an open immersion.
It omits finiteness of `f`, openness of `jB` and source relative smoothness;
`W` need be neither affine nor integral. The proof pulls the graph ideal
inclusion through the flat open chart, rather than through a closed marked map.

`sectionPairGraph_norm_association_unique` retains the finite source map,
source open smooth relative curve, both original source section units on the
whole inverse chart, the target data above, affine `W`,
`IsDomain Γ(W,⊤)` and freeness of the entire chart algebra over `Γ(W,⊤)`
through its displayed scalar map. It concludes that there is exactly one
`u : Γ(W,⊤)ˣ` satisfying `N(cB) = u cA` for the original graph coefficients.
The regular target coefficient gives cancellation. Residual-summand freeness
and a source function field are not added. This extension currently has no
direct import consumer; the existing association API retains its provider.

## R3 on the exact original good open

Write `cA,cB` for the original graph-ideal twists of the pole sections `bA,bB`;
then `aA/cA` and `aB/cB` use sections of the same respective line bundles.
[Norm/SectionPairNormNeighborhood](Norm/SectionPairNormNeighborhood.lean)
defines `sectionPairNormUnitDomain` using the unit loci of the four original
sections `aA,bA,aB,bB`. The graph coefficients need not be units on the marked
boundary. `sectionPairNormUnitDomain_exists_normalized_ratio` constructs a unit
on this exact nonempty open with original generic germ

`R3 = N(aB/cB) / (aA/cA)`.

Its hypotheses retain the separated target projection, finite `f`, both open
smooth relative curves, flat retained map and literal retained-map equation;
the Cartesian marked square, its actual graph-ideal frame and closed target
marked immersion; the prescribed source/target full-boundary section equations
and units; the residual and inverse-infinity factor maps; affine target-boundary
map; a covering family with the entire finite chart algebras free; and integral
ambient parameter product. Six explicit `Mono` inputs concern the original
numerator, graph-twisted pole and pole functionals on both sides. The conclusion
includes an actual factor of `normFullBoundaryMap` through that open and the
section equation `E.app V R3 = 1` on the whole marked-plus-infinity boundary.
The same graph-association unit is used on both components; its inverse gives
R3. [SectionPairNormSpec](Norm/SectionPairNormSpec.lean),
[SectionPairNormalizedUnit](Norm/SectionPairNormalizedUnit.lean) and
[SectionPairTargetGenericRatio](Norm/SectionPairTargetGenericRatio.lean)
retain the original scalar transport, marked cancellation and generic ratios.

[SectionPairNormParameterNeighborhood](Norm/SectionPairNormParameterNeighborhood.lean)
supplies `sectionPairNormParameter_exists_normalized_ratio` for an integral
open first-parameter component. Its whole-source chart/pasting isomorphisms
retain the original finite source and scalar map, with the corresponding six
pulled-functional monicity hypotheses.
[NativeSectionPairParameterComponents](Norm/NativeSectionPairParameterComponents.lean)
constructs a finite affine integral-component cover from the actual normal
stalks of `finalOriginalSource`; an empty source has an empty cover.
[NativeSectionPairNormalizedUnit](Norm/NativeSectionPairNormalizedUnit.lean)
supplies the component version from the original normal Noetherian coefficient
domain, fixed source record, target Serre divisor data, prescribed full-boundary
frames, exact factors and original free charts. It derives the needed
regularity and integral component-parameter product. No integral-whole-source
premise replaces this component construction.

## R5 and the unchanged correction boundary

[Correction/NormalizedUnit](Correction/NormalizedUnit.lean)
supplies `exists_originalCorrectionNormalizedUnit` with generic germ

`R5 = (aA/cA) N(n/d)`.

Here `n,d` are the original correction sections and `cA` is the original
target graph twist. The good open is the literal
`functionalNormProductUnitDomain` of those four functionals. In addition to the
original retained-map, flat parameter-map and marked-square data, the theorem
keeps the correction and target prescribed-boundary equations and unit inputs,
closed target marked immersion, affine target-boundary map, residual and
inverse-infinity factors and entire finite free chart cover. It explicitly
requires integral parameter product and monicity of the four functionals.
The output is a unit, its original generic germ, the full boundary factor,
and value one on that full scheme boundary. Scalar restriction and coproduct
section detection prove this last equality; support containment only supplies
factorization through the open.

[FunctionalUnitBoundary](Correction/FunctionalUnitBoundary.lean) supplies
`normProductMap_preimage_boundary_subset_sectionUnitOpen` from the actual
finite map, residual/inverse-infinity factors and original correction-section
unit. This lower containment theorem needs neither openness of `j` nor
closedness of `z ≫ jA`. `originalCorrectionNorm_boundary_subset_goodOpen`
likewise omits those two unused classes while retaining its displayed
section/frame equations and original maps. The normalized-unit constructor
above retains its own complete hypotheses.

[NativeCorrectionNormalizedUnit](Correction/NativeCorrectionNormalizedUnit.lean)
derives the regularity and integral normal parameter product from the same
`BoundarySectionData`, target Serre divisor data, actual cover/factors/free
charts and a nonempty original affine puncture over a normal Noetherian domain.
[NativeTargetCorrectionSections](Correction/NativeTargetCorrectionSections.lean)
and [NativeCorrectionBoundaryFactors](Correction/NativeCorrectionBoundaryFactors.lean)
retain the original target section choice and boundary maps.
[OriginalCorrectionNormDiagram](Correction/OriginalCorrectionNormDiagram.lean)
provides the two-pair finite/identity diagram;
[OriginalCorrectionActionGeometry](Correction/OriginalCorrectionActionGeometry.lean)
keeps its general schemes and smooth-site maps in native `Scheme.Hom` and
`Scheme.RelativeCurvePencil` namespaces. The
[host action guide](../../../../Transfers/Presheaf/Actions/README.md) records the
separate transfer conclusions and whole-cylinder assembly.
