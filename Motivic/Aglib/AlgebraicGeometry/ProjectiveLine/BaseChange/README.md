# Literal two-localization geometry

`TwoLocalizations.lean` uses the native namespace
`AlgebraicGeometry.RelativeProjectiveLine.TwoLocalizations`. For a commutative
ring `R : Type u`, elements `r : R`, `s : Localization.Away r`, and
`F : C ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))`, it preserves the exact nested
pullbacks returned by `ProjectiveSpace.SourceTargetFullBoundaryAffineAmbients`.
No nonzero condition is required by this transport API.

## Objects and maps

The parameter order is `R r s F`; declarations independent of `s` or `F` omit
that parameter. All object and map names below are abbreviations of the native
maps, not a replacement structure.

- `firstMap R r` and `secondMap R r s` are the two projective coefficient maps.
  Their composite is `projectiveBaseMap R r s`.
- `baseMap R r s` is the literal composite of the two affine localization maps.
- `firstSource R r F := pullback F (firstMap R r)` and
  `firstProjection R r F := pullback.snd F (firstMap R r)`.
- `target R r s := pullback (𝟙 _) (secondMap R r s)`. Its projections are
  `targetMap` and `targetIsoMap`; the latter is the canonical identity-pullback
  isomorphism, with the proved equation `targetIsoMap ≫ secondMap = targetMap`.
- `source R r s F := pullback (firstProjection R r F) (targetMap R r s)`.
  Its projections are `sourceFirstMap` and `sourceTargetMap`.
- `sourceMap` is the composite restriction to `C`; `toProjectiveLine` is
  `sourceTargetMap ≫ targetIsoMap`; `projection` is the latter map followed by
  the final projective-line structural morphism.

`projectiveSquare` and `baseSquare` prove the two Cartesian squares by pasting
the actual pullbacks and `ProjectiveSpace.isPullback_map`. Their equations are
`sourceMap_toProjectiveLine` and `sourceMap_projection`. They do not assume a
Cartesian comparison or identify this source with an independently selected
coefficient-open presentation.

## Geometry and hypotheses

The actual `sourceMap` is an open immersion and affine. Finiteness and flatness
of `F` separately give the corresponding properties of `toProjectiveLine`.
Finiteness gives properness of `projection`; this structural map is not asserted
finite. The theorem `normalStalks` consumes normal stalks of the original `C`
and transports them along the actual open restriction. The theorem
`fiber_component_dimension` consumes `[IsFinite F] [Flat F]` and proves
`topologicalKrullDim Z = 1` for every irreducible component `Z` of each literal
native fiber of `projection`.

The actual specialization is
`Normalization/Compactification/RelativeAffineLine/TwoLocalizationGeometry.lean`.
Its ring is a normal Noetherian domain, `p` is the original quasi-compact étale
affine-line map, and `O` is the already chosen affine coefficient open. The
three theorems are:

- `twoLocalization_normalStalks`, supplied by the constructed normalization's
  `originalCoefficient_normalStalks`, without a new normality premise;
- `twoLocalization_projectiveMap_flat`, supplied by the original `r`,
  `O ≤ basicOpen r`, and whole-chart freeness for the exact `scalarMap` in its
  signature;
- `twoLocalization_fiber_component_dimension`, using those same witnesses.

These statements require neither a nonempty source, positive rank, fiber
surjectivity, source integrality, nor reduced boundaries or fibers. Empty-source
component conclusions are vacuous. The two pasted squares and finite/open/proper
instances apply directly to the same actual map.

These leaves provide the literal layout and its normality, flatness and fiber
component statements. Retained-open smoothness and quasi-affineness, full-boundary
factorization and marked-product frames use the separate interfaces below.

## Retained source and smooth base

`TwoLocalizationRetained.lean` extends the same namespace and parameter order
with a supplied map `j : Y ⟶ C`:

- `retainedSource R r s F j := pullback j (sourceMap R r s F)`;
- `retainedInclusion` and `retainedSourceMap` are respectively its second and
  first projections;
- `retainedProjection := retainedInclusion ≫ projection`.

`retainedBaseSquare` is the proved Cartesian square with top map
`retainedSourceMap`, left map `retainedProjection`, right map
`j ≫ (F ≫ ProjectiveSpace.toSpec R _)`, and bottom map `baseMap`.
The inclusion is open when `j` is open. The first projection is affine and open
without that hypothesis. Relative smooth dimension one is transported through
the square. `retainedSource_quasiAffine` uses the AFFINE first projection and
original quasi-affineness, preserving quasi-compactness; it does not assert that
an arbitrary open of a quasi-affine scheme is quasi-affine.

The actual supplier is
`Normalization/Compactification/RelativeAffineLine/TwoLocalizationRetainedGeometry.lean`.
Its `twoLocalization_retained_open` and
`twoLocalization_retained_quasiAffine` retain the original separatedness of `p`.
The latter constructs original quasi-affineness from
`isQuasiAffine_of_etale_affine_target p`, then proves that the original affine
coefficient restriction is affine before applying the final affine projection.
`twoLocalization_retained_smooth` derives the original relative smoothness from
the etale affine-line map and the same first coefficient open.

For the supplied `t : Spec R ⟶ Spec k`, the exact
`twoLocalizationFieldMap R O a b t` is
`baseMap Γ(O,⊤) a b ≫ O.isoSpec.inv ≫ O.ι ≫ t`.
`twoLocalization_base_smooth` requires `[Smooth t]`.
`twoLocalization_retained_field_smooth` combines that result with retained
relative smoothness. Neither uses normality as a substitute for smoothness, and
neither smoothness theorem needs separatedness. No new geometric choices or
nonemptiness premises occur. Marked-product frame coherence remains a separate
consumer of this literal retained layout.

## Whole marked products and restricted graphs

[TwoLocalizationMarked](TwoLocalizationMarked.lean) adds a supplied original
marking `z : Z ⟶ Y` to the same parameters `R r s F j`.
`markedSource := pullback (z ≫ j) sourceMap` retains the full marked scheme;
`markedLift` maps it to the literal retained source. `markedProductMap` retains
both original projections, and `markedProductSquare` proves its Cartesian
square. The product map is open and flat, and `markedGraphSquare` retains the
restricted original graph. These comparisons require no nonzero localization,
nonempty source, reducedness, smoothness or finiteness premise.

The [marked-frame interface](../../Modules/Invertible/README.md) consumes these
same maps with its supplied original frame and additional geometric hypotheses.
Its coordinate equations are separate from the smoothness and quasi-affineness
statements above.

## Full boundaries, flat projection, and nonempty base

`TwoLocalizationBoundaryGeometry.lean` adds deterministic transport on the same
literal layout. `projection_flat` composes the flat finite-map input with
`RelativeProjectiveLine.toSpec_flat`, proved separately in
`Charts/FlatStructure.lean` using the two actual polynomial charts over any
commutative ring. Flatness is not inferred from fiber dimension or properness.

`boundary_projection_finite` uses the pasted native base square.
`boundary_range_eq_compl` transports the supplied original full complement
identity, and `boundary_disjoint` transports disjointness by preimage.
Neither changes the scheme structure of a boundary. `nonempty_base` assumes
`[IsDomain R]`, `r ≠ 0`, and `s ≠ 0`, and proves that the twice-localized base
spectrum is nonempty. There is no nonempty-source premise.

The actual consumer is
[TwoLocalizationStandardTripleGeometry](../../Normalization/Compactification/RelativeAffineLine/TwoLocalizationStandardTripleGeometry.lean).
It gives the non-frame geometric conjunction on one already selected witness;
it does not combine independently chosen boundaries or affine ambients.
Historical selected-compilation reports and current-pin integration coverage
belong to the [sheafification provenance](../../../../../docs/provenance/hi-presheaf-sheafification-20261020/README.md).
