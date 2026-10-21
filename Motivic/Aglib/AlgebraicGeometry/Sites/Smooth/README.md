# Smooth sites, Nisnevich neighborhoods and coefficient restrictions

For `S : Scheme.{u}`, `Scheme.SmoothSite S` is the existing
`MorphismProperty.Over` selection of smooth, separated and quasi-compact
structure maps. Morphisms are all scheme maps over `S`. Nisnevich covers use
actual residue-field lifting; original germs and inverse-image comparisons use
the original neighborhood colimits.

Smoothness supplies local finite presentation, and quasi-compactness gives
finite type. Topology proofs use cover-specific pullbacks. Noetherian and
affine hypotheses remain where stated; an arbitrary extension field is not
assumed to define an object of a finite-type site.

| Exact import |
| --- |
| `Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Basic` |
| `Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.IntegralComponents` |
| `Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Affine.Opens` |
| `Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Evaluation` |
| `Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.Basic` |
| `Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.Field` |
| `Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.Endpoints` |

Native interfaces:

- `AlgebraicGeometry.Scheme.SmoothSite`
- `AlgebraicGeometry.Scheme.smoothSeparatedFiniteType`
- `AlgebraicGeometry.Scheme.SmoothSite.nisnevichTopology`

Host consumers are `Motivic.Cor`, `Motivic.SheafWithTransfers` and `Motivic.motivicComplex`.

Intended upstream family: `Aglib.AlgebraicGeometry.Sites.Smooth`. Use exact lower
imports; a current motivating consumer does not change the general hypotheses.
Follow the [candidate policy](../../../README.md) and retain the actual maps and
universes when extending these interfaces.

## Relative affine-line endpoints

`AffineLine.Endpoints` supplies the unchanged native interfaces
`AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite`
and `.endpointMorphism`. For `k : Type u`, `[Field k]` and
`X : SmoothSite (Spec (.of k))`, `relativeLineSite X` is
`SmoothSite.product X (AffineLineField.line k)`;
`endpointMorphism X a : X ⟶ relativeLineSite X` for `a : k` is the actual
endpoint map. Their parameters are only the field, smooth-site object and scalar.
The pure
[relative endpoint support diagram](../../RelativeCurve/Pencils/RelativeEndpointSupportDiagram.lean)
is the lower geometric prerequisite.

`AffineLine.Field` retains the pure native
`AlgebraicGeometry.Scheme.SmoothSite.AffineLineField` helpers for the field
point, parameter line, evaluation, ambient product and component support.
Actual correspondence generators remain in the
[host finite-flat curve family](../../../../AlgebraicGeometry/Correspondences/Spans/FiniteFlat/CurveFamily.lean),
under `Motivic.FiniteFlatCurveFamily`.

## Actual integral components

`IntegralComponents` imports the stable [normality interface](Normal.lean).
For `k : Type u`, `[Field k]`, `X : SmoothSite (Spec (.of k))` and
`hZ : Z ∈ irreducibleComponents X.left`, the native namespace
`AlgebraicGeometry.Scheme.SmoothSite` supplies `integralComponent k X Z hZ`
and its `integralComponent_isIntegral` instance. The object retains the original
component open and its structure morphism.

`integralComponentι k X Z hZ` is the original open-subscheme inclusion into `X`;
`integralComponentι_isOpenImmersion` records its open-immersion property.
These four generic helpers have this one candidate provider. The host
correspondence/component-reassembly source imports it; the existing normality
source and core objects are unchanged.

## Affine open restrictions

[Affine.Opens](Affine/Opens.lean) supplies four native helpers in
`AlgebraicGeometry.Scheme.SmoothSite`. For `k : Type u`, `[Field k]`,
`V : SmoothSite (Spec (.of k))` and `W : V.left.Opens` with
`[IsAffine W.toScheme]`, `affineOpenSite V W` retains the structure map
`W.ι ≫ V.hom`. `affineOpenInclusion V W` is the literal inclusion into `V`,
and `affineOpenInclusion_open` gives its open-immersion instance.

`affineOpenOverlap_affine` additionally takes smooth-site objects `X`, `A`
with `[IsAffine X.left]` and `[IsAffine A.left]`, an arrow `i : A ⟶ X` with
`[Etale i.left]`, and `v : V ⟶ X`. Its conclusion is affineness of the actual
`etalePullback i (affineOpenInclusion V W ≫ v)`, whose underlying scheme is
the corresponding pullback of `i.left` and the displayed composite.

## Native coefficient restrictions and the whole original cylinder

For `k : Type u`, `[Field k]`, affine `U : SmoothSite (Spec k)`, an original
`e : T ≅ a1Cylinder (.of k) U` and three successive affine coefficient opens
`B,O,V`, [AffineLine/CoefficientCartesianSquare](AffineLine/CoefficientCartesianSquare.lean)
defines `nativeOriginalCoefficientMap` and `nativeOriginalLineMap` as literal
composites. `nativeOriginalCoefficient_isPullback` identifies the entire final
native affine line as the Cartesian pullback of the original cylinder along
that original-base map. The
[projective-line affine-square interface](../../ProjectiveLine/Neighborhood/README.md)
provides the lower Cartesian squares; no normalization of a triple product of
ring maps or arbitrary open of the cylinder replaces them.

[NativeOriginalBase](AffineLine/NativeOriginalBase.lean) gives the original
field-structure composites, `nativeOriginalBaseSite`, its open inclusion,
and the final native line object/projection. Nonemptiness uses a retained
point of the final coefficient open. [NativeOriginalLineRestriction](AffineLine/NativeOriginalLineRestriction.lean)
packages the line map as a smooth-site arrow and retains the actual Cartesian
square. [CartesianCylinderIso](AffineLine/CartesianCylinderIso.lean) constructs
the general comparison from that square.
[NativeOriginalCylinder](AffineLine/NativeOriginalCylinder.lean) specializes it:
`nativeOriginalCylinderIso` preserves both the base projection and original
parameter coordinate; `nativeOriginalWholeCylinderMap_comp` states that the
map back to `T`, followed by `e.hom`, is exactly `a1Map` of the original base
inclusion. [OriginalCoefficientRestriction](AffineLine/OriginalCoefficientRestriction.lean)
retains the corresponding ordinary coefficient-open arrow and its literal
line/cylinder coordinates.

[NativeMiddleInput](AffineLine/NativeMiddleInput.lean) gives site constructions
for the same input `N : NativeOriginalMiddleInput k`. With the explicit additional
hypothesis `[Etale N.p]`, `nativeCover_mem_nisnevichTopology` proves membership
of the actual two-arrow sieve after any chosen isomorphism from `N.toInput.siteX`
to its target. It uses the stored open puncture, marked complement and section;
source flatness alone is not substituted for étaleness.

[AffineLine/LocalizationHistory](AffineLine/LocalizationHistory.lean) identifies
the endpoints while `OriginalLocalizationHistory` and its source, boundary and
target witnesses are abstract. For a smooth final coefficient-to-field map `t`,
`SourceWitnesses.toNative_lineSite_eq` identifies the native line with
`SmoothSite.mk (boundaryLineProjection Γ(H.V.toScheme, ⊤) ≫ t)`, and
`SourceWitnesses.toNative_sourceMap_eq` identifies its source map with `H.p₂`.
These equalities are proved before the host specializes its representative
geometry; the generic localization and native-input records remain unchanged.

Genuine source and puncture restriction squares induce smooth-site maps with
the same underlying scheme maps. `parameterRestriction` uses the underlying
identity of `N.delta`, and `nativeTransport_compatible` derives the five stored
compatibility equations from the two supplied restriction squares against one
line map. It does not compare independently rebuilt sites or assert those
restriction squares without proof. The application to original representatives
and their whole-cylinder lift remains in the host layer.

[AffineLine/NativeCover](AffineLine/NativeCover.lean) constructs the original
source and puncture before specializing their coefficient data. Over a native
`R : CommRingCat.{u}` and two affine coefficient opens,
`originalAffineRefinedSourceScheme` and `originalAffineRefinedPunctureScheme`
retain the actual restricted schemes; their `Map` declarations retain the two
literal `sourceNativeCoverMap` restrictions. Affineness and étaleness are proved
for those schemes and maps before constructing smooth-site objects. The
`originalAffineRefinedSourceSite` and `originalAffineRefinedPunctureSite`
adapters use a smooth separated quasi-compact structure map from the final line
to the chosen base scheme. They retain the first original restriction, its
coordinate isomorphism and the source's original containment witness. The source
adapter requires the original étale map and affine chosen source open; the
puncture adapter requires an affine original puncture and its open immersion.
`affineEtaleOverArrow` packages the literal map over the actual target site
object, and its composite lemmas retain the underlying map and étaleness after
the chosen target isomorphism.

The same provider composes restriction squares and constructs their morphisms
over the base. [Nisnevich/OriginalNativeCover](Nisnevich/OriginalNativeCover.lean)
proves the resulting cover using the original closed complement and Cartesian
marked lift, followed by the specified target isomorphism. The host source,
puncture and cover declarations specialize these interfaces without changing
their maps or adding a lifting assumption.

For nested coefficient data, prove the construction and its properties over
the native ring object first. At specialization, use the final line's stored
smoothness, separatedness and quasi-compactness proofs rather than searching
again through the coefficient tower. Infer the constructed arrow before
composing it with the cylinder isomorphism so that the concrete goal does not
drive elaboration of its generic arguments.

## Field lifting after both coefficient restrictions

[Nisnevich/NativeCoefficientCover](Nisnevich/NativeCoefficientCover.lean)
retains the original puncture and source coordinates under both restrictions.
In [NativeCoefficientFieldLifting](Nisnevich/NativeCoefficientFieldLifting.lean),
`nativeCoefficientCover_field_lifting` says that every `Spec K` point of the
final native line lifts either through its actual puncture or through its
actual source. Its data are a commutative ring `R : Type u`, two affine
coefficient opens, an open puncture, a closed marked complement and the
original marked section through the source map. This field-lifting assertion
omits source étaleness and affineness. The topology theorem
`nativeCoefficientCover_mem_nisnevichTopology` retains the affine source and
puncture, étale source map and a smooth separated quasi-compact structure
map of the final line to `Spec k`; it concludes membership of the literal
two-arrow sieve in the smooth Nisnevich topology. The
[host refined-cover consumer](../../../../Transfers/Presheaf/Actions/README.md)
binds these arrows to the original whole cylinder and representative restrictions.
Its action-lifting conclusion uses those additional host interfaces.
