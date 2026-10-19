# AlgebraicGeometry / Sites / Smooth

The existing MorphismProperty.Over selection of smooth, separated, quasi-compact structural maps, with all maps over the base. Nisnevich covers use actual residue-field lifting. Generic original germs and inverse-image comparisons use the original neighborhood colimits.

Smooth implies locally finite presentation; quasi-compactness supplies finite type. Topology proofs use cover-specific pullbacks, not arbitrary pullbacks in the smooth category. Noetherian/affine guards remain where present; no arbitrary field-extension object assumption.

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
