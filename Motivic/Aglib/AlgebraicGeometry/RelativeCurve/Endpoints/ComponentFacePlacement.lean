/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeEndpointFiberGenerics
public import Motivic.Aglib.AlgebraicGeometry.BaseChange.PolynomialFiber
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Affine.LineCoordinates
public import Motivic.Aglib.AlgebraicGeometry.Cycles.FiniteCurve.Faces.FiniteDominantFaceCurvePlacement
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyUnitOpen

/-!
# The original component face maps back to its retained curve

The map is constructed from the existing whole-fibre isomorphism, not supplied
as a closed immersion. Canonical affine-cylinder coordinates supply its actual
evaluation square. Going down and the original generic-fibre stalk map give
coheight one for every nonzero pushed whole-face coefficient.


Intended upstream module: `Aglib.AlgebraicGeometry.RelativeCurve.Endpoints.ComponentFacePlacement`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.WholeComponentFiberProjection`,
`Motivic.AlgebraicGeometry.Correspondences.Endpoints.FinitePoint.SupportGraphProjection`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCurve AlgebraicGeometry.PrincipalFamilyUnitOpen
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
    AlgebraicGeometry.PolynomialOpenQuotient
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram

section OriginalMap

variable {k : Type u} [Field k] {V D : Scheme.{u}}
  (p : V ⟶ Spec (.of k)) (d : D ⟶
      _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLine p) (a : k)

/-- The whole original scalar face maps to the unchanged retained curve. -/
def componentFaceCurveMap : fiber
    (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.familyParameter p d) a ⟶ V :=
  (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeFiberIso p d a).inv ≫
      pullback.fst (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.endpoint p a) d

@[reassoc]
theorem componentFaceCurveMap_endpoint :
    componentFaceCurveMap p d a ≫
        _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.endpoint p a =
      fiberInclusion
          (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.familyParameter p d) a ≫
          d := by
  simp only [componentFaceCurveMap, Category.assoc, pullback.condition]
  have h :=
      (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeFiber_isPullback p d
      a).isoPullback_inv_snd
  simpa only [_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeFiberIso,
      fiberInclusion, Category.assoc] using
    congrArg (fun g => g ≫ d) h

@[reassoc]
theorem componentFaceCurveMap_projection :
    componentFaceCurveMap p d a =
      fiberInclusion
          (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.familyParameter p d) a ≫
          d ≫
        pullback.fst p (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line k).hom := by
  have h := congrArg (fun g => g ≫ pullback.fst p
      (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line k).hom)
    (componentFaceCurveMap_endpoint p d a)
  simpa only [Category.assoc,
      _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.endpoint_fst,
      Category.comp_id] using h

instance [IsClosedImmersion d] : IsClosedImmersion (componentFaceCurveMap p d a) := by
  unfold componentFaceCurveMap
  infer_instance

end OriginalMap

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k))) [IsAffine X.left]

attribute [local instance]
  _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates.sectionsAlgebra

/-- The canonical affine-cylinder coordinates preserve the original base map. -/
theorem affineLineIso_inverse_projection :
    (affineLineIso X).inv.left ≫ Spec.map (CommRingCat.ofHom
      (Polynomial.C : Γ(X.left, ⊤) →+* Polynomial Γ(X.left, ⊤))) =
      pullback.fst X.hom (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line k).hom ≫
          (affineIso X).inv.left := by
  apply (cancel_epi (affineLineIso X).hom.left).mp
  have h := congrArg (fun g => g.left)
    (SmoothSite.a1Map_projection (.of k) (affineIso X).hom)
  change (SmoothSite.a1Map (.of k) (affineIso X).hom).left ≫
      pullback.fst X.hom (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line k).hom =
      pullback.fst (Spec.map (CommRingCat.ofHom (scalarMap X)))
        (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line k).hom ≫ (affineIso
            X).hom.left at h
  have hid := congrArg (fun g => g.left) (affineLineIso X).hom_inv_id
  have hid' := congrArg (fun g => g.left) (affineIso X).hom_inv_id
  change (affineLineIso X).hom.left ≫ (affineLineIso X).inv.left = 𝟙 _ at hid
  change (affineIso X).hom.left ≫ (affineIso X).inv.left = 𝟙 _ at hid'
  rw [← Category.assoc, hid, Category.id_comp]
  change _ = (ambientIso (scalarMap X)).hom ≫
    (SmoothSite.a1Map (.of k) (affineIso X).hom).left ≫
      pullback.fst X.hom (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line k).hom ≫
          (affineIso X).inv.left
  erw [reassoc_of% h, ← Category.assoc, ambientIso_fst]
  rw [hid']
  erw [Category.comp_id]
  rfl

variable {V D : Scheme.{u}} (q : V ⟶ X.left)
  (d : D ⟶ _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLine (q ≫
      X.hom)) [IsClosedImmersion d]

/-- Original support map expressed in canonical affine-cylinder coordinates. -/
abbrev componentAffineProjection : D ⟶ Spec (.of (Polynomial Γ(X.left, ⊤))) :=
  d ≫ lineMap X.hom q ≫ (affineLineIso X).inv.left

omit [IsClosedImmersion d] in
private theorem componentAffineProjection_parameter :
    componentAffineProjection X q d ≫ Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (scalarMap X))) =
          _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.familyParameter (q ≫
          X.hom) d := by
  rw [← _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates.affineLineIso_parameter X]
  have hid := congrArg (fun g => g.left) (affineLineIso X).inv_hom_id
  change (affineLineIso X).inv.left ≫ (affineLineIso X).hom.left = 𝟙 _ at hid
  change (d ≫ lineMap X.hom q) ≫
    ((affineLineIso X).inv.left ≫ (affineLineIso X).hom.left) ≫ _ = _
  erw [hid, Category.id_comp]
  change d ≫ (lineMap X.hom q ≫
    pullback.snd X.hom (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])))) = _
  simp only [lineMap, pullback.map, pullback.lift_snd, Category.comp_id]
  rfl

omit [IsClosedImmersion d] in
/-- The exact original curve map makes the canonical evaluation square Cartesian;
there is no supplied face map or base-agreement witness. -/
theorem componentFaceCurveMap_isPullback (a : k) :
    IsPullback (fiberInclusion
        (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.familyParameter (q ≫
        X.hom) d) a)
      (componentFaceCurveMap (q ≫ X.hom) d a ≫ q ≫ (affineIso X).inv.left)
      (componentAffineProjection X q d)
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (scalarMap X a)))) := by
  have hex := ScalarExtensionEndpointFiber.exists_ring_endpoint_square
    (scalarMap X) (componentAffineProjection X q d) a
  rw [componentAffineProjection_parameter] at hex
  obtain ⟨b, hsq⟩ := hex
  have hb : b = componentFaceCurveMap (q ≫ X.hom) d a ≫ q ≫ (affineIso X).inv.left := by
    have h := congrArg (fun g => g ≫ Spec.map (CommRingCat.ofHom
      (Polynomial.C : Γ(X.left, ⊤) →+* Polynomial Γ(X.left, ⊤)))) hsq.w
    have heval : Spec.map (CommRingCat.ofHom
        (Polynomial.evalRingHom (scalarMap X a))) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : Γ(X.left, ⊤) →+*
          Polynomial Γ(X.left, ⊤))) = 𝟙 _ := by
      rw [← Spec.map_comp, ← Spec.map_id]
      congr 1
      ext r
      exact Polynomial.eval_C
    simp only [Category.assoc, heval, Category.comp_id, componentAffineProjection,
      affineLineIso_inverse_projection] at h
    have hl : lineMap X.hom q ≫ pullback.fst X.hom
        (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line k).hom =
        pullback.fst (q ≫ X.hom) (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line
            k).hom ≫ q :=
      lineMap_projection X.hom q
    rw [reassoc_of% hl] at h
    rw [componentFaceCurveMap_projection]
    simpa only [Category.assoc] using h.symm
  simpa only [hb] using hsq

/-- Actual component-face coefficients are placed in codimension one of the
original retained smooth curve, with no support flatness premise. -/
theorem componentFaceCurveMap_coefficient_coheight
    [IsIntegral X.left] [IsIntegral D] [IsNoetherian D]
    [IsSeparated q] [SmoothOfRelativeDimension 1 q]
    [IsFinite (d ≫ lineMap X.hom q)] [IsDominant (d ≫ lineMap X.hom q)]
    (a : k) (y : V)
    (hy : _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (componentFaceCurveMap (q ≫
          X.hom) d a)
        (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber
            (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.familyParameter (q ≫
            X.hom) d) a))) y ≠ 0) :
    Order.coheight y = 1 := by
  let : Nonempty (⊤ : X.left.Opens) :=
    ⟨⟨genericPoint X.left, TopologicalSpace.Opens.mem_top _⟩⟩
  let : IsDomain Γ(X.left, ⊤) := IsIntegral.component_integral ⊤
  let : IsDomain Γ((𝟭 Scheme).obj X.left, ⊤) :=
    inferInstanceAs (IsDomain Γ(X.left, ⊤))
  let : IsIntegrallyClosed Γ(X.left, ⊤) :=
    _root_.AlgebraicGeometry.Scheme.isIntegrallyClosed_sections_of_smooth_field k X.hom
        (isAffineOpen_top X.left)
  let : IsFinite (componentAffineProjection X q d) := by
    change IsFinite ((d ≫ lineMap X.hom q) ≫ (affineLineIso X).inv.left)
    infer_instance
  let : IsDominant (componentAffineProjection X q d) := by
    change IsDominant ((d ≫ lineMap X.hom q) ≫ (affineLineIso X).inv.left)
    infer_instance
  let : SmoothOfRelativeDimension 1 (q ≫ (affineIso X).inv.left) :=
    smoothOfRelativeDimension_comp (n := 1) (m := 0) _ _
  exact Scheme.FiniteDominantFace.original_face_coefficient_coheight
    (componentAffineProjection X q d)
    (fiberInclusion
        (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.familyParameter (q ≫
        X.hom) d) a)
    (componentFaceCurveMap (q ≫ X.hom) d a ≫ q ≫ (affineIso X).inv.left)
    (scalarMap X a) (componentFaceCurveMap_isPullback X q d a)
    (q ≫ (affineIso X).inv.left) (componentFaceCurveMap (q ≫ X.hom) d a) rfl y hy

end AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
