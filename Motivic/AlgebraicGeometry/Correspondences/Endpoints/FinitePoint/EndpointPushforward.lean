/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.FinitePoint.EndpointBalance
public import Motivic.Aglib.AlgebraicGeometry.Cycles.FiniteCurve.Faces.FiniteDominantFaceCoordinates


/-!
# Whole endpoint cycles under the original finite-image map

The normal-base evaluation square proves generic preservation. At generic
target points, every original branch contributes its full quotient length and
residue degree; at nongeneric points, the proved placement gives zero. Thus
finite pushforward retains all collisions and nonreduced endpoint structure.
-/

open _root_.AlgebraicGeometry.Scheme.IntegralCycle
  (genericPushforwardCoefficient_eq_zero_of_not_generic
      toPoints_finitePushforward_ofGenericCoefficients_apply)

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic.RelativeEndpointDiagram
open scoped BigOperators Polynomial

universe u

namespace AlgebraicGeometry.FiniteFlatCurve

/-- At an actual generic target endpoint point, the complete source point
fiber enumerates precisely its generic contributions, with original weights. -/
theorem fiberMap_fundamentalCoefficient_of_generic
    {k : Type u} [Field k] {C D : Scheme.{u}} [IsNoetherian C]
    (f : D ⟶ Spec (.of k[X])) (a : k) (j : C ⟶ D) [IsFinite j]
    (y : fiber f a) (hy : y ∈ genericPoints (fiber f a)) :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (fiberMap f a j)
          (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber (j ≫ f) a))) y =
      ∑ᶠ x : {x : C // j x = fiberInclusion f a y},
        (j.residueDegree x.1 : ℤ) *
          ((Module.length (C.presheaf.stalk x.1)
            ((C.presheaf.stalk x.1) ⧸ Ideal.ofList [scalar (j ≫ f) a x.1])).toNat : ℤ) := by
  classical
  let := _root_.AlgebraicGeometry.Scheme.IntegralCycle.genericPointFintype (fiber (j ≫ f) a)
  rw [← _root_.AlgebraicGeometry.Scheme.IntegralCycle.ofGenericCoefficients_genericMultiplicity,
    toPoints_finitePushforward_ofGenericCoefficients_apply]
  unfold _root_.AlgebraicGeometry.Scheme.IntegralCycle.genericPushforwardCoefficient
  rw [← finsum_eq_sum_of_fintype]
  simp_rw [← finsum_eq_if]
  rw [← finsum_subtype_eq_finsum_cond]
  rw [← finsum_comp_equiv (_root_.AlgebraicGeometry.Scheme.Hom.genericFiberEquiv (fiberMap f a j)
      ⟨y, hy⟩)]
  rw [← finsum_comp_equiv (fiberMapPointEquiv f a j y)]
  apply finsum_congr
  intro x
  rw [fiberMap_residueDegree]
  change ((Module.length ((fiber (j ≫ f) a).presheaf.stalk x.1)
      ((fiber (j ≫ f) a).presheaf.stalk x.1)).toNat : ℤ) * _ = _
  rw [fiber_stalk_length]
  exact mul_comm _ _

end AlgebraicGeometry.FiniteFlatCurve

namespace Motivic.RelativeEndpointDiagram

open AlgebraicGeometry.FiniteFlatCurve

variable {k A : Type u} [Field k] [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  (X Y : SmoothSite (Spec (.of k)))

local instance : IsNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsNoetherian X.left)

/-- The actual whole endpoint pushforward equals its original generic degree
multiple. The same evaluation square derives generic preservation; no flat
support, reduced endpoint, or supplied cycle equality occurs. -/
theorem generator_endpoint_finitePushforward
    (G : FiniteCorrespondenceGenerator
        (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineHom X.hom)
        Y.hom)
    {C : Scheme.{u}} [IsIntegral C] (j : C ⟶ G.scheme)
    [IsFinite j] [IsDominant j] (a : k)
    (p : G.scheme ⟶ Spec (.of A[X])) [IsFinite p] [IsDominant p]
    (b : fiber (G.inclusion ≫
        _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.ambientParameter X.hom
        Y.hom) a ⟶ Spec (.of A))
    (aA : A)
    (hsq : IsPullback (fiberInclusion (G.inclusion ≫
        _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.ambientParameter X.hom
        Y.hom) a)
      b p (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom aA)))) :
    letI : IsNoetherian
        (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLine X.hom) :=
      inferInstanceAs (IsNoetherian
          (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite
          X).left)
    letI : IsNoetherian G.scheme := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType
        G.projection
    letI : IsNoetherian C := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType j
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward
        (fiberMap (G.inclusion ≫
            _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.ambientParameter X.hom
            Y.hom) a j)
        (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber (j ≫ G.inclusion ≫
            _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.ambientParameter X.hom
            Y.hom) a)) =
      (j.residueDegree (genericPoint C) : ℤ) •
        _root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber (G.inclusion ≫
            _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.ambientParameter X.hom
            Y.hom) a) := by
  classical
  let : IsNoetherian (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLine
      X.hom) :=
    inferInstanceAs (IsNoetherian
        (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X).left)
  let : IsNoetherian G.scheme := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType
      G.projection
  let : IsNoetherian C := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType j
  let f := G.inclusion ≫
      _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.ambientParameter X.hom Y.hom
  let r := fiberMap f a j
  let : IsFinite b := MorphismProperty.of_isPullback hsq inferInstance
  have hsource : IsPullback (fiberInclusion (j ≫ f) a) (r ≫ b) (j ≫ p)
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom aA))) :=
    (fiberMap_isPullback f a j).flip.paste_vert hsq
  have hgeneric (x : genericPoints (fiber (j ≫ f) a)) :
      r x.val ∈ genericPoints (fiber f a) :=
    Scheme.FiniteDominantFace.original_face_generic_image_generic (j ≫ p)
      (fiberInclusion (j ≫ f) a) (r ≫ b) aA hsource b r rfl x.val x.property
  apply _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_injective
  ext y
  by_cases hy : y ∈ genericPoints (fiber f a)
  · rw [fiberMap_fundamentalCoefficient_of_generic f a j y hy]
    have h := generator_endpoint_original_length_balance X Y G j a y hy
    dsimp only [f] at hy ⊢
    simp only [map_zsmul, Finsupp.smul_apply, zsmul_eq_mul,
        _root_.AlgebraicGeometry.Scheme.toPoints_fundamentalCycle,
      _root_.AlgebraicGeometry.Scheme.fundamentalPointCycle_apply, dite_eq_left hy,
          _root_.AlgebraicGeometry.Scheme.genericMultiplicity]
    convert h using 1
  · rw [← _root_.AlgebraicGeometry.Scheme.IntegralCycle.ofGenericCoefficients_genericMultiplicity,
      toPoints_finitePushforward_ofGenericCoefficients_apply]
    rw [genericPushforwardCoefficient_eq_zero_of_not_generic r hgeneric _ y hy]
    dsimp only [f] at hy ⊢
    simp only [map_zsmul, Finsupp.smul_apply, zsmul_eq_mul,
        _root_.AlgebraicGeometry.Scheme.toPoints_fundamentalCycle,
      _root_.AlgebraicGeometry.Scheme.fundamentalPointCycle_apply, dite_eq_right hy, mul_zero]

end Motivic.RelativeEndpointDiagram
