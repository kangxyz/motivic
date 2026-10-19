/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.FinitePoint.EndpointPushforward
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Affine.LineCoordinates
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Normal
public import Motivic.Aglib.AlgebraicGeometry.BaseChange.PolynomialFiber


/-!
# Canonical affine coordinates for original generator endpoint pushforward

The actual affine source supplies its normal global-section ring and canonical
polynomial cylinder comparison. The evaluation pushout constructs the same
whole scalar endpoint square. No coordinate projection or Cartesian square is
supplied to the resulting generator consumer.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCurve
open AlgebraicGeometry.PolynomialOpenQuotient
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open scoped Polynomial

universe u


namespace Motivic.RelativeEndpointDiagram

variable {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k))) [IsAffine X.left]

attribute [local instance]
  _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates.sectionsAlgebra

local instance : IsNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsNoetherian X.left)

/-- Whole endpoint pushforward for an actual generator over an integral affine
smooth source. The original source internally supplies every normal-base
coordinate and evaluation-square input to the no-flat whole-cycle balance. -/
theorem affine_generator_endpoint_finitePushforward [IsIntegral X.left]
    (G : FiniteCorrespondenceGenerator
        (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineHom X.hom)
        Y.hom)
    {C : Scheme.{u}} [IsIntegral C] (j : C ⟶ G.scheme)
    [IsFinite j] [IsDominant j] (a : k) :
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
  let : IsNoetherian (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLine
      X.hom) :=
    inferInstanceAs (IsNoetherian
        (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X).left)
  let : IsNoetherian G.scheme := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType
      G.projection
  let : IsNoetherian C := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType j
  let : Nonempty (⊤ : X.left.Opens) :=
    ⟨⟨genericPoint X.left, TopologicalSpace.Opens.mem_top (genericPoint X.left)⟩⟩
  let : IsDomain Γ(X.left, ⊤) := IsIntegral.component_integral ⊤
  let : IsDomain Γ((𝟭 Scheme).obj X.left, ⊤) :=
    inferInstanceAs (IsDomain Γ(X.left, ⊤))
  let : IsIntegrallyClosed Γ(X.left, ⊤) :=
    _root_.AlgebraicGeometry.Scheme.isIntegrallyClosed_sections_of_smooth_field k X.hom
        (isAffineOpen_top X.left)
  let : IsIntegral (_root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite.lineSite
      (k := k) (R := Γ(X.left, ⊤))).left :=
    inferInstanceAs (IsIntegral (Spec (.of (Polynomial Γ(X.left, ⊤)))))
  let : Nonempty (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLine
      X.hom) :=
    ⟨(affineLineIso X).hom.left (genericPoint
      (_root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite.lineSite (k := k) (R := Γ(X.left,
          ⊤))).left)⟩
  let : IsIntegral (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLine
      X.hom) :=
    isIntegral_of_isOpenImmersion (affineLineIso X).inv.left
  let : Surjective G.projection := ⟨G.projection_surjective⟩
  let p : G.scheme ⟶ Spec (.of (Polynomial Γ(X.left, ⊤))) :=
    G.projection ≫ (affineLineIso X).inv.left
  have hp : p ≫ Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (scalarMap X))) =
      G.inclusion ≫
          _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.ambientParameter X.hom
          Y.hom := by
    rw [← affineLineIso_parameter X]
    have hid := congrArg (fun f => f.left) (affineLineIso X).inv_hom_id
    change (affineLineIso X).inv.left ≫ (affineLineIso X).hom.left = 𝟙 _ at hid
    change G.projection ≫ ((affineLineIso X).inv.left ≫ (affineLineIso X).hom.left) ≫
      pullback.snd X.hom (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line k).hom = _
    erw [hid, Category.id_comp]
    rfl
  have hex := ScalarExtensionEndpointFiber.exists_ring_endpoint_square (scalarMap X) p a
  rw [hp] at hex
  obtain ⟨b, hsq⟩ := hex
  exact generator_endpoint_finitePushforward X Y G j a p b (scalarMap X a) hsq

end Motivic.RelativeEndpointDiagram
