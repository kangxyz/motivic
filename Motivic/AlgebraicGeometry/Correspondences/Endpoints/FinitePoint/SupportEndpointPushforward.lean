/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.Relative.AffineGeneratorPushforward


/-!
# Whole endpoint pushforward from the original point support

The actual support-to-image factorization supplies the finite dominant map.
The whole endpoint cycle retains its original generic residue degree, including
all nonreduced lengths and image collisions. No replacement map is supplied.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCurve
open Motivic.RelativeEndpointDiagram

universe u

namespace Motivic.FinitePointCycleCorrespondence

variable {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k)))
  {C V : Scheme.{u}} (q : C ⟶
      _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLine X.hom) (j : V ⟶
      C) [IsOpenImmersion j]
  (c : _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle C)
  (hretained : ∀ x : c.support,
    Set.range (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
        x.val).val.subschemeι ⊆ Set.range j)
  (hfinite : ∀ x : c.support,
    IsFinite ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
        x.val).val.subschemeι ≫ q))
  (hdominant : ∀ x : c.support,
    Set.range ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
        x.val).val.subschemeι ≫ q) ∈
      irreducibleComponents
          (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLine X.hom))
  (g : V ⟶ Y.left) (hbase : j ≫ q ≫
      _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineHom X.hom = g ≫
      Y.hom)


/-- The literal original support-to-image map satisfies whole endpoint cycle
balance over the given integral affine smooth base. -/
theorem original_support_endpoint_finitePushforward [IsAffine X.left] [IsIntegral X.left]
    (x : c.support) (a : k) :
    let e := productMap (X :=
        _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X) (Y :=
        Y) q j c hretained g hbase x
    let G := generator (X :=
        _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X) (Y :=
        Y)
      q j c hretained hfinite hdominant g hbase x
    letI : IsNoetherian
        (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLine X.hom) :=
      inferInstanceAs (IsNoetherian
          (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite
          X).left)
    letI : IsNoetherian ((𝟭 Scheme).obj
        (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X).left)
        :=
      inferInstanceAs (IsNoetherian
          (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite
          X).left)
    letI : IsNoetherian G.scheme := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType
        G.projection
    letI : IsNoetherian e.image := inferInstanceAs (IsNoetherian G.scheme)
    letI : IsFinite e := productMap_isFinite (X :=
        _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X) (Y :=
        Y)
      q j c hretained hfinite g hbase x
    letI : IsFinite e.toImage := _root_.AlgebraicGeometry.Scheme.Hom.isFinite_toImage e
    letI : IsNoetherian (supportScheme c x) :=
        _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType e.toImage
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward
        (fiberMap (G.inclusion ≫
            _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.ambientParameter X.hom
            Y.hom) a e.toImage)
        (_root_.AlgebraicGeometry.Scheme.fundamentalCycle
          (fiber (e.toImage ≫ G.inclusion ≫
              _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.ambientParameter
              X.hom Y.hom) a)) =
      (e.residueDegree (genericPoint (supportScheme c x)) : ℤ) •
        _root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber (G.inclusion ≫
            _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.ambientParameter X.hom
            Y.hom) a) := by
  dsimp only
  let e := productMap (X :=
      _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X) (Y := Y)
      q j c hretained g hbase x
  let G := generator (X :=
      _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X) (Y := Y)
    q j c hretained hfinite hdominant g hbase x
  let : IsFinite e := productMap_isFinite (X :=
      _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X) (Y := Y)
    q j c hretained hfinite g hbase x
  let : IsFinite e.toImage := _root_.AlgebraicGeometry.Scheme.Hom.isFinite_toImage e
  have h := affine_generator_endpoint_finitePushforward X Y G e.toImage a
  have hd : e.toImage.residueDegree (genericPoint (supportScheme c x)) =
      e.residueDegree (genericPoint (supportScheme c x)) := by
    have he := _root_.AlgebraicGeometry.Scheme.Hom.residueDegree_comp e.toImage e.imageι
        (genericPoint (supportScheme c x))
    simpa only [Scheme.Hom.toImage_imageι,
        _root_.AlgebraicGeometry.Scheme.Hom.residueDegree_of_surjectiveOnStalks,
      one_mul, mul_one] using he.symm
  rw [hd] at h
  convert h using 1

end Motivic.FinitePointCycleCorrespondence
