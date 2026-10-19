/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.FinitePoint.SupportGraphProjection
public import Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.WholeComponentFiberRetainedLift


/-!
# The original graph endpoint is the retained whole-component cycle

The actual original finite support sum is identified with open restriction and
native residue pushforward. Neither the retained source-target map nor the
parameter-forgetting map is assumed finite. All finite hypotheses remain on
the original correspondence supports.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCurve Motivic.RelativeEndpointDiagram
open scoped BigOperators

universe u

namespace Motivic.FinitePointCycleCorrespondence

variable {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k)))
  {C V : Scheme.{u}} (q : C ⟶
      _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLine X.hom) (j : V ⟶
      C) [IsOpenImmersion j]
  (g : V ⟶ Y.left) (hbase : j ≫ q ≫
      _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineHom X.hom = g ≫
      Y.hom)

/-- The original retained source-target map after forgetting only the parameter. -/
def retainedEndpointProduct : V ⟶ pullback X.hom Y.hom :=
  pullback.lift
    (j ≫ q ≫ pullback.fst X.hom (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line
        k).hom) g
    (by simpa only [Category.assoc] using hbase)

variable (c : _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle C)
  (hr : ∀ x : c.support,
    Set.range (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
        x.val).val.subschemeι ⊆ Set.range j)

/-- The finite-image product map factors through the canonical original retained lift. -/
theorem productMap_forgetParameter
    (x : c.support) :
    productMap (X :=
        _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X) (Y :=
        Y) q j c hr g hbase x ≫
        forgetParameterProduct X Y =
      IsOpenImmersion.lift j (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
          x.val).val.subschemeι
          (hr x) ≫ retainedEndpointProduct X Y q j g hbase := by
  apply pullback.hom_ext
  · simp only [Category.assoc, forgetParameterProduct, pullback.lift_fst,
      retainedEndpointProduct,
      IsOpenImmersion.lift_fac_assoc]
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun t => t ≫ pullback.fst X.hom
        (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line k).hom)
        (productMap_fst (X :=
            _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X) (Y
            := Y) q j c hr g hbase x))
  · simp only [Category.assoc, forgetParameterProduct, pullback.lift_snd,
      retainedEndpointProduct, pullback.lift_snd]
    exact pullback.lift_snd _ _ _

/-- The scalar on each original support is the unchanged ambient scalar. -/
theorem productMap_parameter (x : c.support) :
    productMap (X :=
        _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X) (Y :=
        Y) q j c hr g hbase x ≫
        _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.ambientParameter X.hom
            Y.hom =
      (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ≫
        q ≫ pullback.snd X.hom (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line
            k).hom := by
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun t => t ≫ pullback.snd X.hom
      (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line k).hom)
      (productMap_fst (X :=
          _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X) (Y :=
          Y) q j c hr g hbase x))

variable [IsNoetherian C]
  (hfinite : ∀ x : c.support,
    IsFinite ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
        x.val).val.subschemeι ≫ q))
  (hdominant : ∀ x : c.support,
    Set.range ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
        x.val).val.subschemeι ≫ q) ∈
      irreducibleComponents
          (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLine X.hom))

/-- The literal original graph endpoint is the native retained whole-component
specialization, with no supplied coefficient identity and no global finiteness premise. -/
theorem toPoints_graph_endpoint_retained_cycle
    [IsAffine X.left] [IsIntegral X.left] (a : k) :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints (FiniteCorrespondence.toIntegralCycle (f
        := X.hom) (g := Y.hom)
      ((Cor.graphFunctor k).map
          (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.endpointMorphism X a) ≫
        correspondence (X :=
            _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X) (Y
            := Y)
          q j c hr hfinite hdominant g hbase)) =
      _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward (retainedEndpointProduct
          X Y q j g hbase)
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
            (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openImmersionRestriction j
          (_root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber
            (q ≫ pullback.snd X.hom (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line
                k).hom) a
            (_root_.AlgebraicGeometry.Scheme.IntegralCycle.fromPoints c)))) := by
  classical
  rw [toPoints_graph_endpoint_original_projection X Y q j c hr hfinite hdominant g hbase a,
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber_retained_sum j
      (q ≫ pullback.snd X.hom (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line
          k).hom) a c hr, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_zsmul]
  apply congrArg (fun z => c x.val • z)
  rw [← AddMonoidHom.comp_apply, ←
      _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward_comp]
  erw [productMap_parameter X Y q j g hbase c hr x]
  rw [Category.assoc, productMap_forgetParameter]

end Motivic.FinitePointCycleCorrespondence
