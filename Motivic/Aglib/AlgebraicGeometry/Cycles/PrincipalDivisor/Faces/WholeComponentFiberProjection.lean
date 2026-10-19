/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Endpoints.ComponentFacePlacement
public import Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.WholeComponentFiber

/-!
# Projecting the original weighted component faces

The global curve projection need not be finite. Its native additive
residue-degree pushforward agrees, component by component, with the original
closed whole-face map. The literal endpoint section recovers the ambient
specialization, preserving every signed weight and image collision.


Intended upstream module:
`Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.WholeComponentFiberProjection`.
Incoming project consumers:
Module prefix: `Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.`
Module suffix: `WholeComponentFiberProjectionSupport`.
-/

open _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
  (componentFaceCurveMap_endpoint componentFaceCurveMap_projection)

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCurve

universe u

namespace AlgebraicGeometry.Scheme.IntegralCycle

variable {k : Type u} [Field k] {V : Scheme.{u}} (p : V ⟶ Spec (.of k))
  [IsNoetherian (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLine p)]
      (a : k)

/-- Each original signed component projects by its actual closed whole-face map,
not by a reduced support or an assumed finite global projection. -/
theorem wholeComponentFiber_projection_single
    (Z : _root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme
        (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLine p)) (n : ℤ) :
    _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward (pullback.fst p
        (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line k).hom)
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
          (_root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber (pullback.snd p
          (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line k).hom) a
        (Finsupp.single Z n))) =
      n • _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
          (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.componentFaceCurveMap p
          Z.val.subschemeι a)
        (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle (fiber
            (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.familyParameter p
            Z.val.subschemeι) a)) := by
  rw [_root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber_single, map_zsmul,
      map_zsmul,
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_finitePushforward_apply,
        _root_.AlgebraicGeometry.Scheme.toPoints_fundamentalCycle]
  rw [← AddMonoidHom.comp_apply, ←
      _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward_comp]
  simp only [componentFaceCurveMap_projection, Category.assoc]

/-- The literal endpoint section recovers the entire specialized point cycle
from its projection, including arbitrary signed component collisions. -/
theorem wholeComponentFiber_endpoint_projection (c : _root_.AlgebraicGeometry.Scheme.IntegralCycle
    (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLine p)) :
    _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
        (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.endpoint p a)
      (_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward (pullback.fst p
          (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line k).hom)
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
            (_root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber (pullback.snd p
            (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line k).hom) a c))) =
      _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
          (_root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber (pullback.snd p
          (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line k).hom) a c) := by
  have h : (_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
      (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.endpoint p a)).comp
      ((_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
        (pullback.fst p (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line
            k).hom)).comp
        (toPoints.comp (_root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber
          (pullback.snd p (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line k).hom)
              a))) =
      toPoints.comp
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber (pullback.snd p
            (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line k).hom) a) := by
    apply Finsupp.addHom_ext
    intro Z n
    simp only [AddMonoidHom.comp_apply]
    rw [wholeComponentFiber_projection_single]
    simp only [_root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber_single, map_zsmul,
        _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_finitePushforward_apply,
      _root_.AlgebraicGeometry.Scheme.toPoints_fundamentalCycle]
    rw [← AddMonoidHom.comp_apply, ←
        _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward_comp,
      componentFaceCurveMap_endpoint]
  exact DFunLike.congr_fun h c

/-- The projected original weighted specialization has exactly the coefficient
at the original endpoint point. No correspondence endpoint equality is assumed. -/
theorem wholeComponentFiber_projection_coefficient
    (c : _root_.AlgebraicGeometry.Scheme.IntegralCycle
        (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLine p)) (x : V) :
    _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward (pullback.fst p
        (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line k).hom)
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
          (_root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber (pullback.snd p
          (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line k).hom) a c)) x =
      _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
          (_root_.AlgebraicGeometry.Scheme.IntegralCycle.wholeComponentFiber (pullback.snd p
          (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line k).hom) a c)
        (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.endpoint p a x) := by
  have : IsClosedImmersion
      (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.endpoint p a) :=
    MorphismProperty.of_isPullback
        (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.endpoint_isPullback p a)
        inferInstance
  have h := congrArg (fun z : _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle
      (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLine p) => z
      (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.endpoint p a x))
    (wholeComponentFiber_endpoint_projection p a c)
  rw [_root_.AlgebraicGeometry.Scheme.residuePushforward_eq_mapDomain_of_surjectiveOnStalks] at h
  change Finsupp.mapDomain
      (⇑(_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.endpoint p a)) _
      (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.endpoint p a x) = _ at h
  rw [Finsupp.mapDomain_apply_of_injective
      (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.endpoint p
      a).isClosedEmbedding.injective] at h
  exact h

end AlgebraicGeometry.Scheme.IntegralCycle
