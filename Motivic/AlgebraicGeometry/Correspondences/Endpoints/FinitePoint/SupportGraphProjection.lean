/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.FinitePoint.SupportGraphEndpoint
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Endpoints.ComponentFacePlacement


/-!
# Original graph endpoints and the literal parameter-forgetting map

The endpoint product map forgets only the original scalar parameter. Composing
with the actual support-to-image factorization retains the original support map,
so the whole-fiber balance can be summed using the native residue pushforward.
The global forgetting map is not assumed finite.
-/

open _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
  (componentFaceCurveMap_projection)

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCurve
open scoped BigOperators

universe u

namespace Motivic.RelativeEndpointDiagram

variable {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k)))

/-- The original ambient product map that forgets only the scalar parameter. -/
def forgetParameterProduct :
    pullback (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineHom
        X.hom) Y.hom ⟶ pullback X.hom Y.hom :=
  pullback.lift
    (pullback.fst (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineHom
        X.hom) Y.hom ≫
      pullback.fst X.hom (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line k).hom)
    (pullback.snd (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineHom
        X.hom) Y.hom)
    (by simpa only [Category.assoc] using
      (pullback.condition (f :=
          _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineHom X.hom) (g
          := Y.hom)))

/-- On the whole scalar fiber, the original graph map is literal forgetting. -/
theorem generatorScalarFiberMap_eq_forget
    (G : FiniteCorrespondenceGenerator
        (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineHom X.hom)
        Y.hom) (a : k) :
    generatorScalarFiberMap X Y G a =
      fiberInclusion (G.inclusion ≫
          _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.ambientParameter X.hom
          Y.hom) a ≫
        G.inclusion ≫ forgetParameterProduct X Y := by
  apply pullback.hom_ext
  · simp only [generatorScalarFiberMap, Category.assoc,
      FiniteCorrespondenceGenerator.graphPullbackMap_fst,
      forgetParameterProduct, pullback.lift_fst]
    exact componentFaceCurveMap_projection X.hom G.projection a
  · simp only [generatorScalarFiberMap, Category.assoc,
      FiniteCorrespondenceGenerator.graphPullbackMap_snd,
      forgetParameterProduct, pullback.lift_snd]
    change (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeFiberIso X.hom
        G.projection a).inv ≫
      pullback.snd (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.endpoint X.hom
          a) G.projection ≫ G.targetProjection =
        fiberInclusion
            (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.familyParameter X.hom
            G.projection) a ≫ G.targetProjection
    have h :=
        (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeFiber_isPullback
        X.hom G.projection a).isoPullback_inv_snd
    simpa only [_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeFiberIso,
        fiberInclusion, Category.assoc] using
      congrArg (fun m => m ≫ G.targetProjection) h

/-- The actual finite-image factor disappears only by its original factorization
identity, before any signed summation or residue-degree collision is simplified. -/
theorem originalSupportScalarFiberMap_eq_forget
    {D : Scheme.{u}}
    (G : FiniteCorrespondenceGenerator
        (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineHom X.hom)
        Y.hom)
    (e : D ⟶ G.scheme) (a : k) :
    fiberMap (G.inclusion ≫
        _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.ambientParameter X.hom
        Y.hom) a e ≫
        generatorScalarFiberMap X Y G a =
      fiberInclusion (e ≫ G.inclusion ≫
          _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.ambientParameter X.hom
          Y.hom) a ≫
        e ≫ G.inclusion ≫ forgetParameterProduct X Y := by
  rw [generatorScalarFiberMap_eq_forget]
  simp only [fiberMap_inclusion_assoc]

end Motivic.RelativeEndpointDiagram

namespace Motivic.FinitePointCycleCorrespondence

open RelativeEndpointDiagram
open _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram

variable {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k)))
  {C V : Scheme.{u}} [IsNoetherian C]
  (q : C ⟶ relativeLine X.hom) (j : V ⟶ C) [IsOpenImmersion j]
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
      irreducibleComponents (relativeLine X.hom))
  (g : V ⟶ Y.left) (hbase : j ≫ q ≫ relativeLineHom X.hom = g ≫ Y.hom)

/-- The literal graph endpoint as the original signed whole-support sum. This
uses residue pushforward on the global forgetting map, never a false finiteness premise. -/
theorem toPoints_graph_endpoint_original_projection
    [IsAffine X.left] [IsIntegral X.left] (a : k) :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints (FiniteCorrespondence.toIntegralCycle (f
        := X.hom) (g := Y.hom)
      ((Cor.graphFunctor k).map (endpointMorphism X a) ≫
        correspondence (X := relativeLineSite X) (Y := Y)
          q j c hretained hfinite hdominant g hbase)) =
      ∑ x : c.support,
        let e := productMap (X := relativeLineSite X) (Y := Y)
          q j c hretained g hbase x
        c x.val • _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
          (fiberInclusion (e ≫ ambientParameter X.hom Y.hom) a ≫
            e ≫ forgetParameterProduct X Y)
          (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle (fiber (e ≫ ambientParameter X.hom
              Y.hom) a)) := by
  classical
  rw [toIntegralCycle_graph_endpoint_original_support X Y q j c hretained
    hfinite hdominant g hbase a, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  dsimp only
  rw [map_zsmul, _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_finitePushforward_apply,
    _root_.AlgebraicGeometry.Scheme.toPoints_fundamentalCycle]
  congr 1
  rw [originalSupportScalarFiberMap_eq_forget]
  simp only [FiniteCorrespondenceGenerator.inclusion, generator,
    Scheme.Hom.toImage_imageι_assoc]
  erw [Scheme.Hom.toImage_imageι_assoc]

end Motivic.FinitePointCycleCorrespondence
