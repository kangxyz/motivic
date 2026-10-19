/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.FinitePoint.SupportEndpointPushforward
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeEndpointFiberGenerics


/-!
# Original signed support fibers compute graph endpoints

The canonical relative-fiber comparison retains the original graph endpoint.
Whole finite-image pushforward replaces each image degree by its original
support fiber, before summing the unchanged signed point-cycle coefficients.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCurve
open Motivic.RelativeEndpointDiagram
open scoped BigOperators

universe u

namespace Motivic.RelativeEndpointDiagram

variable {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k)))
  (G : FiniteCorrespondenceGenerator
      (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineHom X.hom)
      Y.hom) (a : k)

/-- The literal graph pullback is the same whole scalar endpoint fiber. -/
def generatorScalarFiberIso : G.graphPullback
    (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.endpoint X.hom a) ≅
    fiber (G.inclusion ≫
        _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.ambientParameter X.hom
        Y.hom) a :=
  _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeFiberIso X.hom
      G.projection a

/-- The original endpoint product map, expressed on its whole scalar fiber. -/
def generatorScalarFiberMap : fiber (G.inclusion ≫
    _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.ambientParameter X.hom Y.hom) a
    ⟶
    pullback X.hom Y.hom :=
  (generatorScalarFiberIso X Y G a).inv ≫
    G.graphPullbackMap (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.endpoint
        X.hom a) (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.endpoint_base
        X.hom a)

/-- The comparison keeps the literal endpoint map to the source-target product. -/
@[reassoc]
theorem generatorScalarFiberIso_hom_map :
    (generatorScalarFiberIso X Y G a).hom ≫ generatorScalarFiberMap X Y G a =
      G.graphPullbackMap (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.endpoint
          X.hom a) (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.endpoint_base
          X.hom a) := by
  simp only [generatorScalarFiberMap, Iso.hom_inv_id_assoc]

instance : IsFinite (generatorScalarFiberMap X Y G a) := by
  unfold generatorScalarFiberMap
  infer_instance

local instance : IsNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsNoetherian X.left)
local instance : IsNoetherian
    (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLine X.hom) :=
  inferInstanceAs (IsNoetherian
      (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X).left)
local instance : IsNoetherian G.scheme := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType
    G.projection

/-- The canonical comparison preserves the entire original endpoint cycle. -/
theorem generator_graph_endpoint_eq_scalar_pushforward :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward
        (G.graphPullbackMap
            (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.endpoint X.hom a)
            (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.endpoint_base X.hom
            a))
        (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (G.graphPullback
            (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.endpoint X.hom a))) =
      _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (generatorScalarFiberMap X Y G
          a)
        (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber (G.inclusion ≫
            _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.ambientParameter X.hom
            Y.hom) a)) := by
  unfold generatorScalarFiberMap
  rw [_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward_comp,
    AddMonoidHom.comp_apply,
    _root_.AlgebraicGeometry.Scheme.finitePushforward_fundamentalCycle (generatorScalarFiberIso X Y
        G a).inv]

end Motivic.RelativeEndpointDiagram

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



local instance : IsNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsNoetherian X.left)
local instance : IsNoetherian ((𝟭 Scheme).obj
    (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X).left) :=
  inferInstanceAs (IsNoetherian
      (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X).left)

/-- The actual graph endpoint of the original signed point correspondence is
computed on its original whole support fibers. Generic image degrees are
absorbed by the proved finite pushforward, not discarded. -/
theorem toIntegralCycle_graph_endpoint_original_support
    [IsAffine X.left] [IsIntegral X.left] (a : k) :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Y.hom)
      ((Cor.graphFunctor k).map
          (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.endpointMorphism X a) ≫
        correspondence (X :=
            _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X) (Y
            := Y)
          q j c hretained hfinite hdominant g hbase) =
      ∑ x : c.support,
        let e := productMap (X :=
            _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X) (Y
            := Y)
          q j c hretained g hbase x
        let G := generator (X :=
            _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X) (Y
            := Y)
          q j c hretained hfinite hdominant g hbase x
        letI : IsNoetherian G.scheme := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType
            G.projection
        letI : IsNoetherian e.image := inferInstanceAs (IsNoetherian G.scheme)
        letI : IsFinite e := productMap_isFinite (X :=
            _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X) (Y
            := Y)
          q j c hretained hfinite g hbase x
        letI : IsFinite e.toImage := _root_.AlgebraicGeometry.Scheme.Hom.isFinite_toImage e
        letI : IsNoetherian (supportScheme c x) :=
            _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType e.toImage
        c x.val • _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward
          (fiberMap (G.inclusion ≫
              _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.ambientParameter
              X.hom Y.hom) a e.toImage ≫
            generatorScalarFiberMap X Y G a)
          (_root_.AlgebraicGeometry.Scheme.fundamentalCycle
            (fiber (e.toImage ≫ G.inclusion ≫
                _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.ambientParameter
                X.hom Y.hom) a)) := by
  classical
  rw [toIntegralCycle_graph_endpoint X Y q j c hretained hfinite hdominant g hbase a]
  apply Finset.sum_congr rfl
  intro x _
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
  let : IsNoetherian G.scheme := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType
      G.projection
  let : IsNoetherian e.image := inferInstanceAs (IsNoetherian G.scheme)
  let : IsNoetherian (supportScheme c x) :=
      _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType e.toImage
  have hb := original_support_endpoint_finitePushforward X Y q j c hretained
    hfinite hdominant g hbase x a
  rw [_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]
  rw [hb, map_zsmul, ← mul_smul]
  convert congrArg (fun z =>
    (c x.val * (e.residueDegree (genericPoint (supportScheme c x)) : ℤ)) • z)
    (generator_graph_endpoint_eq_scalar_pushforward X Y G a) using 1
  rfl

end Motivic.FinitePointCycleCorrespondence
