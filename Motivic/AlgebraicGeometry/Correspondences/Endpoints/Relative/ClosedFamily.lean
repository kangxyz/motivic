/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.ClosedComponents
public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.Relative.GeneratorComposition
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Endpoints.RelativeFiniteFlatSpecialization

/-!
# Whole relative endpoint correspondence for an embedded finite-flat family

An explicit closed joint map identifies the producer's component images with
the original component schemes. The proved actual generator endpoint formula
then combines with whole-family weighted specialization. The endpoint keeps
the original source scheme, target map, nilpotents, and local multiplicities.
No flatness of the individual component projections is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
open _root_.Motivic

private theorem finitePushforward_congr {P Q : Scheme.{u}} (f g : P ⟶ Q)
    [IsFinite f] [IsFinite g] (h : f = g) (c : IntegralCycle P) :
    IntegralCycle.finitePushforward f c = IntegralCycle.finitePushforward g c := by
  cases h
  rfl

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))}
  {D : Scheme.{u}} (f : D ⟶ relativeLine X.hom) [IsFinite f] [Flat f]
  (j : D ⟶ pullback (relativeLineHom X.hom) Y.hom)
  (hj : j ≫ pullback.fst (relativeLineHom X.hom) Y.hom = f) (a : k)

local instance : IsNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsNoetherian X.left)

include hj in
omit [IsFinite f] [Flat f] in
/-- The whole endpoint retains the original source and target base equation. -/
theorem relativeFiberSpan_base :
    pullback.fst (endpoint X.hom a) f ≫ X.hom =
      (pullback.snd (endpoint X.hom a) f ≫ j ≫
        pullback.snd (relativeLineHom X.hom) Y.hom) ≫ Y.hom := by
  have hb : j ≫ pullback.snd (relativeLineHom X.hom) Y.hom ≫ Y.hom =
      f ≫ relativeLineHom X.hom := by
    rw [← pullback.condition, ← Category.assoc, hj]
  rw [Category.assoc, Category.assoc, hb, ← Category.assoc, ← pullback.condition,
    Category.assoc, endpoint_base]

/-- The original two endpoint coordinates give the actual whole-fiber span map. -/
def relativeFiberSpanMap : pullback (endpoint X.hom a) f ⟶ pullback X.hom Y.hom :=
  pullback.lift (pullback.fst (endpoint X.hom a) f)
    (pullback.snd (endpoint X.hom a) f ≫ j ≫ pullback.snd (relativeLineHom X.hom) Y.hom)
    (relativeFiberSpan_base f j hj a)

omit [IsFinite f] [Flat f] in
@[reassoc (attr := simp)]
theorem relativeFiberSpanMap_fst :
    relativeFiberSpanMap f j hj a ≫ pullback.fst X.hom Y.hom =
      pullback.fst (endpoint X.hom a) f := pullback.lift_fst _ _ _

omit [IsFinite f] [Flat f] in
@[reassoc (attr := simp)]
theorem relativeFiberSpanMap_snd :
    relativeFiberSpanMap f j hj a ≫ pullback.snd X.hom Y.hom =
      pullback.snd (endpoint X.hom a) f ≫ j ≫
        pullback.snd (relativeLineHom X.hom) Y.hom := pullback.lift_snd _ _ _

instance relativeFiberSpanMap_finite : IsFinite (relativeFiberSpanMap f j hj a) :=
  FiniteFlatCorrespondence.isFinite_productMap (pullback.fst (endpoint X.hom a) f)
    (relativeFiberSpanMap f j hj a) (relativeFiberSpanMap_fst f j hj a)

variable [IsClosedImmersion j]

/-- The original component's whole relative fiber is the producer generator's
whole graph pullback, via the actual component-image isomorphism. -/
def relativeComponentFiberIso (z : genericPoints D) :
    pullback (endpoint X.hom a) (RelativeFiniteFlat.componentInclusion z ≫ f) ≅
      (FiniteFlatCorrespondence.componentGenerator f j hj z).graphPullback (endpoint X.hom a) :=
  asIso (pullback.map _ _ _ _ (𝟙 _)
    (FiniteFlatCorrespondence.closedComponentSchemeIso f j hj z).hom (𝟙 _)
    (by simp) (by simp))

/-- This fiber comparison retains the two original maps into the endpoint product. -/
theorem relativeComponentFiberIso_hom_map (z : genericPoints D) :
    (relativeComponentFiberIso f j hj a z).hom ≫
        (FiniteFlatCorrespondence.componentGenerator f j hj z).graphPullbackMap
          (endpoint X.hom a) (endpoint_base X.hom a) =
      RelativeFiniteFlat.componentBaseChangeMap f (endpoint X.hom a) z ≫
        relativeFiberSpanMap f j hj a := by
  apply pullback.hom_ext
  · simp only [Category.assoc, _root_.Motivic.FiniteCorrespondenceGenerator.graphPullbackMap_fst,
      relativeFiberSpanMap_fst, relativeComponentFiberIso, asIso_hom, pullback.map,
      pullback.lift_fst, Category.comp_id, RelativeFiniteFlat.componentBaseChangeMap_fst]
  · simp only [Category.assoc, _root_.Motivic.FiniteCorrespondenceGenerator.graphPullbackMap_snd,
      relativeFiberSpanMap_snd, relativeComponentFiberIso, asIso_hom, pullback.map,
      pullback.lift_snd_assoc, FiniteFlatCorrespondence.closedComponentSchemeIso_hom_target,
      RelativeFiniteFlat.componentBaseChangeMap_snd_assoc]

variable [IsNoetherian D]

local instance : IsNoetherian (pullback (endpoint X.hom a) f) :=
  isNoetherian_of_finiteType (pullback.fst (endpoint X.hom a) f)

local instance (z : genericPoints D) : IsNoetherian
    (pullback (endpoint X.hom a) (RelativeFiniteFlat.componentInclusion z ≫ f)) :=
  isNoetherian_of_finiteType
    (pullback.fst (endpoint X.hom a) (RelativeFiniteFlat.componentInclusion z ≫ f))

omit [AlgebraicGeometry.IsNoetherian D] in
/-- Restriction of one actual component is its entire original relative fiber. -/
theorem toIntegralCycle_relative_component_endpoint (z : genericPoints D) :
    _root_.Motivic.FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Y.hom)
      ((_root_.Motivic.Cor.graphFunctor k).map (endpointMorphism X a) ≫
        (show _root_.Motivic.Cor.mk (relativeLineSite X) ⟶ _root_.Motivic.Cor.mk Y from
          (FiniteFlatCorrespondence.componentGenerator f j hj z).cycle)) =
      IntegralCycle.finitePushforward
        (RelativeFiniteFlat.componentBaseChangeMap f (endpoint X.hom a) z ≫
          relativeFiberSpanMap f j hj a)
        (fundamentalCycle
          (pullback (endpoint X.hom a) (RelativeFiniteFlat.componentInclusion z ≫ f))) := by
  rw [toIntegralCycle_graph_endpoint_generator]
  rw [← finitePushforward_fundamentalCycle (relativeComponentFiberIso f j hj a z).hom,
    ← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp]
  exact finitePushforward_congr _ _ (relativeComponentFiberIso_hom_map f j hj a z) _

/-- Actual graph restriction of the existing weighted producer is the pushed
fundamental cycle of the whole relative endpoint, without reducing any scheme. -/
theorem toIntegralCycle_relative_fundamental_endpoint :
    _root_.Motivic.FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Y.hom)
      ((_root_.Motivic.Cor.graphFunctor k).map (endpointMorphism X a) ≫
        (show _root_.Motivic.Cor.mk (relativeLineSite X) ⟶ _root_.Motivic.Cor.mk Y from
          FiniteFlatCorrespondence.fundamentalCorrespondence f j hj)) =
      IntegralCycle.finitePushforward (relativeFiberSpanMap f j hj a)
        (fundamentalCycle (pullback (endpoint X.hom a) f)) := by
  classical
  let := IntegralCycle.genericPointFintype D
  rw [relativeFiniteFlat_fundamentalCycle_specialization X f a, map_sum]
  rw [FiniteFlatCorrespondence.fundamentalCorrespondence_eq_sum_of_closed]
  change _root_.Motivic.FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Y.hom)
    ((_root_.Motivic.Cor.graphFunctor k).map (endpointMorphism X a) ≫
      ∑ z : genericPoints D, (genericMultiplicity z : ℤ) •
        (show _root_.Motivic.Cor.mk (relativeLineSite X) ⟶ _root_.Motivic.Cor.mk Y from
          (FiniteFlatCorrespondence.componentGenerator f j hj z).cycle)) = _
  rw [Preadditive.comp_sum, map_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [Preadditive.comp_zsmul, map_zsmul, map_zsmul,
    toIntegralCycle_relative_component_endpoint, IntegralCycle.finitePushforward_comp,
    AddMonoidHom.comp_apply]

end AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
