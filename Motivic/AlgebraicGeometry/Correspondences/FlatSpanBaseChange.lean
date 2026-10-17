/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.FiniteFlatClosedComponents
public import Motivic.AlgebraicGeometry.Correspondences.FlatGraphComponentPullback
public import Motivic.Aglib.AlgebraicGeometry.RelativeFiniteFlatFiberGenerics
public import Motivic.Aglib.AlgebraicGeometry.FlatFundamentalCycle
public import Motivic.AlgebraicGeometry.Correspondences.FiniteFlatSpanGraph

/-! # Whole embedded finite-flat spans under flat source base change -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace Motivic.FlatSpanBaseChange

private theorem finitePushforward_congr {P Q : Scheme.{u}} (f g : P ⟶ Q)
    [IsFinite f] [IsFinite g] (h : f = g) (c : IntegralCycle P) :
    IntegralCycle.finitePushforward f c = IntegralCycle.finitePushforward g c := by
  cases h
  rfl

variable {k : Type u} [Field k] {X T Y : SmoothSite (Spec (.of k))}
  {D : Scheme.{u}} (f : D ⟶ T.left) [IsFinite f] [Flat f]
  (j : D ⟶ pullback (T.hom) Y.hom)
  (hj : j ≫ pullback.fst (T.hom) Y.hom = f) (α : X ⟶ T) [Flat α.left]

local instance : IsNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsNoetherian X.left)

include hj in
omit [IsFinite f] [Flat f] [Flat α.left] in
/-- The whole endpoint retains the original source and target base equation. -/
theorem flatFiberSpan_base :
    pullback.fst α.left f ≫ X.hom =
      (pullback.snd α.left f ≫ j ≫
        pullback.snd (T.hom) Y.hom) ≫ Y.hom := by
  have hb : j ≫ pullback.snd (T.hom) Y.hom ≫ Y.hom =
      f ≫ T.hom := by
    rw [← pullback.condition, ← Category.assoc, hj]
  rw [Category.assoc, Category.assoc, hb, ← Category.assoc, ← pullback.condition,
    Category.assoc, MorphismProperty.Over.w]

/-- The original two endpoint coordinates give the actual whole-fiber span map. -/
def flatFiberSpanMap : pullback α.left f ⟶ pullback X.hom Y.hom :=
  pullback.lift (pullback.fst α.left f)
    (pullback.snd α.left f ≫ j ≫ pullback.snd (T.hom) Y.hom)
    (flatFiberSpan_base f j hj α)

omit [IsFinite f] [Flat f] [Flat α.left] in
@[reassoc (attr := simp)]
theorem flatFiberSpanMap_fst :
    flatFiberSpanMap f j hj α ≫ pullback.fst X.hom Y.hom =
      pullback.fst α.left f := pullback.lift_fst _ _ _

omit [IsFinite f] [Flat f] [Flat α.left] in
@[reassoc (attr := simp)]
theorem flatFiberSpanMap_snd :
    flatFiberSpanMap f j hj α ≫ pullback.snd X.hom Y.hom =
      pullback.snd α.left f ≫ j ≫
        pullback.snd (T.hom) Y.hom := pullback.lift_snd _ _ _

instance flatFiberSpanMap_finite : IsFinite (flatFiberSpanMap f j hj α) :=
  FiniteFlatCorrespondence.isFinite_productMap (pullback.fst α.left f)
    (flatFiberSpanMap f j hj α) (flatFiberSpanMap_fst f j hj α)

variable [IsClosedImmersion j]

/-- The original component's whole relative fiber is the producer generator's
whole graph pullback, via the actual component-image isomorphism. -/
def flatComponentFiberIso (z : genericPoints D) :
    pullback α.left (RelativeFiniteFlat.componentInclusion z ≫ f) ≅
      (FiniteFlatCorrespondence.componentGenerator f j hj z).graphPullback α.left :=
  asIso (pullback.map _ _ _ _ (𝟙 _)
    (FiniteFlatCorrespondence.closedComponentSchemeIso f j hj z).hom (𝟙 _)
    (by simp) (by simp))

omit [Flat α.left] in
/-- This fiber comparison retains the two original maps into the endpoint product. -/
theorem flatComponentFiberIso_hom_map (z : genericPoints D) :
    (flatComponentFiberIso f j hj α z).hom ≫
        (FiniteFlatCorrespondence.componentGenerator f j hj z).graphPullbackMap
          α.left (MorphismProperty.Over.w α) =
      RelativeFiniteFlat.componentBaseChangeMap f α.left z ≫
        flatFiberSpanMap f j hj α := by
  apply pullback.hom_ext
  · simp only [Category.assoc, FiniteCorrespondenceGenerator.graphPullbackMap_fst,
      flatFiberSpanMap_fst, flatComponentFiberIso, asIso_hom, pullback.map,
      pullback.lift_fst, Category.comp_id, RelativeFiniteFlat.componentBaseChangeMap_fst]
  · simp only [Category.assoc, FiniteCorrespondenceGenerator.graphPullbackMap_snd,
      flatFiberSpanMap_snd, flatComponentFiberIso, asIso_hom, pullback.map,
      pullback.lift_snd_assoc, FiniteFlatCorrespondence.closedComponentSchemeIso_hom_target,
      RelativeFiniteFlat.componentBaseChangeMap_snd_assoc]

variable [IsNoetherian D]

local instance : IsNoetherian (pullback α.left f) :=
  isNoetherian_of_finiteType (pullback.fst α.left f)

local instance (z : genericPoints D) : IsNoetherian
    (pullback α.left (RelativeFiniteFlat.componentInclusion z ≫ f)) :=
  isNoetherian_of_finiteType
    (pullback.fst α.left (RelativeFiniteFlat.componentInclusion z ≫ f))

omit [AlgebraicGeometry.IsNoetherian D] in
/-- Restriction of one actual component is its entire original relative fiber. -/
theorem toIntegralCycle_flat_component_pullback (z : genericPoints D) :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Y.hom)
      ((Cor.graphFunctor k).map α ≫
        (show Cor.mk T ⟶ Cor.mk Y from
          (FiniteFlatCorrespondence.componentGenerator f j hj z).cycle)) =
      IntegralCycle.finitePushforward
        (RelativeFiniteFlat.componentBaseChangeMap f α.left z ≫
          flatFiberSpanMap f j hj α)
        (fundamentalCycle
          (pullback α.left (RelativeFiniteFlat.componentInclusion z ≫ f))) := by
  rw [FiniteCorrespondenceGenerator.toIntegralCycle_graphFunctor_comp_of_flat]
  rw [← finitePushforward_fundamentalCycle (flatComponentFiberIso f j hj α z).hom,
    ← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp]
  exact finitePushforward_congr _ _ (flatComponentFiberIso_hom_map f j hj α z) _

/-- Actual graph restriction of the existing weighted producer is the pushed
fundamental cycle of the whole relative endpoint, without reducing any scheme. -/
theorem toIntegralCycle_flat_fundamental_pullback :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Y.hom)
      ((Cor.graphFunctor k).map α ≫
        (show Cor.mk T ⟶ Cor.mk Y from
          FiniteFlatCorrespondence.fundamentalCorrespondence f j hj)) =
      IntegralCycle.finitePushforward (flatFiberSpanMap f j hj α)
        (fundamentalCycle (pullback α.left f)) := by
  classical
  let := IntegralCycle.genericPointFintype D
  rw [fundamentalCycle_pullback_eq_second_component_sum α.left f, map_sum]
  simp_rw [componentExteriorSndInclusion_eq_map]
  rw [FiniteFlatCorrespondence.fundamentalCorrespondence_eq_sum_of_closed]
  change FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Y.hom)
    ((Cor.graphFunctor k).map α ≫
      ∑ z : genericPoints D, (genericMultiplicity z : ℤ) •
        (show Cor.mk T ⟶ Cor.mk Y from
          (FiniteFlatCorrespondence.componentGenerator f j hj z).cycle)) = _
  rw [Preadditive.comp_sum, map_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [Preadditive.comp_zsmul, map_zsmul, map_zsmul,
    toIntegralCycle_flat_component_pullback, IntegralCycle.finitePushforward_comp,
    AddMonoidHom.comp_apply]
  rfl

end Motivic.FlatSpanBaseChange

namespace Motivic.Cor

variable {k : Type u} [Field k] {X T Y Z : SmoothSite (Spec (.of k))}
  {D : Scheme.{u}} (f : D ⟶ T.left) [IsFinite f] [Flat f]
  (g : D ⟶ Y.left) (h : f ≫ T.hom = g ≫ Y.hom)
  (α : X ⟶ T) [Flat α.left]

include h in
omit [IsFinite f] [Flat f] [Flat α.left] in
/-- The original base-changed two coordinates satisfy the original base equation. -/
theorem flatSpanPullback_base :
    pullback.fst α.left f ≫ X.hom =
      (pullback.snd α.left f ≫ g) ≫ Y.hom := by
  rw [Category.assoc, ← h, ← Category.assoc, ← pullback.condition,
    Category.assoc, MorphismProperty.Over.w]

/-- Actual graph restriction of an embedded whole finite-flat span by a flat map. -/
theorem graph_ofFiniteFlatSpan_of_flat [IsClosedImmersion (pullback.lift f g h)] :
    (graphFunctor k).map α ≫ ofFiniteFlatSpan (X := T) (Y := Y) f g h =
      ofFiniteFlatSpan (X := X) (Y := Y) (pullback.fst α.left f)
        (pullback.snd α.left f ≫ g) (flatSpanPullback_base f g h α) := by
  have : IsNoetherian D := isNoetherian_of_finiteType f
  apply FiniteCorrespondence.toIntegralCycle_injective
  refine (FlatSpanBaseChange.toIntegralCycle_flat_fundamental_pullback
    (X := X) (T := T) (Y := Y) f
    (pullback.lift f g h) (pullback.lift_fst _ _ _) α).trans ?_
  rw [toIntegralCycle_ofFiniteFlatSpan]
  congr 2
  apply pullback.hom_ext
  · simp only [FlatSpanBaseChange.flatFiberSpanMap_fst]
    exact (pullback.lift_fst _ _ _).symm
  · simp only [FlatSpanBaseChange.flatFiberSpanMap_snd, pullback.lift_snd]
    exact (pullback.lift_snd _ _ _).symm

/-- An arbitrary target coordinate can be forgotten after actual flat graph restriction. -/
theorem graph_ofFiniteFlatSpan_of_flat_postcompose
    [IsClosedImmersion (pullback.lift f g h)] (q : Y ⟶ Z) :
    (graphFunctor k).map α ≫ ofFiniteFlatSpan (X := T) (Y := Z) f (g ≫ q.left)
        (finiteFlatSpan_postcompose_base f g h q) =
      ofFiniteFlatSpan (X := X) (Y := Z) (pullback.fst α.left f)
        (pullback.snd α.left f ≫ g ≫ q.left)
        (flatSpanPullback_base f (g ≫ q.left) (finiteFlatSpan_postcompose_base f g h q) α) := by
  rw [← ofFiniteFlatSpan_comp_graph f g h q, ← Category.assoc,
    graph_ofFiniteFlatSpan_of_flat, ofFiniteFlatSpan_comp_graph]
  rfl

end Motivic.Cor
