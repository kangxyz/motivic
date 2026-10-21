/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Graph.Flat.PointControl
public import Motivic.AlgebraicGeometry.Correspondences.Coproducts.Binary

/-! # Actual support points under graph postcomposition -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Motivic
open _root_.AlgebraicGeometry.Scheme
/-- The Noetherian instance used in this module. -/
local instance postcompositionPointControlNoetherian
    {k : Type u} [Field k] (T : SmoothSite (Spec (.of k))) :
    IsNoetherian ((𝟭 Scheme).obj T.left) := inferInstanceAs (IsNoetherian T.left)

/-- The reduced scheme instance used in this module. -/
local instance postcompositionPointControlReduced
    {k : Type u} [Field k] (T : SmoothSite (Spec (.of k))) :
    IsReduced ((𝟭 Scheme).obj T.left) := inferInstanceAs (IsReduced T.left)

namespace FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme
variable {k : Type u} [Field k] {X V W : SmoothSite (Spec (.of k))}

/-- Every surviving support point after graph postcomposition comes from an
original support point, with its exact source and postcomposed target. -/
theorem exists_point_lift_of_mem_cycle_comp_graph
    (A : FiniteCorrespondenceGenerator X.hom V.hom) (q : V ⟶ W)
    (B : FiniteCorrespondenceGenerator X.hom W.hom)
    (hB : B ∈ ((show Cor.mk X ⟶ Cor.mk V from A.cycle) ≫
      (Cor.graphFunctor k).map q).support) (z : B.scheme) :
    ∃ a : A.scheme, A.projection a = B.projection z ∧
      q.left (A.targetProjection a) = B.targetProjection z := by
  classical
  have hB' : B.toIntegralClosedSubscheme ∈
      (FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := W.hom)
        ((show Cor.mk X ⟶ Cor.mk V from A.cycle) ≫ (Cor.graphFunctor k).map q)).support := by
    change B.toIntegralClosedSubscheme ∈ (Finsupp.mapDomain
      FiniteCorrespondenceGenerator.toIntegralClosedSubscheme _).support
    rw [Finsupp.mapDomain_support_of_injective toIntegralClosedSubscheme_injective]
    exact Finset.mem_image.mpr ⟨B, hB, rfl⟩
  change B.toIntegralClosedSubscheme ∈
    (FiniteCorrespondence.toIntegralCycle (FiniteCorrespondence.incidenceTorPairing k
      (X := X) (Y := V) (Z := W) A.cycle
      (componentGraphCycleOver q.left (MorphismProperty.Over.w q)))).support at hB'
  rw [A.toIntegralCycle_incidenceTorPairing_componentGraph_right k q.left
    (MorphismProperty.Over.w q)] at hB'
  obtain ⟨a, ha⟩ := IntegralCycle.range_subschemeι_subset_of_mem_finitePushforward
    (A.graphPostcompositionMap q.left (MorphismProperty.Over.w q))
    (fundamentalCycle A.scheme) B.toIntegralClosedSubscheme hB' (Set.mem_range_self z)
  change A.graphPostcompositionMap q.left (MorphismProperty.Over.w q) a = B.inclusion z at ha
  refine ⟨a, ?_, ?_⟩
  · have h := congrArg (pullback.fst X.hom W.hom) ha
    change (A.graphPostcompositionMap q.left (MorphismProperty.Over.w q) ≫
      pullback.fst X.hom W.hom) a = B.projection z at h
    rw [graphPostcompositionMap_fst] at h
    exact h
  · have h := congrArg (pullback.snd X.hom W.hom) ha
    change (A.graphPostcompositionMap q.left (MorphismProperty.Over.w q) ≫
      pullback.snd X.hom W.hom) a = B.targetProjection z at h
    rw [graphPostcompositionMap_snd] at h
    exact h

end FiniteCorrespondenceGenerator
namespace FiniteCorrespondence
open _root_.AlgebraicGeometry.Scheme
variable {k : Type u} [Field k] {X V W : SmoothSite (Spec (.of k))}

/-- Signed graph pushforward preserves actual point provenance, despite cancellation. -/
theorem exists_support_point_lift_of_mem_comp_graph
    (β : FiniteCorrespondence X.hom V.hom) (q : V ⟶ W)
    (B : FiniteCorrespondenceGenerator X.hom W.hom)
    (hB : B ∈ (β ≫ (Cor.graphFunctor k).map q).support) (z : B.scheme) :
    ∃ A ∈ β.support, ∃ a : A.scheme, A.projection a = B.projection z ∧
      q.left (A.targetProjection a) = B.targetProjection z := by
  classical
  have hβ : ∑ A ∈ β.support, β A • A.cycle = β := by
    simpa only [Finsupp.sum, FiniteCorrespondenceGenerator.cycle,
      Finsupp.smul_single, smul_eq_mul, mul_one] using β.sum_single
  have hsum : β ≫ (Cor.graphFunctor k).map q =
      ∑ A ∈ β.support, β A • ((show Cor.mk X ⟶ Cor.mk V from A.cycle) ≫
        (Cor.graphFunctor k).map q) := by
    change (incidenceTorPairing k (X := X) (Y := V) (Z := W)).flip
      ((Cor.graphFunctor k).map q) β = _
    conv_lhs => rw [← hβ]
    simp only [map_sum, map_zsmul]
    rfl
  rw [hsum] at hB
  obtain ⟨A, hA, hB⟩ := Finsupp.mem_support_finsetSum B hB
  obtain ⟨a, ha⟩ := A.exists_point_lift_of_mem_cycle_comp_graph q B
    (Finsupp.support_smul hB) z
  exact ⟨A, hA, a, ha⟩

/-- The designated target set is carried to its literal image under a target map. -/
theorem target_mem_image_of_mem_comp_graph
    (β : FiniteCorrespondence X.hom V.hom) (q : V ⟶ W) (x : X.left) (T : Set V.left)
    (hT : ∀ A ∈ β.support, ∀ a : A.scheme,
      A.projection a = x → A.targetProjection a ∈ T)
    (B : FiniteCorrespondenceGenerator X.hom W.hom)
    (hB : B ∈ (β ≫ (Cor.graphFunctor k).map q).support)
    (z : B.scheme) (hz : B.projection z = x) : B.targetProjection z ∈ q.left '' T := by
  obtain ⟨A, hA, a, hs, ht⟩ := exists_support_point_lift_of_mem_comp_graph β q B hB z
  exact ⟨A.targetProjection a, hT A hA a (hs.trans hz), ht⟩

end FiniteCorrespondence
end Motivic
