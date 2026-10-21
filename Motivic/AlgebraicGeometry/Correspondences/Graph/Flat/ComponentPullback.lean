/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Graph.Flat.SourceTor
public import Motivic.AlgebraicGeometry.Correspondences.Graph.Components.Pullback

/-! # Whole flat graph pullbacks, including disconnected sources -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (φ : X.left ⟶ Y.left) (wφ : φ ≫ Y.hom = X.hom)

local instance : IsNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsNoetherian X.left)
local instance : IsReduced ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsReduced X.left)

instance componentGraphPullbackMap_finite
    (C : Set X.left) (hC : C ∈ irreducibleComponents X.left) :
    IsFinite (B.componentGraphPullbackMap φ wφ C hC) := by
  unfold componentGraphPullbackMap
  exact MorphismProperty.pullbackMap (P := @IsFinite)
    (inferInstanceAs (IsFinite (componentGraphGeneratorOver φ wφ C hC).projection))
    (inferInstanceAs (IsFinite (𝟙 B.scheme)))
    (componentGraphGeneratorOver_projection_target φ wφ C hC).symm (by simp)

/-- The actual incidence portion is exactly the clopen source-component portion. -/
theorem componentGraphPullbackMap_range
    (C : Set X.left) (hC : C ∈ irreducibleComponents X.left) :
    Set.range (B.componentGraphPullbackMap φ wφ C hC) =
      (pullback.fst φ B.projection) ⁻¹' C := by
  unfold componentGraphPullbackMap
  rw [Scheme.Pullback.range_map]
  ext z
  rw [Set.mem_inter_iff]
  rw [componentGraphGeneratorOver_range]
  exact and_iff_left ⟨pullback.snd φ B.projection z, rfl⟩

open Classical in
/-- Clopen restriction leaves every original stalk multiplicity unchanged. -/
theorem componentGraphPullback_coefficient
    (C : Set X.left) (hC : C ∈ irreducibleComponents X.left)
    (z : B.graphPullback φ) :
    IntegralCycle.toPoints
      (IntegralCycle.finitePushforward (B.componentGraphPullbackMap φ wφ C hC)
        (fundamentalCycle ((componentGraphGeneratorOver φ wφ C hC).incidence B))) z =
      if pullback.fst φ B.projection z ∈ C then fundamentalPointCycle (B.graphPullback φ) z
      else 0 := by
  classical
  let j := B.componentGraphPullbackMap φ wφ C hC
  rw [IntegralCycle.toPoints_finitePushforward_apply, toPoints_fundamentalCycle,
    residuePushforward_eq_mapDomain_of_surjectiveOnStalks]
  change Finsupp.mapDomain j _ z = _
  by_cases hz : z ∈ Set.range j
  · obtain ⟨t, rfl⟩ := hz
    have hm : pullback.fst φ B.projection (j t) ∈ C := by
      rw [← Set.mem_preimage, ← B.componentGraphPullbackMap_range φ wφ C hC]
      exact Set.mem_range_self t
    rw [ite_eq_left hm, Finsupp.mapDomain_apply_of_injective j.isOpenEmbedding.injective]
    simp only [fundamentalPointCycle_apply]
    have hg : j t ∈ genericPoints (B.graphPullback φ) ↔
        t ∈ genericPoints ((componentGraphGeneratorOver φ wφ C hC).incidence B) :=
      ⟨mem_genericPoints_of_isOpenImmersion j t,
        mem_genericPoints_of_generalizing j (Flat.generalizingMap j) t⟩
    by_cases ht : t ∈ genericPoints ((componentGraphGeneratorOver φ wφ C hC).incidence B)
    · rw [dite_eq_left ht, dite_eq_left (hg.mpr ht)]
      exact congrArg (fun l => (l.toNat : ℤ)) (stalk_length_eq_of_isOpenImmersion j t).symm
    · rw [dite_eq_right ht, dite_eq_right (fun hj => ht (hg.mp hj))]
  · rw [Finsupp.mapDomain_of_notMem_range _ _ hz, ite_eq_right]
    exact fun hm => hz (by
      rw [B.componentGraphPullbackMap_range φ wφ C hC]
      exact hm)


open Classical in
/-- All disjoint source portions reconstruct the whole, unreduced pullback. -/
theorem fundamentalCycle_graphPullback_eq_sum :
    fundamentalCycle (B.graphPullback φ) =
      ∑ C ∈ (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
        (α := X.left)).toFinset,
        if hC : C ∈ irreducibleComponents X.left then
          IntegralCycle.finitePushforward (B.componentGraphPullbackMap φ wφ C hC)
            (fundamentalCycle ((componentGraphGeneratorOver φ wφ C hC).incidence B))
        else 0 := by
  classical
  apply IntegralCycle.toPoints_injective
  ext z
  simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, toPoints_fundamentalCycle]
  obtain ⟨C, hC, hz⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    {pullback.fst φ B.projection z} (isIrreducible_singleton)
  have hzC := hz (Set.mem_singleton _)
  rw [Finset.sum_eq_single C]
  · rw [dite_eq_left hC, B.componentGraphPullback_coefficient φ wφ C hC z,
      ite_eq_left hzC]
  · intro E hE hEC
    have hE' : E ∈ irreducibleComponents X.left := by simpa using hE
    rw [dite_eq_left hE', B.componentGraphPullback_coefficient φ wφ E hE' z,
      ite_eq_right]
    exact fun hzE => hEC (irreducibleComponents_eq_of_mem_of_domain_stalks
      (fun x => SmoothSite.isDomain_stalk k X x) hE' hC hzE hzC)
  · intro hnot
    exact (hnot (by simpa using hC)).elim

instance componentGraph_target_flat [Flat φ]
    (C : Set X.left) (hC : C ∈ irreducibleComponents X.left) :
    Flat (componentGraphGeneratorOver φ wφ C hC).targetProjection := by
  rw [← componentGraphGeneratorOver_projection_target]
  infer_instance

/-- Flat graph precomposition is the entire support pullback, for disconnected sources. -/
theorem toIntegralCycle_graphFunctor_comp_of_flat (α : X ⟶ Y) [Flat α.left] :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Z.hom)
      ((Cor.graphFunctor k).map α ≫ (show Cor.mk Y ⟶ Cor.mk Z from B.cycle)) =
      IntegralCycle.finitePushforward (B.graphPullbackMap α.left (MorphismProperty.Over.w α))
        (fundamentalCycle (B.graphPullback α.left)) := by
  classical
  change FiniteCorrespondence.toIntegralCycle
    ((FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z)).flip B.cycle
      (componentGraphCycleOver α.left (MorphismProperty.Over.w α))) = _
  rw [componentGraphCycleOver_eq_sum, map_sum, map_sum,
    B.fundamentalCycle_graphPullback_eq_sum α.left (MorphismProperty.Over.w α), map_sum]
  apply Finset.sum_congr rfl
  intro C hC
  have hC' : C ∈ irreducibleComponents X.left := by simpa using hC
  have hC'' : C ∈ irreducibleComponents ((𝟭 Scheme).obj X.left) := hC'
  rw [dite_eq_left hC'', dite_eq_left hC']
  change FiniteCorrespondence.toIntegralCycle
    (FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z) _ B.cycle) = _
  rw [FiniteCorrespondence.incidenceTorPairing_cycle,
    incidenceTorCorrespondence_eq_fundamental_of_flat_targetProjection,
    toIntegralCycle_incidenceFundamentalCorrespondence,
    ← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp]
  simp only [B.componentGraphPullbackMap_incidenceMap]

end Motivic.FiniteCorrespondenceGenerator
