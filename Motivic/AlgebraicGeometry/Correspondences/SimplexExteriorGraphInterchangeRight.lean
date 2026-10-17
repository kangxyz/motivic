/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ComponentGraphComposition

/-!
# Postcomposition by actual component graph cycles

For an arbitrary integral correspondence support, composition with the full
component graph cycle is finite pushforward along its postcomposed support
map. The unique middle component meeting the support gives an incidence
isomorphism, while every other component has empty incidence. In particular,
the middle smooth scheme need not be integral or connected.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic

local instance {k : Type u} [Field k] (T : SmoothSite (Spec (.of k))) :
    IsNoetherian ((𝟭 Scheme).obj T.left) :=
  inferInstanceAs (IsNoetherian T.left)

local instance {k : Type u} [Field k] (T : SmoothSite (Spec (.of k))) :
    IsReduced ((𝟭 Scheme).obj T.left) :=
  inferInstanceAs (IsReduced T.left)

namespace FiniteCorrespondenceGenerator

variable (k : Type u) [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (ψ : Y.left ⟶ Z.left) (wψ : ψ ≫ Z.hom = Y.hom)

local instance supportIsNoetherian : IsNoetherian A.scheme :=
  isNoetherian_of_finiteType A.projection

/-- A compatible component graph pushes the original support's fundamental cycle
along the actual postcomposition map, retaining all residue-field degrees. -/
theorem toIntegralCycle_incidenceTorCorrespondence_componentGraph_right
    (D : Set Y.left) (hD : D ∈ irreducibleComponents Y.left)
    (hA : Set.range A.targetProjection ⊆ D) :
    FiniteCorrespondence.toIntegralCycle
      (A.incidenceTorCorrespondence k (Z := Z)
        (componentGraphGeneratorOver (X := Y.left) (Y := Z.left) ψ wψ D hD)) =
      IntegralCycle.finitePushforward (A.graphPostcompositionMap ψ wψ)
        (fundamentalCycle A.scheme) := by
  let B := componentGraphGeneratorOver (X := Y.left) (Y := Z.left) ψ wψ D hD
  have : IsIso (A.incidenceFst B) :=
    A.isIso_incidenceFst_componentGraph k ψ wψ D hD hA
  change FiniteCorrespondence.toIntegralCycle (A.incidenceTorCorrespondence k (Z := Z) B) = _
  rw [A.incidenceTorCorrespondence_eq_fundamental_of_isOpenImmersion_projection k B,
    A.toIntegralCycle_incidenceFundamentalCorrespondence k B]
  simp only [B, A.incidenceMap_componentGraph_right k ψ wψ D hD,
    IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
    finitePushforward_fundamentalCycle]

/-- Postcomposition with the full actual graph cycle is finite pushforward of the
original support, also for disconnected or empty middle smooth schemes. -/
theorem toIntegralCycle_incidenceTorPairing_componentGraph_right :
    FiniteCorrespondence.toIntegralCycle
      (FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z)
        A.cycle (componentGraphCycleOver (X := Y.left) (Y := Z.left) ψ wψ)) =
      IntegralCycle.finitePushforward (A.graphPostcompositionMap ψ wψ)
        (fundamentalCycle A.scheme) := by
  classical
  obtain ⟨D, hD, hA⟩ : ∃ D ∈ irreducibleComponents Y.left,
      Set.range A.targetProjection ⊆ D :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible
      (Set.range A.targetProjection) (by
        simpa only [Set.image_univ] using
          (IrreducibleSpace.isIrreducible_univ A.scheme).image
            A.targetProjection A.targetProjection.continuous.continuousOn)
  rw [componentGraphCycleOver_eq_sum]
  simp only [map_sum]
  rw [Finset.sum_eq_single (ι := Set Y.left) D]
  · rw [dite_eq_left hD, FiniteCorrespondence.incidenceTorPairing_cycle]
    exact A.toIntegralCycle_incidenceTorCorrespondence_componentGraph_right k ψ wψ D hD hA
  · intro E hE hED
    have hE' : E ∈ irreducibleComponents Y.left := by simpa using hE
    rw [dite_eq_left hE', FiniteCorrespondence.incidenceTorPairing_cycle,
      A.incidenceTorCorrespondence_componentGraph_right_of_ne k ψ wψ E D hE' hD hA hED.symm,
      map_zero]
  · intro hnot
    exact (hnot (by simpa using hD)).elim

end FiniteCorrespondenceGenerator

end Motivic
