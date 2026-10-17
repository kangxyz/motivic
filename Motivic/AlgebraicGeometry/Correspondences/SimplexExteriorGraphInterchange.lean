/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.SimplexExteriorGraphInterchangeStalks
public import Motivic.AlgebraicGeometry.Correspondences.SimplexExteriorGraphInterchangeIncidence
public import Motivic.AlgebraicGeometry.Correspondences.SimplexExteriorGraphInterchangeRight
public import Motivic.AlgebraicGeometry.Correspondences.SimplexExterior
public import Motivic.AlgebraicGeometry.Correspondences.GraphFunctor

/-!
# Mixed graph interchange for actual signed exterior correspondences

An arbitrary morphism between geometrically integral smooth parameter schemes
commutes with exterior extension of a finite correspondence. Both sides use
the actual component graph cycles and genuine incidence Tor composition.
The common finite pushforward preserves the full support fundamental cycle,
including residue degrees and coincident images. In particular the result
applies to every original map of barycentric algebraic simplices.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic

local instance {k : Type u} [Field k] (T : SmoothSite (Spec (.of k))) :
    IsNoetherian ((𝟭 Scheme).obj T.left) :=
  inferInstanceAs (IsNoetherian T.left)

local instance {k : Type u} [Field k] (T : SmoothSite (Spec (.of k))) :
    IsReduced ((𝟭 Scheme).obj T.left) :=
  inferInstanceAs (IsReduced T.left)

namespace SimplexExteriorGraph

variable {k : Type u} [Field k] {X Y T T' : SmoothSite (Spec (.of k))}
  (u : T ⟶ T') (V : FiniteCorrespondenceGenerator X.hom Y.hom)
  [GeometricallyIntegral T.hom] [GeometricallyIntegral T'.hom]

/-- A compatible actual graph component has the same full pushed support cycle
as exterior postcomposition on the other side. -/
theorem toIntegralCycle_incidenceTorCorrespondence
    (A : FiniteCorrespondenceGenerator (SmoothSite.product X T).hom
      (SmoothSite.product X T').hom) [IsOpenImmersion A.projection]
    (hA : A.projection ≫ (SmoothSite.productMap (𝟙 X) u).left = A.targetProjection)
    (hRange : Set.range (V.exteriorIdentitySource T) ⊆ Set.range A.projection) :
    FiniteCorrespondence.toIntegralCycle
      (f := (SmoothSite.product X T).hom) (g := (SmoothSite.product Y T').hom)
      (A.incidenceTorCorrespondence k (X := SmoothSite.product X T)
        (Y := SmoothSite.product X T') (Z := SmoothSite.product Y T')
        (V.exteriorIdentityGenerator T')) =
        IntegralCycle.finitePushforward
          ((V.exteriorIdentityGenerator T).graphPostcompositionMap
            (SmoothSite.productMap (𝟙 Y) u).left
            (MorphismProperty.Over.w (SmoothSite.productMap (𝟙 Y) u)))
          (fundamentalCycle (V.exteriorIdentityGenerator T).scheme) := by
  have : IsNoetherian (V.exteriorIdentityGenerator T).scheme :=
    isNoetherian_of_finiteType (V.exteriorIdentityGenerator T).projection
  rw [incidenceTorCorrespondence_eq_fundamental u V A hA,
    A.toIntegralCycle_incidenceFundamentalCorrespondence k]
  rw [← finitePushforward_fundamentalCycle (exteriorIncidenceIso u V A hA hRange).hom]
  rw [← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp]
  simp only [exteriorIncidenceIso_hom_incidenceMap u V A hA hRange,
    IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
    finitePushforward_fundamentalCycle]

/-- Summing the actual graph components retains precisely the exterior source component. -/
theorem toIntegralCycle_incidenceTorPairing_componentGraph_left :
    FiniteCorrespondence.toIntegralCycle
      (FiniteCorrespondence.incidenceTorPairing k
        (X := SmoothSite.product X T) (Y := SmoothSite.product X T')
        (Z := SmoothSite.product Y T')
        (componentGraphCycleOver (X := (SmoothSite.product X T).left)
          (Y := (SmoothSite.product X T').left) (SmoothSite.productMap (𝟙 X) u).left
          (MorphismProperty.Over.w (SmoothSite.productMap (𝟙 X) u)))
        (V.exteriorIdentityGenerator T').cycle) =
      IntegralCycle.finitePushforward
        ((V.exteriorIdentityGenerator T).graphPostcompositionMap
          (SmoothSite.productMap (𝟙 Y) u).left
          (MorphismProperty.Over.w (SmoothSite.productMap (𝟙 Y) u)))
        (fundamentalCycle (V.exteriorIdentityGenerator T).scheme) := by
  classical
  have hC := V.exteriorIdentitySource_range_mem T
  change FiniteCorrespondence.toIntegralCycle
    ((FiniteCorrespondence.incidenceTorPairing k
      (X := SmoothSite.product X T) (Y := SmoothSite.product X T')
      (Z := SmoothSite.product Y T')).flip (V.exteriorIdentityGenerator T').cycle _) = _
  rw [componentGraphCycleOver_eq_sum]
  simp only [map_sum]
  rw [Finset.sum_eq_single (ι := Set (SmoothSite.product X T).left)
    (Set.range (V.exteriorIdentitySource T))]
  · rw [dite_eq_left hC]
    change FiniteCorrespondence.toIntegralCycle
      (FiniteCorrespondence.incidenceTorPairing k (X := SmoothSite.product X T)
        (Y := SmoothSite.product X T') (Z := SmoothSite.product Y T') _ _) = _
    rw [FiniteCorrespondence.incidenceTorPairing_cycle]
    apply toIntegralCycle_incidenceTorCorrespondence u V
    · exact componentGraphGeneratorOver_projection_target _ _ _ _
    · rw [componentGraphGeneratorOver_range]
  · intro D hD hDC
    have hD' : D ∈ irreducibleComponents (SmoothSite.product X T).left := by simpa using hD
    rw [dite_eq_left hD']
    change FiniteCorrespondence.toIntegralCycle
      (FiniteCorrespondence.incidenceTorPairing k (X := SmoothSite.product X T)
        (Y := SmoothSite.product X T') (Z := SmoothSite.product Y T') _ _) = 0
    rw [FiniteCorrespondence.incidenceTorPairing_cycle]
    rw [incidenceTorCorrespondence_eq_zero_of_source_ne u V _
      (componentGraphGeneratorOver_projection_target _ _ _ _)
      (by simpa only [componentGraphGeneratorOver_range] using hDC), map_zero]
  · intro hnot
    exact (hnot (by simpa using hC)).elim

end SimplexExteriorGraph

namespace FiniteCorrespondence

variable {k : Type u} [Field k] {X Y T T' : SmoothSite (Spec (.of k))}
  (u : T ⟶ T') [GeometricallyIntegral T.hom] [GeometricallyIntegral T'.hom]

/-- The mixed graph law on a genuine unit support cycle. -/
theorem exteriorIdentity_graph_interchange_cycle
    (V : FiniteCorrespondenceGenerator X.hom Y.hom) :
    incidenceTorPairing k (X := SmoothSite.product X T) (Y := SmoothSite.product Y T)
      (Z := SmoothSite.product Y T') (exteriorIdentity (X := X) (Y := Y) T V.cycle)
      (componentGraphCycleOver (X := (SmoothSite.product Y T).left)
        (Y := (SmoothSite.product Y T').left) (SmoothSite.productMap (𝟙 Y) u).left
        (MorphismProperty.Over.w (SmoothSite.productMap (𝟙 Y) u))) =
    incidenceTorPairing k (X := SmoothSite.product X T) (Y := SmoothSite.product X T')
      (Z := SmoothSite.product Y T')
      (componentGraphCycleOver (X := (SmoothSite.product X T).left)
        (Y := (SmoothSite.product X T').left) (SmoothSite.productMap (𝟙 X) u).left
        (MorphismProperty.Over.w (SmoothSite.productMap (𝟙 X) u)))
      (exteriorIdentity (X := X) (Y := Y) T' V.cycle) := by
  simp only [exteriorIdentity_cycle]
  apply toIntegralCycle_injective
  rw [(V.exteriorIdentityGenerator T).toIntegralCycle_incidenceTorPairing_componentGraph_right
    k (SmoothSite.productMap (𝟙 Y) u).left
      (MorphismProperty.Over.w (SmoothSite.productMap (𝟙 Y) u)),
    SimplexExteriorGraph.toIntegralCycle_incidenceTorPairing_componentGraph_left u V]

/-- Exterior extension intertwines every parameter graph on all actual signed cycles. -/
theorem exteriorIdentity_graph_interchange (α : FiniteCorrespondence X.hom Y.hom) :
    incidenceTorPairing k (X := SmoothSite.product X T) (Y := SmoothSite.product Y T)
      (Z := SmoothSite.product Y T') (exteriorIdentity (X := X) (Y := Y) T α)
      (componentGraphCycleOver (X := (SmoothSite.product Y T).left)
        (Y := (SmoothSite.product Y T').left) (SmoothSite.productMap (𝟙 Y) u).left
        (MorphismProperty.Over.w (SmoothSite.productMap (𝟙 Y) u))) =
    incidenceTorPairing k (X := SmoothSite.product X T) (Y := SmoothSite.product X T')
      (Z := SmoothSite.product Y T')
      (componentGraphCycleOver (X := (SmoothSite.product X T).left)
        (Y := (SmoothSite.product X T').left) (SmoothSite.productMap (𝟙 X) u).left
        (MorphismProperty.Over.w (SmoothSite.productMap (𝟙 X) u)))
      (exteriorIdentity (X := X) (Y := Y) T' α) := by
  have heq :
      ((incidenceTorPairing k (X := SmoothSite.product X T) (Y := SmoothSite.product Y T)
        (Z := SmoothSite.product Y T')).flip
        (componentGraphCycleOver (X := (SmoothSite.product Y T).left)
          (Y := (SmoothSite.product Y T').left) (SmoothSite.productMap (𝟙 Y) u).left
          (MorphismProperty.Over.w (SmoothSite.productMap (𝟙 Y) u)))).comp
          (exteriorIdentity (X := X) (Y := Y) T) =
      (incidenceTorPairing k (X := SmoothSite.product X T) (Y := SmoothSite.product X T')
        (Z := SmoothSite.product Y T')
        (componentGraphCycleOver (X := (SmoothSite.product X T).left)
          (Y := (SmoothSite.product X T').left) (SmoothSite.productMap (𝟙 X) u).left
          (MorphismProperty.Over.w (SmoothSite.productMap (𝟙 X) u)))).comp
            (exteriorIdentity (X := X) (Y := Y) T') := by
    apply Finsupp.addHom_ext
    intro V n
    have hsingle : Finsupp.single V n = n • V.cycle := by
      simp [FiniteCorrespondenceGenerator.cycle]
    simp only [hsingle, map_zsmul, AddMonoidHom.comp_apply, AddMonoidHom.flip_apply]
    rw [exteriorIdentity_graph_interchange_cycle u V]
  exact congrArg (fun F => F α) heq

end FiniteCorrespondence

namespace Cor

variable {k : Type u} [Field k] {X Y : Cor k} {n m : ℕ}

/-- Every original smooth-site map of actual simplices commutes with signed exterior cycles. -/
theorem simplexExterior_graph_interchange
    (u : AlgebraicSimplex.smoothSiteObj k n ⟶ AlgebraicSimplex.smoothSiteObj k m)
    (α : X ⟶ Y) :
    simplexExterior n α ≫
      (graphFunctor k).map (SmoothSite.productMap (𝟙 Y.toSmoothSite) u) =
      (graphFunctor k).map (SmoothSite.productMap (𝟙 X.toSmoothSite) u) ≫
        simplexExterior m α :=
  FiniteCorrespondence.exteriorIdentity_graph_interchange u α

end Cor

end Motivic
