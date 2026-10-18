/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ForgetBaseCycle
public import Motivic.AlgebraicGeometry.Correspondences.SimplexExteriorGraph

/-! # Original component graphs under forgetting a separated base -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped BigOperators

universe u

namespace Motivic

variable {S T X Y : Scheme.{u}} (r : T ⟶ S) {f : X ⟶ T} {g : Y ⟶ T}
  [IsSeparated r] [LocallyOfFiniteType r] [IsSeparated g] [LocallyOfFiniteType g]
  [IsNoetherian X] [IsReduced X] (a : X ⟶ Y) (ha : a ≫ g = f)

namespace FiniteCorrespondenceGenerator

/-- Every source component gives exactly its original graph after forgetting the base. -/
theorem forgetBase_componentGraphGeneratorOver
    (C : Set X) (hC : C ∈ irreducibleComponents X) :
    (componentGraphGeneratorOver a ha C hC).forgetBase r =
      componentGraphGeneratorOver a
        (show a ≫ (g ≫ r) = f ≫ r by rw [← Category.assoc, ha]) C hC := by
  apply eq_of_graph_range_eq a (show a ≫ (g ≫ r) = f ≫ r by rw [← Category.assoc, ha])
  · exact forgetBase_projection_target r _ a
      (componentGraphGeneratorOver_projection_target a ha C hC)
  · exact componentGraphGeneratorOver_projection_target _ _ _ _
  · rw [forgetBase_range_projection, componentGraphGeneratorOver_range,
      componentGraphGeneratorOver_range]

end FiniteCorrespondenceGenerator

namespace FiniteCorrespondence

/-- The entire original graph cycle is preserved, including empty and disconnected sources. -/
theorem forgetBase_componentGraphCycleOver :
    forgetBase r f g (componentGraphCycleOver a ha) =
      componentGraphCycleOver a
        (show a ≫ (g ≫ r) = f ≫ r by rw [← Category.assoc, ha]) := by
  classical
  rw [componentGraphCycleOver_eq_sum, componentGraphCycleOver_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro C _
  split_ifs with hC
  · simp only [FiniteCorrespondenceGenerator.cycle, forgetBase_single,
      FiniteCorrespondenceGenerator.forgetBase_componentGraphGeneratorOver]
  · exact map_zero _

end FiniteCorrespondence

end Motivic
