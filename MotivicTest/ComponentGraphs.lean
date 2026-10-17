/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ComponentGraphs

/-!
# Consumers of componentwise graph correspondences

These tests retain arbitrary reduced Noetherian sources in their types. They
check finite projection, literal component support, distinct generators and
multiplicity one without assuming the source connected or integral. A final
consumer checks agreement with the original graph for integral sources.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Motivic

universe u

namespace MotivicTest.ComponentGraphs

variable {S X Y : Scheme.{u}} (φ : X ⟶ Y) (g : Y ⟶ S)
  [IsNoetherian X] [IsSeparated g]

section Reduced

variable [IsReduced X] (Z W : Set X) (hZ : Z ∈ irreducibleComponents X)
  (hW : W ∈ irreducibleComponents X)

/-- The geometric support is the given source component, with finite projection. -/
theorem finite_with_literal_image :
    IsFinite (componentGraphGenerator φ g Z hZ).projection ∧
      Set.range (componentGraphGenerator φ g Z hZ).projection = Z :=
  ⟨inferInstance, componentGraphGenerator_range φ g Z hZ⟩

/-- The cycle does not identify distinct source components. -/
theorem separates_components (h : Z ≠ W) :
    componentGraphGenerator φ g Z hZ ≠ componentGraphGenerator φ g W hW := by
  simpa using h

/-- A specified component has exactly its reduced graph multiplicity. -/
theorem component_multiplicity :
    componentGraphCycle φ g (componentGraphGenerator φ g Z hZ) = 1 :=
  componentGraphCycle_coefficient φ g Z hZ

end Reduced

/-- Integral sources recover the original graph cycle. -/
theorem integral_agreement [IsIntegral X] :
    componentGraphCycle φ g = graphCycle φ g :=
  componentGraphCycle_eq_graphCycle φ g

end MotivicTest.ComponentGraphs
