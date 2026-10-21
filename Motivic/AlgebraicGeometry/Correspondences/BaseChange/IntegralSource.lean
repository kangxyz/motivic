/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Generators.BaseField

/-! # Actual correspondences from integral sources to the base

The original generator type has one element, the graph of the structure map.
This applies to all integral smooth affine sources, not only field points.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic

variable {S X : Scheme.{u}} [IsIntegral X] (f : X ⟶ S)

/-- The sole actual generator from an integral source to its base. -/
def structureGraphGenerator : FiniteCorrespondenceGenerator f (𝟙 S) :=
  graphGeneratorOver f (Category.comp_id f)

/-- Every actual closed support over the base is the structure graph. -/
theorem FiniteCorrespondenceGenerator.eq_structureGraphGenerator
    (A : FiniteCorrespondenceGenerator f (𝟙 S)) : A = structureGraphGenerator f := by
  apply eq_of_graph_range_eq f (Category.comp_id f)
  · simpa only [Category.comp_id] using A.projection_base
  · exact graphGeneratorOver_projection_target f (Category.comp_id f)
  · rw [Set.range_eq_univ.mpr A.projection_surjective,
      Set.range_eq_univ.mpr (structureGraphGenerator f).projection_surjective]

/-- Only one integral support can occur in the original correspondence group. -/
theorem structureGenerator_subsingleton :
    Subsingleton (FiniteCorrespondenceGenerator f (𝟙 S)) :=
  ⟨fun A B => (A.eq_structureGraphGenerator f).trans (B.eq_structureGraphGenerator f).symm⟩

/-- An actual signed correspondence to the base is its sole coefficient times the graph. -/
theorem FiniteCorrespondence.eq_coefficient_zsmul_structureGraph
    (a : FiniteCorrespondence f (𝟙 S)) :
    a = a (structureGraphGenerator f) • (structureGraphGenerator f).cycle := by
  ext A
  rw [A.eq_structureGraphGenerator f]
  simp

/-- The actual correspondence group is canonically the integers via the graph coefficient. -/
def structureCorrespondenceEquiv : FiniteCorrespondence f (𝟙 S) ≃+ ℤ where
  toFun a := a (structureGraphGenerator f)
  invFun n := n • (structureGraphGenerator f).cycle
  left_inv a := (a.eq_coefficient_zsmul_structureGraph f).symm
  right_inv n := by simp
  map_add' a b := rfl

end Motivic
