/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.FiniteChart.CompactificationChart

/-! # The fixed-target source boundary from the original actual finite chart -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.EtaleCompactification
variable (X C : Scheme.{u}) [IsIntegral C] [IsLocallyNoetherian C]
  [∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x)]
  {Y S D : Scheme.{u}} (p : Y ⟶ X) [Etale p] [QuasiCompact p] [IsSeparated p]
  (j : X ⟶ C) [IsOpenImmersion j] [QuasiCompact j]
  (q : C ⟶ S) [IsProper q] (d : D ⟶ C) [IsFinite (d ≫ q)]
  (U : X.Opens) [IsFinite (p ∣_ U)]

/-- The original finite chart, rather than an identity for a newly computed finite locus,
controls the complete source normalization infinity. -/
theorem finite_source_infinity_over_finite_chart
    (hbad : (j ''ᵁ U : Set C)ᶜ ⊆ Set.range d) :
    IsFinite (infinityInclusion C (p ≫ j) ≫
      (genericMap C (p ≫ j)).fromNormalization ≫ q) := by
  have := finite_comp_pullback_open_image p j U
  exact finite_infinity_of_finite_target_boundary C (p ≫ j) q d (j ''ᵁ U) hbad

/-- The full original nonreduced source boundary is finite over the same base. -/
theorem finite_full_source_boundary_over_finite_chart
    (hbad : (j ''ᵁ U : Set C)ᶜ ⊆ Set.range d)
    {Z : Scheme.{u}} (s : Z ⟶ Y) [IsFinite (s ≫ p ≫ j ≫ q)] :
    IsFinite (boundaryInclusion C (p ≫ j) s ≫
      (genericMap C (p ≫ j)).fromNormalization ≫ q) := by
  have := finite_source_infinity_over_finite_chart X C p j q d U hbad
  have : IsFinite ((s ≫ inclusion C (p ≫ j)) ≫
      (genericMap C (p ≫ j)).fromNormalization ≫ q) := by
    simpa only [Category.assoc, reassoc_of% (inclusion_over C (p ≫ j))] using
      (inferInstance : IsFinite (s ≫ p ≫ j ≫ q))
  change IsFinite (coprod.desc _ _ ≫ _)
  rw [coprod.desc_comp]
  infer_instance

end AlgebraicGeometry.Scheme.EtaleCompactification
