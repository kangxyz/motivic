/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.Puncture.PointDiagrams

/-! # The actual pointed-puncture zero-section argument on filtered colimits

The punctured projection comparison remains an explicit geometric input.
This file does not establish bounded punctured descent.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Motivic.FiniteEtaleSite
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable (R : CommRingCat.{u}) {X U : SmoothSite (Spec R)} (j : U ⟶ X)
  (Φ : (nisnevichTopology X.left).Point.{u + 1})
  (P : (SmoothSite (Spec R))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

/-- The actual original restrictions and zero sections commute after the existing point colimit. -/
theorem pointedCylinderRestriction_zeroSection_colimit :
    colim.map (pointedCylinderRestriction R j Φ P) ≫
        colim.map (pointedZeroSection R Φ P (pointedPuncture R j Φ)) =
      colim.map (pointedZeroSection R Φ P (pointedBase R Φ)) ≫
        colim.map (pointedRestriction R j Φ P) := by
  rw [← CategoryTheory.Functor.map_comp, pointedCylinderRestriction_zeroSection]
  erw [CategoryTheory.Functor.map_comp]

/-- A punctured projection comparison and vanishing of the base germ force the original
cylinder restriction to vanish. The punctured comparison is not proved here. -/
theorem pointedCylinderRestriction_colimit_eq_zero
    (hbase : IsZero (colimit (pointedBaseValues R Φ P)))
    [IsIso (colim.map (pointedProjection R Φ P (pointedPuncture R j Φ)))] :
    colim.map (pointedCylinderRestriction R j Φ P) = 0 := by
  have hs : colim.map (pointedProjection R Φ P (pointedPuncture R j Φ)) ≫
      colim.map (pointedZeroSection R Φ P (pointedPuncture R j Φ)) = 𝟙 _ := by
    rw [← Functor.map_comp, pointedProjection_zeroSection, CategoryTheory.Functor.map_id]
  have hi : IsIso (colim.map (pointedZeroSection R Φ P (pointedPuncture R j Φ))) := by
    rw [IsIso.eq_inv_of_hom_inv_id hs]
    infer_instance
  apply (cancel_mono (colim.map (pointedZeroSection R Φ P (pointedPuncture R j Φ)))).mp
  rw [Limits.zero_comp, pointedCylinderRestriction_zeroSection_colimit]
  rw [hbase.eq_of_tgt (colim.map (pointedZeroSection R Φ P (pointedBase R Φ))) 0,
    Limits.zero_comp]

/-- If the actual puncture restriction is also injective, its original cylinder germ is zero. -/
theorem pointedCylinder_colimit_isZero
    (hbase : IsZero (colimit (pointedBaseValues R Φ P)))
    [IsIso (colim.map (pointedProjection R Φ P (pointedPuncture R j Φ)))]
    [Mono (colim.map (pointedCylinderRestriction R j Φ P))] :
    IsZero (colimit (pointedCylinderValues R Φ P (pointedBase R Φ))) := by
  have h := pointedCylinderRestriction_colimit_eq_zero R j Φ P hbase
  exact (IsZero.iff_id_eq_zero _).mpr ((cancel_mono
    (colim.map (pointedCylinderRestriction R j Φ P))).mp (by
      simpa only [Category.id_comp, Limits.zero_comp] using h))

end Motivic.FiniteEtaleSite
