/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.Laurent

/-! # Extracted ordinary primitive with the original parameters and maps -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
universe w u
namespace AlgebraicGeometry.Scheme.SmoothSite
/-- The original Laurent opens commute with the actual product maps of cylinders. -/
theorem contractionOpen_naturality (R : CommRingCat.{u})
    {X Y : SmoothSite (Spec R)} (f : X ⟶ Y) :
    contractionOpen R X ≫ a1Map R f =
      productMap f (𝟙 (torus R)) ≫ contractionOpen R Y := by
  change productMap (𝟙 X) (torusInAffineLine R) ≫ productMap f (𝟙 _) =
    productMap f (𝟙 _) ≫ productMap (𝟙 Y) (torusInAffineLine R)
  rw [← productMap_comp, ← productMap_comp]
  simp only [Category.id_comp, Category.comp_id]

end AlgebraicGeometry.Scheme.SmoothSite
