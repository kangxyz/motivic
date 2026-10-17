/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.FiniteCommonImage
public import Mathlib.Data.ZMod.Basic

/-!
# A common image for two possibly nonreduced supports

The selected sources are arbitrary closed subschemes of Spec(Z/4). Neither the
sources nor the ambient scheme are required to be reduced or integral.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace MotivicTest.FiniteCommonImage

example (I : Fin 2 → (Spec (.of (ZMod 4))).IdealSheafData) :
    ∃ (C : Scheme) (j : C ⟶ Spec (.of (ZMod 4))),
      IsClosedImmersion j ∧ IsFinite j ∧
      ∀ i, ∃ r : (I i).subscheme ⟶ C, r ≫ j = (I i).subschemeι := by
  obtain ⟨C, j, hj, hfin, h⟩ := exists_finite_common_closed_image
    (fun i ↦ (I i).subscheme) (fun i ↦ (I i).subschemeι)
    (𝟙 (Spec (.of (ZMod 4)))) Finset.univ ⟨0, Finset.mem_univ 0⟩ (by
      intro i _
      simpa only [Category.comp_id] using (inferInstance : IsFinite (I i).subschemeι))
  refine ⟨C, j, hj, ?_, fun i ↦ h i (Finset.mem_univ i)⟩
  simpa only [Category.comp_id] using hfin

end MotivicTest.FiniteCommonImage
