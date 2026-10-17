/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.ProjectiveEvaluationIncidence

/-! # The unchanged evaluation matrix remains split after coefficient extension -/
@[expose] public noncomputable section
universe u
namespace ProjectiveEvaluationIncidence
variable (A K : Type u) [CommRing A] [CommRing K] [Algebra A K]
  {N : Type u}

/-- Coefficient extension keeps every original evaluation row. -/
theorem matrix_map (a : N → A) (n : ℕ) :
    (matrix A a n).map (algebraMap A K) = matrix K (algebraMap A K ∘ a) n := by
  classical
  ext i q
  by_cases hi : i = q.1 <;> simp [matrix, Matrix.map_apply, hi]

variable [Fintype N]

/-- The literal unit pivot gives full row rank over every coefficient field. -/
theorem mapped_matrix_surjective (a : N → A) (n : ℕ) (j : N) (hj : a j = 1) :
    Function.Surjective ((matrix A a n).map (algebraMap A K)).mulVec := by
  rw [matrix_map]
  exact matrix_surjective K _ n j (by simp [hj])

end ProjectiveEvaluationIncidence
