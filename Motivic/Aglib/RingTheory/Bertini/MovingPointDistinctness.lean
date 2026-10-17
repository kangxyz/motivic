/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.NormalizedMovingPointEvaluation

/-! # The original selected and moving coordinates are distinct on every chart -/
@[expose] public noncomputable section
namespace QuadraticIncidence.MovingPointChart
universe u
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
  {σ : Type u}

/-- Inverting the literal original coordinate difference excludes the diagonal
in every field extension of the chart, with the original structural maps. -/
theorem selected_ne_moving (g : σ → R) (a : σ → B) (d : ℕ) (i₀ : Fin d) (j : σ)
    (K : Type u) [Field K] [Algebra R K] [Algebra B K]
    [Algebra (Ring B d i₀ (algebraMap R B (g j) - a j)) K]
    [IsScalarTower R B K]
    [IsScalarTower B (Ring B d i₀ (algebraMap R B (g j) - a j)) K] :
    algebraMap (Ring B d i₀ (algebraMap R B (g j) - a j)) K ∘
      (algebraMap B (Ring B d i₀ (algebraMap R B (g j) - a j)) ∘ a) ≠
        fun i => algebraMap R K (g i) := by
  let A := Ring B d i₀ (algebraMap R B (g j) - a j)
  intro h
  have hj := congrFun h j
  have ht := difference_ne_zero B d i₀ (algebraMap R B (g j) - a j) K
  apply ht
  rw [map_sub, ← IsScalarTower.algebraMap_apply R B K]
  have he : algebraMap B K (a j) = algebraMap R K (g j) := by
    exact (IsScalarTower.algebraMap_apply B A K (a j)).trans hj
  rw [he, sub_self]

end QuadraticIncidence.MovingPointChart
