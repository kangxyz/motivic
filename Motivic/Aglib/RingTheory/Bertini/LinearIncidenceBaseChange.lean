/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.LinearIncidenceAlgebra

/-! # Actual coefficient-field specialization of linear incidence equations -/
@[expose] public noncomputable section
open MvPolynomial
universe u v
namespace LinearIncidence
variable (A K E : Type u) [CommRing A] [CommRing K] [CommRing E]
  [Algebra A K] [Algebra A E] [Algebra K E] [IsScalarTower A K E]
  {N : Type u} {Q : Type v} [Fintype N]

/-- Specialization retains the images of all original parameter variables. -/
def specialize (M : Matrix Q N A) (h : CoordinateRing M →ₐ[A] E) :
    CoordinateRing (M.map (algebraMap A K)) →ₐ[K] E := by
  let x := fun n => h (coordinates M n)
  apply Ideal.Quotient.liftₐ _ (aeval x)
  intro f hf
  have hk : ideal (M.map (algebraMap A K)) ≤ RingHom.ker (aeval x).toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨q, rfl⟩
    change aeval x (equation (M.map (algebraMap A K)) q) = 0
    have hz := congrArg h (congrFun (equations_hold M) q)
    simpa [equation, x, Matrix.mulVec, dotProduct, Matrix.map_apply,
      IsScalarTower.algebraMap_apply A K E] using hz
  exact hk hf

@[simp]
theorem specialize_coordinates (M : Matrix Q N A) (h : CoordinateRing M →ₐ[A] E) (n : N) :
    specialize A K E M h (coordinates (M.map (algebraMap A K)) n) =
      h (coordinates M n) := by
  change aeval (fun n => h (coordinates M n)) (X n) = _
  exact aeval_X _ _

/-- The entire old incidence image lies in the new image, not only its variables. -/
theorem image_mem_specialize_range (M : Matrix Q N A)
    (h : CoordinateRing M →ₐ[A] E) (c : CoordinateRing M) :
    h c ∈ (specialize A K E M h).range := by
  let f := specialize A K E M h
  have ht : (⊤ : Subalgebra A (CoordinateRing M)) ≤
      (f.range.restrictScalars A).comap h := by
    rw [← adjoin_coordinates_eq_top M]
    apply Algebra.adjoin_le
    rintro _ ⟨n, rfl⟩
    exact ⟨_, specialize_coordinates A K E M h n⟩
  exact ht (show c ∈ (⊤ : Subalgebra A (CoordinateRing M)) from trivial)

end LinearIncidence
