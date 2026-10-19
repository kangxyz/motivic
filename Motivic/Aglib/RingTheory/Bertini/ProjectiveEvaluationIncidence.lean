/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.LinearIncidenceGenericFiber
public import Motivic.Aglib.RingTheory.Bertini.IncidenceCoefficientDimension
public import Motivic.Aglib.RingTheory.Bertini.IncidenceNonDominance

/-! # Actual linear-form evaluation incidence on a normalized projective chart -/
@[expose] public noncomputable section
open _root_.MvPolynomial
universe u
namespace ProjectiveEvaluationIncidence
variable (A : Type u) [CommRing A] {N : Type u} [Fintype N]

/-- Every row is one original linear form, evaluated at the actual chart coordinates. -/
def matrix (a : N → A) (n : ℕ) : Matrix (Fin n) (Fin n × N) A := by
  classical
  exact fun i q => if i = q.1 then a q.2 else 0

/-- The original normalized projective coordinate supplies a literal right inverse. -/
theorem matrix_surjective (a : N → A) (n : ℕ) (j : N) (hj : a j = 1) :
    Function.Surjective (matrix A a n).mulVec := by
  classical
  intro v
  refine ⟨fun q => if q.2 = j then v q.1 else 0, ?_⟩
  ext i
  simp [matrix, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, hj]

/-- The full incidence ring imposes all original homogeneous evaluations. -/
abbrev Ring (a : N → A) (n : ℕ) := LinearIncidence.CoordinateRing (matrix A a n)

/-- The same original coefficients define the parameter map. -/
def parameterMap (k : Type u) [CommRing k] [Algebra k A] (a : N → A) (n : ℕ) :
    MvPolynomial (Fin n × N) k →ₐ[k] Ring A a n :=
  aeval (LinearIncidence.coordinates (matrix A a n))

end ProjectiveEvaluationIncidence
