/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.QuadraticParameterTuple

/-! # Literal coefficient extension of the original quadratic tuple -/
@[expose] public noncomputable section
open Module MvPolynomial
universe u
namespace QuadraticIncidence
variable {A B σ : Type u} [CommRing A] [CommRing B]

/-- Each original tuple basis polynomial is unchanged by coefficient extension. -/
theorem parameterBasis_map (f : A →+* B) (d : ℕ) (q : Fin d × Exponent σ) (i : Fin d) :
    MvPolynomial.map f (parameterBasis A σ d q i).val =
      (parameterBasis B σ d q i).val := by
  classical
  by_cases h : i = q.1
  · subst i
    simp only [parameterBasis_apply, Pi.single_eq_same, monomialBasis_coe,
      map_monomial, map_one]
  · simp [parameterBasis_apply, Pi.single_eq_of_ne h]

variable [Fintype σ]

/-- The tuple over any field of a moving point is literally the coefficient
extension of the one original ground-field polynomial tuple. -/
theorem parameterTuple_map (f : A →+* B) (d : ℕ)
    (c : Fin d × Exponent σ → A) (i : Fin d) :
    MvPolynomial.map f (parameterTuple A σ d c i).val =
      (parameterTuple B σ d (f ∘ c) i).val := by
  classical
  simp only [parameterTuple, Finset.sum_apply, Pi.smul_apply, Submodule.coe_sum,
    Submodule.coe_smul, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [smul_eq_C_mul, map_mul, map_C, parameterBasis_map, ← smul_eq_C_mul]
  rfl

end QuadraticIncidence
