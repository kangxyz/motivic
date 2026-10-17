/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.QuadraticIncidenceRank

/-! # The original quadratic polynomial tuple of a coefficient choice -/
@[expose] public noncomputable section
open Module MvPolynomial
universe u
namespace QuadraticIncidence

/-- The actual polynomial tuple in the fixed original monomial basis. -/
def parameterTuple (A : Type u) [CommRing A] (σ : Type u) [Fintype σ] (d : ℕ)
    (c : Fin d × Exponent σ → A) : Fin d → restrictTotalDegree σ A 2 :=
  ∑ q, c q • parameterBasis A σ d q

/-- The literal monomial parameters are recovered unchanged. -/
@[simp]
theorem parameterTuple_repr (A : Type u) [CommRing A] (σ : Type u) [Fintype σ]
    (d : ℕ) (c : Fin d × Exponent σ → A) (q : Fin d × Exponent σ) :
    (parameterBasis A σ d).repr (parameterTuple A σ d c) q = c q := by
  classical
  simp only [parameterTuple, map_sum, map_smul, Basis.repr_self]
  simp [Finsupp.single_apply]

end QuadraticIncidence
