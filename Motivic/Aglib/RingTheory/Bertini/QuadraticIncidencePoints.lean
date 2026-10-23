/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.QuadraticIncidenceRank
public import Motivic.Aglib.RingTheory.Bertini.QuadraticIncidenceBaseChange

/-! # Actual polynomial points of the universal incidence quotient

Monomial coefficients satisfy the universal equations precisely because the
original polynomial values and weighted differentials do. No relation on a
separately chosen matrix is imposed.
-/
@[expose] public noncomputable section
open Module TensorProduct KaehlerDifferential _root_.MvPolynomial LinearMap
universe u
namespace QuadraticIncidence
variable (k R K : Type u) [CommRing k] [CommRing R] [Field K]
  [Algebra k R] [Algebra R K] {σ : Type u} [Fintype σ]

/-- Monomial expansion carries the literal coefficient vectors to the original
value and cotangent constraints. -/
theorem sum_parameterCoefficients_smul (g : σ → R) (a : σ → K)
    (d : ℕ) (w : Fin d → K) (p : Fin d → restrictTotalDegree σ K 2) :
    (∑ q, (parameterBasis K σ d).repr p q • coefficientVector k R K g a d w q) =
      normalizedJetConstraints
        (quadraticResidueJet k R K g a (fun i => algebraMap R K (g i))) w p := by
  let J := normalizedJetConstraints
    (quadraticResidueJet k R K g a (fun i => algebraMap R K (g i))) w
  have hv (q : Fin d × Exponent σ) :
      coefficientVector k R K g a d w q = J (parameterBasis K σ d q) := by
    simpa [J] using coefficientVector_eq_constraint k R K g a d w q
  simp_rw [hv, ← map_smul]
  rw [← map_sum, (parameterBasis K σ d).sum_repr]

/-- The original values and weighted differentials force the actual coefficient
vector equation over the field of the moving point. -/
theorem sum_parameterCoefficients_eq_zero (g : σ → R) (a : σ → K)
    (d : ℕ) (w : Fin d → K) (p : Fin d → restrictTotalDegree σ K 2)
    (hvalue : ∀ i, eval (fun j => algebraMap R K (g j)) (p i).val = eval a (p i).val)
    (hderiv : ∑ i, w i • residueGeneratorGradient k R K g
      (fun j => eval (fun l => algebraMap R K (g l)) (pderiv j (p i).val)) = 0) :
    (∑ q, (parameterBasis K σ d).repr p q • coefficientVector k R K g a d w q) = 0 := by
  rw [sum_parameterCoefficients_smul]
  apply Prod.ext
  · ext i
    exact sub_eq_zero.mpr (hvalue i)
  · exact hderiv

end QuadraticIncidence
