/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.QuadraticIncidencePointMap

/-! # Original parameter equations vanish at every genuine bad point

The parameter map uses the literal quotient variables. Its kernel equations
therefore exclude bad polynomial tuples at every field-valued chart point,
not merely at the initially selected point.
-/
@[expose] public noncomputable section
open Module TensorProduct KaehlerDifferential _root_.MvPolynomial
universe u
namespace QuadraticIncidence
variable (k R A : Type u) [CommRing k] [CommRing R] [CommRing A]
  [Algebra k R] [Algebra R A] [Algebra k A]
  {σ : Type u} [Fintype σ]

/-- The original ground-coefficient parameter map into the full incidence quotient. -/
def parameterMap (g : σ → R) (a : σ → A) (d : ℕ) (w : Fin d → A) :
    MvPolynomial (Fin d × Exponent σ) k →ₐ[k] CoordinateRing k R A g a d w :=
  aeval (LinearIncidence.coordinates (ProjectiveIncidence.coefficientMatrix (R := A)
    (coefficientVector k R A g a d w)))

variable (K : Type u) [Field K] [Algebra R K] [Algebra A K] [Algebra k K]
  [IsScalarTower R A K] [IsScalarTower k A K] [Algebra.Smooth k R]

/-- A full incidence kernel relation vanishes at the actual unchanged parameter
coefficients of any polynomial tuple with equal values and dependent gradients. -/
theorem parameter_relation_vanishes
    (g : σ → R) (a : σ → A) (d : ℕ) (w : Fin d → A)
    (p : Fin d → restrictTotalDegree σ K 2)
    (hvalue : ∀ i, eval (fun j => algebraMap R K (g j)) (p i).val =
      eval (algebraMap A K ∘ a) (p i).val)
    (hderiv : ∑ i, algebraMap A K (w i) • residueGeneratorGradient k R K g
      (fun j => eval (fun l => algebraMap R K (g l)) (pderiv j (p i).val)) = 0)
    (f : MvPolynomial (Fin d × Exponent σ) k)
    (hf : parameterMap k R A g a d w f = 0) :
    aeval (fun q => (parameterBasis K σ d).repr p q) f = 0 := by
  let h := pointMap k R A K g a d w p hvalue hderiv
  have he : aeval (fun q => (parameterBasis K σ d).repr p q) =
      (h.restrictScalars k).comp (parameterMap k R A g a d w) := by
    ext q
    simp [parameterMap, h]
  rw [he, AlgHom.comp_apply, hf, map_zero]

end QuadraticIncidence
