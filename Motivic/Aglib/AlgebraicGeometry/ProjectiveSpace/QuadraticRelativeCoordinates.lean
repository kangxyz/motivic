/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.RelativePolynomialCoordinates
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.QuadraticZeroRow

/-! # The relative polynomial coordinate has exactly the original quadratic base map -/
@[expose] public noncomputable section
open MvPolynomial
universe u
namespace QuadraticIncidence.InfinityChart
variable (k B : Type u) [Field k] [CommRing B] [Algebra k B]
  {σ : Type u} [Fintype σ] (g : σ → B) (d : ℕ)

/-- Literal preservation of every original base function after adjoining the auxiliary row. -/
theorem originalFunction_prepend_succ (a : Exponent σ → k)
    (c : Fin d × Exponent σ → k) (i : Fin d) :
    aeval g (parameterTuple k σ (d + 1) (prependParameters k d a c) i.succ).val =
      aeval g (parameterTuple k σ d c i).val := by
  simp only [originalFunction_eq_sum_rows, prependParameters, Fin.cases_succ]

/-- The relative coordinate map, a canonical relabeling of the same finite full tuple. -/
def quadraticRelativeCoordinateHom (a : Exponent σ → k) (c : Fin d × Exponent σ → k) :
    Polynomial (MvPolynomial (Fin d) k) →+* B :=
  relativeCoordinateHom k B d
    (fun i => aeval g (parameterTuple k σ (d + 1) (prependParameters k d a c) i).val)

/-- Composing with constants retains the original base map exactly. -/
theorem quadraticRelativeCoordinateHom_comp_C
    (a : Exponent σ → k) (c : Fin d × Exponent σ → k) :
    (quadraticRelativeCoordinateHom k B g d a c).comp Polynomial.C =
      quadraticCoordinateHom k B g d c := by
  rw [quadraticRelativeCoordinateHom, relativeCoordinateHom_comp_C]
  congr 1
  ext i
  simpa only [aeval_X] using originalFunction_prepend_succ k B g d a c i

end QuadraticIncidence.InfinityChart
